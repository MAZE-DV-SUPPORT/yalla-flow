"""Dial Flow â€” Arabic+English dictation with a GPU-composited web UI.

Architecture: Python engine (recording, Cohere transcription, Flow cleanup,
hotkeys, tray, chimes) + pywebview/WebView2 frontend (web/index.html) for
true 60fps animation. Config lives in %APPDATA%\\ArabicDictation (frozen)
or the project dir (dev). Errors go to app.log.
"""

import base64
import ctypes
import glob
import hashlib
import io
import json
import concurrent.futures as cf
import logging
import math
import os
import queue
import re
import sys
import threading
import shutil
import time
import wave
import webbrowser
import winreg
import winsound
from datetime import datetime

import keyboard
import numpy as np
import pyperclip
import pystray
import requests
import sounddevice as sd
import soundfile as sf
import webview
from dotenv import load_dotenv
from PIL import Image

APP_DIR = os.path.dirname(os.path.abspath(__file__))
if getattr(sys, "frozen", False):
    RESOURCE_DIR = sys._MEIPASS
    CONFIG_DIR = os.path.join(os.environ.get("APPDATA", APP_DIR), "DialFlow")
else:
    RESOURCE_DIR = APP_DIR
    CONFIG_DIR = APP_DIR
os.makedirs(CONFIG_DIR, exist_ok=True)
# one-time migration from the Yalla Flow era: carry over key, settings and
# history so nobody re-onboards after the rename
_LEGACY_DIR = os.path.join(os.environ.get("APPDATA", ""), "ArabicDictation")
if (getattr(sys, "frozen", False)
        and not os.path.exists(os.path.join(CONFIG_DIR, ".env"))
        and os.path.isdir(_LEGACY_DIR)):
    for _f in (".env", "settings.json", "history.json"):
        _src = os.path.join(_LEGACY_DIR, _f)
        if os.path.exists(_src):
            try:
                shutil.copyfile(_src, os.path.join(CONFIG_DIR, _f))
            except OSError:
                pass

APP_VERSION = "5.4.0"
PILL_W, PILL_H = 150, 38    # expanded (recording/processing)
MINI_W, MINI_H = 76, 16     # idle: the edge tab, flush to the docked edge
HOVER_W, HOVER_H = 190, 46  # hovered: status text + cancel / open controls
PANEL_W, PANEL_H = 232, 150  # expanded popup: status + dock picker
# Docked to a side everything stands up â€” including HOVER. A wide hover box
# on a side dock was shorter than the upright bar it grew from, so the window
# shrank vertically out from under the cursor: mouseleave fired, the pill
# shrank back, the cursor was inside again, mouseenter fired. That loop is
# what made the side buttons unclickable. Every grown size below CONTAINS
# the size it grows from, on both axes â€” see _grow_to_contain.
VPILL_W, VPILL_H = 38, 150
VMINI_W, VMINI_H = 16, 76
VHOVER_W, VHOVER_H = 54, 178
PILL_PAD = 0                # flush: the tab is a handle ON the edge
DOCKS = ("left", "bottom", "right")
PILL_BG = "#171320"  # warm plum-black â€” matches the app's dark identity
UPDATE_API = "https://api.github.com/repos/Dialverse-ai/dial-flow/releases/latest"
UPDATE_EVERY_H = 6  # re-check interval; a launch-only check never reaches a
                    # tray-resident app that stays open for days
API_URL = "https://api.cohere.com/v2/audio/transcriptions"
CHAT_URL = "https://api.cohere.com/v2/chat"
MODELS_URL = "https://api.cohere.com/v1/models"
MODEL = "cohere-transcribe-arabic-07-2026"
CLEANUP_MODELS = ["command-a-03-2025", "command-r-plus-08-2024", "command-r-08-2024"]
SAMPLE_RATE = 16000
MAX_SECONDS = 900
# 16kHz PCM16 is ~32KB/s, so one request per 30s is ~0.96MB. Bigger single
# uploads stall mid-write on a slow uplink (field failures at 145s/4.5MB and
# 214s/6.7MB on 2026-07-31, then 117s/3.6MB on 2026-08-03).
#
# 45s (~1.44MB) was measured failing on the live link while 0.96MB went
# through in 12.2s under the SAME conditions, so this is the empirical
# margin, not a guess. Paired with the connect-timeout fix in _asr; either
# alone is not enough.
CHUNK_SECONDS = 30
ENV_FILE = os.path.join(CONFIG_DIR, ".env")
ICON_FILE = os.path.join(RESOURCE_DIR, "app.ico")
UI_FILE = os.path.join(RESOURCE_DIR, "web", "index.html")
PILL_FILE = os.path.join(RESOURCE_DIR, "web", "pill.html")
HISTORY_FILE = os.path.join(CONFIG_DIR, "history.json")
NOTES_FILE = os.path.join(CONFIG_DIR, "notes.json")
SETTINGS_FILE = os.path.join(CONFIG_DIR, "settings.json")
AUDIO_DIR = os.path.join(CONFIG_DIR, "audio")
AUDIO_KEEP = 40  # rolling cap of kept recordings (~10MB worst case)

logging.basicConfig(filename=os.path.join(CONFIG_DIR, "app.log"), level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s")

DEFAULT_SETTINGS = {
    "flow_mode": True,
    "rec_mode": "toggle",
    "record_key": "f9",
    "lang_key": "f10",
    "command_key": "f8",
    "refine_key": "f4",
    "note_key": "f7",
    # Hold the GPU off deep idle while recording, so the 7W -> 100W wake-up
    # lands while he is talking instead of the moment he stops. OFF by default
    # (09-25): the blanking turned out to be this laptop's power delivery
    # failing the spike - the same transient hard-powers the machine off - and
    # holding the GPU at ~49W for the whole take ADDS sustained load to the
    # thing that is failing. It only removes the P-state wake, not the watts.
    "gpu_hold": False,
    "chime_on": True,
    "chime_volume": 40,
    "mic_device": "",
    "dictionary": "dialverse = Dialverse",
    "language": "auto",
    "tone": "auto",
    "app_aware": True,
    "asr_engine": "local",     # "local" (on-device Whisper) or "cloud"
    "paste_mode": "paste",
    "snippets": [],
    "theme": "system",
    "pill_pos": "bottom",
    "autostart": False,
    "idle_pill": True,
    "audio_enhance": True,
}

# ---- per-app formatting context (Wispr-style) ----

_CTX_BY_EXE = {
    "olk.exe": "email", "outlook.exe": "email", "thunderbird.exe": "email",
    "whatsapp.exe": "chat", "slack.exe": "chat", "telegram.exe": "chat",
    "discord.exe": "chat", "ms-teams.exe": "chat", "teams.exe": "chat",
    "messenger.exe": "chat",
    "winword.exe": "docs", "notepad.exe": "docs", "notion.exe": "docs",
    "obsidian.exe": "docs", "onenote.exe": "docs", "wordpad.exe": "docs",
    "code.exe": "code", "cursor.exe": "code", "devenv.exe": "code",
    "windowsterminal.exe": "code", "wt.exe": "code",
}
# browsers get categorized by tab title instead
_CTX_TITLE_HINTS = (
    ("gmail", "email"), ("outlook", "email"), ("proton mail", "email"),
    ("whatsapp", "chat"), ("slack", "chat"), ("telegram", "chat"),
    ("discord", "chat"), ("teams", "chat"),
    ("google docs", "docs"), ("notion", "docs"),
)
APP_PROMPTS = {
    "email": "The text will be pasted into an EMAIL. Organize it as clean "
             "email prose: short clear paragraphs, complete sentences; keep a "
             "greeting or sign-off only if the speaker actually said one.",
    "chat": "The text will be pasted into a CHAT app. Keep it short and "
            "natural, like a message to a colleague â€” no formal restructuring.",
    "docs": "The text will be pasted into a DOCUMENT. Use structured prose "
            "with paragraph breaks; if the speaker enumerates items, format "
            "them as a list with '- ' bullets.",
    "code": "The text will be pasted into a CODE EDITOR or terminal. Plain "
            "text only: no markdown, no smart quotes, and never reformat "
            "technical tokens, paths or identifiers.",
    "general": "",
}
TONE_PROMPTS = {
    "auto": "Match the speaker's natural tone.",
    "professional": "Polish the wording into professional, "
                    "workplace-appropriate language (same meaning, no new "
                    "content).",
    "casual": "Keep the wording relaxed and conversational.",
    "prompt": "",  # handled by PROMPT_MODE â€” it replaces the whole recipe
}

# Dictating a prompt to an AI is this app's dominant use. The FIRST version
# of this rewrote the speaker's words into imperative task lists â€” "what is
# flow mode 2.0?" came back as "1. Explain what Flow Mode 2.0 is." That is
# fabrication, not formatting. This version reorganizes and nothing else.
# Spoken filler. Deliberately a SHORT list of words that carry no meaning in
# any reading. "like" is not here on purpose: stripping it turned "should feel
# like paper" into "should feel paper". Same for "sort of" / "kind of" /
# "actually" - they hedge, and a hedge is content. When in doubt it stays; the
# cost of leaving an "um" in is nothing, the cost of eating a real word is a
# sentence that no longer says what he said.
_FILLER = re.compile(
    r"\b(?:umm?|uh+|er+|hmm+|you know|i mean|ok so|okay so|so yeah)\b[,\s]*"
    r"|(?:يعني|امم|"
    r"ياعني)[،\s]*",
    re.IGNORECASE)

# A line is a TASK if it reads as something to do. Deliberately cue-based and
# conservative: a missed task still lands in notes, where he will see it, but
# a false positive puts words in his mouth as a commitment he never made.
_TASK_CUES = re.compile(
    r"\b(?:i (?:need|have) to|i should|i must|i gotta|gotta|need to|"
    r"remind me to|remember to|don'?t forget to|make sure (?:to|i)|"
    r"todo|to-do|task|i'?ll|i will|let'?s|we (?:need|should) to|"
    # "I want to ..." is how he actually states an intention out loud - most
    # of a real take's tasks were being missed without it
    r"i want to|i wanna|i'?d like to|i would like to|i'?m going to|"
    r"i'?m gonna|we want to|"
    r"should get done|has to (?:be|get) done)\b"
    r"|لازم|يجب|محتاج"
    r"|فاكرني|متنساش",
    re.IGNORECASE)

# A bare imperative is a task even with no cue phrase in front of it: dictating
# a to-do list, people say "ping Sam about the SMS thing", not "I need to ping
# Sam". Anchored to the START of the clause so "I asked him to review it" - a
# report, not a task - does not match.
_TASK_VERB = re.compile(
    r"^(?:ping|send|call|email|text|check|finish|fix|write|review|ask|tell|"
    r"book|buy|update|add|remove|delete|deploy|ship|test|push|merge|read|"
    r"schedule|follow up|reply|answer|confirm|chase|prep|prepare|draft|"
    r"clean|set up|sort out|look into|reach out)\b",
    re.IGNORECASE)

# Dropped when building a title - they name nothing.
_STOP = {"the", "and", "also", "then", "but", "for", "with", "that", "this",
         "today", "really", "just", "need", "needs", "want", "wanna", "gotta",
         "should", "would", "could", "about", "from", "into", "some", "then",
         "have", "has", "had", "was", "were", "are", "our", "its", "his",
         "her", "their", "you", "your", "they", "them", "there", "here",
         "what", "when", "where", "which", "who", "how", "why", "all",
         "can", "will", "not", "yeah", "okay", "think", "thinking", "like",
         "make", "made", "get", "got", "put", "one", "two", "now"}

# Leading connectives to shave once a clause is standing on its own.
_LEAD = re.compile(
    r"^(?:and|also|then|plus|but|so|ok|okay|yeah|well|now)\b[,\s]*"
    r"|^(?:و|كمان|برضه)\s*",
    re.IGNORECASE)


def _split_clauses(text):
    """Split ONLY where the speaker actually ended a sentence.

    This used to also split on the connectives "and / also / then / plus",
    on the theory that dictation has little punctuation. On real speech that
    was a disaster: "the details for the client and their phone number and
    when they were called" became three entries reading "Their phone number",
    "When they were called", "Everything", and "so on and so forth" left a
    note that said only "Forth". A connective joins phrases far more often
    than it starts a thought, and there is no reliable way to tell which from
    a regex.

    So: terminators and line breaks only. A long unpunctuated run stays whole -
    one big faithful note is worth more than twenty fragments of one, and the
    raw transcript is always there underneath."""
    parts = re.split(r"(?<=[.!?؟۔])\s+|\n+", text)
    return [p.strip(" ,،;:-") for p in parts if p.strip(" ,،;:-")]


def _tidy_clause(s):
    s = _FILLER.sub(" ", s)
    # repeat: dictation stacks these ("and also yeah, remind me..."), and a
    # single pass left "Yeah remind me to..." sitting at the front of a task
    for _ in range(4):
        stripped = _LEAD.sub("", s, count=1).lstrip()
        if stripped == s:
            break
        s = stripped
    s = re.sub(r"\s{2,}", " ", s).strip(" ,،;:-")
    return s[:1].upper() + s[1:] if s and s[:1].isascii() else s


# Small enough that the model restructures instead of compressing, big enough
# that a normal 30-second take is still a single call.
NOTE_CHUNK_CHARS = 900


def _oversize_split(parts, limit):
    """Break only the pieces that are too long for one call, at commas."""
    for p in parts:
        if len(p) <= limit * 1.6:
            yield p
            continue
        bits = re.split(r"(?<=[,،])\s+", p)
        if len(bits) == 1:
            # No sentence ends AND no commas - four minutes of unbroken speech.
            # Wrap on whitespace as a last resort. A sentence split across two
            # chunks costs one extra line; leaving it whole cost 65% of what he
            # said, because the model summarises what it cannot restructure.
            words, buf = p.split(), ""
            for w in words:
                if buf and len(buf) + len(w) + 1 > limit:
                    yield buf
                    buf = w
                else:
                    buf = f"{buf} {w}".strip()
            if buf:
                yield buf
            continue
        buf = ""
        for bit in bits:
            if buf and len(buf) + len(bit) + 1 > limit:
                yield buf
                buf = bit
            else:
                buf = f"{buf} {bit}".strip()
        if buf:
            yield buf


def _chunk_for_notes(text, limit=NOTE_CHUNK_CHARS):
    """Cut at sentence ends, never mid-sentence, packing up to `limit` chars.

    A single unpunctuated run longer than the limit still has to be broken up,
    or the model summarises it exactly as before - one real take arrived as a
    5970-character run with no full stop in it. It is cut at COMMAS near the
    limit: a comma in the transcript is a pause the speaker actually made.
    Connectives are deliberately not used, since splitting on "and"/"also" is
    what produced fragments like "Their phone number". With no commas either,
    it is left whole rather than cut blind."""
    out, cur = [], ""
    for part in _oversize_split(_split_clauses(text), limit):
        if cur and len(cur) + len(part) + 1 > limit:
            out.append(cur)
            cur = part
        else:
            cur = f"{cur} {part}".strip()
    if cur:
        out.append(cur)
    return out or [text]


def _organize_locally(text):
    """Sort a dump into tasks and notes with no model and no network.

    This is the floor, not the ceiling: it is cue-based, so it will miss a
    task phrased sideways. That is the right way to be wrong here - a missed
    task is still visible under notes, whereas inventing a commitment the
    user never made is the failure they would never forgive. The raw
    transcript sits one click away regardless."""
    tasks, notes = [], []
    for clause in _split_clauses(text):
        tidy = _tidy_clause(clause)
        if len(tidy) < 2:
            continue
        # The cue must sit near the FRONT of the sentence. Searching the whole
        # clause meant any long ramble containing "I need to" somewhere in its
        # middle was promoted wholesale to a task - which is exactly how a
        # 400-character run-on ended up as a single checkbox, with the actual
        # task buried inside it. A bare imperative must start the sentence.
        head = tidy[:60].lower()
        is_task = bool(_TASK_CUES.search(head) or _TASK_VERB.match(tidy))
        # A "task" the length of a paragraph is not a task, whatever it says.
        # Better to leave it in notes, intact, than to put a wall of text
        # behind a checkbox he can never meaningfully tick.
        if is_task and len(tidy) > 180:
            is_task = False
        (tasks if is_task else notes).append(tidy)
    if not tasks and not notes:
        return None
    # built from the TIDIED lines, not the raw text - off the raw it read
    # "finish clickup research umm", with the filler it had just removed
    head = (tasks + notes)[0]
    words = [w for w in re.sub(r"[^\w\s؀-ۿ]", " ", head).split()
             if len(w) > 2 and w.lower() not in _STOP][:4]
    return {"title": " ".join(words)[:60], "tasks": tasks, "notes": notes,
            "by": "local"}


NOTE_PROMPT = (
    "You are filing a spoken brain-dump into a personal notebook. The speaker "
    "talks in Egyptian Arabic, English, or both in one sentence.\n\n"
    "Split what they said into two piles and return STRICT JSON:\n"
    '{"title": "...", "tasks": ["..."], "notes": ["..."]}\n\n'
    "tasks  = things they intend to DO. Anything phrased as needing to happen: "
    "'I need to X', 'remind me to X', 'X should get done', 'لازم أعمل X'.\n"
    "notes  = everything else. Thoughts, decisions, observations, questions, "
    "context, things they are chewing on.\n"
    "title  = 4 words or fewer naming what this dump was about. Plain, "
    "concrete, no colons, no 'Notes on'.\n\n"
    "RULES, in order of importance:\n"
    "1. NEVER invent. Every task and every note must come from something they "
    "actually said. If they said four things, you return four things. Do not "
    "add a task they did not ask for, do not infer a next step, do not "
    "helpfully expand.\n"
    "2. NEVER drop. Everything they said lands in exactly one pile. If you "
    "cannot tell which, it is a note. Losing a sentence is worse than filing "
    "it in the wrong pile.\n"
    "3. Tidy only. Cut 'umm', 'you know', 'يعني', false starts and repeated "
    "words. Fix grammar. Keep THEIR words, phrasing and language otherwise - "
    "an Arabic sentence stays Arabic, an English one stays English, a mixed "
    "one stays mixed. Do not translate, summarise, or make it more formal.\n"
    "4. KEEP EVERY NAME, exactly as spoken. Clients, people, products, "
    "screens, companies, numbers. 'I like that Marcus Elderberry shows the "
    "client details' must not become 'client details are shown' - the name is "
    "usually the only thing that makes the line findable later.\n"
    "5. One task per line, one thought per note. Split a run-on into separate "
    "entries rather than making one long line.\n"
    "6. Never merge two different things into one entry to make it shorter.\n\n"
    "Return ONLY the JSON object. No markdown fence, no commentary.\n\n"
    "What they said:\n"
)

PROMPT_MODE = (
    "You are a TRANSCRIPT FORMATTER. The text is speech dictated by a user "
    "who will send it to an AI assistant. You reorganize their words. You "
    "do not rewrite them.\n"
    "ALLOWED â€” pick whatever structure the content actually calls for:\n"
    "- Prose in paragraphs, separated by a blank line, when they are "
    "explaining, describing or reasoning. Most speech is this. Do NOT force "
    "it into a list.\n"
    "- A numbered list only where they genuinely enumerate separate items.\n"
    "- Nested sub-points (indented '-' under a number, or 1.1 / 1.2) when "
    "one item carries several sub-questions or sub-requests.\n"
    "- A mix: a paragraph of context, then a list, then more prose. Real "
    "dictation is usually mixed, and the output should be too.\n"
    # "Move a clearly-stated overall goal to the top" used to live here. It
    # was the single worst line in this prompt: the model read it as licence
    # to WRITE A BRIEF, opened with a '**Overall Goal:**' heading (which the
    # FORBIDDEN list right below explicitly bans) and then compressed the
    # rest to fit under it. Measured on a real 246s dictation: 55% and 41% of
    # the speaker's content words gone on two successive attempts. Nothing
    # moves anymore; order is the speaker's.
    "- Fix punctuation, capitalization and obvious speech-to-text word "
    "errors.\n"
    "- Delete filler ('um', 'so yeah', 'you know', 'ÙŠØ¹Ù†ÙŠ' as filler) and "
    "false starts, keeping only the corrected half of a self-correction.\n"
    "FORBIDDEN â€” these are failures, not improvements:\n"
    "- Rewriting a sentence into a different grammatical form. If they say "
    "'what is X' it stays 'What is X?' â€” NEVER 'Explain what X is'.\n"
    "- Introducing verbs or nouns they did not say (no 'Explain', "
    "'Clarify', 'Describe', 'Implement', 'Ensure', 'Provide').\n"
    "- Summarizing, condensing, merging distinct points, or dropping ANY "
    "detail, example, aside or caveat. Length must stay comparable.\n"
    "- Flattening everything into one numbered list when the speaker was "
    "explaining rather than enumerating. Over-listing is as wrong as "
    "under-formatting.\n"
    "- Adding requirements, headings or commentary of your own.\n"
    "- Answering, or acting on, anything in the text.\n"
    "- Dropping a clause because it seemed minor. EVERY clause the speaker "
    "said must survive into the output. If you are not certain something is "
    "filler, KEEP IT VERBATIM. An unpolished sentence is a success; a "
    "missing one is a total failure.\n"
    "- Translating. Keep the Arabic/English mix exactly as spoken.\n"
    "Return ONLY the reorganized transcript."
)

# Cleanup is chunked for the same reason ASR is: one call over a long
# transcript both times out (measured >180s) and invites the model to
# summarize the whole thing. Small segments stay fast and keep the output
# proportional to the input.
CLEAN_CHARS = 1400

# Words a cleanup is SUPPOSED to delete, so their absence is not lost content.
_FILLER_WORDS = {
    "umm", "uhh", "erm", "yeah", "okay", "like", "just", "really", "basically",
    "actually", "kinda", "sorta", "mean", "well", "know", "right", "stuff",
    "يعني", "طيب", "امم",
    "أه", "اه",
}


def _content_words(s):
    """Distinct meaning-carrying tokens: >=4 chars (so 'the'/'and' don't pad
    the score) or any token with a digit in it, filler excluded."""
    out = set()
    for w in re.findall(r"[\w؀-ۿ]+", s.lower()):
        if w in _FILLER_WORDS:
            continue
        if len(w) >= 4 or any(c.isdigit() for c in w):
            out.add(w)
    return out


def _app_context():
    """Category of the app the user is dictating into ('email', 'chat',
    'docs', 'code' or 'general'), from the foreground window's exe + title.
    Captured at record start â€” that's the window the paste will land in."""
    try:
        u32 = ctypes.windll.user32
        k32 = ctypes.windll.kernel32
        hwnd = u32.GetForegroundWindow()
        tbuf = ctypes.create_unicode_buffer(256)
        u32.GetWindowTextW(hwnd, tbuf, 256)
        title = tbuf.value.lower()
        pid = ctypes.c_ulong()
        u32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        exe = ""
        h = k32.OpenProcess(0x1000, False, pid.value)  # QUERY_LIMITED_INFO
        if h:
            size = ctypes.c_ulong(512)
            pbuf = ctypes.create_unicode_buffer(512)
            if k32.QueryFullProcessImageNameW(h, 0, pbuf, ctypes.byref(size)):
                exe = os.path.basename(pbuf.value).lower()
            k32.CloseHandle(h)
        if exe in _CTX_BY_EXE:
            return _CTX_BY_EXE[exe]
        for hint, cat in _CTX_TITLE_HINTS:
            if hint in title:
                return cat
        return "general"
    except Exception:
        return "general"


QUOTA_MSG = ("API quota used up - switch to the local engine in Settings, "
             "or upgrade the Cohere key")

# ---------------------------------------------------------------- local ASR
# Runs Whisper on this machine: no API, no quota, no upload. large-v3-turbo
# is ~1.6GB and near large-v3 quality. Measured on this laptop over a 229s
# take: 9.4s on the RTX 3060 (24x realtime), 101s on CPU int8 (2.3x). GPU is
# used whenever the CUDA runtime can be found, CPU otherwise.
LOCAL_ASR_REPO = "deepdml/faster-whisper-large-v3-turbo-ct2"
# Deliberately NOT under CONFIG_DIR: running from source that resolves to the
# repo, which would both dump 1.6GB into git's working tree and make the
# packaged app download its own second copy. One machine, one model.
MODEL_DIR = os.path.join(os.environ.get("APPDATA", CONFIG_DIR),
                         "DialFlow", "models")


def _enable_cuda_dlls():
    """Put the CUDA runtime on the DLL search path.

    ctranslate2 needs cublas/cudnn beside it. They ship as pip wheels rather
    than in the frozen bundle (bundling them would add ~1GB to the exe), so
    look for them wherever a Python on this machine installed them, then fall
    back to a cuda/ folder next to the app."""
    roots = []
    try:
        import site
        roots += [p for p in site.getsitepackages() if os.path.isdir(p)]
        u = site.getusersitepackages()
        if isinstance(u, str) and os.path.isdir(u):
            roots.append(u)
    except Exception:
        pass
    # The frozen app has no site-packages of its own, so look where pip
    # actually put the wheels: per-user and per-machine Python trees, plus a
    # cuda/ folder shipped beside the exe.
    for base in (os.environ.get("APPDATA", ""),
                 os.environ.get("LOCALAPPDATA", ""),
                 os.environ.get("ProgramFiles", ""),
                 os.environ.get("LOCALAPPDATA", "") + r"\Programs"):
        if not base:
            continue
        for pat in ("Python\\Python3*\\site-packages",
                    "Python\\Python3*\\Lib\\site-packages",
                    "Python3*\\Lib\\site-packages"):
            roots += glob.glob(os.path.join(base, pat))
    roots.append(os.path.join(os.path.dirname(sys.executable), "cuda"))
    roots.append(os.path.join(APP_DIR, "cuda"))
    found = 0
    for root in roots:
        for sub in ("nvidia",):
            base = os.path.join(root, sub)
            if not os.path.isdir(base):
                continue
            for name in os.listdir(base):
                d = os.path.join(base, name, "bin")
                if os.path.isdir(d):
                    try:
                        os.add_dll_directory(d)
                        os.environ["PATH"] = d + os.pathsep + os.environ["PATH"]
                        found += 1
                    except OSError:
                        pass
    logging.info("cuda dll dirs registered: %s", found)
    return found > 0


_LOOP_REPS = 4   # a phrase repeated this many times back-to-back is a loop


def _strip_loop(text):
    """Collapse a Whisper decoding loop.

    The decoder gets stuck on trailing silence and re-emits the same word or
    short phrase until the segment ends ("...tomorrow tomorrow tomorrow
    tomorrow"). Real speech does not repeat a phrase four times in a row, so
    any 1-4 word phrase repeated _LOOP_REPS+ times consecutively collapses to
    one occurrence. Compared on letters only, since the loop usually carries
    punctuation with it.

    ponytail: a genuine "no no no no" also collapses to "no". Raise
    _LOOP_REPS if that ever shows up in real dictation.
    """
    words = text.split()
    keys = [re.sub(r"[^\w؀-ۿ]", "", w.lower()) for w in words]
    out, i = [], 0
    while i < len(words):
        hit = False
        for size in range(4, 0, -1):
            if i + size * _LOOP_REPS > len(words) or not any(keys[i:i + size]):
                continue
            phrase, j = keys[i:i + size], i + size
            while keys[j:j + size] == phrase:
                j += size
            if (j - i) // size >= _LOOP_REPS:
                out.extend(words[i:i + size])
                i, hit = j, True
                break
        if not hit:
            out.append(words[i])
            i += 1
    return " ".join(out)


def _fullscreen_app_active():
    """True while a full-screen app, a D3D full-screen game or Windows
    presentation mode owns the display - the same signal Windows uses to hold
    back its own notifications."""
    try:
        state = ctypes.c_int(0)
        if ctypes.windll.shell32.SHQueryUserNotificationState(
                ctypes.byref(state)) != 0:
            return False
        # 2 QUNS_BUSY, 3 QUNS_RUNNING_D3D_FULL_SCREEN, 4 QUNS_PRESENTATION_MODE
        return state.value in (2, 3, 4)
    except Exception:
        return False


def _on_battery():
    """True when running on battery. Holding the GPU awake costs ~32W more
    than letting it idle, which is worth it plugged in and not worth it on
    a battery."""
    try:
        class _SPS(ctypes.Structure):
            _fields_ = [("ACLineStatus", ctypes.c_byte),
                        ("BatteryFlag", ctypes.c_byte),
                        ("BatteryLifePercent", ctypes.c_byte),
                        ("SystemStatusFlag", ctypes.c_byte),
                        ("BatteryLifeTime", ctypes.c_ulong),
                        ("BatteryFullLifeTime", ctypes.c_ulong)]
        s = _SPS()
        if ctypes.windll.kernel32.GetSystemPowerStatus(ctypes.byref(s)):
            return s.ACLineStatus == 0        # 0 offline, 1 online, 255 unknown
    except Exception:
        logging.exception("power status check failed")
    return False


class LocalASR:
    """Lazy Whisper. Loading costs seconds and ~1.6GB of disk, so it happens
    once, off the hotkey path, and only if local mode is actually used."""

    def __init__(self):
        self._model = None
        self._lock = threading.Lock()
        self.device = "?"
        self.status = "idle"

    def available(self):
        try:
            import faster_whisper  # noqa: F401
            return True
        except Exception:
            return False

    def ready(self):
        return self._model is not None

    def load(self, on_status=None):
        """Build the model. Downloads it on first use (~1.6GB)."""
        with self._lock:
            if self._model is not None:
                return self._model
            from faster_whisper import WhisperModel
            os.makedirs(MODEL_DIR, exist_ok=True)
            cached = any(LOCAL_ASR_REPO.split("/")[-1].lower() in d.lower()
                         for d in os.listdir(MODEL_DIR)) if \
                os.path.isdir(MODEL_DIR) else False
            self.status = "loading" if cached else "downloading"
            if on_status:
                on_status(self.status)
            gpu = _enable_cuda_dlls()
            attempts = ([("cuda", "float16")] if gpu else []) + \
                       [("cpu", "int8")]
            last = None
            for device, ctype in attempts:
                try:
                    t0 = time.time()
                    # once the snapshot is on disk, load it WITHOUT contacting
                    # Hugging Face: this is meant to run with no network at
                    # all, and a revision check would both leak a request and
                    # stall startup on a bad link
                    m = WhisperModel(LOCAL_ASR_REPO, device=device,
                                     compute_type=ctype,
                                     download_root=MODEL_DIR,
                                     local_files_only=cached,
                                     cpu_threads=min(14, os.cpu_count() or 8))
                    self._model = m
                    self.device = device
                    self.status = "ready"
                    logging.info("local ASR ready on %s (%s) in %.1fs",
                                 device, ctype, time.time() - t0)
                    if on_status:
                        on_status("ready")
                    return m
                except Exception as e:
                    last = e
                    logging.warning("local ASR on %s failed: %s", device,
                                    str(e)[:200])
            self.status = "failed"
            if on_status:
                on_status("failed")
            raise last if last else RuntimeError("local ASR unavailable")

    def warm(self):
        """Wake the GPU NOW, while he is still talking.

        Measured on this laptop: the 3060 idles at P8, 210MHz, 7.3W and slams
        to P0, 1980MHz, 99.5W the instant a take is transcribed - a 92W step
        in under a second. The panel is driven by the Intel iGPU off the same
        chassis power budget, and that transient makes the display link
        re-train: the screen blanks and comes back. There are no TDR events,
        so nothing is crashing; it is purely the rate of change.

        The total power is the same either way. What this buys is WHEN it
        happens: at the start of a recording, when he is speaking and not
        watching, instead of the moment he stops and is waiting for text.

        MEASURED, so the trade is explicit:
          cold  -> transcription steps  7.3W -> 119W  (P8, 210MHz -> P0)
          held  -> transcription steps 35.5W -> 119W  (already P0, 1965MHz)
        The step only shrinks by about a fifth, because the power is the
        COMPUTE, not the clock. What it does remove completely is the
        P8 -> P0 power-state change, and on a hybrid laptop that RTD3 wake is
        the more likely trigger for the panel re-training than the wattage.

        The cost is real: ~39W average for as long as he is recording, versus
        7W. So it is skipped on battery, where that matters most and where the
        screen is least likely to be the thing he is watching anyway.

        A single warm does NOT work - the GPU returns to P8 about five seconds
        after the work stops, so it is asleep again by the time he stops
        talking. It has to be held."""
        if self._model is None or self.device != "cuda":
            return
        try:
            segs, _ = self._model.transcribe(
                np.zeros(SAMPLE_RATE // 2, dtype=np.float32),
                beam_size=1, vad_filter=False, language="en",
                condition_on_previous_text=False)
            # the generator is lazy - it must be consumed or no GPU work runs
            for _ in segs:
                break
        except Exception:
            logging.exception("gpu warm failed (harmless)")

    def hold_warm(self, still_recording):
        """Keep the GPU off deep idle for as long as the take runs."""
        if self._model is None or self.device != "cuda":
            return
        if _on_battery():
            logging.info("gpu hold skipped - on battery")
            return
        t0 = time.time()
        n = 0
        # 1.5s was measured: 3s lets it fall back to P3/P5 between pulses
        while still_recording() and time.time() - t0 < MAX_SECONDS:
            self.warm()
            n += 1
            time.sleep(1.5)
        if n:
            logging.info("gpu held awake for %.0fs (%d pulses)",
                         time.time() - t0, n)

    def transcribe(self, audio, lang):
        """audio: float32 mono at SAMPLE_RATE. Returns text."""
        m = self.load()
        kw = {}
        if lang in ("ar", "en"):
            kw["language"] = lang
        else:
            # Detect the language PER SEGMENT. Whisper otherwise decides once,
            # from the first 30 seconds, and then forces the rest of the take
            # into it - which is how an English stretch inside a mostly-Arabic
            # dictation came out transliterated into Arabic script.
            kw["multilingual"] = True
        segs, _info = m.transcribe(
            audio, beam_size=5, vad_filter=True,
            vad_parameters=dict(min_silence_duration_ms=500),
            # Whisper loops on trailing silence and room noise: it re-emits
            # the last word until the segment runs out. Not feeding the
            # previous segment's text back in as the next segment's prompt
            # stops the loop from sustaining itself across segments, and
            # _strip_loop below cleans up whatever still gets through.
            #
            # repetition_penalty was tried here and removed: it biases the
            # decoder against ALL repetition, not just loops, and on a real
            # 246s take it turned "base setup" into "bass setup". Two guards
            # that cost no accuracy beat a third that trades some away.
            condition_on_previous_text=False,
            **kw)
        return _strip_loop(" ".join(s.text.strip() for s in segs).strip())


LOCAL_ASR = LocalASR()


def _quota_exhausted(body):
    """Is this 429 a hard monthly cap rather than a transient burst limit?

    Cohere trial keys allow 1000 calls/month and answer with an explicit
    message once that is spent. Retrying that only consumes more of the
    cap, so it must be told apart from a per-minute throttle."""
    b = (body or "").lower()
    return ("trial key" in b
            or "calls / month" in b
            or "calls/month" in b
            or "monthly" in b and "limit" in b)


def _speech_present(audio):
    """Cheap voice-activity check: is there ANY 100ms window loud enough to
    plausibly be speech? Silent accidental taps must never reach the API â€”
    the model hallucinates words from amplified nothing."""
    win = SAMPLE_RATE // 10
    n = len(audio) // win
    if n == 0:
        return False
    return any(
        float(np.sqrt(np.mean(audio[i * win:(i + 1) * win] ** 2))) > 0.008
        for i in range(n))


def _enhance_audio(audio):
    """Near-zero-latency mic cleanup before transcription: high-pass out
    sub-75Hz rumble, then a GENTLE lift for quiet speech. Conservative on
    purpose â€” hot gain amplifies background media/noise into hallucination
    fuel and pushes real speech toward clipping."""
    if len(audio) < 1600:
        return audio
    spec = np.fft.rfft(audio)
    freqs = np.fft.rfftfreq(len(audio), 1.0 / SAMPLE_RATE)
    spec[freqs < 75] = 0
    audio = np.fft.irfft(spec, n=len(audio)).astype(np.float32)
    rms = float(np.sqrt(np.mean(audio ** 2)))
    if 0.005 < rms < 0.06:
        # only lift genuinely-quiet speech, mildly (max 12 dB), and never
        # touch clips that are near-silence (nothing there to lift)
        audio = audio * min(0.06 / rms, 4.0)
    peak = float(np.max(np.abs(audio)))
    if peak > 0.90:
        audio = audio * (0.90 / peak)
    return audio


def _apply_autostart(enabled):
    """Register/unregister launch-at-login via the per-user Run key â€”
    the no-installer way to start with Windows. Only meaningful when frozen."""
    try:
        key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                             r"Software\Microsoft\Windows\CurrentVersion\Run",
                             0, winreg.KEY_SET_VALUE)
        if enabled and getattr(sys, "frozen", False):
            winreg.SetValueEx(key, "DialFlow", 0, winreg.REG_SZ,
                              f'"{sys.executable}" --minimized')
        else:
            try:
                winreg.DeleteValue(key, "DialFlow")
            except FileNotFoundError:
                pass
        try:  # drop the Yalla Flow era's entry so both don't launch
            winreg.DeleteValue(key, "YallaFlow")
        except FileNotFoundError:
            pass
        winreg.CloseKey(key)
    except OSError:
        logging.exception("autostart update failed")

def _load_pill_html():
    """The floating bar's markup lives in web/pill.html so it can be
    designed like any other page. Falls back to a minimal bar if the
    file is missing so the app still records."""
    try:
        with open(PILL_FILE, encoding="utf-8") as f:
            html = f.read()
        # A NUL anywhere in here truncates the WHOLE page at that byte:
        # pywebview hands the markup to WebView2 as a NUL-terminated string,
        # so everything after it is silently dropped. v5.1.0 shipped with one
        # stray NUL in a string literal 36KB in — the DOM still parsed and the
        # bar still LOOKED right, but its <script> was cut mid-token, so the
        # page had no behaviour at all: no hover, no drag, no dock picker.
        # Nothing raised, and nothing was logged. Strip and shout instead.
        bad = sum(1 for c in html if ord(c) < 0x20 and c not in "\n\r\t")
        if bad:
            logging.error("pill.html has %d control character(s) — stripping. "
                          "Left in, they truncate the page and kill the bar.",
                          bad)
            html = "".join(c for c in html
                           if ord(c) >= 0x20 or c in "\n\r\t")
        return html
    except OSError:
        logging.exception("pill.html missing â€” using fallback")
        return ("<!DOCTYPE html><html><body style='background:#171320'>"
                "<script>window.app={start(){},level(){},mode(){},"
                "done(){},failed(){},reckey(){},pos(){},vert(){}}"
                "</script></body></html>")


PILL_HTML = _load_pill_html()


class Settings(dict):
    def __init__(self):
        super().__init__(DEFAULT_SETTINGS)
        try:
            with open(SETTINGS_FILE, encoding="utf-8") as f:
                self.update(json.load(f))
        except (OSError, ValueError):
            pass
        if self.get("language") == "ar":
            # the pinned-Arabic option is gone; anyone left on it would have
            # had no button to switch away with
            self["language"] = "auto"

    def save(self):
        try:
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(dict(self), f, ensure_ascii=False, indent=1)
        except OSError:
            logging.exception("settings save failed")


def _bar_note(freq, dur, sr, decay=16.0):
    """One soft struck-bar (marimba-like) note: warm detuned harmonics with a
    fast attack and natural exponential decay â€” not a raw electronic sine."""
    n = int(sr * dur)
    t = np.arange(n) / sr
    env = np.exp(-t * decay)
    attack = min(int(sr * 0.004), n)
    env[:attack] *= np.linspace(0.0, 1.0, attack)
    w = (np.sin(2 * np.pi * freq * t)
         + 0.34 * np.sin(2 * np.pi * freq * 2.008 * t)
         + 0.13 * np.sin(2 * np.pi * freq * 3.011 * t))
    return w * env


def _chime_wav(notes, amp, sr=44100, total=0.45, decay=16.0):
    """notes: (freq_hz, offset_ms) pairs layered into one soft chime."""
    total_len = int(sr * total)
    mix = np.zeros(total_len)
    for freq, off_ms in notes:
        note = _bar_note(freq, max(0.05, total - 0.02), sr, decay)
        i0 = int(sr * off_ms / 1000)
        end = min(total_len, i0 + len(note))
        mix[i0:end] += note[:end - i0]
    peak = np.max(np.abs(mix))
    if peak > 0:
        mix *= amp / peak
    pcm = (mix * 32767).astype("<i2")
    buf = io.BytesIO()
    with wave.open(buf, "wb") as f:
        f.setnchannels(1)
        f.setsampwidth(2)
        f.setframerate(sr)
        f.writeframes(pcm.tobytes())
    return buf.getvalue()


class _KEYBDINPUT(ctypes.Structure):
    _fields_ = [("wVk", ctypes.c_ushort), ("wScan", ctypes.c_ushort),
                ("dwFlags", ctypes.c_ulong), ("time", ctypes.c_ulong),
                ("dwExtraInfo", ctypes.POINTER(ctypes.c_ulong))]


class _INPUT_UNION(ctypes.Union):
    _fields_ = [("ki", _KEYBDINPUT), ("padding", ctypes.c_byte * 32)]


class _INPUT(ctypes.Structure):
    _anonymous_ = ("u",)
    _fields_ = [("type", ctypes.c_ulong), ("u", _INPUT_UNION)]


_paste_extra = ctypes.c_ulong(0)


def _send_ctrl_vk(letter_vk):
    """Layout-independent Ctrl+<key> via SendInput virtual keys.

    keyboard.send('ctrl+v') resolves the letter through the ACTIVE keyboard
    layout â€” with an Arabic layout (browsers, WhatsApp Web) that misfires and
    nothing happens. VK codes name the physical shortcut, which Windows apps
    recognize under any layout."""
    def key(vk, up=False):
        inp = _INPUT(type=1)  # INPUT_KEYBOARD
        inp.ki = _KEYBDINPUT(vk, 0, 2 if up else 0, 0,
                             ctypes.pointer(_paste_extra))
        return inp

    seq = [key(0x11), key(letter_vk), key(letter_vk, True), key(0x11, True)]
    arr = (_INPUT * len(seq))(*seq)
    sent = ctypes.windll.user32.SendInput(len(seq), arr, ctypes.sizeof(_INPUT))
    if sent != len(seq):
        logging.error("key injection incomplete: %s/%s events", sent, len(seq))


def _send_paste():
    _send_ctrl_vk(0x56)  # Ctrl+V


def _send_copy():
    _send_ctrl_vk(0x43)  # Ctrl+C


def _send_type(text):
    """Simulate real keystrokes via KEYEVENTF_UNICODE for fields that block
    Ctrl+V (terminals, some CRM iframes). Newlines go as VK_RETURN â€” many
    editors ignore a typed U+000A. Sent in chunks so target apps keep up."""
    UNICODE, KEYUP = 0x0004, 0x0002

    def ki(vk, scan, flags):
        inp = _INPUT(type=1)
        inp.ki = _KEYBDINPUT(vk, scan, flags, 0, ctypes.pointer(_paste_extra))
        return inp

    seq = []
    for ch in text.replace("\r\n", "\n"):
        if ch == "\n":
            seq += [ki(0x0D, 0, 0), ki(0x0D, 0, KEYUP)]
            continue
        units = ch.encode("utf-16-le")
        for i in range(0, len(units), 2):
            scan = units[i] | (units[i + 1] << 8)
            seq += [ki(0, scan, UNICODE), ki(0, scan, UNICODE | KEYUP)]
    for i in range(0, len(seq), 200):
        chunk = seq[i:i + 200]
        arr = (_INPUT * len(chunk))(*chunk)
        ctypes.windll.user32.SendInput(len(chunk), arr, ctypes.sizeof(_INPUT))
        time.sleep(0.01)


def _parse_dictionary(text):
    pairs = []
    for line in text.splitlines():
        if "=" in line:
            a, b = line.split("=", 1)
        elif "->" in line:
            a, b = line.split("->", 1)
        else:
            continue
        a, b = a.strip(), b.strip()
        if a and b:
            pairs.append((a, b))
    return pairs


def _apply_dictionary(text, pairs):
    for a, b in pairs:
        if a.isascii():
            text = re.sub(rf"\b{re.escape(a)}\b", b, text, flags=re.IGNORECASE)
        else:
            text = text.replace(a, b)
    return text


def _match_snippet(text, snippets):
    """Say a snippet's trigger and get its text.

    Two shapes:
      exact match            -> paste the whole template
      trigger + more speech  -> if the template contains {}, the rest of the
                                dictation is substituted in. That turns a
                                snippet into a reusable PROMPT FRAMING:
                                "code review framing <what you want reviewed>"
    Returns (text, consumed_rest) or None.
    """
    def norm(s):
        return re.sub(r"\s+", " ", s).strip().strip(".!?,ØŒØŸ ").lower()

    n = norm(text)
    if not n:
        return None
    for s in snippets or []:
        trig = norm(s.get("t") or "")
        body = s.get("x") or ""
        if not trig or not body:
            continue
        if n == trig:
            # a framing with no content yet: leave the placeholder visible
            return body.replace("{}", "").strip() if "{}" in body else body
        if "{}" in body and n.startswith(trig + " "):
            rest = text.strip()[len(trig):].lstrip(" ,ØŒ:-").strip()
            if rest:
                return body.replace("{}", rest)
    return None


class Engine:
    """Recording + transcription + optional AI cleanup. UI-agnostic."""

    def __init__(self, api_key, settings, on_state, on_transcript, on_language,
                 on_cancelled_take=None, on_last_text=None, on_engine=None,
                 on_note=None):
        self.api_key = api_key
        self.settings = settings
        self.on_state = on_state
        self.on_transcript = on_transcript
        self.on_language = on_language
        self.on_cancelled_take = on_cancelled_take or (lambda audio: None)
        self.on_engine = on_engine or (lambda status: None)
        self.on_note = on_note or (lambda entry: None)
        self.on_last_text = on_last_text or (lambda: "")
        self._raw_once = False
        self.language = settings.get("language", "auto")
        self.recording = False
        self.frames = queue.Queue()
        self.stream = None
        self.started_at = None
        self.level = 0.0
        self.lock = threading.Lock()
        self._clean_model_idx = 0
        self.mode = "dictate"       # or "command" (voice-edit selection)
        self._app_ctx = "general"   # focused-app category at record start
        self._cmd_selection = ""
        # serializes the clipboard between command-mode's empty-sentinel
        # capture and worker threads pasting results
        self._clip_lock = threading.Lock()
        # bumped by cancel(); a worker whose generation is stale drops its
        # result instead of pasting into whatever the user is now doing
        self._gen = 0
        self._last_partial = None
        self.quitting = False
        # ONE pooled session for every API call. Bare requests.post() builds
        # and throws away a Session per call, so each ASR chunk and each Flow
        # chunk paid a fresh DNS + TCP + TLS handshake â€” 300-500ms apiece, and
        # a long take makes half a dozen of them. Keep-alive makes all but the
        # first free.
        self._http = requests.Session()
        self.rebuild_chimes()
        # first device-open of a session is the slow one â€” take that hit now
        threading.Thread(target=self._prewarm_mic, daemon=True).start()
        # ...and the first TLS handshake likewise: open the socket before the
        # user ever hits record, so take one is as fast as take two
        threading.Thread(target=self._prewarm_http, daemon=True).start()
        # ...and the local model too. Loading is seconds (or a 1.6GB download
        # the very first time), and doing it lazily would put all of that in
        # front of his first transcript.
        if self.settings.get("asr_engine", "local") == "local":
            threading.Thread(target=self._prewarm_local, daemon=True).start()

    def _prewarm_local(self):
        try:
            LOCAL_ASR.load(on_status=self.on_engine)
        except Exception:
            logging.exception("local ASR prewarm failed")
            self.on_engine("failed")

    def _prewarm_http(self):
        """Open the TLS connection to the API up front and leave it pooled."""
        try:
            self._http.get(MODELS_URL,
                           headers={"Authorization": f"Bearer {self.api_key}"},
                           timeout=(5, 10))
        except Exception:
            logging.debug("http prewarm skipped", exc_info=True)

    def cancel(self):
        """Drop whatever is in flight. A live recording is still written to
        disk first â€” cancelling must never be the thing that loses audio,
        and the saved take stays retryable from history."""
        self._gen += 1
        audio = None
        with self.lock:
            was = self.recording
            # snapshot what Undo would need BEFORE the mode is reset below
            undo_ctx = {"mode": self.mode, "lang": self.language,
                        "ctx": getattr(self, "_app_ctx", "general"),
                        "raw": getattr(self, "_raw_once", False),
                        # started_at is None until the first take ever runs
                        "secs": time.time() - (getattr(self, "started_at", None)
                                               or time.time())}
            if was:
                self.recording = False
                self.level = 0.0
                try:
                    self.stream.stop()
                    self.stream.close()
                except Exception:
                    logging.exception("cancel: stream close failed")
                chunks = []
                while not self.frames.empty():
                    chunks.append(self.frames.get())
                if chunks:
                    audio = np.concatenate(chunks).flatten()
            # unconditional: a mode left at "command" would route the NEXT
            # ordinary dictation through the voice-edit path with a stale
            # selection and paste over whatever the user is doing
            self.mode = "dictate"
            self._starting = False
            self._want_stop = False
        self._undo = None
        if audio is not None and len(audio) > SAMPLE_RATE // 2 \
                and _speech_present(audio):
            # Only a plain dictation or a notebook take can be undone. Command
            # and refine act on a selection / last paste that may have moved
            # on in the seconds since, so replaying them could edit the wrong
            # text - worse than not offering it.
            if undo_ctx["mode"] in ("dictate", "note"):
                self._undo = dict(undo_ctx, audio=audio, at=time.time())
            self.on_cancelled_take(audio)
        self.on_state("idle", "Cancelled")

    UNDO_WINDOW_S = 10

    def undo_available(self):
        u = getattr(self, "_undo", None)
        return bool(u) and time.time() - u["at"] <= self.UNDO_WINDOW_S

    def undo(self):
        """Finish the take that was just cancelled, exactly as if it had not
        been: a dictation pastes, a notebook take files. The audio was kept in
        memory for this; the copy saved to history is separate."""
        u, self._undo = getattr(self, "_undo", None), None
        if not u or time.time() - u["at"] > self.UNDO_WINDOW_S or self.recording:
            return False
        audio = u["audio"]
        if self.settings.get("audio_enhance", True):
            try:
                audio = _enhance_audio(audio)
            except Exception:
                logging.exception("undo: enhance failed - using raw")
        logging.info("undo: finishing a cancelled %s take (%.0fs)",
                     u["mode"], len(audio) / SAMPLE_RATE)
        self.on_state("transcribing", "")
        if u["mode"] == "note":
            self._spawn(self._note_transcribe, audio, u["secs"], u["lang"])
        else:
            self._spawn(self._transcribe, audio, u["secs"], u["lang"],
                        u["ctx"], u["raw"])
        return True

    def _prewarm_mic(self):
        try:
            s = sd.InputStream(samplerate=SAMPLE_RATE, channels=1,
                               dtype="float32", device=self._resolve_device())
            s.start()
            s.stop()
            s.close()
        except Exception:
            pass

    def rebuild_chimes(self):
        amp = max(0, min(100, self.settings.get("chime_volume", 40))) / 100 * 0.5
        # start: short ~140ms tick â€” it plays synchronously before the mic
        # opens, so its length is pure key-to-recording latency
        self.start_wav = _chime_wav([(659, 0), (988, 55)], amp,
                                    total=0.14, decay=30.0)
        # stop: full marimba tail (plays async, costs nothing)
        self.stop_wav = _chime_wav([(880, 0), (587, 65)], amp)

    def _play(self, wav_bytes, block):
        if not self.settings.get("chime_on", True):
            return
        if block:
            winsound.PlaySound(wav_bytes, winsound.SND_MEMORY)
        else:
            threading.Thread(target=winsound.PlaySound,
                             args=(wav_bytes, winsound.SND_MEMORY),
                             daemon=True).start()

    # A block counts as clipping only when several samples hit the rail, not
    # one. Auto-gain mics touch full scale on single transients constantly and
    # a single-sample test would light the warning on every plosive.
    CLIP_LEVEL = 0.985
    CLIP_MIN_SAMPLES = 4
    CLIP_HOLD_S = 0.35

    def _audio_callback(self, indata, frames_count, time_info, status):
        if self.recording:
            self.frames.put(indata.copy())
            self.level = self._meter_level(
                float(np.sqrt(np.mean(indata ** 2))))
            # Too-loud is measured on the RAW signal. The meter above is
            # auto-ranged to this microphone, so a loud voice always reads as
            # full there - it can show "quiet" but never "clipping".
            if int(np.count_nonzero(np.abs(indata) >= self.CLIP_LEVEL)) \
                    >= self.CLIP_MIN_SAMPLES:
                self._clip_until = time.time() + self.CLIP_HOLD_S

    @property
    def clipping(self):
        return self.recording and time.time() < getattr(self, "_clip_until", 0)

    # Meter calibration. Raw RMS is a terrible thing to drive a meter with:
    # loudness is perceived logarithmically, and mic gain varies enormously
    # between machines. Measured across Mazen's real takes his voice sits at
    # RMS 0.002-0.011 (median -49 dBFS), so the old `min(1, rms*9)` mapping
    # put ALL of his speech under 0.10 and every voiced block fell below the
    # 0.16 "hearing" gate — the bar showed silence while he was talking.
    #
    # So: work in dB, and auto-calibrate the top of the scale to whatever
    # this mic actually delivers. A quiet mic and a hot mic both end up
    # using the full range.
    METER_FLOOR_DB = -62.0    # below this is treated as silence
    # 18 dB is about the working range of conversational speech. Wider (26)
    # was measured pushing his whole voice into the top of the scale — every
    # block reading 0.6-0.9, which is as uninformative as reading zero. At 18
    # his quiet blocks land near 0.25 and his louder ones near 0.8, so the
    # meter actually tracks how he is speaking.
    METER_RANGE_DB = 18.0
    METER_CEIL_MIN = -46.0    # never let the ceiling collapse onto the floor

    def _meter_level(self, rms):
        """Perceptual 0..1 for the meters, auto-ranged to this microphone."""
        if rms <= 1e-6:
            return 0.0
        db = 20.0 * math.log10(rms)
        if db < self.METER_FLOOR_DB:
            return 0.0
        # ceiling rises instantly to a new peak, then decays slowly, so a
        # single loud syllable does not permanently desensitise the meter
        ceil = getattr(self, "_meter_ceil", self.METER_CEIL_MIN)
        ceil = db if db > ceil else ceil - 0.05      # ~3 dB/sec decay at 60Hz
        self._meter_ceil = max(ceil, self.METER_CEIL_MIN)
        lo = self._meter_ceil - self.METER_RANGE_DB
        return max(0.0, min(1.0, (db - lo) / (self._meter_ceil - lo)))

    def mic_name(self):
        """The input actually in use, by name. 'System default' is resolved
        to the real device, because that is the case where the mic silently
        changes under you (plugging in a headset moves the default)."""
        try:
            idx = self._resolve_device()
            if idx is None:
                return sd.query_devices(kind="input")["name"]
            return sd.query_devices(idx)["name"]
        except Exception:
            return ""

    def _resolve_device(self):
        name = self.settings.get("mic_device", "")
        if not name:
            return None
        for i, dev in enumerate(sd.query_devices()):
            if dev["max_input_channels"] > 0 and dev["name"] == name:
                return i
        return None

    def toggle_language(self):
        # No Arabic-only setting. Auto already handles Arabic AND code-switch;
        # pinning "ar" only ever did harm - it forced spoken English to be
        # transcribed into Arabic script. English stays, for the case where
        # auto-detect guesses wrong on a short take.
        order = ["auto", "en"]
        cur = self.language if self.language in order else "auto"
        self.language = order[(order.index(cur) + 1) % len(order)]
        self.settings["language"] = self.language
        self.settings.save()
        self.on_language(self.language)

    def start_recording(self):
        try:
            self._start_inner()
        except Exception as e:
            logging.exception("start_recording failed")
            self.recording = False
            self.on_state("error", f"Error: {e}")

    def stop_recording(self):
        try:
            self._stop_inner()
        except Exception as e:
            logging.exception("stop_recording failed")
            self.recording = False
            self.on_state("error", f"Error: {e}")

    def toggle_recording(self):
        if self.recording:
            self.stop_recording()
        else:
            # Hold Shift while starting for ONE raw take: no Flow, no tone,
            # exactly as spoken. For the chat message that a numbered list
            # would ruin, without a trip into Settings.
            try:
                self._raw_once = keyboard.is_pressed("shift")
            except Exception:
                self._raw_once = False
            self.start_recording()

    def start_refine(self):
        """Speak a correction that is applied to the LAST thing pasted â€”
        'make it shorter', 'drop point three', 'Ø§Ø¹Ù…Ù„Ù‡Ø§ Ø±Ø³Ù…ÙŠØ©'. Command mode
        needs you to select text first; this reaches for what you just
        dictated, which is usually what you want to iterate on."""
        if self.recording:
            self.stop_recording()
            return
        if not self.on_last_text():
            self.on_state("error", "Nothing to refine yet")
            return
        self.mode = "refine"
        self.start_recording()

    def toggle_refine(self):
        if self.recording:
            self.stop_recording()
        else:
            self.start_refine()

    def toggle_note(self):
        """A take that goes into the notebook instead of the cursor. Same
        recording path as everything else â€” it only differs at the end, where
        it is filed under today rather than pasted into whatever window
        happens to be focused."""
        if self.recording:
            self.stop_recording()
            return
        self.mode = "note"
        self.start_recording()

    def _start_inner(self):
        with self.lock:
            if self.recording:
                return
            self._starting = True
            # NB: _want_stop is NOT reset here â€” hold-to-talk can release the
            # key during start_command's clipboard capture (before this runs),
            # and that early release must still stop the recording below
            # UI first: the pill starts expanding the instant the key lands;
            # the chime and mic-open happen behind the animation
            self.started_at = time.time()
            if self.mode != "command" and self.settings.get("app_aware", True):
                self._app_ctx = _app_context()
            else:
                self._app_ctx = "general"
            # The mode rides along so the bar can say WHERE this take will go.
            # An F7 notebook take used to look identical to a normal dictation,
            # and whether the text is about to paste into the focused field or
            # be filed away is exactly what you want to know before letting go.
            self.on_state("recording",
                          self.mode if self.mode != "dictate" else "")
            try:
                # ~140ms tick, played before the mic opens. Anything raising
                # in here (winsound on a busy device, a bad mic index) used
                # to leave _starting stuck True, which poisons _want_stop and
                # makes EVERY later recording abort the instant it starts.
                self._play(self.start_wav, block=True)
                self.frames = queue.Queue()
                self.stream = sd.InputStream(
                    samplerate=SAMPLE_RATE, channels=1, dtype="float32",
                    device=self._resolve_device(),
                    callback=self._audio_callback,
                )
                self.stream.start()
            except Exception as e:
                logging.exception("recording start failed")
                self._starting = False
                self._want_stop = False
                self.mode = "dictate"
                self.on_state("error", f"Mic error: {e}")
                return
            self.recording = True
            self._starting = False
            self.last_paste_blind = False     # per take, never inherited
            self._start_watchdog()
            # Move the GPU's 7W -> 100W wake-up to HERE, where he is talking,
            # instead of the moment he stops and stares at the screen waiting.
            # Off-thread and after the mic is already live, so it can never
            # delay or interfere with the take itself.
            if self.settings.get("asr_engine", "local") == "local" \
                    and self.settings.get("gpu_hold", True):
                threading.Thread(
                    target=LOCAL_ASR.hold_warm,
                    args=(lambda: self.recording,), daemon=True).start()
        # hold-to-talk: if the key was released during the ~300ms prep,
        # honor it now instead of recording forever
        if getattr(self, "_want_stop", False):
            self._want_stop = False
            self._stop_inner()

    def _start_watchdog(self):
        """Stop at MAX_SECONDS instead of recording forever. Without this a
        forgotten take grows the frame queue unbounded (~64KB/s) and then
        gets silently truncated at stop time â€” minutes of speech vanishing
        with no message."""
        started = self.started_at

        def watch():
            while not self.quitting:
                time.sleep(1.0)
                if not self.recording or self.started_at != started:
                    return
                if time.time() - started >= MAX_SECONDS:
                    logging.warning("watchdog: stopping at %ss", MAX_SECONDS)
                    self.on_state("recording", "limit")
                    self.stop_recording()
                    return
        threading.Thread(target=watch, daemon=True).start()

    def _stop_inner(self):
        with self.lock:
            if not self.recording:
                if getattr(self, "_starting", False):
                    self._want_stop = True
                return
            self.recording = False
            self.level = 0.0
            self.stream.stop()
            self.stream.close()
            self._play(self.stop_wav, block=False)
            elapsed = time.time() - self.started_at
            chunks = []
            while not self.frames.empty():
                chunks.append(self.frames.get())
            mode, self.mode = self.mode, "dictate"
            raw_once, self._raw_once = self._raw_once, False
            if not chunks or elapsed < 0.3:
                self.on_state("idle", "Too short â€” ignored")
                return
            audio = np.concatenate(chunks).flatten()[: MAX_SECONDS * SAMPLE_RATE]
            if not _speech_present(audio):
                # silent/accidental tap â€” never send it: the model invents
                # words ("ÙØ±Ø§Øº", "â™«") from amplified nothing
                self.on_state("idle", "Nothing heard â€” skipped")
                return
            if self.settings.get("audio_enhance", True):
                try:
                    audio = _enhance_audio(audio)
                except Exception:
                    logging.exception("audio enhance failed â€” using raw")
            self.on_state("transcribing", "")
            # snapshot EVERYTHING the worker needs â€” a second recording
            # started mid-transcription must not swap state under it
            if mode == "note":
                self._spawn(self._note_transcribe, audio, elapsed,
                            self.language)
            elif mode == "command":
                self._spawn(self._command_transcribe, audio, elapsed,
                            self.language, self._cmd_selection)
            elif mode == "refine":
                self._spawn(self._command_transcribe, audio, elapsed,
                            self.language, self.on_last_text(), True)
            else:
                self._spawn(self._transcribe, audio, elapsed, self.language,
                            self._app_ctx, raw_once)

    def _spawn(self, fn, *args):
        """Run a worker with a top-level guard. An unguarded raise killed the
        thread silently: no transcript, no error in the UI, and the pill stuck
        on 'Transcribingâ€¦' until restart."""
        def run():
            try:
                fn(*args)
            except Exception:
                logging.exception("%s crashed", fn.__name__)
                self._worker_state("error", "Something went wrong â€” see app.log")
        threading.Thread(target=run, daemon=True).start()

    def _split_points(self, audio):
        """Cut a long take into <=CHUNK_SECONDS pieces, snapping each cut to
        the quietest 20ms window inside a +/-3s search band so we land in a
        pause instead of mid-word."""
        step = CHUNK_SECONDS * SAMPLE_RATE
        if len(audio) <= step:
            return [(0, len(audio))]
        slack = 3 * SAMPLE_RATE
        win = SAMPLE_RATE // 50
        cuts, pos = [0], step
        while pos < len(audio) - slack:
            lo, hi = max(cuts[-1] + SAMPLE_RATE, pos - slack), min(len(audio), pos + slack)
            band = audio[lo:hi]
            n = len(band) // win
            if n:
                rms = [float(np.sqrt(np.mean(band[i * win:(i + 1) * win] ** 2)))
                       for i in range(n)]
                pos = lo + int(np.argmin(rms)) * win
            cuts.append(pos)
            pos += step
        cuts.append(len(audio))
        return list(zip(cuts[:-1], cuts[1:]))

    def _asr(self, wav_bytes, lang):
        """Transcribe one already-encoded WAV. Returns (text, error)."""
        data = {"model": MODEL, "language": "ar" if lang == "auto" else lang}
        last_err = "Network error â€” check connection"
        for attempt in range(4):
            try:
                resp = self._http.post(
                    API_URL,
                    headers={"Authorization": f"Bearer {self.api_key}"},
                    data=data,
                    files={"file": ("audio.wav", io.BytesIO(wav_bytes),
                                    "audio/wav")},
                    # (connect, read) — and the FIRST value is what actually
                    # matters here. urllib3 leaves the connect timeout as the
                    # socket timeout while the request BODY is being sent, so
                    # it caps how long a single send() may block, not just
                    # connection setup. On a congested uplink the TCP window
                    # closes and one send() on a chunk-sized body blocks well
                    # past 10s -> "write operation timed out", while the 300s
                    # read timeout never comes into play at all.
                    #
                    # Measured 2026-08-03 on the same link, same 1.44MB body:
                    #   connect=10  -> FAILED at 10.5s
                    #   connect=60  -> OK in 20.1s
                    #   connect=120 -> OK in 17.2s
                    # A real connection error still fails fast (TCP refuses or
                    # DNS fails immediately), so a high value costs nothing.
                    timeout=(90, 300),
                )
            except requests.RequestException:
                logging.exception("asr attempt %s/4 failed", attempt + 1)
                time.sleep(2.0 * (attempt + 1))
                continue
            if resp.status_code == 200:
                return resp.json().get("text", "").strip(), None
            if resp.status_code == 429:
                # Two very different things arrive as 429. A per-minute
                # burst limit clears on its own, so retrying is right. A
                # MONTHLY quota does not clear for days or weeks, and every
                # retry BURNS another call against the very cap that is
                # blocking us - 4 attempts x N chunks per take, all wasted.
                # Field failure 2026-08-19: the trial key hit its 1000
                # calls/month cap and the app reported "Network error -
                # check connection", which sent everyone hunting a
                # connectivity problem that did not exist.
                body = (resp.text or "")[:400]
                if _quota_exhausted(body):
                    logging.error("API QUOTA EXHAUSTED: %s", body)
                    return None, QUOTA_MSG
                last_err = "Rate limited - try again in a minute"
                logging.warning("rate limited (attempt %s/4): %s",
                                attempt + 1, body[:160])
                time.sleep(5.0)
                continue
            logging.error("api %s: %s", resp.status_code, resp.text[:300])
            return None, f"API error {resp.status_code}"
        return None, last_err

    def _asr_audio(self, audio, lang, on_progress=None):
        """Transcribe a float32 take of ANY length.

        Long dictations used to fail outright: 16kHz PCM16 is ~32KB/s, so a
        3.5-minute take is a ~6.7MB single upload and a slow uplink times the
        write out (field failures 2026-07-31). Splitting into CHUNK_SECONDS
        pieces keeps every request ~1.4MB, which uploads reliably â€” and a
        chunk that still fails only costs its own slice, not the whole take.

        'auto' maps to 'ar': the API REQUIRES a language and rejects 'auto'
        (probed), and the code-switch model handles pure English under 'ar'.
        """
        # Reset up front, not per-branch: the single-span fast path below
        # returns without touching it, so a previous chunked take that lost a
        # chunk left the flag set and the NEXT clean take was reported as
        # partial data loss. Covers transcribe_file retries and command mode.
        self._last_partial = None

        # LOCAL: no upload, so none of the chunking exists. The whole take
        # goes through in one pass and neither length nor uplink matters.
        if self.settings.get("asr_engine", "local") == "local":
            try:
                if on_progress:
                    on_progress(1, 1)
                t0 = time.time()
                text = LOCAL_ASR.transcribe(audio, lang)
                logging.info("local ASR: %.0fs audio in %.1fs on %s",
                             len(audio) / SAMPLE_RATE, time.time() - t0,
                             LOCAL_ASR.device)
                return (text, None) if text else (None, "Nothing recognized")
            except Exception as e:
                logging.exception("local ASR failed")
                return None, f"Local model failed - {type(e).__name__}"

        spans = self._split_points(audio)
        if len(spans) == 1:
            buf = io.BytesIO()
            sf.write(buf, audio, SAMPLE_RATE, format="WAV", subtype="PCM_16")
            text, err = self._asr(buf.getvalue(), lang)
            return (None, err) if err else ((text or "").strip(), None)

        # UPLOAD ONE CHUNK AT A TIME. Do not "optimise" this into a thread
        # pool — that was tried and it reintroduced the exact bug chunking
        # exists to prevent.
        #
        # Chunking is not about request count, it is about how many BYTES are
        # in flight on a narrow uplink. Firing N chunks together puts the
        # whole take on the wire again, just split across N sockets that share
        # the same upstream bandwidth, so every one of them crawls and they
        # all hit the write timeout together. Field failure 2026-08-03: a
        # 117s take split into 3 chunks, all 4 attempts of all 3 chunks timing
        # out in lockstep (identical log timestamps). The same audio, same
        # network, uploaded sequentially minutes later: every chunk succeeded
        # in 6-14 seconds.
        #
        # Sequential is also strictly better on failure: a chunk that dies
        # does not drag its siblings down with it.
        parts, failed, quota = [], 0, False
        for i, (a, b) in enumerate(spans):
            if on_progress:
                on_progress(i + 1, len(spans))
            buf = io.BytesIO()
            sf.write(buf, audio[a:b], SAMPLE_RATE, format="WAV", subtype="PCM_16")
            text, err = self._asr(buf.getvalue(), lang)
            if err:
                logging.error("chunk %s/%s failed: %s", i + 1, len(spans), err)
                failed += 1
                if err == QUOTA_MSG:
                    # the cap is account-wide; the remaining chunks cannot
                    # succeed and each attempt spends more of it
                    quota = True
                    logging.error("stopping after chunk %s/%s - quota is gone",
                                  i + 1, len(spans))
                    break
                continue
            if text:
                parts.append(text)
        if not parts:
            return None, QUOTA_MSG if quota else "Network error - check connection"
        out = " ".join(parts)
        if failed:
            # partial beats nothing, but it must NOT read as a clean success:
            # the entry gets flagged so the row offers Retry on the full audio
            logging.warning("%s/%s chunks lost", failed, len(spans))
            self._last_partial = (failed, len(spans))
        else:
            self._last_partial = None
        return out, None

    def _keep_audio(self, wav_bytes, t0):
        """Persist the take BEFORE any network I/O â€” a failed upload must
        never cost the user a re-record. Rolling cap; oldest pruned."""
        try:
            os.makedirs(AUDIO_DIR, exist_ok=True)
            name = f"{int(t0 * 1000)}.wav"
            with open(os.path.join(AUDIO_DIR, name), "wb") as f:
                f.write(wav_bytes)
            for old in sorted(os.listdir(AUDIO_DIR))[:-AUDIO_KEEP]:
                os.remove(os.path.join(AUDIO_DIR, old))
            return name
        except OSError:
            logging.exception("audio save failed")
            return ""

    def _worker_state(self, state, detail=""):
        """State pushes from finished/finishing workers. A live recording
        owns the status UI â€” a stale worker's 'cleaning'/'idle'/'error' must
        not stomp it on the main window or the pill."""
        if self.recording:
            return
        self.on_state(state, detail)

    def _cancelled(self, gen):
        return gen != self._gen

    # Windows whose focus means a Ctrl+V lands nowhere: the desktop and the
    # taskbar. Deliberately narrow - a false "it went nowhere" would tell him
    # to paste again into a field that already got the text.
    _BLIND_CLASSES = ("Progman", "WorkerW", "Shell_TrayWnd",
                      "Shell_SecondaryTrayWnd")

    @classmethod
    def _paste_is_blind(cls):
        try:
            u = ctypes.windll.user32
            fg = u.GetForegroundWindow()
            if not fg:
                return True
            buf = ctypes.create_unicode_buffer(64)
            u.GetClassNameW(fg, buf, 64)
            return buf.value in cls._BLIND_CLASSES
        except Exception:
            return False

    def _insert_text(self, text):
        """Deliver text into the focused field. The transcript always lands
        in the clipboard too â€” manual Ctrl+V is the recovery path."""
        with self._clip_lock:
            pyperclip.copy(text)
            # the bar reads this to say "copied - Ctrl+V" instead of a word
            # count when nothing that accepts text had focus
            self.last_paste_blind = self._paste_is_blind()
            if self.settings.get("paste_mode", "paste") == "type":
                _send_type(text)
            else:
                # Wait for the clipboard to actually hold the text instead of
                # sleeping a flat 150ms and hoping. Typically returns in a few
                # ms â€” and unlike the fixed guess it is still correct when a
                # clipboard manager makes the write slower than 150ms.
                deadline = time.monotonic() + 0.15
                while time.monotonic() < deadline:
                    try:
                        if pyperclip.paste() == text:
                            break
                    except Exception:
                        break
                    time.sleep(0.005)
                _send_paste()

    def _transcribe(self, audio, duration, lang, app_ctx="general",
                    raw_once=False):
        t0 = time.time()
        gen = self._gen
        buf = io.BytesIO()
        sf.write(buf, audio, SAMPLE_RATE, format="WAV", subtype="PCM_16")
        wav = buf.getvalue()
        # stays SYNCHRONOUS on purpose: persisting before any network I/O is
        # what guarantees a failed upload never costs the user a re-record.
        # It is a local write of a couple of MB â€” tens of ms against seconds
        # of model latency, so there is nothing here worth trading away.
        audio_name = self._keep_audio(wav, t0)
        text, err = self._asr_audio(
            audio, lang,
            lambda i, n: self._worker_state("transcribing", f"{i}/{n}"))
        if self._cancelled(gen):
            logging.info("transcribe cancelled â€” result dropped")
            return
        if err:
            # the take is safe on disk â€” surface a retryable failed entry
            # in the feed instead of throwing the recording away
            entry = {
                "ts": time.time(), "lang": lang, "text": "",
                "secs": round(duration, 1), "words": 0,
                "latency": round(time.time() - t0, 1), "cleaned": False,
                "raw": "", "audio": audio_name, "app": app_ctx,
                "failed": err,
            }
            self.on_transcript(entry)
            self._worker_state("error", err + (" â€” take saved, retry from "
                                               "history" if audio_name else ""))
            return
        if not text:
            self._worker_state("idle", "Nothing recognized")
            return

        snippet = None if raw_once else _match_snippet(
            text, self.settings.get("snippets"))
        if snippet is not None:
            self._insert_text(snippet)
            entry = {
                "ts": time.time(), "lang": lang, "text": snippet,
                "secs": round(duration, 1), "words": len(snippet.split()),
                "latency": round(time.time() - t0, 1), "cleaned": False,
                "raw": "", "audio": audio_name, "app": app_ctx,
                "snippet": True,
            }
            self.on_transcript(entry)
            self._worker_state("idle", "")
            return

        raw_text = text
        cleaned = False
        if raw_once:
            logging.info("raw take (shift held) â€” Flow skipped")
        elif self.settings.get("flow_mode", True):
            self._worker_state("cleaning", "")
            out = self._flow_clean(text, app_ctx)
            if out:
                text, cleaned = out, True
            else:
                logging.warning("flow cleanup unavailable â€” pasted raw")

        text = _apply_dictionary(
            text, _parse_dictionary(self.settings.get("dictionary", "")))

        if self._cancelled(gen):
            logging.info("cancelled during cleanup â€” not pasting")
            return
        self._insert_text(text)
        entry = {
            "ts": time.time(),
            "lang": lang,
            "text": text,
            "secs": round(duration, 1),
            "words": len(text.split()),
            "latency": round(time.time() - t0, 1),
            "cleaned": cleaned,
            "raw": raw_text if cleaned else "",  # for "Undo AI edit"
            "audio": audio_name,                 # for retry / extract audio
            "app": app_ctx,                      # for per-app insights
        }
        partial = self._last_partial
        if partial:
            lost, total = partial
            entry["partial"] = f"{lost} of {total} sections were lost"
        self.on_transcript(entry)
        if partial:
            self._worker_state(
                "error", f"Part of that take was lost ({partial[0]}/"
                         f"{partial[1]} sections) â€” retry from history")
        else:
            self._worker_state("idle", "" if cleaned or not self.settings.get(
                "flow_mode", True)
                else "Pasted raw â€” Flow couldn't reach the AI")

    def transcribe_file(self, path, lang, on_progress=None):
        """Re-run transcription on a kept recording. Returns text or None.
        Goes through the chunked path too â€” retries were failing on exactly
        the long takes that needed them most."""
        try:
            audio, sr = sf.read(path, dtype="float32")
        except Exception:
            logging.exception("retry: audio read failed")
            return None
        if audio.ndim > 1:
            audio = audio.mean(axis=1)
        text, err = self._asr_audio(audio, lang, on_progress)
        if err:
            logging.error("retry failed: %s", err)
        return text or None

    # ---------- command mode (voice-edit selection) ----------

    def start_command(self):
        """Wispr-style voice edit: grab the current selection via clipboard,
        then record a spoken instruction to apply to it."""
        if self.recording:
            return
        # mark "starting" through the clipboard capture too, so a hold-mode
        # release in this window queues _want_stop instead of getting lost
        self._starting = True
        with self._clip_lock:
            try:
                old_clip = pyperclip.paste()
            except Exception:
                old_clip = ""
            try:
                pyperclip.copy("")   # sentinel: empty = nothing was selected
                _send_copy()
                time.sleep(0.18)     # let the target app service WM_COPY
                sel = pyperclip.paste()
            except Exception:
                logging.exception("command: clipboard capture failed")
                sel = ""
        if not sel.strip():
            self._starting = False
            self._want_stop = False
            try:
                pyperclip.copy(old_clip)
            except Exception:
                pass
            self.on_state("error", "Select some text first, then press "
                          f"{self.settings.get('command_key', 'f8').upper()}")
            return
        self._cmd_selection = sel
        self.mode = "command"
        self.start_recording()

    def toggle_command(self):
        if self.recording:
            self.stop_recording()
        else:
            self.start_command()

    def stop_command(self):
        self.stop_recording()

    def _command_transcribe(self, audio, duration, lang, selection,
                            refine=False):
        t0 = time.time()
        gen = self._gen
        # command takes were the one path that never hit disk â€” a failed or
        # cancelled voice-edit used to cost the recording outright
        buf = io.BytesIO()
        sf.write(buf, audio, SAMPLE_RATE, format="WAV", subtype="PCM_16")
        audio_name = self._keep_audio(buf.getvalue(), t0)
        instruction, err = self._asr_audio(audio, "auto")
        if self._cancelled(gen):
            logging.info("command cancelled before edit â€” nothing pasted")
            return
        if err or not instruction:
            self._worker_state("error", err or "Didn't catch the instruction")
            return
        self._worker_state("cleaning", "")
        out = self._chat(
            "You edit text by voice command. Apply the INSTRUCTION to the "
            "TEXT and return ONLY the edited text â€” no quotes, no commentary, "
            "no explanation. Preserve the text's original language and "
            "formatting style unless the instruction says otherwise (e.g. "
            "asks for a translation).\n\n"
            f"INSTRUCTION: {instruction}\n\nTEXT:\n{selection}")
        if not out:
            self._worker_state("error", "Edit failed â€” try again")
            return
        if self._cancelled(gen):
            # the user dismissed this edit and has almost certainly moved on;
            # pasting now would dump it into an unrelated window
            logging.info("command cancelled during edit â€” not pasting")
            return
        # insertion replaces the still-highlighted selection in the target app
        self._insert_text(out)
        entry = {
            "ts": time.time(),
            "lang": lang,
            "text": out,
            "secs": round(duration, 1),
            "words": len(out.split()),
            "latency": round(time.time() - t0, 1),
            "cleaned": True,
            "raw": selection,     # "Undo AI edit" restores the original
            "cmd": instruction,   # shown as the edit badge tooltip
            "audio": audio_name,
            "refine": refine,
        }
        self.on_transcript(entry)
        self._worker_state("idle", "")

    # ---------- AI cleanup ----------

    def _organize_note(self, text):
        """Split a dump into {title, tasks, notes}. Never returns None.

        Sorting happens on this machine by default, like transcription does.
        A Cohere key is an upgrade, not a requirement: it reads intent better
        and tidies grammar properly, but the notebook must not stop working
        because a key expired, and it must not need the network to file a
        thought. If the key is missing, dead or unconvincing, the local
        splitter answers instead."""
        if self.api_key and not getattr(self, "_chat_dead", False):
            ai = self._organize_note_chunked(text)
            if ai:
                ai["by"] = "ai"
                return ai
        return _organize_locally(text)

    def _organize_note_chunked(self, text):
        """Organize a dump in pieces small enough that the model cannot
        summarise it.

        A single call on a long take came back holding 35-41% of what he said.
        That is not a prompt problem - a model asked to restructure 9000
        characters in one response compresses, however firmly it is told not
        to. The fix is the same one the Flow cleanup already uses: cut the
        text at sentence boundaries and ask about one piece at a time, where
        there is nothing to compress.

        A piece the model mangles or refuses is kept as a NOTE, verbatim.
        Nothing he said is ever dropped on the floor - previously a failure
        here handed the whole take to the local splitter, which shredded it."""
        chunks = _chunk_for_notes(text)
        if len(chunks) == 1:
            got = self._organize_note_ai(chunks[0])
            return got or None
        logging.info("note organize: %d chunks", len(chunks))
        tasks, notes, title = [], [], ""
        won = 0
        for i, chunk in enumerate(chunks):
            got = self._organize_note_ai(chunk)
            if got:
                won += 1
                title = title or got.get("title") or ""
                tasks.extend(got.get("tasks", []))
                notes.extend(got.get("notes", []))
            else:
                # keep the piece rather than lose it
                logging.warning("note organize: chunk %d/%d kept raw",
                                i + 1, len(chunks))
                notes.append(chunk.strip())
        if not won:
            return None
        return {"title": title[:60], "tasks": tasks, "notes": notes}

    def _organize_note_ai(self, text):
        out = self._chat(NOTE_PROMPT + text)
        if not out:
            return None
        # models still fence JSON now and then despite being told not to
        out = re.sub(r"^\s*```(?:json)?|```\s*$", "", out.strip()).strip()
        try:
            data = json.loads(out)
        except ValueError:
            # last resort: the first {...} span in the reply
            m = re.search(r"\{.*\}", out, re.S)
            if not m:
                logging.warning("note organize: no JSON in reply")
                return None
            try:
                data = json.loads(m.group(0))
            except ValueError:
                logging.warning("note organize: unparseable JSON")
                return None
        if not isinstance(data, dict):
            return None

        def lines(key):
            v = data.get(key) or []
            if isinstance(v, str):
                v = [v]
            return [s.strip() for s in v
                    if isinstance(s, str) and s.strip()][:60]

        tasks, notes = lines("tasks"), lines("notes")
        if not tasks and not notes:
            return None
        # A dump that comes back far shorter than it went in means the model
        # summarised instead of sorting, which is the one failure the raw copy
        # exists to catch - but we would rather file the raw take than show a
        # confident, lossy version of it.
        kept = sum(len(s) for s in tasks + notes)
        if kept < len(text) * 0.45:
            logging.warning("note organize: model returned %d%% of the dump - "
                            "summarised instead of sorting, using local split",
                            round(kept * 100 / max(1, len(text))))
            return None
        title = (data.get("title") or "").strip().strip(".:")
        return {"title": title[:60], "tasks": tasks, "notes": notes}

    def _note_transcribe(self, audio, duration, lang):
        """Transcribe a notebook take and hand it to the app to file. Nothing
        here touches the clipboard or the focused window."""
        t0 = time.time()
        gen = self._gen
        buf = io.BytesIO()
        sf.write(buf, audio, SAMPLE_RATE, format="WAV", subtype="PCM_16")
        audio_name = self._keep_audio(buf.getvalue(), t0)
        text, err = self._asr_audio(
            audio, lang,
            lambda i, n: self._worker_state("transcribing", f"{i}/{n}"))
        if self._cancelled(gen):
            logging.info("note cancelled - result dropped")
            return
        if err:
            self._worker_state("error", err)
            return
        if not text:
            self._worker_state("idle", "Nothing recognized")
            return
        text = _apply_dictionary(
            text, _parse_dictionary(self.settings.get("dictionary", "")))
        self._worker_state("cleaning", "")
        org = self._organize_note(text)
        if self._cancelled(gen):
            return
        entry = {
            "ts": time.time(),
            "day": time.strftime("%Y-%m-%d"),
            "raw": text,
            "title": (org or {}).get("title") or "",
            "tasks": [{"id": f"{int(time.time()*1000)}-{i}", "text": t,
                       "done": False, "done_ts": None}
                      for i, t in enumerate((org or {}).get("tasks", []))],
            "notes": (org or {}).get("notes") or ([text] if not org else []),
            "organized": bool(org),
            # which splitter produced this. The page badges it, and the answer
            # has to be honest: he reads "AI" as "these are not exactly my
            # words" and "On device" as "nothing left this machine".
            "by": (org or {}).get("by", "local"),
            "secs": round(duration, 1),
            "words": len(text.split()),
            "audio": audio_name,
        }
        self.on_note(entry)
        n = len(entry["tasks"])
        self._worker_state("idle", "Noted" + (f" - {n} task{'s'*(n!=1)}" if n else ""))

    def _chat(self, prompt):
        """One Cohere chat call with the model-fallback chain. Transient
        failures (429, network blips) retry â€” a silently skipped cleanup
        reads to the user as 'the feature is broken'."""
        transient = 0
        # Snapshot the fallback cursor into a LOCAL. _clean_chunked now calls
        # this from several threads at once; sharing the live attribute let
        # four segments each advance it on the same dead model, burning the
        # whole 3-model chain in one step, and the read-then-index across the
        # while guard could raise IndexError. Advances are published back
        # monotonically under the existing lock.
        idx = self._clean_model_idx
        while idx < len(CLEANUP_MODELS):
            model = CLEANUP_MODELS[idx]
            try:
                resp = self._http.post(
                    CHAT_URL,
                    headers={"Authorization": f"Bearer {self.api_key}"},
                    json={"model": model,
                          "messages": [{"role": "user", "content": prompt}],
                          "temperature": 0.1,
                          # generous ceiling: cleanup output is the same
                          # length as its input, never a summary
                          "max_tokens": 4000},
                    # a whole-transcript cleanup was measured taking >180s and
                    # timing out at the old 45s, which is why every long take
                    # silently pasted raw
                    timeout=(10, 150),
                )
            except requests.RequestException:
                logging.exception("chat call failed")
                transient += 1
                if transient > 2:
                    return None
                time.sleep(1.5 * transient)
                continue
            if resp.status_code == 200:
                try:
                    parts = resp.json()["message"]["content"]
                    out = "".join(p.get("text", "") for p in parts).strip()
                    return out or None
                except (KeyError, IndexError, TypeError):
                    logging.error("chat parse failed: %s", resp.text[:300])
                    return None
            if resp.status_code == 401:
                # A bad key is not transient and is identical on every model,
                # so walking the chain just buys three more 401s. Latch it:
                # the notebook falls straight through to the local splitter
                # instead of stalling ~2s on a doomed round-trip per note.
                # Cleared by save_key, so pasting a good key works at once.
                self._chat_dead = True
                logging.error("chat disabled - API key rejected (401)")
                return None
            if resp.status_code == 429:
                # a spent monthly cap will not clear; retrying only eats more
                if _quota_exhausted(resp.text or ""):
                    logging.error("cleanup skipped - API quota exhausted")
                    return None
                transient += 1
                if transient > 2:
                    return None
                time.sleep(3.0)
                continue
            if resp.status_code == 422:
                # NO_VALID_RESPONSE_GENERATED: Cohere refusing to answer THIS
                # request on THIS model. It used to return None, which is a
                # straight "pasted raw" for the user (three times on
                # 2026-08-28); a sibling model usually answers it fine.
                # Deliberately does NOT publish the cursor: the model is
                # healthy, so demoting it for the whole session over one odd
                # chunk would be wrong.
                logging.warning("chat model %s gave no response (422)", model)
                idx += 1
                continue
            if resp.status_code in (400, 404):
                logging.warning("chat model %s unavailable (%s)", model,
                                resp.status_code)
                idx += 1
                with self.lock:
                    self._clean_model_idx = max(self._clean_model_idx, idx)
                continue
            logging.warning("chat api %s: %s", resp.status_code, resp.text[:200])
            return None
        # every model 404'd (key lost access?) â€” re-probe from the top next
        # call instead of staying dead for the rest of the session
        self._clean_model_idx = 0
        return None

    @staticmethod
    def _text_chunks(text, limit=CLEAN_CHARS):
        """Split on sentence ends so each cleanup call is small. Keeps the
        model from compressing a whole transcript into a summary, and keeps
        every request well inside the timeout."""
        if len(text) <= limit:
            return [text]
        parts, buf = [], ""
        for piece in re.split(r"(?<=[.!?ØŸà¥¤\n])\s+", text):
            if buf and len(buf) + len(piece) + 1 > limit:
                parts.append(buf.strip())
                buf = piece
            else:
                buf = f"{buf} {piece}".strip()
        if buf.strip():
            parts.append(buf.strip())
        return parts or [text]

    @staticmethod
    def _plausible(original, cleaned):
        """Is this cleanup trustworthy enough to paste?

        A language model can degenerate â€” one real run returned
        '(100)(2)(3)(4)(3)(3)(3)â€¦' for a paragraph of speech â€” or quietly
        summarize. For a text-FIDELITY task the output must be checked, not
        assumed. Rejecting a bad cleanup costs polish; accepting one costs
        the user's actual words.

        Length alone used to be the whole gate, and it let real content out
        through the floor: at 0.55 the model could delete FORTY-FIVE PERCENT
        of a segment and still be pasted. That is the "it cut half of what I
        said" failure. Length is now only a coarse net; the real check is that
        the speaker's own content words survived, which also catches a cleanup
        that drops a point and pads the gap back up with prose.

        The length floor stays low on purpose - it is now only a degeneracy
        net. Raising it instead of adding the content check just traded the
        old false accepts for false rejects: a segment thick with 'يعني' and
        'you know' legitimately cleans down to 0.7 of its length with every
        single point intact, and rejecting that costs polish for nothing. It
        is lower than the old 0.55 for that reason, not looser: what used to
        pass at 0.56 with half the points gone now fails the content check."""
        if not cleaned or not cleaned.strip():
            return False, "empty"
        ratio = len(cleaned) / max(1, len(original))
        if ratio < 0.45:
            return False, f"summarized to {ratio:.0%}"
        if ratio > 1.7:
            return False, f"ballooned to {ratio:.0%}"
        said = _content_words(original)
        if said:
            kept = len(said & _content_words(cleaned)) / len(said)
            if kept < 0.85:
                lost = sorted(said - _content_words(cleaned))[:6]
                return False, f"dropped {1 - kept:.0%} of content words {lost}"
        words = cleaned.split()
        if len(words) > 12 and len(set(words)) / len(words) < 0.25:
            return False, "degenerate repetition"
        letters = sum(c.isalpha() or c.isspace() for c in cleaned)
        if letters / len(cleaned) < 0.55:
            return False, "mostly punctuation/digits"
        return True, ""

    def _clean_one(self, recipe, label, chunk, idx, total):
        """Clean one segment, validate it, retry once, else keep the
        original words."""
        tag = f" (part {idx} of {total})" if total > 1 else ""
        why = ""
        for attempt in range(2):
            # The retry used to re-send the IDENTICAL prompt. At temperature
            # 0.1 that mostly returns the identical rejected answer, so the
            # second attempt was a wasted round-trip. Tell it what it did.
            fix = (f"\n\nYOUR PREVIOUS ATTEMPT WAS REJECTED: {why}. You lost "
                   "the speaker's words. Redo it keeping EVERY point, name, "
                   "number and aside; change only punctuation, filler and "
                   "layout." if why else "")
            got = self._chat(f"{recipe}{fix}\n\n{label}{tag}: {chunk}")
            if got is None:
                return None                      # transport failure
            ok, why = self._plausible(chunk, got)
            if ok:
                return got
            logging.warning("cleanup rejected (%s), attempt %s/2: %r",
                            why, attempt + 1, got[:120])
        return ""                                 # keep the original text

    def _clean_chunked(self, recipe, text, label):
        """Run `recipe` over the text in segments. A segment that fails or
        comes back untrustworthy keeps its ORIGINAL text â€” losing the user's
        words is strictly worse than leaving them unpolished."""
        chunks = self._text_chunks(text)
        if len(chunks) == 1:
            # `got or None` keeps _clean_one's contract: None is a transport
            # failure and "" is "the model answered but _plausible rejected
            # it". Both mean nothing was cleaned, which is what the chunked
            # path signals with `if failed + rejected == len(chunks)`. Mapping
            # "" to the original text instead stamped the history entry
            # cleaned=True and hid the "pasted raw" status from the user.
            return self._clean_one(recipe, label, chunks[0], 1, 1) or None
        # Segments are cleaned independently and re-joined in order, so the
        # sequential loop just stacked one full model latency per 1400 chars
        # â€” a 3-chunk take waited for three round-trips back to back. Run
        # them together; the join below still restores the original order.
        got_by_i = {}
        # Width matters: at 4 workers a long take ran in waves (a 5-chunk take
        # paid two full round-trips back to back), which is most of why Flow
        # feels so much slower than raw transcription. These are tiny requests
        # to a hosted API, not local CPU work, so the pool can be as wide as
        # the take is long.
        with cf.ThreadPoolExecutor(max_workers=min(12, len(chunks))) as pool:
            futs = {pool.submit(self._clean_one, recipe, label, c,
                                i + 1, len(chunks)): i
                    for i, c in enumerate(chunks)}
            for f in cf.as_completed(futs):
                i = futs[f]
                try:
                    got_by_i[i] = f.result()
                except Exception:
                    logging.exception("cleanup segment %s crashed", i + 1)
                    got_by_i[i] = None
        out, failed, rejected = [], 0, 0
        for i, c in enumerate(chunks):
            got = got_by_i.get(i)
            if got:
                out.append(got)
            else:
                if got is None:
                    failed += 1      # transport failure
                else:
                    rejected += 1    # model returned something untrustworthy
                out.append(c)        # keep the user's own words
        if failed or rejected:
            logging.warning("cleanup: %s/%s segments left raw "
                            "(%s network, %s rejected)",
                            failed + rejected, len(chunks), failed, rejected)
        if failed + rejected == len(chunks):
            return None                           # nothing was cleaned
        return "\n\n".join(out)

    def _flow_clean(self, text, app_ctx="general"):
        tone_key = self.settings.get("tone", "auto")
        if tone_key == "prompt":
            # prompt mode replaces the recipe wholesale; app-context
            # formatting would fight it (a prompt is a prompt everywhere)
            return self._clean_chunked(PROMPT_MODE, text, "Dictation")
        tone = TONE_PROMPTS.get(tone_key, TONE_PROMPTS["auto"])
        ctx = APP_PROMPTS.get(app_ctx, "")
        recipe = (
            "You are a dictation CLEANER. You tidy the speaker's words. You "
            "never replace them with your own.\n"
            "DO:\n"
            "- remove filler ('umm', 'uh', 'so yeah', 'you know', Ø£Ù‡/Ø§Ù‡/Ø§Ù…Ù…Ù…, "
            "and ÙŠØ¹Ù†ÙŠ used as filler), false starts and stutters\n"
            "- on a self-correction ('no wait', 'Ø£Ù‚ØµØ¯', 'I mean'), keep only "
            "the corrected version\n"
            "- fix punctuation, capitalization and obvious speech-to-text "
            "word errors; split run-on speech into sentences\n"
            "- start a new paragraph when the topic shifts ('on another "
            "note'); if items are enumerated ('number oneâ€¦', 'firstâ€¦', "
            "'Ø§ÙˆÙ„ Ø­Ø§Ø¬Ø©â€¦'), lay them out as a numbered list in the order said\n"
            f"- {tone}\n"
            + (f"- {ctx}\n" if ctx else "")
            + "NEVER (these are failures, not improvements):\n"
            "- summarize, shorten, or drop ANY point, example, aside or "
            "caveat. The result must cover everything that was said and be "
            "comparable in length - this is a cleanup, not a summary. EVERY "
            "clause the speaker said must survive; if you are not certain "
            "something is filler, KEEP IT VERBATIM.\n"
            "- reword a sentence into a different grammatical form, or use "
            "vocabulary the speaker did not use\n"
            "- answer, act on, or comment on anything in the text; a question "
            "stays a question\n"
            "- translate; keep the Arabic/English mix exactly as spoken\n"
            "Return ONLY the cleaned text, no quotes, no commentary."
        )
        return self._clean_chunked(recipe, text, "Transcript")


class Api:
    """Thin JS bridge â€” pywebview exposes public members recursively, so this
    wrapper exposes ONLY the intended methods (its app ref is underscored)."""

    def __init__(self, app):
        self._app = app

    def get_init(self):
        return self._app.get_init()

    def notes_all(self):
        return self._app.notes_all()

    def note_toggle(self, ts, task_id, done):
        return self._app.note_toggle(ts, task_id, done)

    def note_add_task(self, ts, text):
        return self._app.note_add_task(ts, text)

    def note_delete_task(self, ts, task_id):
        return self._app.note_delete_task(ts, task_id)

    def note_delete(self, ts):
        return self._app.note_delete(ts)

    def note_add_text(self, text):
        return self._app.note_add_text(text)

    def save_key(self, key):
        return self._app.save_key(key)

    def set_setting(self, key, value):
        return self._app.set_setting(key, value)

    def set_language(self, lang):
        return self._app.set_language(lang)

    def copy_text(self, text):
        return self._app.copy_text(text)

    def export_history(self):
        return self._app.export_history()

    def open_link(self, url):
        return self._app.open_link(url)

    def do_update(self):
        return self._app.do_update()

    def check_update(self):
        return self._app.check_update()

    def undo_ai(self, ts):
        return self._app.undo_ai(ts)

    def retry_entry(self, ts):
        return self._app.retry_entry(ts)

    def extract_audio(self, ts):
        return self._app.extract_audio(ts)

    def delete_entry(self, ts):
        return self._app.delete_entry(ts)

    def quit(self):
        return self._app.quit()


class PillApi:
    """JS bridge for the floating pill â€” deliberately separate from Api so
    the always-on-top HUD cannot reach history, settings or the API key."""

    def __init__(self, app):
        self._app = app

    def pill_drag_start(self):
        return self._app.pill_drag_start()

    def pill_drag_move(self, dx, dy):
        return self._app.pill_drag_move(dx, dy)

    def pill_drag_end(self):
        return self._app.pill_drag_end()

    def pill_set_pos(self, pos):
        return self._app.pill_set_pos(pos)

    def pill_panel(self, open_):
        return self._app.pill_panel(open_)

    def pill_cancel(self):
        return self._app.pill_cancel()

    def pill_open(self):
        return self._app.pill_open()

    def pill_ready(self):
        return self._app.pill_ready()

    def pill_hover_in(self):
        return self._app.pill_hover_in()

    def pill_hover_out(self):
        return self._app.pill_hover_out()

    def pill_undo(self):
        return self._app.pill_undo()

    def pill_copy_last(self):
        return self._app.pill_copy_last()

    def pill_snooze(self):
        return self._app.pill_snooze()


class DialFlow:
    """Bridges the engine to the web UI."""

    def __init__(self):
        self.settings = Settings()
        self.engine = None
        self.main_win = None
        self.pill_win = None
        self.tray = None
        self.quitting = False
        # RLock: writers also mutate entries under it (retry un-fails a dict
        # while another thread may be serializing the same list)
        self._hist_lock = threading.RLock()
        self.history = self._load_history()
        self._notes_lock = threading.RLock()
        self.notes = self._load_notes()

    # ---------- js api ----------

    def get_init(self):
        load_dotenv(ENV_FILE)
        key = os.environ.get("COHERE_API_KEY")
        logo = ""
        try:
            img = Image.open(ICON_FILE)
            buf = io.BytesIO()
            img.save(buf, format="PNG")
            logo = base64.b64encode(buf.getvalue()).decode()
        except Exception:
            pass
        if key and self.engine is None:
            self._boot_engine(key)
        user = (os.environ.get("USERNAME") or "").split(" ")[0].split(".")[0]
        return {
            "key_set": bool(key),
            # masked so the Settings row can show WHICH key is loaded without
            # putting the secret on screen
            "key_hint": (key[:4] + "…" + key[-4:]) if key and len(key) > 12 else "",
            "logo": logo,
            "user": user.capitalize() if user else "",
            "version": APP_VERSION,
            "settings": dict(self.settings),
            "history": self.history[-500:],
            "devices": self._devices(),
        }

    def save_key(self, key):
        key = (key or "").strip()
        try:
            r = requests.get(MODELS_URL,
                             headers={"Authorization": f"Bearer {key}"}, timeout=10)
            ok = r.status_code == 200
        except requests.RequestException:
            ok = False
        if not ok:
            return {"ok": False}
        with open(ENV_FILE, "w", encoding="utf-8") as f:
            f.write(f"COHERE_API_KEY={key}\n")
        os.environ["COHERE_API_KEY"] = key
        if self.engine is None:
            logging.info("api key saved on first run")
            self._boot_engine(key)
        else:
            # REPLACING a key (quota ran out, rotation). Swap it on the live
            # engine — booting a second one would spawn another level pusher
            # and pill follower, and the two would fight over the pill.
            self.engine.api_key = key
            self.engine._clean_model_idx = 0   # re-probe the cleanup models
            self.engine._chat_dead = False     # a 401 latch is about the OLD key
            logging.info("api key replaced")
        return {"ok": True, "init": {
            "settings": dict(self.settings),
            "history": self.history[-500:],
            "devices": self._devices(),
        }}

    def set_setting(self, key, value):
        self.settings[key] = value
        self.settings.save()
        if key in ("rec_mode", "record_key", "lang_key", "command_key",
                   "refine_key", "note_key"):
            self._bind_hotkeys()
            if key == "record_key":
                self._js(self.pill_win, f"app.reckey({json.dumps(value)})")
        elif key == "chime_volume" and self.engine:
            self.engine.rebuild_chimes()
        elif key == "mic_device" and self.engine:
            self._js(self.pill_win,
                     f"app.mic({json.dumps(self.engine.mic_name())})")
        elif key == "theme":
            self._push_pill_theme()
        elif key == "autostart":
            _apply_autostart(bool(value))
        elif key == "theme":
            self._apply_titlebar()
        elif key == "idle_pill":
            if value:
                threading.Timer(0.1, self._show_pill_idle).start()
            elif self.engine is None or not self.engine.recording:
                self._pill_visible = False
                try:
                    self.pill_win.hide()
                except Exception:
                    pass
        return dict(self.settings)

    def set_language(self, lang):
        if self.engine:
            self.engine.language = lang
        self.settings["language"] = lang
        self.settings.save()

    def copy_text(self, text):
        pyperclip.copy(text)

    def export_history(self):
        if not self.history or self.main_win is None:
            return None
        path = self.main_win.create_file_dialog(
            webview.SAVE_DIALOG,
            save_filename=f"dictations_{datetime.now():%Y-%m-%d}.txt")
        if not path:
            return None
        if isinstance(path, (list, tuple)):
            path = path[0]
        try:
            with open(path, "w", encoding="utf-8") as f:
                for e in self.history:
                    when = datetime.fromtimestamp(e["ts"]).strftime("%Y-%m-%d %H:%M")
                    f.write(f"[{when}] ({e['lang']}) {e['text']}\n\n")
            return len(self.history)
        except OSError:
            logging.exception("export failed")
            return None

    def open_link(self, url):
        if url.startswith("https://"):
            webbrowser.open(url)

    # ---------- per-transcript actions ----------

    def _find_entry(self, ts):
        for e in self.history:
            if e.get("ts") == ts:
                return e
        return None

    def undo_ai(self, ts):
        e = self._find_entry(ts)
        if not e or not e.get("raw"):
            return None
        with self._hist_lock:
            e["text"] = e["raw"]
            e["words"] = len(e["text"].split())
            e["cleaned"] = False
            e["raw"] = ""
        self._save_history()
        return e

    def delete_entry(self, ts):
        e = self._find_entry(ts)
        if not e:
            return False
        with self._hist_lock:
            self.history.remove(e)
        if e.get("audio"):
            try:
                os.remove(os.path.join(AUDIO_DIR, e["audio"]))
            except OSError:
                pass
        self._save_history()
        return True

    def extract_audio(self, ts):
        e = self._find_entry(ts)
        if not e or not e.get("audio") or self.main_win is None:
            return None
        src = os.path.join(AUDIO_DIR, e["audio"])
        if not os.path.exists(src):
            return None
        stamp = datetime.fromtimestamp(e["ts"]).strftime("%Y-%m-%d_%H%M")
        path = self.main_win.create_file_dialog(
            webview.SAVE_DIALOG, save_filename=f"dictation_{stamp}.wav")
        if not path:
            return None
        if isinstance(path, (list, tuple)):
            path = path[0]
        try:
            shutil.copyfile(src, path)
            return True
        except OSError:
            logging.exception("extract audio failed")
            return None

    def retry_entry(self, ts):
        e = self._find_entry(ts)
        if (not e or not e.get("audio") or self.engine is None
                or self.engine.recording):
            return False
        threading.Thread(target=self._retry_worker, args=(e,), daemon=True).start()
        return True

    def _retry_worker(self, e):
        path = os.path.join(AUDIO_DIR, e["audio"])
        self.engine._worker_state("transcribing", "")
        text = self.engine.transcribe_file(
            path, e.get("lang", "ar"),
            lambda i, n: self.engine._worker_state("transcribing", f"{i}/{n}"))
        if not text:
            # re-push the entry so the feed row (and its Retry button)
            # renders back out of its 'Retryingâ€¦' state
            self._js(self.main_win,
                     f"app.updateEntry({json.dumps(e, ensure_ascii=False)})")
            self.engine._worker_state("error", "Retry failed â€” see app.log")
            return
        raw = text
        cleaned = False
        if self.settings.get("flow_mode", True):
            self.engine._worker_state("cleaning", "")
            out = self.engine._flow_clean(text)
            if out:
                text, cleaned = out, True
        text = _apply_dictionary(
            text, _parse_dictionary(self.settings.get("dictionary", "")))
        with self._hist_lock:
            e["text"] = text
            e["words"] = len(text.split())
            e["cleaned"] = cleaned
            e["raw"] = raw if cleaned else ""
            e.pop("failed", None)  # a successful retry un-fails the entry
        self._save_history()
        self._js(self.main_win,
                 f"app.updateEntry({json.dumps(e, ensure_ascii=False)})")
        self.engine._worker_state("idle", "Transcript updated")

    def quit(self):
        self._shutdown()

    # ---------- self-update ----------

    @staticmethod
    def _vtuple(s):
        nums = re.findall(r"\d+", s or "")
        return tuple(int(x) for x in nums[:3]) if nums else (0,)

    def _update_loop(self):
        """A launch check alone never reaches an app that stays open for days
        (or starts minimized to the tray and is never opened). Re-check on a
        schedule and announce through the tray, not just the in-app banner."""
        time.sleep(4)
        while not self.quitting:
            self._do_update_check()
            for _ in range(UPDATE_EVERY_H * 60):
                if self.quitting:
                    return
                time.sleep(60)

    def _do_update_check(self):
        """Returns a dict for the Settings 'Check now' button; also drives
        the banner + tray toast. Never raises."""
        try:
            r = requests.get(UPDATE_API, timeout=15,
                             headers={"User-Agent": "DialFlow"})
            if r.status_code != 200:
                logging.warning("update check http %s", r.status_code)
                return {"status": "error", "version": APP_VERSION}
            data = r.json()
            tag = data.get("tag_name", "")
            if self._vtuple(tag) <= self._vtuple(APP_VERSION):
                return {"status": "current", "version": APP_VERSION}
            asset = next((a for a in data.get("assets", [])
                          if a.get("name", "").lower().endswith(".exe")), None)
            if not asset:
                logging.warning("release %s has no .exe asset", tag)
                return {"status": "error", "version": APP_VERSION}
            self._update_url = asset["browser_download_url"]
            # integrity metadata: a truncated download used to be swapped in
            # anyway and bricked the install with "Failed to load Python DLL"
            self._update_size = asset.get("size") or 0
            self._update_sha = (asset.get("digest") or "").split("sha256:")[-1]
            logging.info("update available: %s", tag)
            self._js(self.main_win, f"app.updateAvailable({json.dumps(tag)})")
            # toast once per version â€” the banner is invisible when the app
            # sits in the tray, which is where it spends most of its life
            if getattr(self, "_notified_tag", None) != tag:
                self._notified_tag = tag
                self._notify(f"Dial Flow {tag} is ready",
                             "Open Dial Flow and hit Update now â€” it installs "
                             "itself and restarts.")
            return {"status": "available", "tag": tag, "version": APP_VERSION}
        except Exception:
            logging.exception("update check failed")
            return {"status": "error", "version": APP_VERSION}

    def _notify(self, title, message):
        if self.tray is None:
            return
        try:
            self.tray.notify(message, title)
        except Exception:
            logging.exception("tray notify failed")

    def check_update(self):
        """Manual check from Settings / the tray menu."""
        return self._do_update_check()

    def _tray_check_update(self):
        def run():
            res = self._do_update_check()
            if res.get("status") == "current":
                self._notify("Dial Flow is up to date",
                             f"You're on {APP_VERSION}, the latest version.")
            elif res.get("status") == "error":
                self._notify("Couldn't check for updates",
                             "No connection to GitHub â€” see app.log.")
        threading.Thread(target=run, daemon=True).start()

    def do_update(self):
        if not getattr(self, "_update_url", None):
            return {"ok": False, "reason": "no update"}
        if not getattr(sys, "frozen", False):
            # running from source â€” swapping sys.executable would clobber
            # the Python interpreter itself
            return {"ok": False, "reason": "dev"}
        threading.Thread(target=self._update_worker, daemon=True).start()
        return {"ok": True}

    def _download_update(self, path):
        """Fetch the new exe and PROVE it is intact before it is allowed to
        replace a working install. A flaky uplink truncates a 34MB download
        silently; the old 'bigger than 5MB' check passed such a file, the
        swap happened, and the app died on launch with 'Failed to load
        Python DLL' because the PyInstaller archive was cut short."""
        want_size = getattr(self, "_update_size", 0)
        want_sha = getattr(self, "_update_sha", "")
        last = "download failed"
        for attempt in range(3):
            try:
                r = requests.get(self._update_url, timeout=(15, 120),
                                 stream=True)
                r.raise_for_status()
                sha = hashlib.sha256()
                got = 0
                with open(path, "wb") as f:
                    for chunk in r.iter_content(1 << 16):
                        f.write(chunk)
                        sha.update(chunk)
                        got += len(chunk)
                if want_size and got != want_size:
                    last = f"truncated ({got} of {want_size} bytes)"
                elif want_sha and sha.hexdigest() != want_sha:
                    last = "checksum mismatch"
                elif got < 5_000_000:
                    last = "downloaded file suspiciously small"
                else:
                    logging.info("update verified: %s bytes, sha256 ok", got)
                    return True, ""
                logging.warning("update attempt %s rejected: %s",
                                attempt + 1, last)
            except requests.RequestException as e:
                last = f"network error ({type(e).__name__})"
                logging.warning("update attempt %s failed: %s", attempt + 1, last)
            time.sleep(2.0 * (attempt + 1))
        return False, last

    def _update_worker(self):
        """Download the new exe, verify it, then hand off to a script that
        swaps the file once this process exits and relaunches the app."""
        try:
            self._js(self.main_win, "app.updateState('downloading')")
            new_path = os.path.join(CONFIG_DIR, "DialFlow_update.exe")
            ok, why = self._download_update(new_path)
            if not ok:
                # leave the working install completely alone
                try:
                    os.remove(new_path)
                except OSError:
                    pass
                logging.error("update aborted: %s", why)
                self._js(self.main_win,
                         f"app.updateState('failed', {json.dumps(why)})")
                self._notify("Update failed â€” nothing was changed",
                             f"{why}. Dial Flow {APP_VERSION} is still "
                             "installed; try again later.")
                return
            cur = sys.executable
            bat = os.path.join(CONFIG_DIR, "update.bat")
            # The swap races this process's own exit â€” Windows keeps the exe
            # locked until every thread is gone, so retry for ~45s rather
            # than failing once and silently relaunching the OLD build.
            #
            # Then KEEP the old exe as .prev and pause before launching. A
            # freshly written unsigned exe is often still held by Defender's
            # scan; launching into that produced a one-shot "Failed to load
            # Python DLL ... _MEIxxxx\\python312.dll" because the onefile
            # archive could not finish unpacking. If the new build will not
            # start at all, .prev is a working build to fall back to.
            prev = os.path.join(os.path.dirname(cur), "DialFlow_prev.exe")
            # Paths go in through the ENVIRONMENT, never interpolated into
            # the script: a user profile like C:\Users\Ù…Ø­Ù…Ø¯ cannot be encoded
            # in the ASCII/OEM codepage cmd.exe reads .bat files in, and the
            # write raised UnicodeEncodeError AFTER the whole 34MB download.
            with open(bat, "w", encoding="ascii") as f:
                f.write('@echo off\n'
                        'ping -n 4 127.0.0.1 >nul\n'
                        'set RETRY=0\n'
                        ':retry\n'
                        'del /q "%DF_PREV%" >nul 2>&1\n'
                        'move /y "%DF_CUR%" "%DF_PREV%" >nul 2>&1\n'
                        'if not errorlevel 1 goto swap\n'
                        'set /a RETRY+=1\n'
                        'if %RETRY% GEQ 15 goto fail\n'
                        'ping -n 4 127.0.0.1 >nul\n'
                        'goto retry\n'
                        ':swap\n'
                        'move /y "%DF_NEW%" "%DF_CUR%" >nul 2>&1\n'
                        'if errorlevel 1 goto restore\n'
                        'ping -n 3 127.0.0.1 >nul\n'
                        'start "" "%DF_CUR%"\n'
                        'goto end\n'
                        ':restore\n'
                        'move /y "%DF_PREV%" "%DF_CUR%" >nul 2>&1\n'
                        ':fail\n'
                        'start "" "%DF_CUR%"\n'
                        ':end\n'
                        'del "%~f0"\n')
            import subprocess
            env = dict(os.environ, DF_CUR=cur, DF_NEW=new_path, DF_PREV=prev)
            subprocess.Popen(["cmd", "/c", bat], env=env,
                             creationflags=0x08000000)  # CREATE_NO_WINDOW
            logging.info("self-update handoff started")
            time.sleep(0.5)
            self._shutdown()
        except Exception:
            logging.exception("self-update failed")
            self._js(self.main_win, "app.updateState('failed')")
            self._notify("Update failed â€” nothing was changed",
                         f"Dial Flow {APP_VERSION} is still installed.")

    # ---------- engine wiring ----------

    def _last_text(self):
        """Most recent thing actually pasted â€” what refine acts on."""
        with self._hist_lock:
            for e in reversed(self.history):
                if e.get("text") and not e.get("failed"):
                    return e["text"]
        return ""

    def on_engine(self, status):
        """Speech-engine state for the bubble. Worth surfacing because the
        very first local run downloads ~1.5GB, and 'nothing happens when I
        press F9' during that is indistinguishable from a broken app."""
        info = {
            "mode": self.settings.get("asr_engine", "local"),
            "status": status,
            "device": LOCAL_ASR.device if status == "ready" else "",
        }
        self._engine_info = info
        self._js(self.pill_win, f"app.engine({json.dumps(info)})")
        self._js(self.main_win, f"app.engine({json.dumps(info)})")

    def _keep_cancelled_take(self, audio):
        """A cancelled recording is still saved and listed, so 'cancel' can
        never be the click that destroys minutes of speech."""
        try:
            t0 = time.time()
            buf = io.BytesIO()
            sf.write(buf, audio, SAMPLE_RATE, format="WAV", subtype="PCM_16")
            name = self.engine._keep_audio(buf.getvalue(), t0)
            self._cancelled_ts = t0          # the entry an Undo replaces
            self._on_transcript({
                "ts": t0, "lang": self.engine.language, "text": "",
                "secs": round(len(audio) / SAMPLE_RATE, 1), "words": 0,
                "latency": 0, "cleaned": False, "raw": "", "audio": name,
                "app": "general", "failed": "Cancelled â€” audio kept",
            })
        except Exception:
            logging.exception("keeping cancelled take failed")

    def _boot_engine(self, key):
        self.engine = Engine(key, self.settings, self._on_state,
                             self._on_transcript, self._on_language,
                             self._keep_cancelled_take, self._last_text,
                             self.on_engine, self.on_note)
        self._bind_hotkeys()
        threading.Thread(target=self._level_pusher, daemon=True).start()
        threading.Thread(target=self._pill_follower, daemon=True).start()
        threading.Timer(1.5, self._show_pill_idle).start()
        # tell the bubble which engine it is on as soon as it exists
        threading.Timer(2.0, lambda: self.on_engine(
            LOCAL_ASR.status if self.settings.get("asr_engine", "local")
            == "local" else "ready")).start()

    def _bind_hotkeys(self):
        if self.engine is None:
            return
        keyboard.unhook_all()
        rk = self.settings["record_key"]
        lk = self.settings["lang_key"]
        ck = self.settings.get("command_key", "f8")
        fk = self.settings.get("refine_key", "f4")
        nk = self.settings.get("note_key", "f7")
        if fk and fk not in (rk, ck, lk):
            keyboard.add_hotkey(fk, self._debounced(self.engine.toggle_refine),
                                suppress=False)
        if nk and nk not in (rk, ck, lk, fk):
            keyboard.add_hotkey(nk, self._debounced(self.engine.toggle_note),
                                suppress=False)
        elif nk:
            # f7 was removed from the language-key choices for exactly this
            # reason, but f11/f12 are still offered in both lists. Say so
            # rather than leaving the notebook key quietly dead.
            logging.warning("notebook key %s collides with another hotkey - "
                            "the notebook key is unavailable", nk)
        if self.settings["rec_mode"] == "hold":
            keyboard.on_press_key(rk, lambda e: self.engine.start_recording(),
                                  suppress=False)
            keyboard.on_release_key(rk, lambda e: self.engine.stop_recording(),
                                    suppress=False)
            if ck and ck != rk:
                keyboard.on_press_key(ck, lambda e: self.engine.start_command(),
                                      suppress=False)
                keyboard.on_release_key(ck, lambda e: self.engine.stop_command(),
                                        suppress=False)
        else:
            keyboard.add_hotkey(rk, self._debounced(self.engine.toggle_recording),
                                suppress=False)
            if ck and ck != rk:
                keyboard.add_hotkey(ck, self._debounced(self.engine.toggle_command),
                                    suppress=False)
        keyboard.add_hotkey(lk, self._debounced(self.engine.toggle_language),
                            suppress=False)
        # Esc kills whatever is in flight. This HAS to be a global hotkey: the
        # bubble is WS_EX_NOACTIVATE and never takes keyboard focus, so a
        # keydown handler inside pill.html can never fire. Not suppressed and
        # gated on _busy(), so when nothing is recording every other app sees
        # Esc exactly as it did before.
        keyboard.add_hotkey("esc", self._esc_cancel, suppress=False)
        if ck and ck == rk:
            logging.warning("command key %s collides with record key â€” "
                            "command mode is unavailable", ck)
            self._js(self.main_win, "app.keyClash(true)")
        else:
            self._js(self.main_win, "app.keyClash(false)")

    @staticmethod
    def _debounced(fn, gap=0.4):
        """Windows repeats KEY_DOWN while a key is held, and keyboard's
        hotkey handler fires on every repeat â€” so resting on F9 toggled
        recording on/off dozens of times. Ignore repeats inside `gap`."""
        state = {"t": 0.0}

        def wrapped(*_a):
            now = time.time()
            if now - state["t"] < gap:
                return
            state["t"] = now
            fn()
        return wrapped

    def _js(self, win, code):
        if win is None or self.quitting:
            return
        try:
            win.evaluate_js(code)
        except Exception:
            pass

    def _apply_pill_exstyle(self, hwnd):
        """Make the pill a HUD, not a second app.

        NOACTIVATE  - never steal focus from the field being dictated into.
        TOOLWINDOW  - keep it out of the taskbar and alt-tab.
        ~APPWINDOW  - MUST be cleared: pywebview's WinForms host sets
                      WS_EX_APPWINDOW, and APPWINDOW FORCES a taskbar button
                      even when TOOLWINDOW is set. Setting TOOLWINDOW alone
                      looked correct and changed nothing, which is why the
                      bubble still showed up as its own window.

        The shell only re-evaluates taskbar membership when a window is
        shown, so an already-visible pill is bounced once to apply it."""
        GWL_EXSTYLE = -20
        NOACTIVATE, TOOLWINDOW, APPWINDOW = 0x08000000, 0x00000080, 0x00040000
        u32 = ctypes.windll.user32
        ex = u32.GetWindowLongPtrW(hwnd, GWL_EXSTYLE)
        want = (ex | NOACTIVATE | TOOLWINDOW) & ~APPWINDOW
        if want == ex:
            return
        u32.SetWindowLongPtrW(hwnd, GWL_EXSTYLE, want)
        if u32.IsWindowVisible(hwnd):
            u32.ShowWindow(hwnd, 0)   # SW_HIDE
            u32.ShowWindow(hwnd, 8)   # SW_SHOWNA â€” visible, never activated
        logging.info("pill ex-style 0x%08X -> 0x%08X", ex, want)

    def _hide_pill_from_taskbar(self):
        """Best-effort pre-show stamp. pywebview does not create the native
        window until the first show(), so this usually no-ops on a hidden
        pill and _round_pill applies it right after the first show."""
        try:
            native = self.pill_win.native
            if native is None:
                return
            h = native.Handle
            hwnd = int(h.ToInt64()) if hasattr(h, "ToInt64") else int(h)
            self._apply_pill_exstyle(hwnd)
            self._pill_hwnd = hwnd
        except Exception:
            logging.debug("pre-show pill ex-style unavailable", exc_info=True)

    def _round_pill(self, attempt=0):
        """Round the pill via the DWM compositor â€” GDI window regions are
        ignored by WebView2's composited rendering, but DWM corner preference
        (the API behind every Win11 app's rounded corners) always applies.
        Must run after the first show(); hidden windows have no native form."""
        if getattr(self, "_pill_rounded", False):
            return
        try:
            h = self.pill_win.native.Handle
            phwnd = int(h.ToInt64()) if hasattr(h, "ToInt64") else int(h)
            # DWM must do the rounding: the window is OPAQUE (background_color
            # =PILL_BG, never transparent=True) and pill.html paints html with
            # the same colour, so a CSS border-radius only stops BODY painting
            # its gradient in the corner â€” the pixel underneath stays #171320.
            # On a light wallpaper that reads as a hard-cornered dark ear.
            # Only DWM actually clips the window so the desktop shows through.
            corner = ctypes.c_int(3)  # DWMWCP_ROUNDSMALL
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                phwnd, 33, ctypes.byref(corner), 4)
            # hide the OS border by painting it the pill's own background â€”
            # the DWMWA_COLOR_NONE sentinel renders as a LITERAL near-white
            # color on some builds (that was the ghost capsule around the
            # bubble). The design's hairline edge is drawn in CSS.
            border = ctypes.c_uint(0x00201317)  # COLORREF BGR of #171320
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                phwnd, 34, ctypes.byref(border), 4)
            # HUD behavior: WS_EX_NOACTIVATE so showing the pill can never
            # steal focus from the field the user is dictating into, and
            # WS_EX_TOOLWINDOW so it is NOT a taskbar/alt-tab entry â€” without
            # it the bubble reads as a second app window, which is exactly
            # the "it's a whole separate tab" complaint.
            self._apply_pill_exstyle(phwnd)
            self._pill_hwnd = phwnd  # cached for the native animator
            # re-assert every time: the WinForms host can restore
            # WS_EX_APPWINDOW when the window is re-shown
            self._apply_pill_exstyle(phwnd)
            try:
                # dark form backing â€” kills the white fringe that peeks out
                # around the web content at tiny sizes / during resizes.
                # NB: the assembly must be referenced before the namespace
                # import works under pythonnet â€” a bare import fails silently.
                import clr
                clr.AddReference("System.Drawing")
                import System.Drawing
                self.pill_win.native.BackColor = \
                    System.Drawing.ColorTranslator.FromHtml(PILL_BG)
            except Exception:
                logging.exception("pill backcolor failed")
            self._pill_rounded = True
        except Exception:
            if attempt < 4:
                threading.Timer(0.4, self._round_pill,
                                args=(attempt + 1,)).start()
            else:
                logging.exception("pill rounding failed")

    @staticmethod
    def _work_area():
        """Work rect (l, t, r, b) of the monitor under the cursor â€” excludes
        the taskbar, and follows the user across monitors."""
        class POINT(ctypes.Structure):
            _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]

        class MRECT(ctypes.Structure):
            _fields_ = [("l", ctypes.c_long), ("t", ctypes.c_long),
                        ("r", ctypes.c_long), ("b", ctypes.c_long)]

        class MONITORINFO(ctypes.Structure):
            _fields_ = [("cbSize", ctypes.c_ulong), ("rcMonitor", MRECT),
                        ("rcWork", MRECT), ("dwFlags", ctypes.c_ulong)]

        u32 = ctypes.windll.user32
        pt = POINT()
        u32.GetCursorPos(ctypes.byref(pt))
        u32.MonitorFromPoint.argtypes = [POINT, ctypes.c_ulong]
        u32.MonitorFromPoint.restype = ctypes.c_void_p
        hmon = u32.MonitorFromPoint(pt, 2)  # MONITOR_DEFAULTTONEAREST
        mi = MONITORINFO()
        mi.cbSize = ctypes.sizeof(MONITORINFO)
        u32.GetMonitorInfoW(ctypes.c_void_p(hmon), ctypes.byref(mi))
        return mi.rcWork.l, mi.rcWork.t, mi.rcWork.r, mi.rcWork.b

    def dock(self):
        pos = self.settings.get("pill_pos", "bottom")
        return pos if pos in DOCKS else "bottom"

    def _is_vert(self):
        """Side docks stand the bar up."""
        return self.dock() in ("left", "right")

    def _pill_anchor(self, size=None, dock=None):
        """TOP-LEFT position for the docked edge the user chose. Three docks
        only: bottom-middle, left-middle, right-middle.

        `size` MUST be the size the pill will BE, not the one it currently
        has â€” anchoring with the pre-resize size made a side-docked pill grow
        past its edge and then jump when the follower corrected it.

        PILL_PAD is 0: the tab is pinned FLUSH to the edge, so the docked
        side never moves when the box grows â€” every expansion happens away
        from the edge, which is what keeps the cursor inside the window."""
        try:
            l, t, r, b = self._work_area()
            w, h = size or getattr(self, "_pill_wh", (MINI_W, MINI_H))
            d = dock or self.dock()
            if d == "left":
                return l + PILL_PAD, t + (b - t - h) // 2
            if d == "right":
                return r - PILL_PAD - w, t + (b - t - h) // 2
            return l + (r - l - w) // 2, b - PILL_PAD - h
        except Exception:
            return None

    def _pill_size_for(self, target, dock=None):
        """The (w, h) a given visual state occupies at a given dock."""
        vert = (dock or self.dock()) in ("left", "right")
        if target == "panel":
            return (PANEL_W, PANEL_H)   # always horizontal â€” the picker needs width
        if target == "hover":
            return (VHOVER_W, VHOVER_H) if vert else (HOVER_W, HOVER_H)
        if target:
            return (VPILL_W, VPILL_H) if vert else (PILL_W, PILL_H)
        return (VMINI_W, VMINI_H) if vert else (MINI_W, MINI_H)

    @staticmethod
    def _grow_to_contain(end, start):
        """A hover box must never be smaller than the box it grew from on
        EITHER axis. If it is, the window edge sweeps past the cursor, the
        webview fires mouseleave, we shrink, the cursor is inside again and
        mouseenter fires â€” an infinite resize flicker with unclickable
        buttons. The sizes above already satisfy this; this is the guard
        that keeps a future size tweak from silently reintroducing it."""
        return (max(end[0], start[0]), max(end[1], start[1]))

    def _snap_pos(self, x, y, w, h):
        """Nearest of the three docks for a window the user just dropped â€”
        whichever edge its centre is closest to."""
        try:
            l, t, r, b = self._work_area()
        except Exception:
            return self.dock()
        cx, cy = x + w / 2, y + h / 2
        d = {"left": max(0, cx - l),
             "right": max(0, r - cx),
             "bottom": max(0, b - cy)}
        return min(d, key=d.get)

    def _move_pill(self):
        # never re-anchor mid-animation: the animator and the traveller own the
        # window while they run, and a move with the stale _pill_wh yanks it
        if getattr(self, "_pill_animating", False):
            return
        w, h = getattr(self, "_pill_wh", (MINI_W, MINI_H))
        anchor = self._pill_anchor((w, h))
        if anchor and self.pill_win is not None:
            try:
                self.pill_win.move(anchor[0], anchor[1])
            except Exception:
                pass

    # ---------- pill drag + controls (called from PILL_HTML) ----------

    class _RECT(ctypes.Structure):
        _fields_ = [("l", ctypes.c_long), ("t", ctypes.c_long),
                    ("r", ctypes.c_long), ("b", ctypes.c_long)]

    def _pill_rect(self):
        hwnd = getattr(self, "_pill_hwnd", None)
        if not hwnd:
            return None
        rc = DialFlow._RECT()
        ctypes.windll.user32.GetWindowRect(hwnd, ctypes.byref(rc))
        return rc

    def pill_drag_start(self):
        """Begin a drag. WM_NCLBUTTONDOWN was the obvious approach and it
        did NOT work here: ReleaseCapture only affects the calling thread,
        and the JS bridge runs on a worker, so the modal drag loop never
        took over from WebView2's own pointer capture. The window appeared
        to follow the cursor but its real position never changed, so the
        drop always snapped back to where it started. Driving SetWindowPos
        from JS pointer deltas is boring and actually works."""
        self._pill_dragging = True
        rc = self._pill_rect()
        self._drag_origin = (rc.l, rc.t) if rc else None
        return bool(self._drag_origin)

    def pill_drag_move(self, dx, dy):
        """Offset from where the drag began, in physical pixels."""
        hwnd = getattr(self, "_pill_hwnd", None)
        if not hwnd or not getattr(self, "_drag_origin", None):
            return
        x0, y0 = self._drag_origin
        try:
            ctypes.windll.user32.SetWindowPos(
                hwnd, 0, int(x0 + dx), int(y0 + dy), 0, 0,
                0x0001 | 0x0004 | 0x0010)  # NOSIZE | NOZORDER | NOACTIVATE
        except Exception:
            logging.exception("pill drag move failed")

    def pill_drag_end(self):
        """Dock to the nearest zone and remember it."""
        try:
            rc = self._pill_rect()
            if rc is not None:
                pos = self._snap_pos(rc.l, rc.t, rc.r - rc.l, rc.b - rc.t)
                changed = pos != self.dock()
                if pos != self.settings.get("pill_pos"):
                    self.settings["pill_pos"] = pos
                    self.settings.save()
                logging.info("pill docked %s", pos)
                self._js(self.pill_win, f"app.pos({json.dumps(pos)})")
                if changed:
                    # dropping on a different edge changes ORIENTATION, so the
                    # box has to be rebuilt at the new size â€” sliding the old
                    # shape over left a wide bar lying across a side edge.
                    # No early return: `finally` runs regardless, and for a
                    # left<->right drop the size is unchanged so _animate_pill
                    # early-outs and _move_pill is the only thing that actually
                    # repositions the window.
                    threading.Thread(target=self._relayout_pill,
                                     daemon=True).start()
        except Exception:
            logging.exception("pill drag end failed")
        finally:
            self._drag_origin = None
            self._pill_dragging = False
            self._move_pill()

    def pill_set_pos(self, pos):
        """Explicit dock choice from the pill's position picker."""
        if pos in DOCKS and pos != self.dock():
            threading.Thread(target=self._travel_pill, args=(pos,),
                             daemon=True).start()
            logging.info("pill travelling to %s (picker)", pos)

    def _travel_path(self, src, dst, size):
        """Top-left waypoints for a trip from one docked edge to another,
        hugging the work area the whole way. The pill never cuts across the
        screen â€” it retracts to a nub, runs ALONG the edges through the
        corner between them, and rises at the destination. Left<->right goes
        the long way round the bottom, which is the only route that stays on
        an edge."""
        l, t, r, b = self._work_area()
        w, h = size
        cx, cy = l + (r - l - w) // 2, t + (b - t - h) // 2
        edge = {"bottom": (cx, b - h), "left": (l, cy), "right": (r - w, cy)}
        bl, br = (l, b - h), (r - w, b - h)
        corners = {
            ("bottom", "left"): [bl], ("left", "bottom"): [bl],
            ("bottom", "right"): [br], ("right", "bottom"): [br],
            ("left", "right"): [bl, br], ("right", "left"): [br, bl],
        }
        return [edge[src]] + corners.get((src, dst), []) + [edge[dst]]

    def _travel_pill(self, pos):
        """Retract â†’ run along the edge â†’ rise at the new dock. The old
        behaviour swapped geometry in one frame, so a dock change from the
        picker just teleported."""
        src = self.dock()
        nub = (16, 16)
        # Commit the dock BEFORE the trip. The loops below use explicit path
        # coordinates and the captured `src`, so nothing here needs the old
        # value â€” but any _animate_pill that starts mid-trip (a recording, a
        # hover) then anchors at the DESTINATION edge instead of materialising
        # on the one we are leaving.
        self.settings["pill_pos"] = pos
        self.settings.save()
        self._js(self.pill_win, f"app.pos({json.dumps(pos)})")
        # take the animation token so a later _animate_pill cancels this trip
        # cleanly instead of the two fighting over SetWindowPos
        self._anim_token = getattr(self, "_anim_token", 0) + 1
        token = self._anim_token
        self._pill_animating = True
        try:
            self._js(self.pill_win, "app.moving(true)")
            hwnd = getattr(self, "_pill_hwnd", None)
            try:
                dpi = ctypes.windll.user32.GetDpiForWindow(hwnd) / 96.0 \
                    if hwnd else 1.0
            except Exception:
                dpi = 1.0

            def put(x, y, w, h):
                if hwnd:
                    ctypes.windll.user32.SetWindowPos(
                        hwnd, 0, int(x), int(y), int(w * dpi), int(h * dpi),
                        0x0004 | 0x0010)  # SWP_NOZORDER | SWP_NOACTIVATE
                else:
                    self.pill_win.resize(w, h)
                    self.pill_win.move(int(x), int(y))
                self._pill_wh = (w, h)

            # 1. retract to the nub, in place, against the current edge
            start = getattr(self, "_pill_wh", (MINI_W, MINI_H))
            a0 = self._pill_anchor(start, src) or (0, 0)
            for i in range(1, 7):
                if token != self._anim_token or self.quitting:
                    return
                k = i / 6.0
                w = round(start[0] + (nub[0] - start[0]) * k)
                h = round(start[1] + (nub[1] - start[1]) * k)
                a = self._pill_anchor((w, h), src) or a0
                put(a[0], a[1], w, h)
                time.sleep(0.016)

            # 2. run the polyline, constant speed, eased as a whole
            pts = self._travel_path(src, pos, nub)
            segs = [(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]
            lens = [max(1.0, abs(p2[0] - p1[0]) + abs(p2[1] - p1[1]))
                    for p1, p2 in segs]
            total = sum(lens)
            steps = 26
            for i in range(1, steps + 1):
                if token != self._anim_token or self.quitting:
                    return
                u = i / steps
                u = u * u * (3 - 2 * u)          # ease-in-out over the trip
                d = u * total
                for (p1, p2), ln in zip(segs, lens):
                    if d <= ln or (p1, p2) == segs[-1]:
                        f = min(1.0, d / ln)
                        put(p1[0] + (p2[0] - p1[0]) * f,
                            p1[1] + (p2[1] - p1[1]) * f, *nub)
                        break
                    d -= ln
                time.sleep(0.34 / steps)

        except Exception:
            logging.exception("pill travel failed")
        finally:
            # unconditional: a cancelled trip must never leave the contents
            # faded out, or the pill sits on screen as a blank slab
            self._js(self.pill_win, "app.moving(false)")
            if token == self._anim_token:
                self._pill_animating = False
                # 3. rise into whatever state the engine owns, at the new dock
                self._relayout_pill()

    def _relayout_pill(self):
        """Re-apply the current visual state at the orientation the new dock
        implies."""
        if getattr(self, "_panel_open", False):
            self._animate_pill("panel")
        elif getattr(self, "_hover_grown", False):
            self._animate_pill("hover")
        else:
            self._animate_pill(self._busy())

    def pill_cancel(self):
        """X on the pill: drop whatever is in flight."""
        if self.engine is not None:
            self.engine.cancel()

    def pill_open(self):
        self._show_main()

    def pill_ready(self):
        """The bar's page has loaded and is asking for its state.

        Everything Python pushes at startup â€” dock, hotkey, engine â€” used to
        be fired on timers 1.5s and 2.0s after boot and was silently dropped
        if the WebView2 had not finished loading yet. A cold start of the
        419MB onefile takes longer than that, so the bar could come up
        believing the engine was idle while it was still loading the model.
        The page asking is the only ordering that cannot race: it cannot ask
        before it exists."""
        try:
            self._js(self.pill_win, "app.reckey(%s)"
                     % json.dumps(self.settings["record_key"]))
            self._js(self.pill_win, "app.pos(%s)" % json.dumps(self.dock()))
            info = getattr(self, "_engine_info", None)
            if info:
                self._js(self.pill_win, f"app.engine({json.dumps(info)})")
            if self.engine is not None:
                self._js(self.pill_win,
                         f"app.mic({json.dumps(self.engine.mic_name())})")
            self._push_pill_theme()
        except Exception:
            logging.exception("pill_ready failed")

    def _push_pill_theme(self):
        """The bar itself stays a dark ink slab in both themes (a parchment
        bar all but vanished on a light desktop); only the roomy panel follows
        the theme. So the page needs to know which one is active."""
        try:
            dark = "true" if self._theme_is_dark() else "false"
            self._js(self.pill_win, f"app.theme({dark})")
        except Exception:
            logging.exception("pill theme push failed")

    # A take longer than this is not thrown away on one stray Esc. Esc is the
    # most-pressed key on the keyboard - it closes dialogs, menus, autocomplete
    # - and a global hook sees every press. On a short take one press is fine;
    # on four minutes of talking it is a disaster.
    ESC_CONFIRM_AFTER_S = 30
    ESC_CONFIRM_WINDOW_S = 2.0

    def _esc_cancel(self):
        """Global Esc, gated: only a take that is actually in flight is
        touched, so this is invisible the other 99% of the time."""
        if self.engine is None or not self._busy():
            return
        eng = self.engine
        long_take = (eng.recording and
                     time.time() - eng.started_at > self.ESC_CONFIRM_AFTER_S)
        if long_take:
            armed = getattr(self, "_esc_armed_at", 0)
            if time.time() - armed > self.ESC_CONFIRM_WINDOW_S:
                self._esc_armed_at = time.time()
                self._js(self.pill_win, "app.escArmed(%d)"
                         % int(self.ESC_CONFIRM_WINDOW_S * 1000))
                return
        self._esc_armed_at = 0
        eng.cancel()

    def pill_undo(self):
        """The Undo on a just-cancelled take: finish it instead."""
        if self.engine is None or not self.engine.undo():
            return False
        self._pill_undo_open = False
        ts = getattr(self, "_cancelled_ts", None)
        if ts is not None:
            # the take is being finished now - its "Cancelled - audio kept"
            # entry would otherwise sit next to the real one forever
            self.delete_entry(ts)
            self._js(self.main_win, "app.removeEntry(%s)" % json.dumps(ts))
            self._cancelled_ts = None
        return True

    def pill_copy_last(self):
        """Put the last take back on the clipboard - for when the paste went
        into the wrong window, or nowhere."""
        text = self._last_text()
        if not text:
            return False
        try:
            pyperclip.copy(text)
            return True
        except Exception:
            logging.exception("copy last failed")
            return False

    SNOOZE_S = 3600

    def pill_snooze(self):
        """'Hide for 1 hour' - for a screen share or a presentation. Only the
        idle tab hides; a recording always shows, since recording without a
        visible indicator is the one state that must never be silent."""
        self._snooze_until = time.time() + self.SNOOZE_S
        self._panel_open = False
        logging.info("floating bar hidden for %d min", self.SNOOZE_S // 60)
        if not self._busy():
            try:
                self._pill_visible = False
                self.pill_win.hide()
            except Exception:
                pass
        return True

    def _unsnooze(self):
        self._snooze_until = 0
        if not self._busy():
            self._show_pill_idle()

    def _pill_hidden_by_policy(self):
        """Idle tab should be off screen: snoozed, or a full-screen app /
        presentation owns the display."""
        if time.time() < getattr(self, "_snooze_until", 0):
            return True
        return bool(getattr(self, "_fullscreen_busy", False))

    def _busy(self):
        """Any state that owns the expanded pill â€” including the failure
        hold, which a hover-out used to shrink out from under."""
        return (getattr(self, "_pill_failing", False)
                or getattr(self, "_pill_processing", False)
                or (self.engine is not None and self.engine.recording))

    def pill_panel(self, open_):
        """Open/close the bigger popup that houses the dock picker."""
        self._panel_open = bool(open_)
        if open_:
            # The panel takes the cursor from hover â€” mirror the JS, which
            # already does `if(on)hovering=false`. Without this Python still
            # believed it was hovered on close and settled at the hover size
            # while the DOM was painting the plain tab.
            self._hover_grown = False
        target = "panel" if open_ else self._busy()
        threading.Thread(target=self._animate_pill, args=(target,),
                         daemon=True).start()

    def pill_hover_in(self):
        """Grow so the label and controls have room. This has to work DURING
        a recording too â€” cancelling mid-take is the whole point of the
        button."""
        if getattr(self, "_pill_dragging", False) or \
                getattr(self, "_panel_open", False):
            return
        self._hover_grown = True
        threading.Thread(target=self._animate_pill, args=("hover",),
                         daemon=True).start()

    def pill_hover_out(self):
        if not getattr(self, "_hover_grown", False):
            return
        # clear the flag even mid-drag, otherwise the pill stays stuck at
        # hover size forever while the JS believes it is no longer hovered
        self._hover_grown = False
        if getattr(self, "_pill_dragging", False) or \
                getattr(self, "_panel_open", False):
            return
        # back to whichever size the engine state owns
        threading.Thread(target=self._animate_pill, args=(self._busy(),),
                         daemon=True).start()

    def _pill_follower(self):
        """Keeps the pill on the monitor the cursor is on. It must NOT run
        while the user is dragging â€” it was re-anchoring every 0.35s, which
        teleported the pill back mid-drag and meant the drop position read
        as unchanged, so it never docked anywhere new."""
        tick = 0
        was_hidden = False
        while not self.quitting:
            if (getattr(self, "_pill_visible", False)
                    and not getattr(self, "_pill_animating", False)
                    and not getattr(self, "_pill_dragging", False)):
                self._move_pill()
            tick += 1
            if tick % 3 == 0:                        # ~1s is plenty for this
                self._fullscreen_busy = _fullscreen_app_active()
                hidden = self._pill_hidden_by_policy()
                if hidden != was_hidden:
                    was_hidden = hidden
                    self._apply_hide_policy(hidden)
            time.sleep(0.35)

    def _apply_hide_policy(self, hidden):
        """Step the idle tab aside for a full-screen app / presentation or a
        snooze, and bring it back after. Never touches a live take - a
        recording must always be visible."""
        if self.engine is None or self._busy():
            return
        try:
            if hidden:
                self._pill_visible = False
                self.pill_win.hide()
                logging.info("floating bar stepped aside (%s)",
                             "full-screen app" if getattr(
                                 self, "_fullscreen_busy", False) else "snoozed")
            else:
                if time.time() >= getattr(self, "_snooze_until", 0):
                    self._snooze_until = 0
                self._show_pill_idle()
        except Exception:
            logging.exception("hide policy failed")

    def _set_pill_corners(self, small):
        """DWM corner preference per state: ROUNDSMALL (~4px) for the resting
        tab, ROUND (~8px) for the expanded states. DWM is what genuinely clips
        the window â€” the CSS radius alone cannot, because the window is opaque
        (see _round_pill). The CSS radii are matched to these so the painted
        arc sits ON the clipped arc instead of inside it.

        The cost is that DWM rounds all four corners, including the two that
        meet the screen edge. At PILL_PAD 0 that notch lands against the work
        area boundary and is far less visible than a square dark ear over a
        white document, which is what the asymmetric-CSS-only approach gave."""
        hwnd = getattr(self, "_pill_hwnd", None)
        if not hwnd:
            return
        try:
            corner = ctypes.c_int(3 if small else 2)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                hwnd, 33, ctypes.byref(corner), 4)
        except Exception:
            pass

    def _animate_pill(self, expand):
        """Eased window-size animation between the idle bubble and the full
        pill, anchored to its docked corner so it grows in place. Drives raw
        SetWindowPos on the cached hwnd â€” pywebview's resize/move marshal
        through the UI thread and stutter, especially right after show().

        expand: True -> recording pill, False -> idle bubble, "hover" ->
        the slightly wider size that fits the label and controls."""
        vert = self._is_vert()
        end = self._pill_size_for(expand)
        # the panel is the only state that goes horizontal on a side dock;
        # hover now stands up with the bar, so no orientation ever flips
        # under the cursor
        # Clamp hover against the state it grows FROM (the tab or the recording
        # bar), NOT against whatever the window happens to be right now. Using
        # the live size fed the 232x150 PANEL in on a panel->hover transition:
        # on a bottom dock end became == start so the box never shrank back,
        # and on a side dock it produced a 232x178 slab that is neither size.
        if expand == "hover":
            end = self._grow_to_contain(end, self._pill_size_for(self._busy()))
        # bump the token only once we know we will actually animate: bumping
        # before the early-outs below cancelled a running animation and left
        # _pill_animating stuck True, which froze the follower and every
        # later resize
        expand = bool(expand)
        start = getattr(self, "_pill_wh", (MINI_W, MINI_H))
        if start == end:
            return
        # anchor for the DESTINATION size, so a side-docked pill grows
        # against its screen edge instead of drifting off it
        anchor = self._pill_anchor(end)
        hwnd = getattr(self, "_pill_hwnd", None)
        if anchor is None or self.pill_win is None:
            self._pill_wh = end
            return
        # An orientation flip (upright bar -> wide hover bar) has no sensible
        # in-between shape: tweening 38x150 to 190x44 sweeps through squares
        # and the content reflows every frame. That is the "glitching out"
        # when moving to a side-docked bubble. Cross-orientation changes snap.
        flip = (start[1] > start[0]) != (end[1] > end[0])
        self._anim_token = getattr(self, "_anim_token", 0) + 1
        token = self._anim_token
        self._pill_animating = True
        try:
            if expand:
                self._set_pill_corners(small=False)
                time.sleep(0.03)  # let the just-shown window settle first
            try:
                dpi = ctypes.windll.user32.GetDpiForWindow(hwnd) / 96.0 \
                    if hwnd else 1.0
            except Exception:
                dpi = 1.0

            def place(w, h):
                """Re-anchor for the size being shown, so the pill keeps
                hugging its docked edge for the whole animation."""
                a = self._pill_anchor((w, h)) or anchor
                if hwnd:
                    ctypes.windll.user32.SetWindowPos(
                        hwnd, 0, a[0], a[1], int(w * dpi), int(h * dpi),
                        0x0004 | 0x0010)  # SWP_NOZORDER | SWP_NOACTIVATE
                else:
                    self.pill_win.resize(w, h)
                    self.pill_win.move(a[0], a[1])
                self._pill_wh = (w, h)

            if flip:
                # swap layout and geometry in the same beat
                self._js(self.pill_win,
                         "app.vert(%s)" % ("true" if vert else "false"))
                place(*end)
                time.sleep(0.02)
            else:
                self._js(self.pill_win,
                         "app.vert(%s)" % ("true" if vert else "false"))
                # design spec: grow 180ms strong ease-out, shrink 200ms in-out
                steps = 16
                dt = (0.180 if expand else 0.200) / steps
                for i in range(1, steps + 1):
                    if token != self._anim_token or self.quitting:
                        return
                    t = i / steps
                    t = 1 - (1 - t) ** 3 if expand else t * t * (3 - 2 * t)
                    place(round(start[0] + (end[0] - start[0]) * t),
                          round(start[1] + (end[1] - start[1]) * t))
                    time.sleep(dt)
            self._pill_wh = end
            # reconcile: the native SetWindowPos path resizes the form behind
            # WinForms' back, and a same-size framework resize is skipped as a
            # no-op â€” so jiggle by 1px first to force a real layout pass that
            # snaps the WebView2 content to the final bounds
            try:
                a = self._pill_anchor(end) or anchor
                self.pill_win.resize(end[0] + 1, end[1] + 1)
                time.sleep(0.02)
                self.pill_win.resize(end[0], end[1])
                self.pill_win.move(a[0], a[1])
            except Exception:
                pass
            if not expand:
                self._set_pill_corners(small=True)
        except Exception:
            self._pill_wh = end
        finally:
            if token == self._anim_token:
                self._pill_animating = False

    def _pill_to_idle(self):
        """Direct settle (no success flash â€” error, toggle, etc.): empty the
        frame, shrink, then breathe the idle core back in."""
        if self.pill_win is None:
            return
        threading.Thread(target=self._pill_settle, args=(False,),
                         daemon=True).start()

    def _pill_settle(self, flash):
        """Design T3 timeline: flash 0-300ms â†’ contents empty while the
        window shrinks 300-500ms â†’ idle core fades in and breathes."""
        try:
            # a full-screen app or presentation owns the screen: skip the
            # receipt entirely rather than flash it over someone's slides
            if flash and not getattr(self, "_fullscreen_busy", False):
                # hand the bubble what the take actually produced, so the
                # success beat can say "42 words" instead of just blinking
                summ = dict(getattr(self, "_last_summary", None) or {})
                # the paste went nowhere (desktop / taskbar had focus): say
                # the text is on the clipboard instead of a word count
                if self.engine is not None and getattr(
                        self.engine, "last_paste_blind", False):
                    summ["blind"] = True
                self._js(self.pill_win, "app.done(%s)"
                         % json.dumps(summ or None))
                # a blind paste stays up longer - it is an instruction to act
                # on, not a receipt to glance at
                time.sleep(1.6 if summ.get("blind") else 0.30)
            if self.engine is not None and self.engine.recording:
                return  # a new recording started mid-flash â€” leave the pill
            if self._pill_hidden_by_policy():
                self._pill_visible = False
                self._js(self.pill_win, "app.mode('mini')")
                self.pill_win.hide()
                return
            if self.settings.get("idle_pill", True):
                self._js(self.pill_win, "app.mode('')")  # empty while moving
                self._pill_visible = True
                self._animate_pill(False)
                self._js(self.pill_win, "app.mode('mini')")  # coreIn 400ms
            else:
                self._pill_visible = False
                self.pill_win.hide()
        except Exception:
            pass

    def _show_pill_idle(self):
        """Startup: put the tiny idle bubble on screen (never activates)."""
        if self.pill_win is None or self.engine is None:
            return
        if not self.settings.get("idle_pill", True):
            return
        if self._pill_hidden_by_policy():
            return  # snoozed, or a full-screen app owns the screen
        if self._busy():
            return  # a take is live â€” do not shrink its HUD to a bubble
        try:
            prev_fg = ctypes.windll.user32.GetForegroundWindow()
            self.pill_win.show()
            # size for the dock we are ACTUALLY on â€” hard-coding the horizontal
            # MINI started a side-docked tab as a 76x16 bar lying across the
            # edge, with the upright 34px core clipped inside 16px of height
            mw, mh = self._pill_size_for(False)
            self.pill_win.resize(mw, mh)
            self._pill_wh = (mw, mh)
            self._js(self.pill_win, "app.mode('mini')")
            self._js(self.pill_win,
                     f"app.reckey({json.dumps(self.settings['record_key'])})")
            # self.dock() â€” NOT the raw setting. The stored default was the
            # stale "bottom-center", which is not one of DOCKS, so the JS
            # stamped an unstyled dock-bottom-center class and the tab lost
            # its edge radius entirely.
            self._js(self.pill_win, "app.pos(%s)" % json.dumps(self.dock()))
            self._move_pill()
            self._pill_visible = True
            threading.Timer(0.05, self._restore_focus, args=(prev_fg,)).start()
            threading.Timer(0.25, self._round_pill).start()
        except Exception:
            logging.exception("idle pill show failed")

    def _on_state(self, state, detail):
        started = self.engine.started_at if state == "recording" else 0
        self._js(self.main_win,
                 f"app.setState({json.dumps(state)}, {json.dumps(detail)}, "
                 f"{started or 0})")
        if self.pill_win is not None:
            try:
                if state == "recording":
                    # remember the user's focused window: showing the pill may
                    # activate it (first show, before NOACTIVATE applies) and
                    # would un-focus the field they want to dictate into
                    prev_fg = ctypes.windll.user32.GetForegroundWindow()
                    self._move_pill()
                    self.pill_win.show()
                    self._pill_visible = True
                    self._pill_processing = False
                    threading.Timer(0.05, self._restore_focus,
                                    args=(prev_fg,)).start()
                    threading.Timer(0.25, self._round_pill).start()
                    self._esc_armed_at = 0
                    self._pill_undo_open = False
                    # where the take goes, how long it may run, and which mic
                    # is listening - the bar shows the mic name only when it
                    # differs from the last take's
                    take = {"mode": detail or "dictate", "cap": MAX_SECONDS,
                            "mic": self.engine.mic_name()}
                    self._js(self.pill_win,
                             f"app.start({started}, {json.dumps(take)})")
                    threading.Thread(target=self._animate_pill, args=(True,),
                                     daemon=True).start()
                elif state in ("transcribing", "cleaning"):
                    # keep the pill expanded with a spinner until the text lands
                    self._pill_processing = True
                    self._js(self.pill_win, "app.mode('processing')")
                elif state == "error":
                    # a failed take must be visible without opening the app â€”
                    # the pill holds the failure until it is acknowledged or
                    # the next recording starts
                    self._pill_processing = False
                    self._show_pill_now()
                    threading.Thread(target=self._pill_fail, args=(detail,),
                                     daemon=True).start()
                elif (state == "idle" and detail == "Cancelled"
                      and self.engine is not None
                      and self.engine.undo_available()):
                    # hold a "Cancelled - Undo" beat instead of vanishing: a
                    # stray Esc or a misclick on the X should be one click to
                    # reverse, not minutes of speech to repeat
                    self._pill_processing = False
                    threading.Thread(target=self._pill_cancelled,
                                     daemon=True).start()
                elif getattr(self, "_pill_processing", False) and state == "idle":
                    # designed T3 exit: success flash â†’ empty shrink â†’ breathe.
                    # A cancel arrives as ("idle", "Cancelled") too â€” it must
                    # NOT play the success flash.
                    self._pill_processing = False
                    threading.Thread(
                        target=self._pill_settle,
                        args=(detail != "Cancelled",), daemon=True).start()
                else:
                    self._pill_processing = False
                    self._pill_to_idle()
            except Exception:
                pass

    def _show_pill_now(self):
        """Bring the pill up without stealing focus from the user's field."""
        try:
            prev_fg = ctypes.windll.user32.GetForegroundWindow()
            self.pill_win.show()
            self._pill_visible = True
            threading.Timer(0.05, self._restore_focus, args=(prev_fg,)).start()
            threading.Timer(0.25, self._round_pill).start()
        except Exception:
            logging.exception("pill show failed")

    def _pill_fail(self, detail):
        """Hold a readable failure on the pill, then settle back to idle."""
        self._pill_failing = True
        try:
            msg = (detail or "Transcription failed").split(" â€” ")[0]
            self._animate_pill(True)
            self._js(self.pill_win, f"app.failed({json.dumps(msg)})")
            for _ in range(60):          # ~6s, but yield to a new recording
                if self.quitting or (self.engine is not None
                                     and self.engine.recording):
                    return
                time.sleep(0.1)
            self._pill_failing = False
            self._pill_settle(False)
        except Exception:
            logging.exception("pill fail state failed")
        finally:
            self._pill_failing = False

    def _pill_cancelled(self):
        """Hold 'Cancelled - Undo' for the undo window, then settle. Yields
        at once to a new recording, and ends early if Undo is clicked (the
        engine then drives the pill through processing as normal)."""
        self._pill_failing = True          # keeps hover-out from shrinking it
        self._pill_undo_open = True
        try:
            self._animate_pill(True)
            self._js(self.pill_win, "app.cancelled(%d)"
                     % int(Engine.UNDO_WINDOW_S * 1000))
            end = time.time() + Engine.UNDO_WINDOW_S
            while time.time() < end:
                if (self.quitting or not self._pill_undo_open
                        or (self.engine is not None and self.engine.recording)):
                    return
                time.sleep(0.1)
            self._pill_failing = False
            self._pill_settle(False)
        except Exception:
            logging.exception("pill cancelled state failed")
        finally:
            self._pill_failing = False
            self._pill_undo_open = False

    @staticmethod
    def _restore_focus(prev_hwnd):
        try:
            if prev_hwnd and ctypes.windll.user32.GetForegroundWindow() != prev_hwnd:
                ctypes.windll.user32.SetForegroundWindow(prev_hwnd)
        except Exception:
            pass

    def _on_transcript(self, entry):
        if entry.get("text") and not entry.get("failed"):
            secs = entry.get("secs") or 0
            self._last_summary = {
                "words": entry.get("words", 0),
                "secs": round(secs),
                "wpm": round(entry["words"] / (secs / 60)) if secs > 2 else 0,
                "cleaned": bool(entry.get("cleaned")),
            }
        with self._hist_lock:
            self.history.append(entry)
        self._save_history()
        self._js(self.main_win, f"app.addEntry({json.dumps(entry, ensure_ascii=False)})")

    def _on_language(self, lang):
        self._js(self.main_win, f"app.setLanguage({json.dumps(lang)})")

    def _level_pusher(self):
        while not self.quitting:
            if self.engine is not None and self.engine.recording:
                lv = round(self.engine.level, 4)
                clip = "true" if self.engine.clipping else "false"
                self._js(self.main_win, f"app.setLevel({lv})")
                self._js(self.pill_win, f"app.level({lv}, {clip})")
                time.sleep(0.04)
            else:
                time.sleep(0.15)

    # ---------- windows / tray ----------

    def _devices(self):
        try:
            return ["System default"] + sorted({
                d["name"] for d in sd.query_devices()
                if d["max_input_channels"] > 0})
        except Exception:
            return ["System default"]

    def _load_history(self):
        try:
            with open(HISTORY_FILE, encoding="utf-8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return []

    def _save_history(self):
        """Serialized + atomic: concurrent workers (transcribe, retry, JS
        bridge) must never interleave writes, and a crash mid-write must
        never leave truncated JSON (which _load_history reads as 'no
        history' and silently starts over)."""
        with self._hist_lock:
            try:
                tmp = HISTORY_FILE + ".tmp"
                with open(tmp, "w", encoding="utf-8") as f:
                    json.dump(self.history[-500:], f, ensure_ascii=False,
                              indent=1)
                os.replace(tmp, HISTORY_FILE)
            except OSError:
                logging.exception("history save failed")

    def _load_notes(self):
        try:
            with open(NOTES_FILE, encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, list) else []
        except (OSError, ValueError):
            return []

    def _save_notes(self):
        """Same discipline as history: serialized and atomic. These are the
        user's own words with nowhere else to live, so a torn write is not
        recoverable from anywhere. Unlike history there is no cap - a
        notebook you silently truncate is not a notebook."""
        with self._notes_lock:
            try:
                tmp = NOTES_FILE + ".tmp"
                with open(tmp, "w", encoding="utf-8") as f:
                    json.dump(self.notes, f, ensure_ascii=False, indent=1)
                os.replace(tmp, NOTES_FILE)
            except OSError:
                logging.exception("notes save failed")

    def on_note(self, entry):
        """File a finished notebook take and show it immediately."""
        try:
            self.notes.append(entry)
            self._save_notes()
            self._js(self.main_win, "app.note(%s)" % json.dumps(entry))
            logging.info("noted: %d task(s), %d note(s)%s",
                         len(entry.get("tasks", [])),
                         len(entry.get("notes", [])),
                         "" if entry.get("organized") else " (filed raw)")
        except Exception:
            logging.exception("on_note failed")

    def _find_note(self, ts):
        for e in self.notes:
            if e.get("ts") == ts:
                return e
        return None

    def notes_all(self):
        return self.notes

    def note_toggle(self, ts, task_id, done):
        """Tick or untick one task. Stores WHEN it was done, so a day can
        later show what actually got finished on it."""
        e = self._find_note(ts)
        if not e:
            return False
        for t in e.get("tasks", []):
            if t.get("id") == task_id:
                t["done"] = bool(done)
                t["done_ts"] = time.time() if done else None
                self._save_notes()
                return True
        return False

    def note_add_task(self, ts, text):
        """Add a task by hand to an existing entry - the one thing dictation
        cannot do is amend a dump you already filed."""
        e, text = self._find_note(ts), (text or "").strip()
        if not e or not text:
            return False
        e.setdefault("tasks", []).append({
            "id": f"{int(time.time()*1000)}-m", "text": text[:500],
            "done": False, "done_ts": None})
        self._save_notes()
        return True

    def note_delete_task(self, ts, task_id):
        e = self._find_note(ts)
        if not e:
            return False
        before = len(e.get("tasks", []))
        e["tasks"] = [t for t in e.get("tasks", []) if t.get("id") != task_id]
        if len(e["tasks"]) != before:
            self._save_notes()
            return True
        return False

    def note_delete(self, ts):
        before = len(self.notes)
        self.notes = [e for e in self.notes if e.get("ts") != ts]
        if len(self.notes) != before:
            self._save_notes()
            return True
        return False

    def note_add_text(self, text):
        """Typed entry. Goes through the same organizer as a spoken one, so a
        typed dump and a spoken dump land in the notebook identically."""
        text = (text or "").strip()
        if not text:
            return False
        threading.Thread(target=self._note_text_worker, args=(text,),
                         daemon=True).start()
        return True

    def _note_text_worker(self, text):
        org = None
        try:
            if self.engine is not None:
                org = self.engine._organize_note(text)
        except Exception:
            logging.exception("organize failed for typed note")
        self.on_note({
            "ts": time.time(), "day": time.strftime("%Y-%m-%d"),
            "raw": text, "title": (org or {}).get("title") or "",
            "tasks": [{"id": f"{int(time.time()*1000)}-{i}", "text": t,
                       "done": False, "done_ts": None}
                      for i, t in enumerate((org or {}).get("tasks", []))],
            "notes": (org or {}).get("notes") or ([text] if not org else []),
            "organized": bool(org), "by": (org or {}).get("by", "local"),
            "secs": 0,
            "words": len(text.split()), "audio": "", "typed": True,
        })

    def _setup_tray(self):
        try:
            img = Image.open(ICON_FILE)
            menu = pystray.Menu(
                pystray.MenuItem("Open Dial Flow",
                                 lambda: self._show_main(), default=True),
                pystray.MenuItem("Check for updates",
                                 lambda: self._tray_check_update()),
                # the way back from "Hide for 1 hour" before the hour is up
                pystray.MenuItem("Show floating bar",
                                 lambda: self._unsnooze()),
                pystray.MenuItem("Quit", lambda: self._shutdown()),
            )
            self.tray = pystray.Icon("DialFlow", img,
                                     "Dial Flow â€” F9 to record", menu)
            threading.Thread(target=self.tray.run, daemon=True).start()
        except Exception:
            logging.exception("tray setup failed")
            self.tray = None

    def _show_main(self):
        try:
            self.main_win.show()
            self.main_win.restore()
        except Exception:
            pass

    def _on_closing(self):
        """Window X pressed: hide to tray instead of quitting."""
        if self.quitting or self.tray is None:
            return True
        try:
            self.main_win.hide()
            if not self.settings.get("_tray_tip_shown"):
                self.settings["_tray_tip_shown"] = True
                self.settings.save()
                try:
                    self.tray.notify("Still running â€” hotkeys stay active. "
                                     "Right-click the tray icon to quit.",
                                     "Dial Flow")
                except Exception:
                    pass
        except Exception:
            pass
        return False

    def _shutdown(self):
        if self.quitting:
            return
        self.quitting = True
        if self.engine is not None:
            self.engine.quitting = True
        try:
            keyboard.unhook_all()
        except Exception:
            pass
        if self.tray is not None:
            try:
                self.tray.stop()
            except Exception:
                pass
        for w in list(webview.windows):
            try:
                w.destroy()
            except Exception:
                pass

    def _theme_is_dark(self):
        pref = self.settings.get("theme", "system")
        if pref in ("dark", "light"):
            return pref == "dark"
        try:  # system: mirror Windows' app theme
            key = winreg.OpenKey(
                winreg.HKEY_CURRENT_USER,
                r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
            light, _ = winreg.QueryValueEx(key, "AppsUseLightTheme")
            winreg.CloseKey(key)
            return not light
        except OSError:
            return False

    def _apply_titlebar(self):
        """DWMWA_USE_IMMERSIVE_DARK_MODE on the main window, matched to the
        UI theme so the titlebar doesn't clash with the page."""
        if self.main_win is None:
            return
        try:
            h = self.main_win.native.Handle
            hwnd = int(h.ToInt64()) if hasattr(h, "ToInt64") else int(h)
            val = ctypes.c_int(1 if self._theme_is_dark() else 0)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 20,
                                                       ctypes.byref(val), 4)
        except Exception:
            logging.exception("titlebar theme failed")

    def _post_start(self):
        self._hide_pill_from_taskbar()
        self._setup_tray()
        threading.Thread(target=self._update_loop, daemon=True).start()
        # keep the Run-key path fresh in case the exe was moved
        if self.settings.get("autostart") and getattr(sys, "frozen", False):
            _apply_autostart(True)
        # launched at login: start quietly in the tray
        if "--minimized" in sys.argv:
            try:
                self.main_win.hide()
            except Exception:
                pass
        # theme-matched titlebar + rounded pill region (best effort)
        self._apply_titlebar()
        # pill region is applied on first show â€” hidden pywebview windows
        # have no native form yet, so it can't be rounded here

    def run(self):
        sw = ctypes.windll.user32.GetSystemMetrics(0)
        sh = ctypes.windll.user32.GetSystemMetrics(1)
        self.main_win = webview.create_window(
            "Dial Flow", UI_FILE, js_api=Api(self),
            width=1160, height=780, min_size=(960, 640),
            background_color="#131316" if self._theme_is_dark() else "#FAFAF8")
        self.main_win.events.closing += self._on_closing
        self.pill_win = webview.create_window(
            "Dial Flow â€” recording", html=PILL_HTML, js_api=PillApi(self),
            width=PILL_W, height=PILL_H, x=sw // 2 - PILL_W // 2, y=sh - 118,
            # override pywebview's silent 200x100 default min â€” it must be
            # allowed to shrink all the way down to the idle tab. Use the
            # SMALLEST dimension across both orientations: the horizontal tab
            # is 76x16 but the upright one is 16x76, and a min width of 76
            # would clamp a side-docked tab to a square.
            min_size=(min(MINI_W, VMINI_W), min(MINI_H, VMINI_H)),
            frameless=True, on_top=True, hidden=True, resizable=False,
            focus=False, background_color=PILL_BG)
        logging.info("app started")
        webview.start(func=self._post_start, debug=False)
        # Hard exit. concurrent.futures registers an atexit hook that JOINS
        # every pool worker, so quitting mid-upload hung the tray for seconds
        # waiting on a 300s-timeout socket. Every worker here is already a
        # daemon and nothing is deferred to exit â€” Settings.save() and
        # _save_history() both write at each mutation â€” so there is no state
        # to lose by skipping the interpreter's shutdown dance.
        os._exit(0)


def main():
    ctypes.windll.kernel32.CreateMutexW(None, False, "DialFlow.Singleton")
    if ctypes.windll.kernel32.GetLastError() == 183:  # ERROR_ALREADY_EXISTS
        ctypes.windll.user32.MessageBoxW(
            None, "Dial Flow is already running â€” check your taskbar or "
                  "system tray.", "Dial Flow", 0x40)
        return
    ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
        "Dialverse.DialFlow")
    DialFlow().run()


if __name__ == "__main__":
    main()
