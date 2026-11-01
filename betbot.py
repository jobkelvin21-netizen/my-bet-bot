#!/usr/bin/env python3
"""
betbot.py — everything in ONE file.

    python3 betbot.py          start (asks SportyBet phone / password / balance, then
                               detaches to the background — you can close the terminal)
    python3 betbot.py stop     stop the background bot
    python3 betbot.py status   is it running?
    python3 betbot.py fg       run in the foreground (debugging)

Telegram commands: /startbot /stopbot /slow /clear /switch /login /balance
                   /matches /status /pitch /raw /shutdown

Lock a game:   /slow
               SportyBet- <SportyBet match url>
               Bet365URL- <bet365 match link>   (the GOAL SIGNAL - opened directly)
               Home- <home team>                (bet365 spelling; optional but recommended)
               Away- <away team>
               Bet365- <FI>                     (ONLY if the match is not found by team names)

GOAL SIGNAL : the bet365 match page - the pitch marker OR the ticker line, whichever lands first, ONE per goal.
              Goals that were already played when the page opened are history and never fire.
SCORE FEED  : the bet365 live list (SS). It only CASHES OUT when a score goes down (and keeps the goal count right).
HOW A BET IS SENT: every order opens its OWN brand-new HTTPS connection and encryption channel and is sent
straight away. The rebet is the SAME request, sent only after the first bet was ANSWERED plus REBET_GAP.
"""
from __future__ import annotations

import asyncio
import base64
import difflib
import getpass
import hashlib
import html
import http.client
import json
import math
import multiprocessing
import os
import re
import secrets
import shutil
import signal
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.parse
import urllib.request
import uuid
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

import aiohttp
from loguru import logger
from cryptography.hazmat.primitives import padding as spad
from cryptography.hazmat.primitives.asymmetric import padding as apad
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPublicNumbers
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes


# =====================================================================
# CONFIG
# =====================================================================
CONFIG_FILE = Path.home() / ".betbot_config.json"
PID_FILE = Path.home() / ".betbot.pid"
LOG_FILE = Path.home() / "betbot.log"

PASTE_TG_TOKEN = ""
PASTE_TG_CHAT = "7377233973"

HARD_CAP = 9000.0          # absolute ceiling for the profit of ONE bet (env can only go lower)


def _saved_cfg() -> dict:
    try:
        return json.loads(CONFIG_FILE.read_text())
    except Exception:
        return {}


_CFG = _saved_cfg()


class Config:
    TELEGRAM_BOT_TOKEN = os.getenv("TG_TOKEN") or _CFG.get("token") or PASTE_TG_TOKEN
    TELEGRAM_CHAT_ID = os.getenv("TG_CHAT") or _CFG.get("chat_id") or PASTE_TG_CHAT
    MAX_PROFIT_PER_BET = min(float(os.getenv("MAX_PROFIT", str(HARD_CAP))), HARD_CAP)
    MAX_REBET = int(os.getenv("MAX_REBET", "1"))           # 1 bet + 1 rebet = 2 requests
    REBET_GAP = float(os.getenv("REBET_GAP", "0.3"))       # pause AFTER bet 1 was answered, before the rebet
    BET_WAIT = float(os.getenv("BET_WAIT", "4"))           # max wait for bet 1's answer before the rebet is dropped
    ACCEPT_ODDS_CHANGE = os.getenv("ACCEPT_ODDS_CHANGE", "0") in ("1", "true", "yes")
    SPORTYBET_BASE_URL = os.getenv("SPORTYBET_URL", "https://www.sportybet.com")
    BET365_LIVE_URL = os.getenv("BET365_LIVE_URL", "https://www.bet365.nl/#/IP/B1")
    STATUS_POLL = float(os.getenv("STATUS_POLL", "5"))     # page watchdog interval
    HALF_POLL = float(os.getenv("HALF_POLL", "2"))         # API poll for 1st half / HT / 2nd half
    PRICE_POLL = float(os.getenv("PRICE_POLL", "0.1"))     # safety-net read of the page odds
    PRICE_MAX_AGE = float(os.getenv("PRICE_MAX_AGE", "2.0"))   # a cached page price older than this is not used
    PAGE_TIMEOUT = float(os.getenv("PAGE_TIMEOUT", "0.25"))    # max wait for ONE page read when the cache is empty
    FEED_WAIT = float(os.getenv("FEED_WAIT", "20"))        # wait for FI in feed
    API_TIMEOUT = float(os.getenv("API_TIMEOUT", "30"))    # SportyBet arm timeout
    PITCH_QUIET_SECS = float(os.getenv("PITCH_QUIET_SECS", "1.5"))       # the first seconds of the match records = history
    PITCH_DEBOUNCE = float(os.getenv("PITCH_DEBOUNCE", "12"))            # the other source's signal for the SAME goal is ignored this long
    PITCH_FRESH_MINUTES = float(os.getenv("PITCH_FRESH_MINUTES", "5"))   # a goal older than this many match minutes is history

    REBET_GAP = float(os.getenv("REBET_GAP", "0.25"))          # pause after bet 1 was ANSWERED, before the rebet (0.25 s at most)
    HISTORY_SECS = float(os.getenv("HISTORY_SECS", "6"))       # after every (re)connect of the match page the feed only LEARNS
    SS_AHEAD_SECS = float(os.getenv("SS_AHEAD_SECS", "15"))    # SS counted a goal this recently and the pitch record comes now = still live
    BALANCE_POLL = float(os.getenv("BALANCE_POLL", "5"))       # real SportyBet balance, read in the background
    CASHOUT_POLL = float(os.getenv("CASHOUT_POLL", "1.0"))     # while waiting for the market to open again
    CASHOUT_MAX_SECS = float(os.getenv("CASHOUT_MAX_SECS", "900"))
    MISSED_GOAL_SECS = float(os.getenv("MISSED_GOAL_SECS", "20"))
    CONFIRM_SECS = float(os.getenv("CONFIRM_SECS", "40"))

    FT_SILENCE_SECS = float(os.getenv("FT_SILENCE_SECS", "120"))     # API silent this long after minute 85 = full time
    FT_NOMARKET_SECS = float(os.getenv("FT_NOMARKET_SECS", "180"))   # no open next-goal market this long after minute 85 = full time


logger.remove()
logger.add(sys.stderr, level="INFO",
           format="<green>{time:HH:mm:ss}</green> | <level>{level: <7}</level> | {message}")


def _ord(n: int) -> str:
    if 10 <= n % 100 <= 20:
        return f"{n}th"
    return f"{n}{ {1:'st',2:'nd',3:'rd'}.get(n % 10,'th') }"


def _wat(ts: Optional[float]) -> str:
    """Nigeria time (WAT = UTC+1, no daylight saving) with milliseconds."""
    from datetime import datetime, timedelta, timezone
    t = datetime.fromtimestamp(float(ts or time.time()), timezone(timedelta(hours=1)))
    return t.strftime("%H:%M:%S.") + f"{t.microsecond // 1000:03d} WAT"


# =====================================================================
# SPORTYBET  (API)
# =====================================================================
BASE = Config.SPORTYBET_BASE_URL
_SB_HOST = urllib.parse.urlparse(BASE).netloc
CASH_REF = BASE + "/ng/m/my_accounts/open_bets?from=nav_bar"     # the page the real cash-out calls come from
UA = ("Mozilla/5.0 (Linux; Android 13) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/122.0.0.0 Mobile Safari/537.36")
N_HEX = ("c207d6f2db3fa03c7545b7e73d97550f30ef5c3019c4ba5f303fe7b1d2059c22"
         "eebde8a8cbd87310e91f84f7ecf697d365dfdb7ad5522b6fb185ea33281cf456"
         "ed845320a2e59cbaf507b1741554a478f7c21e06996018a20f00b0baffc65aeeb"
         "3b36193f6992b0f240ce84bce3bc07a4187d5ba5c5543884a6b624aab0507cf")

NEXTGOAL_RE = re.compile(r"(next\s*goal|\b\d{1,2}(?:st|nd|rd|th)\s*goals?\b)", re.I)
GOAL_NUM_RE = re.compile(r"(\d{1,2})(?:st|nd|rd|th)\s*goals?\b", re.I)
HALF1_RE = re.compile(r"1st\s*half|first\s*half", re.I)
HALF2_RE = re.compile(r"2nd\s*half|second\s*half", re.I)


def _b64e(b: bytes) -> str:
    return base64.b64encode(b).decode()


def _md5h(s: str) -> str:
    return hashlib.md5(str(s).encode()).hexdigest()


def _aes_encrypt(plain: str, key: bytes) -> str:
    iv = secrets.token_bytes(16)
    p = spad.PKCS7(128).padder()
    data = p.update(plain.encode()) + p.finalize()
    c = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
    return _b64e(iv + c.update(data) + c.finalize())


def _aes_decrypt(payload: str, key: bytes) -> str:
    raw = base64.b64decode(payload.strip())
    d = Cipher(algorithms.AES(key), modes.CBC(raw[:16])).decryptor()
    data = d.update(raw[16:]) + d.finalize()
    try:
        u = spad.PKCS7(128).unpadder()
        return (u.update(data) + u.finalize()).decode()
    except Exception:
        return data.decode("utf-8", "ignore")


_RSA_KEY = None


def _rsa_pub():
    global _RSA_KEY
    if _RSA_KEY is None:
        _RSA_KEY = RSAPublicNumbers(65537, int(N_HEX, 16)).public_key()
    return _RSA_KEY


def _period_rank(name: str) -> int:
    """1st-half market first, then full-time, then 2nd-half."""
    if HALF1_RE.search(name or ""):
        return 0
    if HALF2_RE.search(name or ""):
        return 2
    return 1


def _goal_num_in_name(name: str) -> Optional[int]:
    m = GOAL_NUM_RE.search(name or "")
    return int(m.group(1)) if m else None


def _to_int(x: Any, default: int = 0) -> int:
    try:
        return int(float(str(x)))
    except Exception:
        return default


def _floor2(x: float) -> float:
    return math.floor(float(x) * 100.0 + 1e-9) / 100.0


def _brief(r: dict) -> str:
    """One short line for a failed order: the server's code and its own words."""
    bits = [f"bizCode {r.get('bizCode', r.get('http', '?'))}"]
    msg = r.get("innerMsg") or r.get("message") or r.get("msg") or ""
    if msg:
        bits.append(str(msg)[:160])
    return " | ".join(bits)


def _server_view(r: dict) -> Optional[dict]:
    """What a 4510 reply says about the market we bet on."""
    try:
        sent = (r.get("_sent") or {}).get("selection") or {}
        parts = str(sent.get("id", "")).split("/")          # uof:1/sr:sport:1/8/6?goalnr=2
        mid, oid = parts[-2], parts[-1].split("?")[0]
        spec = str(sent.get("specifier") or "")
        for ev in ((r.get("data") or {}).get("fcOutcomes") or []):
            for m in ev.get("markets") or []:
                if str(m.get("id")) != mid:
                    continue
                if spec and str(m.get("specifier") or "") != spec:
                    continue
                for o in m.get("outcomes") or []:
                    if str(o.get("id")) == oid:
                        return {"status": _to_int(m.get("status"), -1),
                                "odds": float(o.get("odds") or 0),
                                "prob": str(o.get("probability") or ""),
                                "active": o.get("isActive"),
                                "sent_odds": float(sent.get("odds") or 0),
                                "sent_prob": str(sent.get("probability") or "")}
    except Exception:
        pass
    return None


def _prob_same(a: str, b: str) -> bool:
    try:
        return abs(float(a) - float(b)) < 0.0005
    except Exception:
        return a == b


def _diag_4510(r: dict) -> str:
    """One line that says exactly what differed between the order and the server's market."""
    if r.get("bizCode") != 4510:
        return ""
    v = _server_view(r)
    if not v:
        return "🔎 DIAG: the reply did not contain our market - cannot compare"
    open_ = v["status"] == 0
    same_odds = abs(v["odds"] - v["sent_odds"]) < 0.005
    same_prob = _prob_same(v["prob"], v["sent_prob"])
    why = []
    if not open_:
        why.append("market was already SUSPENDED/CLOSED on the server when the order arrived")
    if not same_odds:
        why.append("odds had moved")
    if not same_prob:
        why.append("probability sent was not the current one")
    return (f"🔎 DIAG: market status {v['status']} ({'open' if open_ else 'NOT open'}) · "
            f"odds sent {v['sent_odds']:.2f} / server {v['odds']:.2f} ({'same' if same_odds else 'DIFFERENT'}) · "
            f"probability sent {v['sent_prob']} / server {v['prob']} ({'same' if same_prob else 'DIFFERENT'})"
            f"\n➡️ " + ("; ".join(why) if why else "nothing differs"))


def _fix_from_4510(r: dict) -> str:
    """The server's probability to retry with - ONLY when the market is open and active, the odds are exactly
    what we sent and only the probability differs. Anything else: no retry."""
    v = _server_view(r)
    if not v or v["status"] != 0 or v["active"] in (0, "0", False) or not v["prob"]:
        return ""
    if abs(v["odds"] - v["sent_odds"]) >= 0.005 or _prob_same(v["prob"], v["sent_prob"]):
        return ""
    return v["prob"]


def _label_key(s: str) -> str:
    """Same normalisation the page reader uses, so a label can be mapped back to its market."""
    return re.sub(r"[^a-z0-9]", "", (s or "").lower())


# ---------------------------------------------------------------------
# match phase from the SportyBet event API (1st half / HT / 2nd half / FT)
# ---------------------------------------------------------------------
_PHASE_KEYS = {"matchstatus", "periodname", "currentperiod", "period", "periodtext", "perioddesc",
               "statusdesc", "statusname", "statustext", "eventstatus", "phase", "matchperiod",
               "playstatus", "livestatus"}
_SR_STATUS = {"6": "1", "7": "2", "31": "HT", "100": "FT"}      # Sportradar numeric match status codes


def _phase_from_text(t: Any, numeric_ok: bool = False) -> str:
    """'1st half' -> '1'   '2nd half' -> '2'   'Halftime' -> 'HT'   'Ended' -> 'FT'   unknown -> ''"""
    s = re.sub(r"\s+", " ", re.sub(r"[^a-z0-9 ]+", " ", str(t or "").lower())).strip()
    if not s:
        return ""
    if re.search(r"extra|overtime|penalt|\bpen\b", s):
        return ""
    if re.search(r"\bhalf ?time\b|\bht\b|\bbreak\b|\bpaused\b", s):
        return "HT"
    if re.search(r"\bfull ?time\b|\bft\b|\bended\b|\bfinished\b|\bclosed\b", s):
        return "FT"
    if re.search(r"\b(2nd|second|h2|2h)\b", s):
        return "2"
    if re.search(r"\b(1st|first|h1|1h)\b", s):
        return "1"
    if numeric_ok and s in ("1", "2"):
        return s
    return ""


def _api_phase(data: Any) -> str:
    """Reads the match phase from the SportyBet event API reply. Searches the reply (up to 3
    levels deep, top level first) for a period / status field. Never looks inside 'markets' or
    'outcomes' (market names like '1st Half - Next Goal' would give false answers)."""
    if not isinstance(data, dict):
        return ""
    queue: List[Tuple[dict, int]] = [(data, 0)]
    while queue:
        sc, depth = queue.pop(0)
        for k, v in sc.items():
            kl = str(k).lower()
            if kl in ("markets", "outcomes"):
                continue
            if isinstance(v, dict):
                if depth < 3:
                    queue.append((v, depth + 1))
                continue
            if (kl in _PHASE_KEYS or "period" in kl) and isinstance(v, (str, int)) \
                    and not isinstance(v, bool):
                if kl == "matchstatus" and str(v).strip() in _SR_STATUS:
                    return _SR_STATUS[str(v).strip()]
                ph = _phase_from_text(v, numeric_ok=kl in ("period", "currentperiod"))
                if ph:
                    return ph
    return ""


def _api_clock(data: Any) -> Optional[float]:
    """Minutes played, from the event reply's 'playedSeconds' ('88:18' = 88 min 18 s). None if not there."""
    if not isinstance(data, dict):
        return None
    queue: List[Tuple[dict, int]] = [(data, 0)]
    while queue:
        sc, depth = queue.pop(0)
        for k, v in sc.items():
            kl = str(k).lower()
            if kl in ("markets", "outcomes"):
                continue
            if isinstance(v, dict):
                if depth < 3:
                    queue.append((v, depth + 1))
            elif kl == "playedseconds":
                m = re.match(r"\s*(\d+)(?::(\d+))?", str(v))
                if m:
                    return int(m.group(1)) + (int(m.group(2)) / 60.0 if m.group(2) else 0.0)
    return None


def _api_fields(data: Any) -> str:
    """Short list of the plain fields of the event reply, nested ones too (diagnostics only)."""
    if not isinstance(data, dict):
        return "no data"
    bits: List[str] = []
    queue: List[Tuple[str, dict, int]] = [("", data, 0)]
    while queue:
        pre, sc, depth = queue.pop(0)
        for k, v in sc.items():
            if str(k).lower() in ("markets", "outcomes"):
                continue
            if isinstance(v, dict):
                if depth < 2:
                    queue.append((f"{pre}{k}.", v, depth + 1))
            elif isinstance(v, (str, int, float)) and not isinstance(v, bool) and len(str(v)) <= 40:
                bits.append(f"{pre}{k}={v}")
    return ", ".join(bits)[:1200]


# =====================================================================
# HOME / AWAY SAFETY  (which bet365 team is which SportyBet outcome)
# =====================================================================
_TEAM_STOP = {"fc", "cf", "sc", "afc", "fk", "cd", "ud", "sd", "ac", "as", "club", "the", "de"}


def _norm_team(s: str) -> str:
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = re.sub(r"\([^)]*\)", " ", s)                      # esports tags:  Tottenham (THREAT)
    s = re.sub(r"[^a-z0-9 ]+", " ", s.lower())
    return " ".join(t for t in s.split() if t not in _TEAM_STOP)


def _sim(a: str, b: str) -> float:
    na, nb = _norm_team(a), _norm_team(b)
    if not na or not nb:
        return 0.0
    if na == nb:
        return 1.0
    if na in nb or nb in na:
        return 0.9
    ta, tb = set(na.split()), set(nb.split())
    return max(len(ta & tb) / max(1, len(ta | tb)),
               difflib.SequenceMatcher(None, na, nb).ratio())


def _split_teams(name: str) -> Tuple[str, str, bool]:
    """'A v B' -> (A, B, False);  'A @ B' -> (A, B, True)  (the first team is the AWAY side)."""
    m = re.search(r"\s+(vs|v|@)\s+", name or "", re.I)
    if not m:
        return (name or "").strip(), "", False
    return name[:m.start()].strip(), name[m.end():].strip(), m.group(1) == "@"


def _pair_match(p: Tuple[str, str], q: Tuple[str, str]) -> Optional[int]:
    """0 = p[0]~q[0] and p[1]~q[1];  1 = swapped;  None = cannot tell."""
    straight = _sim(p[0], q[0]) + _sim(p[1], q[1])
    swapped = _sim(p[0], q[1]) + _sim(p[1], q[0])
    if max(straight, swapped) < 0.9 or abs(straight - swapped) < 0.35:
        return None
    return 0 if straight > swapped else 1


def _sb_pair_from_url(url: str) -> Tuple[str, str]:
    """.../Red_Star_FC_vs_Saint-Etienne/sr:match:72037392 -> ('Red Star FC', 'Saint-Etienne')"""
    m = re.search(r"/([^/]+?)_vs_([^/]+?)/sr:match", url or "")
    if not m:
        return "", ""
    return m.group(1).replace("_", " ").strip(), m.group(2).replace("_", " ").strip()


def _resolve_sides(n365: str, sb_pair: Tuple[str, str],
                   user: Optional[Tuple[str, str]]) -> Dict[str, Any]:
    """Decides which SportyBet outcome (Home / Away) each bet365 score slot belongs to.

    bet365 'A v B' : A is HOME, B is AWAY, and SS 'x-y' is A's score first.
    bet365 'A @ B' : A is AWAY, B is HOME.
    SportyBet      : the FIRST team in '<A>_vs_<B>' is the Home outcome.
    Teams are matched by NAME, so a different order on the two sites is detected and
    handled. If you also give Home-/Away-, they must agree with bet365's order, or
    betting for that game is BLOCKED (alerts still go out)."""
    first, second, first_is_away = _split_teams(n365)
    have_sb = bool(sb_pair and sb_pair[0] and sb_pair[1])
    notes: List[str] = []
    blocked = ""
    by_order = not first_is_away                       # bet365 rule: first team = home side
    m = _pair_match((first, second), sb_pair) if (second and have_sb) else None
    first_is_sb_home = by_order if m is None else (m == 0)
    verified = m is not None
    if m is not None and first_is_sb_home != by_order:
        notes.append("ℹ️ SportyBet lists the teams in the opposite order to bet365 — mapped by team names")
    if user and user[0] and user[1]:
        u365 = _pair_match((first, second), user) if second else None   # 0: bet365's first team is your Home
        usb = _pair_match(sb_pair, user) if have_sb else None           # 0: SportyBet's first team is your Home
        want365 = 1 if first_is_away else 0
        if u365 is not None and u365 != want365:
            blocked = f"your Home-/Away- disagree with bet365's order ({n365})"
        elif usb is not None and usb != 0:
            if m is None:
                blocked = (f"your Home- ({user[0]}) is listed second on SportyBet "
                           f"({sb_pair[0]} vs {sb_pair[1]}) and the two sites' teams could not be matched")
            else:
                notes.append("ℹ️ SportyBet lists your Home- team second — mapped by team names")
        elif u365 is not None and usb is not None and m is not None and first_is_sb_home != by_order:
            blocked = "team names on bet365 and SportyBet contradict your Home-/Away-"
        if not blocked:
            if u365 is None and usb is None:
                notes.append("⚠️ could not match your Home-/Away- names to either site — check the spelling")
            else:
                verified = True
                notes.append("✅ Home-/Away- confirmed against "
                             + ("both sites" if (u365 is not None and usb is not None) else "one site"))
    if not verified:
        notes.append("⚠️ home/away not verified by names — using bet365 order (Home v Away)")
    side_map = {"home": "home" if first_is_sb_home else "away",
                "away": "away" if first_is_sb_home else "home"}
    return {"map": side_map, "blocked": blocked, "notes": notes, "verified": verified,
            "t365": (first, second)}


@dataclass
class ArmedSelection:
    event_id: str
    sport_id: str
    market_id: str
    outcome_id: str
    specifier: str
    odds: float
    probability: str          # sent exactly as the API gave it (a STRING, like the standalone bet.py)
    product: str
    side: str
    market_name: str = ""
    outcome_name: str = ""
    goal_no: Optional[int] = None
    period_rank: int = 1
    market_desc: str = ""

    @property
    def dom_labels(self) -> List[str]:
        """The header(s) this market has ON THE SPORTYBET PAGE, e.g. '1st Half - 2nd Goal'.
        (The event API calls the same market '1st Half - Next Goal', which is not on the page.)"""
        out: List[str] = []
        if self.goal_no:
            pre = "1st Half - " if self.period_rank == 0 else ("2nd Half - " if self.period_rank == 2 else "")
            out.append(f"{pre}{_ord(self.goal_no)} Goal")
        for nm in (self.market_desc, self.market_name):
            if nm and GOAL_NUM_RE.search(nm) and nm not in out:
                out.append(nm)
        return out


class SportyBetClient:
    def __init__(self):
        self.cookie = ""
        self.user_id = ""
        self.logged_in = False
        self._conns: List[http.client.HTTPSConnection] = []     # kept-alive connections (GET / login only — NEVER orders)
        self._conn_lock = threading.Lock()

    def _headers(self, extra: Optional[dict] = None) -> dict:
        h = {"User-Agent": UA, "Accept": "application/json, text/plain, */*",
             "Origin": BASE, "Referer": BASE + "/ng/m/",
             "Platform": "wap", "ClientId": "wap", "OperId": "2"}
        if self.cookie:
            h["Cookie"] = self.cookie
        if extra:
            h.update(extra)
        return h

    def _new_conn(self) -> http.client.HTTPSConnection:
        return http.client.HTTPSConnection(_SB_HOST, timeout=20)

    def _take_conn(self) -> Tuple[http.client.HTTPSConnection, bool]:
        with self._conn_lock:
            if self._conns:
                return self._conns.pop(), True
        return self._new_conn(), False

    def _give_conn(self, c) -> None:
        with self._conn_lock:
            if len(self._conns) < 8:
                self._conns.append(c)
                return
        try:
            c.close()
        except Exception:
            pass

    def _request(self, method: str, path: str, body: Optional[bytes], headers: dict,
                 idempotent: bool) -> Tuple[int, bytes]:
        """One HTTPS request over a kept-alive connection. Used for login and GET reads only.
        A connection the server closed while idle is replaced and the request re-sent — for a
        POST only when the server dropped us before answering. ORDERS DO NOT USE THIS."""
        stale = (http.client.RemoteDisconnected, ConnectionResetError, BrokenPipeError,
                 http.client.CannotSendRequest, http.client.ResponseNotReady)
        for attempt in range(2):
            c, reused = self._take_conn() if attempt == 0 else (self._new_conn(), False)
            try:
                c.request(method, path, body=body, headers=headers)
                r = c.getresponse()
                data = r.read()
                if r.will_close:
                    c.close()
                else:
                    self._give_conn(c)
                return r.status, data
            except Exception as e:
                try:
                    c.close()
                except Exception:
                    pass
                if attempt == 0 and reused and (idempotent or isinstance(e, stale)):
                    continue
                raise
        raise RuntimeError("unreachable")

    def _post(self, path: str, data: bytes, headers: dict) -> Tuple[int, bytes]:
        return self._request("POST", path, data, headers, False)

    def _getjson(self, path: str, params: Optional[dict] = None, referer: Optional[str] = None) -> dict:
        full = path + (("?" + urllib.parse.urlencode(params)) if params else "")
        st, body = self._request("GET", full, None,
                                 self._headers({"Referer": referer} if referer else None), True)
        return json.loads(body)

    def _phone_variants(self, p: str) -> List[str]:
        d = "".join(c for c in str(p) if c.isdigit())
        bare = d.lstrip("0")
        if bare.startswith("234"):
            bare = bare[3:]
        out = []
        for v in (d, bare, "234" + bare, "0" + bare):
            if v and v not in out:
                out.append(v)
        return out

    # ---------- encrypted calls on ONE connection that the caller owns (fresh per order) ----------
    @staticmethod
    def _post_on(c: http.client.HTTPSConnection, path: str, data: bytes,
                 headers: dict) -> Tuple[int, bytes]:
        c.request("POST", path, body=data, headers=headers)
        r = c.getresponse()
        return r.status, r.read()

    def _open_channel_on(self, c: http.client.HTTPSConnection,
                         referer: Optional[str] = None) -> Tuple[Optional[bytes], Optional[str]]:
        aes = secrets.token_bytes(16)
        plain = "password=" + urllib.parse.quote(_b64e(aes), safe="")
        wrapped = _b64e(_rsa_pub().encrypt(plain.encode(), apad.PKCS1v15()))
        extra = {"Content-Type": "text/plain"}
        if referer:
            extra["Referer"] = referer
        st, body = self._post_on(c, "/api/ng/base/cipher", wrapped.encode(), self._headers(extra))
        cj = json.loads(body)
        if cj.get("bizCode") != 10000:
            return None, None
        return aes, cj["data"]["transId"]

    def _send_on(self, c: http.client.HTTPSConnection, aes: bytes, tid: str, path: str,
                 payload: dict, referer: Optional[str] = None) -> dict:
        js = json.dumps(payload, separators=(",", ":"))
        extra = {"Content-Type": "application/json;charset=UTF-8",
                 "encryption-type": "2", "transId": tid}
        if referer:
            extra["Referer"] = referer
        st, body = self._post_on(c, path, _aes_encrypt(js, aes).encode(), self._headers(extra))
        try:
            return json.loads(_aes_decrypt(body.decode(), aes))
        except Exception:
            try:
                return json.loads(body.decode())
            except Exception:
                return {"http": st, "raw": body.decode("utf-8", "ignore")[:400]}

    def login(self, phone: str, password: str) -> bool:
        st, body = self._post("/api/ng/patron/cipher", b"",
                              self._headers({"Content-Type": "text/plain"}))
        cj = json.loads(body)
        urs = cj["data"]["ursId"]
        key = base64.b64decode(cj["data"]["password"])

        def try_login(u: str):
            device = str(uuid.uuid4())
            form = (f"username={urllib.parse.quote(u)}"
                    f"&password={urllib.parse.quote(_md5h(password))}"
                    f"&keepSignedIn=false")
            st, body = self._post("/api/ng/patron/accessToken",
                                  _aes_encrypt(form, key).encode(),
                                  self._headers({"Content-Type": "text/plain",
                                                 "encryption-type": "1", "ursId": urs,
                                                 "Fingerprint": secrets.token_hex(16),
                                                 "Cookie": f"deviceId={device}"}))
            try:
                resp = json.loads(_aes_decrypt(body.decode(), key))
            except Exception:
                resp = json.loads(body)
            return resp, device

        for v in self._phone_variants(phone):
            resp, device = try_login(v)
            if resp.get("bizCode") == 10000:
                d = resp.get("data") or {}
                self.cookie = (f"deviceId={device}; accessToken={d.get('accessToken','')}; "
                               f"refreshToken={d.get('refreshToken','')}; "
                               f"userId={d.get('userId','')}")
                self.user_id = str(d.get("userId") or "")
                self.logged_in = True
                logger.success("[SPORTY] login OK")
                return True
        return False

    def fetch_event(self, event_id: str) -> dict:
        for path in ("/api/ng/factsCenter/event", "/api/ng/realSportsGame/getEvent"):
            try:
                j = self._getjson(path, {"eventId": event_id, "_t": int(time.time() * 1000)})
                if j.get("data") or j.get("bizCode") == 10000:
                    return j.get("data") or j
            except Exception as e:
                logger.warning(f"[SPORTY] fetch_event {path}: {type(e).__name__}: {e}")
        return {}

    def _markets(self, data: dict) -> List[dict]:
        out = []

        def walk(n):
            if isinstance(n, dict):
                txt = [str(n.get(k) or "") for k in ("name", "marketName", "desc")]
                if any(NEXTGOAL_RE.search(t) for t in txt) or str(n.get("marketId") or "") in ("8", "14"):
                    out.append(n)
                for v in n.values():
                    walk(v)
            elif isinstance(n, list):
                for v in n:
                    walk(v)

        walk(data)
        return out

    def _cands_from_data(self, data: dict, event_id: str, side: str,
                         goal_no: Optional[int], half: Optional[int] = None) -> List[ArmedSelection]:
        """Every OPEN next-goal market for this side, best first: the right goal number, then
        1st-half before full-time before 2nd-half, then the higher price.
        A market is OPEN only when its status is 0 (2 / 3 = suspended / settled)."""
        cands: List[ArmedSelection] = []
        for m in self._markets(data):
            if _to_int(m.get("status"), 0) != 0:           # only status 0 is open for betting
                continue
            name = str(m.get("name") or m.get("marketName") or "")
            desc = str(m.get("desc") or "")
            mname = desc or name or "Next Goal"
            both = f"{name} {desc}"
            mid = str(m.get("id") or m.get("marketId") or "")
            product = str(m.get("product") or m.get("productId") or "1")
            sport_id = str(m.get("sportId") or "sr:sport:1")
            spec = str(m.get("specifier") or m.get("specifiers") or "")
            ms = re.search(r"goalnr=(\d+)", spec)
            if not ms and not re.fullmatch(r"(?:(?:1st|2nd) Half - )?\d{1,2}(?:st|nd|rd|th) Goal", desc.strip(), re.I):
                continue                                   # time-window markets ("5 minutes - 1st goal from 26 to 30") are NOT next-goal markets
            gnum = int(ms.group(1)) if ms else (_goal_num_in_name(both) or goal_no)
            pr = _period_rank(both)
            if goal_no is not None and gnum is not None and gnum != goal_no:
                continue                                   # a goal that already happened / a later one: never bet it
            if (half == 2 and pr == 0) or (half == 1 and pr == 2):
                continue                                   # that half is not being played
            outcomes = m.get("outcomes") or m.get("odds") or m.get("items") or []
            if isinstance(outcomes, dict):
                outcomes = list(outcomes.values())
            for o in outcomes:
                if not isinstance(o, dict):
                    continue
                if o.get("isActive") in (0, "0", False):   # locked outcome
                    continue
                oname = str(o.get("desc") or o.get("name") or o.get("outcomeName") or "")
                oid = str(o.get("id") or o.get("outcomeId") or "")
                try:
                    odds = float(o.get("odds") or o.get("price") or 0)
                except Exception:
                    odds = 0.0
                if odds <= 1.01 or not oid:
                    continue
                low = oname.lower()
                s = "home" if ("home" in low or low in ("1", "h")) else (
                    "away" if ("away" in low or low in ("2", "a")) else None)
                if s != side:
                    continue
                cands.append(ArmedSelection(
                    event_id=event_id, sport_id=sport_id, market_id=mid,
                    outcome_id=oid, specifier=spec if isinstance(spec, str) else "",
                    odds=odds, probability=str(o.get("probability") or ""),
                    product=product, side=s, market_name=mname, outcome_name=oname,
                    goal_no=gnum, period_rank=pr, market_desc=desc))

        def key(a: ArmedSelection):
            gn = a.goal_no
            match = 0 if (goal_no is not None and gn == goal_no) else (1 if gn is None else 2)
            return (match, a.period_rank, -a.odds)

        cands.sort(key=key)
        out: List[ArmedSelection] = []
        seen = set()
        for c in cands:                                    # one entry per market, keep the best 3
            k = (c.market_id, c.specifier, c.outcome_id)
            if k not in seen:
                seen.add(k)
                out.append(c)
        return out[:3]

    def arms_from_data(self, data: dict, event_id: str, goal_no: Optional[int] = None,
                       half: Optional[int] = None) -> Dict[str, List[ArmedSelection]]:
        """Open next-goal markets per side (1st-half, then full-time fallbacks) from one event reply."""
        out: Dict[str, List[ArmedSelection]] = {}
        for side in ("home", "away"):
            c = self._cands_from_data(data, event_id, side, goal_no, half)
            if c:
                out[side] = c
        return out

    def arm_all(self, event_id: str, goal_no: Optional[int] = None,
                half: Optional[int] = None) -> Dict[str, List[ArmedSelection]]:
        data = self.fetch_event(event_id)
        return self.arms_from_data(data, event_id, goal_no, half) if data else {}

    def stake_for_odds(self, odds: float, balance: float = 0.0) -> float:
        """Stake whose PROFIT can never go above the hard cap (rounded DOWN to the kobo) and
        never above the money available. 0.0 = nothing can be staked."""
        if odds <= 1.01:
            return 0.0
        stake = _floor2(float(Config.MAX_PROFIT_PER_BET) / (odds - 1.0))
        if balance and balance > 0:
            stake = min(stake, _floor2(balance))
            return stake if stake >= 10.0 else 0.0
        return max(10.0, stake)

    # ---------- ORDERS: exactly the way the standalone bet.py sends them ----------
    def _build_order(self, arm: ArmedSelection, stake_ngn: float) -> Tuple[dict, dict]:
        units = int(round(float(stake_ngn) * 10000))
        sid = f"uof:{arm.product}/{arm.sport_id}/{arm.market_id}/{arm.outcome_id}"
        if arm.specifier:
            sid += f"?{arm.specifier}"
        sel: Dict[str, Any] = {"eventId": arm.event_id, "id": sid,
                               "odds": f"{float(arm.odds):.2f}",
                               "probability": str(arm.probability or ""),
                               "banker": False, "betPosition": 0, "sportId": arm.sport_id}
        if arm.specifier:
            sel["specifier"] = arm.specifier
        order: Dict[str, Any] = {
            "bizType": 1, "orderType": 1,
            "subBizType": 2 if str(arm.product) == "1" else 1,
            "paymentType": 0, "actualPayAmount": units, "isBonusFactor": False,
            "ticket": {"selections": [sel],
                       "bets": [{"selectedSystems": [1],
                                 "stake": {"value": units},
                                 "selectionRefs": [{"selectionIndex": 0}]}]}}
        if Config.ACCEPT_ODDS_CHANGE:
            order["acceptOddsChange"] = True
        return order, sel

    def place_fresh(self, arm: ArmedSelection, stake: float, odds: float) -> dict:
        """ONE bet on a BRAND-NEW connection with a BRAND-NEW encryption channel, nothing pooled,
        nothing pre-opened (identical to bet.py). If the server answers 19414 ('unable to decrypt')
        it never read the order, so ONE more try on another fresh connection is safe. Any other
        outcome, including a network error after the order was sent, is NEVER re-sent."""
        arm = replace(arm, odds=float(odds))
        order, sel = self._build_order(arm, stake)
        resp: dict = {"bizCode": -1, "message": "no attempt"}
        for attempt in range(2):
            c = self._new_conn()
            try:
                try:
                    aes, tid = self._open_channel_on(c)
                except Exception as e:                      # nothing was sent yet: safe to retry
                    resp = {"bizCode": -1, "message": f"cipher: {type(e).__name__}: {e}"}
                    continue
                if not aes or not tid:
                    resp = {"bizCode": -1, "message": "cipher failed"}
                    continue
                try:
                    resp = self._send_on(c, aes, tid, "/api/ng/orders/order", order)
                except Exception as e:                      # may or may not have been placed: never resend
                    resp = {"bizCode": -2, "message": f"{type(e).__name__}: {e}"}
                    break
                if resp.get("bizCode") == 19414 and attempt == 0:
                    continue                                # server could not read it: nothing placed
                break
            finally:
                try:
                    c.close()
                except Exception:
                    pass
        resp["_sent"] = {"selection": sel, "stake": stake, "fresh_conn": True,
                         "acceptOddsChange": bool(Config.ACCEPT_ODDS_CHANGE)}
        resp["_odds"], resp["_stake"] = float(odds), float(stake)
        return resp

    # ---------- CASH OUT: the standalone cashout.py flow, on a fresh connection ----------
    def cashout_bet(self, bet_id: str, stake: float, amount: float) -> dict:
        c = self._new_conn()
        try:
            aes, tid = self._open_channel_on(c, CASH_REF)
            if not aes or not tid:
                return {"bizCode": -1, "message": "cipher failed"}

            def send(path: str, payload: dict) -> dict:
                return self._send_on(c, aes, tid, path, payload, CASH_REF)

            send("/api/ng/realSportsGame/cashOut/data", {"betId": bet_id})
            cur = str(float(amount))
            last: dict = {}
            for _ in range(5):
                last = send("/api/ng/realSportsGame/cashOut",
                            {"betId": bet_id, "usedStake": str(float(stake)),
                             "isPartial": False, "amount": cur})
                if last.get("bizCode") == 10000:
                    return last
                if last.get("bizCode") == 32000:           # the offer moved: take the new amount
                    new = (last.get("data") or {}).get("maxCashOutAmount")
                    if new and str(float(new)) != cur:
                        cur = str(float(new))
                        time.sleep(0.4)
                        continue
                break
            return last
        except Exception as e:
            return {"bizCode": -2, "message": f"{type(e).__name__}: {e}"}
        finally:
            try:
                c.close()
            except Exception:
                pass

    def open_bets(self) -> List[str]:
        try:
            lst = self._getjson("/api/ng/realSportsGame/cashAbleBets",
                                {"pageSize": 30, "pageNum": 1, "_t": int(time.time() * 1000)},
                                CASH_REF)
        except Exception as e:
            logger.warning(f"[SPORTY] open_bets: {type(e).__name__}: {e}")
            return []

        def walk(n, acc):
            if isinstance(n, dict):
                acc.append(n)
                for v in n.values():
                    walk(v, acc)
            elif isinstance(n, list):
                for v in n:
                    walk(v, acc)
            return acc

        out = []
        for n in walk(lst.get("data"), []):
            bid = n.get("id") or n.get("betId")
            if bid and "bet" in str(bid):
                out.append(str(bid))
        return list(dict.fromkeys(out))

    def cashout_all(self) -> Tuple[int, int, List[str]]:
        """(cashed, failed, reasons). Every failure says why."""
        ok = fail = 0
        notes: List[str] = []
        bids = self.open_bets()
        if not bids:
            notes.append("no open bets found on this account")
        for bid in bids:
            try:
                off = self._getjson("/api/ng/realSportsGame/cashAbleBet",
                                    {"betId": bid, "_t": int(time.time() * 1000)}, CASH_REF)
                d = off.get("data") or {}
                co = d.get("cashOut") or {}
                amt = float(co.get("maxCashOutAmount") or 0)
                stake = float(d.get("stake") or 0)
                if amt <= 0:
                    fail += 1
                    notes.append(f"{bid}: cash out is not offered right now")
                    continue
                r = self.cashout_bet(bid, stake, amt)
                if r.get("bizCode") == 10000:
                    ok += 1
                else:
                    fail += 1
                    notes.append(f"{bid}: {_brief(r)}")
            except Exception as e:
                fail += 1
                notes.append(f"{bid}: {type(e).__name__}: {e}")
        return ok, fail, notes

    def get_balance(self) -> Optional[float]:
        """The real balance in naira, from the call the SportyBet site itself makes (the value is in 1/10000 naira)."""
        try:
            j = self._getjson("/api/ng/pocket/v1/wallet/assetsInfo", {"_t": int(time.time() * 1000)})
            v = (j.get("data") or {}).get("balance")
            return float(v) / 10000.0 if v is not None else None
        except Exception as e:
            logger.warning(f"[SPORTY] balance: {type(e).__name__}: {e}")
            return None

    def market_open(self, data: dict, bet: dict) -> bool:
        """True when the market this bet was placed on is open again (status 0) in the event API."""
        try:
            for m in self._markets(data):
                mid = str(m.get("id") or m.get("marketId") or "")
                spec = str(m.get("specifier") or m.get("specifiers") or "")
                if mid == str(bet.get("market_id")) and spec == str(bet.get("specifier") or "") \
                        and _to_int(m.get("status"), -1) == 0:
                    return True
        except Exception:
            pass
        return False

    def find_bet_ids(self, order_id: str, event_id: str, claimed: set) -> List[str]:
        """The cash-out id of a bet: the open bet whose record contains this ORDER id; if none does,
        the open bets that contain this match's event id. Ids already taken by another bet are skipped."""
        try:
            lst = self._getjson("/api/ng/realSportsGame/cashAbleBets",
                                {"pageSize": 30, "pageNum": 1, "_t": int(time.time() * 1000)}, CASH_REF)
        except Exception as e:
            logger.warning(f"[SPORTY] cashAbleBets: {type(e).__name__}: {e}")
            return []
        by_order: List[str] = []
        by_event: List[str] = []

        def walk(n):
            if isinstance(n, dict):
                bid = n.get("id") or n.get("betId")
                if bid and "bet" in str(bid) and str(bid) not in claimed:
                    dump = json.dumps(n, default=str)
                    if order_id and order_id in dump:
                        by_order.append(str(bid))
                    elif event_id and event_id in dump:
                        by_event.append(str(bid))
                for v in n.values():
                    walk(v)
            elif isinstance(n, list):
                for v in n:
                    walk(v)

        walk(lst.get("data"))
        return list(dict.fromkeys(by_order or by_event))

    def cashout_one(self, bet: dict, claimed: set) -> dict:
        """Cash out ONE bet. {'ok': True} when done; otherwise why not (the caller keeps polling)."""
        try:
            bid = str(bet.get("bet_id") or "")
            if not bid:
                ids = self.find_bet_ids(str(bet.get("order_id") or ""), str(bet.get("event_id") or ""), claimed)
                if not ids:
                    return {"ok": False, "why": "bet not listed as cashable yet"}
                bid = ids[0]
                bet["bet_id"] = bid
            claimed.add(bid)
            off = self._getjson("/api/ng/realSportsGame/cashAbleBet",
                                {"betId": bid, "_t": int(time.time() * 1000)}, CASH_REF)
            d = off.get("data") or {}
            co = d.get("cashOut") or {}
            amt = float(co.get("maxCashOutAmount") or 0)
            stake = float(d.get("stake") or 0)
            if amt <= 0:
                return {"ok": False, "why": "no cash-out offer yet"}
            r = self.cashout_bet(bid, stake, amt)
            if r.get("bizCode") == 10000:
                return {"ok": True, "amount": amt, "bet_id": bid}
            return {"ok": False, "why": _brief(r)}
        except Exception as e:
            return {"ok": False, "why": f"{type(e).__name__}: {e}"}


# =====================================================================
# SPORTYBET DOM  (headless browser, kept alive, reads odds)
# =====================================================================
# A market block is found by its TITLE (the first text pieces of div.m-table__wrapper - never the hidden
# description text, never innerText, so no page layout is forced) and its price is read from the Home / Away
# cells. The block found is remembered, so later reads touch ONE element.
DOM_JS = """(pairs) => {
  const key = s => (s || '').toLowerCase().replace(/[^a-z0-9]/g, '');
  const cache = (window.__bbw = window.__bbw || {});
  const missAt = (window.__bbm = window.__bbm || {});
  const titleKeys = w => {
    const out = [];
    const tw = document.createTreeWalker(w, NodeFilter.SHOW_TEXT);
    let acc = '', n = 0, node;
    while (n < 5 && (node = tw.nextNode())) {
      const t = (node.data || '').replace(/\\s+/g, ' ').trim();
      if (!t) continue;
      acc += t; n++;
      out.push(key(acc));
    }
    return out;
  };
  const lastOdds = s => {
    const m = (s || '').replace(/\\s+/g, ' ').match(/[0-9]+[.,][0-9]+/g);
    return m ? parseFloat(m[m.length - 1].replace(',', '.')) : null;
  };
  const read = (w, side) => {
    const cells = Array.from(w.querySelectorAll('div.m-table-cell'));
    for (const c of cells) {
      const t = (c.textContent || '').replace(/\\s+/g, ' ').trim().toLowerCase();
      if (t.startsWith(side)) {
        const v = lastOdds(t.slice(side.length));
        if (v !== null) return v;
      }
    }
    if (cells.length === 3) {
      const v = lastOdds(cells[side === 'home' ? 0 : 2].textContent);
      if (v !== null) return v;
    }
    return null;
  };
  const locate = (want) => {
    const c = cache[want];
    if (c && c.isConnected && titleKeys(c).includes(want)) return c;
    const now = Date.now();
    if (missAt[want] && now - missAt[want] < 250) return null;
    for (const x of document.querySelectorAll('div.m-table__wrapper')) {
      if (titleKeys(x).includes(want)) { cache[want] = x; return x; }
    }
    missAt[want] = now;
    return null;
  };
  const find = (labels, side) => {
    for (const label of labels) {
      const w = locate(key(label));
      if (!w) continue;
      const o = read(w, side);
      if (o !== null) return {o: o, l: label};
    }
    return null;
  };
  return pairs.map(p => find(p[0], p[1]));
}"""

# Installs (once per page load) a MutationObserver that PUSHES the Home / Away price into the bot
# the moment the page changes it (window.bbPush = Playwright binding). Re-calling it with new
# labels just switches the markets that are watched.
WATCH_JS = """(labels) => {
  if (!window.__bbFind) window.__bbFind = """ + DOM_JS + """;
  const sig = JSON.stringify(labels);
  if (window.__bbSig !== sig) { window.__bbSig = sig; window.__bbLast = {}; }
  window.__bbLabels = labels;
  if (window.__bbWatching) { if (window.__bbKick) window.__bbKick(); return true; }
  window.__bbWatching = true;
  window.__bbLast = window.__bbLast || {};
  window.__bbQueued = false;
  const run = () => {
    window.__bbQueued = false;
    const L = window.__bbLabels;
    if (!L || typeof window.bbPush !== 'function') return;
    const res = window.__bbFind([[L.home || [], 'home'], [L.away || [], 'away']]);
    ['home', 'away'].forEach((s, i) => {
      const r = res[i];
      if (r && r.o > 1.01) {
        const k = r.o + '|' + r.l;
        if (window.__bbLast[s] !== k) { window.__bbLast[s] = k; window.bbPush(s, r.o, r.l); }
      }
    });
  };
  const kick = () => { if (!window.__bbQueued) { window.__bbQueued = true; queueMicrotask(run); } };
  window.__bbKick = kick;
  new MutationObserver(kick).observe(document.documentElement,
                                     {subtree: true, childList: true, characterData: true});
  kick();
  return true;
}"""

DOM_HEADERS_JS = """() => Array.from(document.querySelectorAll('div.m-table__wrapper'))
  .map(w => {
    const tw = document.createTreeWalker(w, NodeFilter.SHOW_TEXT);
    let node;
    while ((node = tw.nextNode())) {
      const t = (node.data || '').replace(/\\s+/g, ' ').trim();
      if (t) return t;
    }
    return '';
  }).filter(Boolean)"""

# Diagnostics: what the block with this header REALLY contains, cell by cell.
DOM_PROBE_JS = """(labels) => {
  const key = s => (s || '').toLowerCase().replace(/[^a-z0-9]/g, '');
  const wanted = (labels || []).map(key);
  const out = [];
  for (const w of document.querySelectorAll('div.m-table__wrapper')) {
    const tw = document.createTreeWalker(w, NodeFilter.SHOW_TEXT);
    let acc = '', n = 0, node, hit = '';
    while (n < 5 && (node = tw.nextNode())) {
      const t = (node.data || '').replace(/\\s+/g, ' ').trim();
      if (!t) continue;
      acc += t; n++;
      if (wanted.includes(key(acc))) { hit = acc; break; }
    }
    if (!hit) continue;
    const cells = Array.from(w.querySelectorAll('div.m-table-cell')).map(c =>
      (c.textContent || '').replace(/\\s+/g, ' ').trim() || '(empty)');
    out.push(hit + ' => ' + (cells.join(' | ') || '(no cells)'));
  }
  return out.slice(0, 3);
}"""

DOM_STATUS_JS = """() => {
  const el = document.querySelector('div.left-team-cell')
          || document.querySelector('div.m-eventDetail')
          || document.querySelector('section.m-eventDetail');
  return el ? (el.innerText || '') : '';
}"""

_PERIOD_CODES = {"H1", "H2", "HT", "FT", "ET", "AET", "PEN", "1H", "2H"}


def _parse_sb_text(txt: str) -> Dict[str, Any]:
    """Reads SportyBet's own scoreboard text (taken from live captures):
      match page : 'Red Star FC vs Saint-Etienne / Match Tracker Statistics / Red Star / 1st / | / 34:37 / 0 / : / 1'
      list row   : '34:17 / H1 / Red Star FC / Saint-Etienne / 0 / 1'
    Used ONLY to check the teams and score when a game is locked (never for the half)."""
    out: Dict[str, Any] = {"teams": None, "score": None, "clock": "", "period": ""}
    lines = [l.strip() for l in (txt or "").split("\n") if l.strip()]
    if not lines:
        return out
    if re.search(r"\s+vs\s+", lines[0], re.I):
        a, b = re.split(r"\s+vs\s+", lines[0], maxsplit=1, flags=re.I)
        out["teams"] = (a.strip(), b.strip())
    m = re.search(r"([^\n|]+?)\s*\n\s*\|\s*\n\s*(\d{1,3}:\d{2})\s*\n\s*(\d{1,2})\s*\n\s*:\s*\n\s*(\d{1,2})", txt)
    if m:
        out["period"], out["clock"] = m.group(1).strip(), m.group(2)
        out["score"] = (int(m.group(3)), int(m.group(4)))
    if not (out["teams"] and out["score"]):
        names = [l for l in lines if not re.fullmatch(r"\d{1,3}:\d{2}", l)
                 and l.upper() not in _PERIOD_CODES and not l.isdigit()]
        nums = [l for l in lines if l.isdigit()]
        if len(names) == 2:                               # the short list-row text only
            out["teams"] = out["teams"] or (names[0], names[1])
            if not out["score"] and len(nums) >= 2:
                out["score"] = (int(nums[-2]), int(nums[-1]))
            if re.fullmatch(r"\d{1,3}:\d{2}", lines[0]):
                out["clock"] = out["clock"] or lines[0]
            per = next((l.upper() for l in lines if l.upper() in _PERIOD_CODES), "")
            out["period"] = out["period"] or per
    return out


class SportyBetDom:
    def __init__(self):
        self._pw = None
        self._browser = None
        self._page = None
        self.http_status = 0
        self.on_price: Optional[Callable[[str, float, str], None]] = None   # called by the page the moment a price changes

    @property
    def alive(self) -> bool:
        return bool(self._page and not self._page.is_closed())

    def _push(self, _source, side, odds, label):
        """Playwright binding: the page calls this on every Home / Away price change."""
        cb = self.on_price
        if cb:
            try:
                cb(str(side), float(odds), str(label))
            except Exception:
                pass

    async def open(self, url: str) -> bool:
        """Loads the match page headless. Only counts as OPEN when the server answered HTTP 200
        and the market tables are on the page (reloads the page up to 2 times if they are not)."""
        from playwright.async_api import async_playwright
        await self.close()
        self.http_status = 0
        try:
            self._pw = await async_playwright().start()
            self._browser = await self._pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
                      "--disable-blink-features=AutomationControlled"],
            )
            ctx = await self._browser.new_context(viewport={"width": 1400, "height": 950},
                                                  locale="en-US")

            async def _lite(route):                       # text only: skip images / fonts / media
                if route.request.resource_type in ("image", "media", "font"):
                    await route.abort()
                else:
                    await route.continue_()

            await ctx.route("**/*", _lite)
            self._page = await ctx.new_page()
            try:
                await self._page.expose_binding("bbPush", self._push)   # the page pushes prices to us
            except Exception as e:
                logger.warning(f"[DOM] expose_binding: {e!r} (falling back to polling only)")
            for attempt in range(3):
                resp = await self._page.goto(url, wait_until="domcontentloaded", timeout=45000)
                self.http_status = resp.status if resp else 0
                if self.http_status == 200:
                    break
                logger.warning(f"[DOM] HTTP {self.http_status} (try {attempt + 1}/3)")
                await asyncio.sleep(1.5)
            if self.http_status != 200:
                logger.error(f"[DOM] page did not load: HTTP {self.http_status}")
                await self.close()
                return False
            for _rl in range(3):
                try:
                    await self._page.wait_for_selector("div.m-table__wrapper", timeout=12000)
                    break
                except Exception:
                    logger.warning(f"[DOM] no market tables yet (try {_rl + 1}/3)")
                    if _rl < 2:
                        try:
                            await self._page.reload(wait_until="domcontentloaded", timeout=30000)
                        except Exception:
                            pass
            logger.success(f"[DOM] match page open (HTTP {self.http_status})")
            return True
        except Exception as e:
            logger.error(f"[DOM] open: {e}")
            await self.close()
            return False

    async def close(self):
        for c in (getattr(self._browser, "close", None), getattr(self._pw, "stop", None)):
            if c:
                try:
                    await asyncio.wait_for(c(), timeout=5)
                except Exception:
                    pass
        self._pw = self._browser = self._page = None

    async def _eval(self, js: str, arg: Any = None, timeout: float = 3.0) -> Any:
        """page.evaluate with a hard time limit — a busy page can never stall the bot."""
        page = self._page
        if not (page and not page.is_closed()):
            return None
        try:
            coro = page.evaluate(js) if arg is None else page.evaluate(js, arg)
            return await asyncio.wait_for(coro, timeout=timeout)
        except Exception:
            return None

    async def reload(self) -> None:
        page = self._page
        if page and not page.is_closed():
            try:
                await page.reload(wait_until="domcontentloaded", timeout=30000)
            except Exception as e:
                logger.warning(f"[DOM] reload: {e!r}")

    async def watch(self, labels_home, labels_away) -> bool:
        """(Re)points the in-page price watcher at these market headers."""
        v = await self._eval(WATCH_JS, {"home": list(labels_home or []),
                                        "away": list(labels_away or [])}, 2.0)
        return bool(v)

    async def market_count(self) -> int:
        v = await self._eval("document.querySelectorAll('div.m-table__wrapper').length")
        try:
            return int(v or 0)
        except Exception:
            return 0

    async def headers(self) -> List[str]:
        """Every market header on the page right now (diagnostics)."""
        v = await self._eval(DOM_HEADERS_JS)
        return [str(h) for h in v] if v else []

    async def probe(self, labels) -> List[str]:
        """What the block(s) with this header really contain, cell by cell (diagnostics)."""
        if isinstance(labels, str):
            labels = [labels]
        labels = [l for l in (labels or []) if l]
        if not labels:
            return []
        v = await self._eval(DOM_PROBE_JS, labels, 2.5)
        return [str(x) for x in v] if v else []

    @staticmethod
    def _pick(x: Any) -> Optional[Tuple[float, str]]:
        try:
            return float(x["o"]), str(x["l"])
        except Exception:
            return None

    async def odds_detail(self, labels, side: str, timeout: float = 2.5) -> Optional[Tuple[float, str]]:
        """(odds, header it was read from) for the first label found on the page, else None."""
        if isinstance(labels, str):
            labels = [labels]
        labels = [l for l in (labels or []) if l]
        if not labels:
            return None
        v = await self._eval(DOM_JS, [[labels, side.lower()]], timeout)
        return self._pick(v[0]) if v else None

    async def odds_pair(self, labels_home, labels_away,
                        timeout: float = 2.5) -> List[Optional[Tuple[float, str]]]:
        """Home and Away price in ONE page read."""
        v = await self._eval(DOM_JS, [[list(labels_home or []), "home"],
                                      [list(labels_away or []), "away"]], timeout)
        if not v or len(v) != 2:
            return [None, None]
        return [self._pick(v[0]), self._pick(v[1])]

    async def info(self) -> Dict[str, Any]:
        """Teams (Home, Away) and score exactly as SportyBet shows them now (lock-time check only)."""
        txt = await self._eval(DOM_STATUS_JS)
        return _parse_sb_text(txt or "")


# =====================================================================
# BET365 SCORE FEED  (SS parsing - CASHES OUT when a score goes down, keeps the goal count right)
# =====================================================================
CHROME = os.getenv("BET365_CHROME", "/usr/bin/google-chrome")
RUN_AS = os.getenv("BET365_RUN_AS", "botuser")
DISPLAY = os.getenv("BET365_DISPLAY", ":77")
TZ = os.getenv("BET365_TZ", "Europe/Amsterdam")
CDP_PORT = int(os.getenv("BET365_CDP_PORT", "9333"))
STALL_SECS = float(os.getenv("BET365_STALL_SECS", "90"))
FIRST_DATA_SECS = float(os.getenv("BET365_FIRST_DATA_SECS", "120"))
DISALLOW_CONFIRM = float(os.getenv("DISALLOW_CONFIRM_SECS", "0.6"))
LIST_FLUSH_SECS = float(os.getenv("BET365_LIST_FLUSH_SECS", "12"))
ANNOUNCED_FILE = Path.home() / ".betbot_announced.json"   # FIs already sent to Telegram

# FI = the bet365 fixture (match) ID.
RE_FI = re.compile(r"(?:^|[|;,\s])FI=(\d{6,})", re.I)
RE_NA = re.compile(r"(?:^|[|;,\s])NA=([^|;]+)", re.I)
RE_SS = re.compile(r"(?:^|[|;,\s])SS=(\d{1,2}\s*[-:]\s*\d{1,2})", re.I)
RE_OV = re.compile(r"OV(\d{6,})C\d+", re.I)
SPLIT = re.compile(r"[|\x01\x08]")
HAS_VS = re.compile(r"\bv\b|\bvs\b|@", re.I)
MARK = ("FI=", "NA=", "SS=", "ID=", "OV")
RE_REC = re.compile(r"^([A-Z]{2});")
SS_MAX = int(os.getenv("SS_MAX", "25"))      # a football score above this is noise, not a score


def _plausible(h: int, a: int) -> bool:
    return 0 <= h <= SS_MAX and 0 <= a <= SS_MAX


def _chunk_rows(rows: List[str], limit: int = 3300) -> List[List[str]]:
    """Splits lines into Telegram messages by SIZE, so a line is never cut in half."""
    out: List[List[str]] = []
    cur: List[str] = []
    n = 0
    for r in rows:
        if cur and n + len(r) + 1 > limit:
            out.append(cur)
            cur, n = [], 0
        cur.append(r)
        n += len(r) + 1
    if cur:
        out.append(cur)
    return out


class ScoreTracker:
    """Turns raw bet365 frames into {FI: name/score} and clean +1 / -1 score steps.

    Only a match's OWN record may set its score:
      * a snapshot 'EV;...' record carries FI / NA / SS itself, or
      * an update frame is  <topic OV<FI>C..> <marker U/F/I/D> <fields>  and the
        fields belong to that one topic.
    Child records (MA / PA / CT / stats ...) are ignored and the FI context never leaks
    from one record into the next (that leak produced the fake '41-37').
    A goal is ONLY a one-side +1 step; anything else is treated as noise."""

    def __init__(self):
        self.state: Dict[str, dict] = {}
        self.touched: set = set()
        self.strict = True
        self.watch_fi: Optional[str] = None
        self.on_change: Optional[Callable] = None
        self._pending: Dict[str, Tuple[Tuple[int, int], float]] = {}

    def _apply(self, fi: str, name: str, ss_raw: Optional[str]):
        prev = self.state.get(fi) or {}
        nm = name or prev.get("name", "")
        h, a, ss = prev.get("h"), prev.get("a"), prev.get("ss", "")
        if ss_raw:
            try:
                nh, na = map(int, re.sub(r"\s+", "", ss_raw.replace(":", "-")).split("-"))
            except ValueError:
                nh = na = None
            if nh is not None and _plausible(nh, na):
                if h is None:                                  # first clean score = baseline
                    h, a, ss = nh, na, f"{nh}-{na}"
                elif (nh, na) != (h, a):
                    dh, da = nh - h, na - a
                    if (dh, da) in ((1, 0), (0, 1), (-1, 0), (0, -1)):   # one goal up / down
                        ph, pa = h, a
                        h, a, ss = nh, na, f"{nh}-{na}"
                        self._pending.pop(fi, None)
                        if fi == self.watch_fi and self.on_change:
                            self.on_change(fi, ph, pa, nh, na, nm)       # act right now
                    else:                                      # a jump: noise unless it repeats
                        pend = self._pending.get(fi)
                        if pend and pend[0] == (nh, na) and time.time() - pend[1] <= 15:
                            if fi == self.watch_fi:            # other sports resync all day: no log spam
                                logger.warning(f"[FEED] resync FI {fi}: {h}-{a} -> {nh}-{na}")
                            h, a, ss = nh, na, f"{nh}-{na}"
                            self._pending.pop(fi, None)
                        else:
                            self._pending[fi] = ((nh, na), time.time())
        if nm or h is not None:
            self.state[fi] = {"name": nm, "ss": ss, "h": h, "a": a, "updated": time.time()}
            self.touched.add(fi)

    def feed(self, text: str) -> None:
        self.touched = set()
        topic_fi: Optional[str] = None
        for part in SPLIT.split(text):
            part = part.strip()
            if not part:
                continue
            mr = RE_REC.match(part)
            rtype = mr.group(1) if mr else ""
            if rtype:                                          # a full record
                topic_fi = None
                if rtype != "EV" and self.strict:
                    continue                                   # child record: never a score
                mf = RE_FI.search(part)                        # the fixture ID (FI), never an event ID
                if not mf:
                    continue
                mn = RE_NA.search(part)
                name = mn.group(1).strip() if mn else ""
                if name and not HAS_VS.search(name):
                    name = ""
                ms = RE_SS.search(part)
                self._apply(mf.group(1), name, ms.group(1) if ms else None)
                continue
            mo = RE_OV.search(part)
            if mo and "=" not in part:                         # update topic  OV<FI>C...
                topic_fi = mo.group(1)
                continue
            if topic_fi and "=" in part:                       # fields of that topic only
                ms = RE_SS.search(part)
                if ms:
                    self._apply(topic_fi, "", ms.group(1))
                topic_fi = None
            # markers ('U' / 'F' / 'I' / 'D') and unrelated parts leave topic_fi alone


class Bet365Feed:
    def __init__(self):
        self.callback: Optional[Callable] = None
        self.alerter = None
        self.tracker = ScoreTracker()
        self.tracker.on_change = self._on_change
        self.running = False
        self._want_run = False
        self._task = self._list_task = None
        self._watch: Optional[str] = None
        self._goals_seen: set = set()
        self._last_data_at: Optional[float] = None
        self._last_alert_at = 0.0
        self._pw = self._browser = self._page = self._proc = None
        self._profile: Optional[str] = None
        self._cooldown = 0.0
        self._announced: Dict[str, float] = self._load_announced()
        self._seen: Dict[str, float] = {}            # first time an FI was seen (waits for its score)
        self._pending_tg: List[str] = []
        self._initial_dump_done = False
        self._up_at = 0.0
        self._raw_fi: Optional[str] = None
        self._raw_buf: deque = deque(maxlen=30)

    def set_alerter(self, a):
        self.alerter = a

    def set_callback(self, cb):
        self.callback = cb

    def watch(self, fi: str):
        self._watch = str(fi)
        self.tracker.watch_fi = self._watch
        self._goals_seen = set()

    def unwatch(self):
        self._watch = None
        self.tracker.watch_fi = None
        self._goals_seen = set()

    def get_match(self, fi: str) -> Optional[dict]:
        s = self.tracker.state.get(str(fi))
        if not s:
            return None
        return {"match_id": str(fi), "name": s["name"], "ss": s["ss"],
                "home_score": s["h"] or 0, "away_score": s["a"] or 0}

    async def wait_match(self, fi: str, secs: float = 20.0) -> Optional[dict]:
        end = time.time() + secs
        while time.time() < end:
            r = self.get_match(fi)
            if r:
                return r
            await asyncio.sleep(0.25)
        return None

    def _roll_day(self):
        # A FI is announced ONCE, ever. Only trim very old entries to keep the file small.
        if len(self._announced) > 3000:
            cutoff = time.time() - 36 * 3600
            self._announced = {k: v for k, v in self._announced.items() if v >= cutoff}

    def _load_announced(self) -> Dict[str, float]:
        try:
            d = json.loads(ANNOUNCED_FILE.read_text())
            cutoff = time.time() - 36 * 3600
            return {str(k): float(v) for k, v in d.items() if float(v) >= cutoff}
        except Exception:
            return {}

    def save_announced(self):
        try:
            tmp = ANNOUNCED_FILE.with_suffix(".tmp")
            tmp.write_text(json.dumps(self._announced))
            tmp.replace(ANNOUNCED_FILE)
        except Exception as e:
            logger.warning(f"[FEED] save announced: {e!r}")

    @staticmethod
    def _row(fi: str, ss: str, name: str) -> str:
        return f"<code>{fi}</code>  {ss or '?'}  {html.escape(name)}"

    def _queue(self, fi: str, name: str, ss: str):
        self._roll_day()
        if not fi or not name or fi in self._announced:
            return
        if not HAS_VS.search(name):
            return
        if not ss:                                   # give the score a moment to arrive, so the list shows it
            if time.time() - self._seen.setdefault(fi, time.time()) < 8:
                return
        self._announced[fi] = time.time()
        self._pending_tg.append(self._row(fi, ss, name))

    def _queue_all(self):
        self._roll_day()
        for fi, s in sorted(self.tracker.state.items(), key=lambda x: (x[1].get("name") or "")):
            self._queue(fi, s.get("name") or "", s.get("ss") or "")

    async def _flusher(self):
        while self._want_run:
            await asyncio.sleep(LIST_FLUSH_SECS)
            if not self._initial_dump_done and self.running and self.tracker.state:
                self._queue_all()
                self._initial_dump_done = True
            if not self._pending_tg or not self.alerter:
                continue
            rows, self._pending_tg = self._pending_tg, []
            for chunk in _chunk_rows(rows):
                try:
                    await self.alerter.send("📋 <b>Bet365 live (FI · score · match)</b>\n" + "\n".join(chunk))
                except Exception:
                    pass

    async def send_full_list(self):
        """/matches: EVERY live match the feed knows — FI, score, teams — even ones sent before."""
        rows = []
        for fi, s in sorted(self.tracker.state.items(), key=lambda x: (x[1].get("name") or "")):
            name = s.get("name") or ""
            if name and HAS_VS.search(name):
                rows.append(self._row(fi, s.get("ss") or "", name))
        if not rows:
            await self.alerter.send("No named matches yet — wait for feed UP")
            return
        chunks = _chunk_rows(rows)
        for i, chunk in enumerate(chunks, 1):
            head = f"📋 <b>All live bet365 matches: {len(rows)}</b> (FI · score · match)  part {i}/{len(chunks)}\n"
            await self.alerter.send(head + "\n".join(chunk))

    def raw_start(self, fi: str):
        self._raw_fi = str(fi)
        self._raw_buf.clear()

    async def raw_dump(self):
        if not self._raw_fi:
            await self.alerter.send("Send <code>/raw FI</code> first, wait a few updates, then <code>/raw</code>")
            return
        if not self._raw_buf:
            await self.alerter.send(f"No frames mentioning {self._raw_fi} yet")
            return
        out = "\n\n".join(self._raw_buf)
        for i in range(0, len(out), 2000):
            await self.alerter.send("<pre>" + html.escape(out[i:i + 2000]) + "</pre>")

    async def start(self):
        if self._want_run and self._task and not self._task.done():
            return
        self._want_run = True
        self._task = asyncio.create_task(self._run())

    async def stop(self):
        self._want_run = False
        self.running = False
        for t in (self._list_task, self._task):
            if t and not t.done():
                t.cancel()
                try:
                    await asyncio.wait_for(asyncio.shield(t), timeout=3.0)
                # CancelledError is not an Exception: without this, /stopbot
                # propagated it and silently killed the Telegram polling loop.
                except (Exception, asyncio.CancelledError):
                    pass
        self._list_task = self._task = None
        await self._teardown()

    # ---------- frame path: no awaits, no telegram ----------
    def _on_frame(self, ev):
        try:
            payload = getattr(ev, "payload", ev)
            text = (payload.decode("utf-8", "ignore")
                    if isinstance(payload, (bytes, bytearray)) else str(payload))
        except Exception:
            return
        if len(text) < 6 or text[:16].lstrip()[:1] == "{":     # (no full-frame copy)
            return
        if not any(m in text for m in MARK):
            return
        if self._raw_fi and self._raw_fi in text:             # /raw FI diagnostic
            self._raw_buf.append(text.encode("unicode_escape").decode()[:700])
        self._last_data_at = time.time()
        self.tracker.feed(text)                                # a score step fires from inside here
        for fi in self.tracker.touched:
            s = self.tracker.state.get(fi) or {}
            n = s.get("name") or ""
            if n:
                self._queue(fi, n, s.get("ss") or "")

    def _on_change(self, fi: str, ph: int, pa: int, h: int, a: int, name: str):
        """Called by the tracker the moment the LOCKED game's score steps by one."""
        if fi != self._watch:
            return
        try:
            _dlog(f"SCORE_FEED fi={fi} {ph}-{pa} -> {h}-{a}")
        except Exception:
            pass
        pt, t = ph + pa, h + a
        base = {"match_id": fi, "name": name, "prev_ss": f"{ph}-{pa}",
                "ss": f"{h}-{a}", "home_score": h, "away_score": a, "ts": time.time()}
        if t > pt:
            if t in self._goals_seen:
                return
            dh, da = h - ph, a - pa
            scorer = ("home" if dh > 0 and da <= 0 else
                      "away" if da > 0 and dh <= 0 else
                      "home" if dh > da else
                      "away" if da > dh else "")
            if not scorer:
                return
            self._goals_seen.add(t)
            self._emit({**base, "event": "goal", "scorer": scorer,
                        "goal_no": pt + 1, "goals_added": t - pt})
        elif t < pt:
            asyncio.get_running_loop().call_later(
                DISALLOW_CONFIRM, self._confirm_disallowed, fi, pt, dict(base))

    def _confirm_disallowed(self, fi: str, prev_total: int, base: dict):
        s = self.tracker.state.get(fi) or {}
        if (s.get("h") or 0) + (s.get("a") or 0) >= prev_total or fi != self._watch:
            return
        self._goals_seen = {x for x in self._goals_seen if x < prev_total}
        self._emit({**base, "event": "disallowed",
                    "ss": s.get("ss", base["ss"]),
                    "home_score": s.get("h"), "away_score": s.get("a")})

    def _emit(self, evt: dict):
        if self.callback:                                  # act FIRST, log afterwards
            try:
                r = self.callback(evt)
                if asyncio.iscoroutine(r):
                    asyncio.ensure_future(r)
            except Exception as e:
                logger.error(f"[FEED] callback: {e}")
        logger.info(f"[FEED] {evt['event']} {evt.get('scorer','')} "
                    f"{evt['prev_ss']}->{evt['ss']} {evt.get('name','')}")

    def _bind(self, page):
        def on_ws(ws):
            u = (getattr(ws, "url", "") or "").lower()
            if "zap" in u or "sportspublisher" in u:
                ws.on("framereceived", self._on_frame)
        page.on("websocket", on_ws)

    async def _tg(self, text: str, gap: float = 300.0):
        now = time.time()
        if now - self._last_alert_at < gap or not self.alerter:
            return
        self._last_alert_at = now
        try:
            await self.alerter.send(text)
        except Exception:
            pass

    def _cmd(self, use_xvfb=False) -> List[str]:
        flags = [CHROME, f"--remote-debugging-port={CDP_PORT}",
                 f"--user-data-dir={self._profile}", "--remote-allow-origins=*",
                 "--no-first-run", "--no-default-browser-check", "--no-sandbox",
                 "--disable-dev-shm-usage", "--disable-blink-features=AutomationControlled",
                 "--use-gl=angle", "--use-angle=swiftshader", "--enable-unsafe-swiftshader",
                 "--lang=en-US", "--window-size=1600,900", "about:blank"]
        env = ["env", f"TZ={TZ}", "LANG=en_US.UTF-8"]
        cmd = (env + ["xvfb-run", "-a", "-s", "-screen 0 1920x1080x24"] + flags
               if use_xvfb else env + [f"DISPLAY={DISPLAY}"] + flags)
        if hasattr(os, "geteuid") and os.geteuid() == 0 and RUN_AS not in ("", "root"):
            cmd = ["sudo", "-u", RUN_AS] + cmd
        return cmd

    def _kill(self):
        if self._profile:
            try:
                subprocess.run(["pkill", "-f", "--", f"--user-data-dir={self._profile}"], timeout=5)
            except Exception:
                pass
        if self._proc and self._proc.poll() is None:
            try:
                self._proc.terminate()
            except Exception:
                pass
        self._proc = None

    async def _spawn(self, use_xvfb: bool) -> bool:
        self._kill()
        if self._profile:
            shutil.rmtree(self._profile, ignore_errors=True)
        self._profile = f"/tmp/b365-chrome-{int(time.time())}"
        self._proc = subprocess.Popen(self._cmd(use_xvfb), stdout=subprocess.DEVNULL,
                                      stderr=subprocess.DEVNULL, start_new_session=True)
        for _ in range(40):
            await asyncio.sleep(0.5)
            if self._proc.poll() is not None:
                return False
            try:
                urllib.request.urlopen(f"http://127.0.0.1:{CDP_PORT}/json/version", timeout=1).read()
                return True
            except Exception:
                pass
        return False

    async def _start_browser(self) -> bool:
        from playwright.async_api import async_playwright
        if not await self._spawn(False) and not await self._spawn(True):
            return False
        try:
            self._pw = await async_playwright().start()
            self._browser = await self._pw.chromium.connect_over_cdp(f"http://127.0.0.1:{CDP_PORT}")
            ctx = self._browser.contexts[0]
            self._page = ctx.pages[0] if ctx.pages else await ctx.new_page()
            self._bind(self._page)
            await self._page.goto(Config.BET365_LIVE_URL, wait_until="commit", timeout=45000)
            asyncio.create_task(self._cookies(self._page))
            return True
        except Exception as e:
            logger.error(f"[FEED] browser: {e}")
            return False

    async def _cookies(self, page):
        for _ in range(12):
            await asyncio.sleep(2.5)
            try:
                body = (await page.inner_text("body", timeout=1500) or "").lower()
                if "uses cookies" in body:
                    for t in ("Accept all", "Accept All", "Alles accepteren", "Akkoord"):
                        try:
                            await page.click(f"text={t}", timeout=1500)
                            return
                        except Exception:
                            pass
            except Exception:
                return

    async def _teardown(self):
        self.running = False
        for c in (getattr(self._browser, "close", None), getattr(self._pw, "stop", None)):
            if c:
                try:
                    await asyncio.wait_for(c(), timeout=5)
                except Exception:
                    pass
        self._pw = self._browser = self._page = None
        self._kill()
        if self._profile:
            shutil.rmtree(self._profile, ignore_errors=True)

    async def _watch_loop(self) -> str:
        t0, last = time.time(), 0.0
        self._last_data_at = None
        while self._want_run:
            await asyncio.sleep(0.25)
            now = time.time()
            if self._proc and self._proc.poll() is not None:
                return "browser exited"
            if self._last_data_at is None:
                if now - t0 > 40 and now - last > 20:
                    last = now
                    try:
                        if "attention required" in (await self._page.title()).lower():
                            await self._tg("Bet365 blocked this IP - change VPN server")
                            self._cooldown = 120.0
                            return "IP blocked"
                    except Exception:
                        pass
                if now - t0 > FIRST_DATA_SECS:
                    return "no data after load"
            else:
                if not self.running:
                    self.running = True
                    self._up_at = now
                    logger.success("[FEED] UP")
                    await self._tg("Bet365 feed ON", 30.0)
                if (self.tracker.strict and now - self._up_at > 45
                        and not any(v.get("name") for v in self.tracker.state.values())):
                    self.tracker.strict = False      # safety net if 'EV' is not the record tag
                    logger.warning("[FEED] no EV records found — switched to loose parsing")
                if now - self._last_data_at > STALL_SECS:
                    return f"no data {int(now - self._last_data_at)}s"
        return "stopped"

    async def _run(self):
        backoff = 5.0
        while self._want_run:
            try:
                if not await self._start_browser():
                    await self._tg("Bet365 browser failed - retrying")
                    await self._teardown()
                    await asyncio.sleep(backoff)
                    backoff = min(backoff * 2, 120.0)
                    continue
                backoff = 5.0
                if self._list_task and not self._list_task.done():
                    self._list_task.cancel()
                self._list_task = asyncio.create_task(self._flusher())
                reason = await self._watch_loop()
                if not self._want_run:
                    break
                logger.warning(f"[FEED] restart: {reason}")
                await self._teardown()
                await asyncio.sleep(3.0 + self._cooldown)
                self._cooldown = 0.0
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.error(f"[FEED] loop: {e!r}")
                await self._teardown()
                await asyncio.sleep(5.0)
        await self._teardown()


# =====================================================================
# BET365 GOAL SIGNAL = the bet365 MATCH page. The pitch marker (ST;LE=GO...) OR the ticker line (ST;ET=1),
# whichever lands first, ONE signal per goal.  A record is a NEW goal unless it is:
#   - inside the first PITCH_QUIET_SECS of the match records (the history bet365 replays when the page opens),
#   - a goal older than PITCH_FRESH_MINUTES on the match clock (old history that arrives late),
#   - the exact same record again, or the other source's signal for the SAME goal (same team, PITCH_DEBOUNCE s).
# The message type byte (0x14 / 0x15) is NOT used: bet365 sends live goals in both.
# =====================================================================
_FIELD_RE = re.compile(r"^([A-Z0-9]{1,4})=")


def _pitch_records(body: bytes) -> List[Tuple[str, Dict[str, str]]]:
    recs: List[Tuple[str, Dict[str, str]]] = []
    ctype: Optional[str] = None
    cur: Dict[str, str] = {}
    for tok in body.split(b";"):
        if not tok:
            continue
        st = tok.decode("latin-1").strip("|")
        if not st:
            continue
        if "=" in st and _FIELD_RE.match(st):
            k, _, v = st.partition("=")
            cur[k] = v
        else:
            if ctype is not None:
                recs.append((ctype, cur))
            ctype, cur = st, {}
    if ctype is not None:
        recs.append((ctype, cur))
    return recs


def _pitch_minute(f: Dict[str, str]) -> str:
    m = re.search(r"#(\d+)'#", f.get("PD", "") or "")
    return m.group(1) if m else (f.get("TM", "") or "")


PATCH2_APPLIED = True
PITCH_LOG = Path.home() / "betbot_pitch.log"


def _plog(line: str) -> None:
    """Every goal record the match-page feed receives, and every decision, with UTC time, in its own file."""
    try:
        if PITCH_LOG.exists() and PITCH_LOG.stat().st_size > 5_000_000:
            PITCH_LOG.replace(PITCH_LOG.with_suffix(".log.1"))
        with PITCH_LOG.open("a", encoding="utf-8") as fh:
            fh.write(time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime()) + " UTC | " + line + "\n")
    except Exception:
        pass


def _goal_n(f: Dict[str, str]) -> Optional[int]:
    """ID=1003-3 -> 3: the goal number counted from 0, both teams together (the real goal number is n + 1)."""
    m = re.match(r"^\d+-(\d+)$", (f.get("ID") or "").strip())
    return int(m.group(1)) if m else None


def _units_balance(r: Any) -> Optional[float]:
    """A SportyBet reply carries the balance in 1/10000 naira (73896700 = N7,389.67)."""
    try:
        return float((r.get("data") or {}).get("balance")) / 10000.0
    except Exception:
        return None


PATCH3_APPLIED = True


def _api_ended(data: Any) -> bool:
    """True when a status-like field of the SportyBet event reply says the match is OVER (ended / finished / full time).
    'closed' is NOT used: a market or the betting can be closed in the middle of a match."""
    if not isinstance(data, dict):
        return False
    queue: List[Tuple[dict, int]] = [(data, 0)]
    while queue:
        sc, depth = queue.pop(0)
        for k, v in sc.items():
            kl = str(k).lower()
            if kl in ("markets", "outcomes"):
                continue
            if isinstance(v, dict):
                if depth < 3:
                    queue.append((v, depth + 1))
                continue
            if isinstance(v, bool):
                if v and kl in ("ended", "isended", "finished", "isfinished", "matchended"):
                    return True
                continue
            if isinstance(v, (str, int)) and any(w in kl for w in ("status", "state", "period", "phase")):
                s = str(v).strip().lower()
                if kl == "matchstatus" and s == "100":
                    return True
                if re.search(r"\b(ended|finished|full ?time|ft|aet)\b", re.sub(r"[^a-z0-9 ]+", " ", s)):
                    return True
    return False


# ---------- timing log (log-only: never raises, never affects the bot) ----------
TIMING_LOG = Path.home() / "betbot_timing.log"
_TL_N = [0]
_MKT: Dict[str, list] = {}


def _ts(t: float) -> str:
    return time.strftime("%H:%M:%S", time.gmtime(t)) + f".{int((t % 1) * 1000):03d}"


def _dlog(line: str) -> None:
    try:
        _TL_N[0] += 1
        if _TL_N[0] % 200 == 1 and TIMING_LOG.exists() and TIMING_LOG.stat().st_size > 5_000_000:
            TIMING_LOG.replace(TIMING_LOG.with_suffix(".log.1"))
        try:
            ld = os.getloadavg()[0]
        except Exception:
            ld = -1.0
        with TIMING_LOG.open("a", encoding="utf-8") as fh:
            fh.write(f"{_ts(time.time())} UTC | load {ld:.2f} | {line}\n")
    except Exception:
        pass


def _trk_market(res, now: float) -> None:
    """Logs when the SportyBet page's Home/Away price for the armed market disappears / returns."""
    try:
        for sd, det in zip(("home", "away"), res):
            seen = bool(det and det[0] > 1.01)
            st = _MKT.get(sd)
            if st is None:
                _MKT[sd] = [seen, 0.0]
                continue
            if seen:
                if not st[0]:
                    _dlog(f"SPORTY_MARKET {sd} OPEN odds={det[0]} {det[1]}")
                st[0], st[1] = True, 0.0
            elif st[0]:
                if st[1] == 0.0:
                    st[1] = now
                elif now - st[1] >= 0.3:
                    _dlog(f"SPORTY_MARKET {sd} GONE (first missed at {_ts(st[1])})")
                    st[0], st[1] = False, 0.0
    except Exception:
        pass


class PitchFeed:
    def __init__(self, feed):
        self.feed = feed
        self.cb: Optional[Callable[[dict], None]] = None
        self.fresh_cb: Optional[Callable[[int], bool]] = None     # is a goal of this match minute recent enough?
        self.url = self.ev = self.fi = ""
        self.page = None
        self._bid = None
        self._task: Optional[asyncio.Task] = None
        self.team: Dict[str, str] = {}
        self._goal_seen: set = set()
        self._goal_q: deque = deque()
        self._last_fire: Dict[str, float] = {}
        self.last_fire = 0.0
        self.frames = self.ignored = self.fired = self.dupes = 0
        self.first_rec_at = self.last_frame_at = 0.0
        self.log: deque = deque(maxlen=10)                        # last decisions, shown by /pitch
        self.state = "idle"

    # ---------- control ----------
    def open(self, url: str, fi: str) -> bool:
        self.reset()
        m = re.search(r"/EV(\d{6,})", url or "")
        if not m:
            self.state = "bad url"
            return False
        self.url, self.ev, self.fi = url.strip(), m.group(1), str(fi)
        self.state = "starting"
        self._task = asyncio.ensure_future(self._run())
        return True

    def reset(self) -> None:
        t, self._task = self._task, None
        if t and not t.done():
            t.cancel()
        pg, self.page = self.page, None
        if pg is not None:
            try:
                asyncio.ensure_future(self._close_page(pg))
            except Exception:
                pass
        self.url = self.ev = self.fi = ""
        self.team.clear()
        self._goal_seen.clear()
        self._goal_q.clear()
        self._last_fire.clear()
        self.last_fire = 0.0
        self.frames = self.ignored = self.fired = self.dupes = 0
        self.first_rec_at = self.last_frame_at = 0.0
        self.ws_at = 0.0
        self.log.clear()
        self._bid = None
        self.state = "idle"

    @staticmethod
    async def _close_page(pg) -> None:
        try:
            await asyncio.wait_for(pg.close(), timeout=4)
        except Exception:
            pass

    async def _tell(self, text: str) -> None:
        a = getattr(self.feed, "alerter", None)
        if a:
            try:
                await a.send(text)
            except Exception:
                pass

    async def _new_page(self, br) -> None:
        try:
            ctxs = br.contexts
            ctx = ctxs[0] if ctxs else await br.new_context()
            page = await ctx.new_page()
            page.on("websocket", self._on_ws)
            self.page, self._bid = page, id(br)
            self.frames = 0
            self.first_rec_at = self.last_frame_at = 0.0         # the page replays the history again: quiet window restarts
            self.state = "loading the match page"
            await page.goto(self.url, wait_until="commit", timeout=45000)
            asyncio.ensure_future(self.feed._cookies(page))
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.warning(f"[PITCH] open page: {type(e).__name__}: {e}")

    async def _run(self) -> None:
        opened_at, told_conn, told_silent, told_url, regoto = 0.0, False, False, False, 0
        try:
            while self.url:
                br = getattr(self.feed, "_browser", None)
                if br is None:
                    self.state = "waiting for Chrome"
                    await asyncio.sleep(0.5)
                    continue
                if self.page is None or self.page.is_closed() or self._bid != id(br):
                    self.page = None
                    await self._new_page(br)
                    opened_at, told_conn, told_silent, told_url, regoto = time.time(), False, False, False, 0
                    if self.page is None:
                        await asyncio.sleep(3.0)
                        continue
                    try:
                        await self.page.bring_to_front()          # a hidden tab can be throttled by Chrome
                    except Exception:
                        pass
                await asyncio.sleep(1.0)
                now = time.time()
                if self.frames and not told_conn:
                    told_conn = True
                    self.state = "connected"
                    await self._tell(f"🎬 Goal feed connected - match page EV{self.ev}, frames flowing")
                if not self.frames and now - opened_at > 25 and not told_silent:
                    told_silent = True
                    self.state = "no frames"
                    await self._tell(f"⚠️ Match page open for 25 s but NO frames yet. Check the Bet365URL- link: {self.url}")
                if self.last_frame_at and now - self.last_frame_at > 30 and now - opened_at > 30:
                    self.last_frame_at = now                      # stalled connection: reload the match page right away
                    self.state = "reconnecting (no frames for 30 s)"
                    await self._tell("⚠️ Goal feed: no frames for 30 s - reloading the match page")
                    try:
                        await self.page.reload(wait_until="commit", timeout=45000)
                    except Exception:
                        pass
                try:
                    u = self.page.url or ""
                except Exception:
                    u = ""
                if self.ev in u:
                    regoto = 0
                elif now - opened_at > 8:
                    if regoto < 3:
                        regoto += 1
                        try:
                            await self.page.goto(self.url, wait_until="commit", timeout=45000)
                        except Exception:
                            pass
                    elif not told_url:
                        told_url = True
                        await self._tell("⚠️ bet365 keeps leaving the match page (the match may be over or the link is wrong).")
        except asyncio.CancelledError:
            pass
        except Exception as e:
            logger.error(f"[PITCH] run: {type(e).__name__}: {e}")

    # ---------- frames (hot path: byte checks first, nothing built for frames we do not need) ----------
    def _on_ws(self, ws) -> None:
        try:
            u = (getattr(ws, "url", "") or "").lower()
            if "zap" in u or "sportspublisher" in u:
                self.ws_at = time.time()        # a new connection replays the match history: the feed only LEARNS for HISTORY_SECS
                _plog(f"WEBSOCKET opened: {u[:90]}")
                ws.on("framereceived", self._on_frame)
        except Exception:
            pass

    def _on_frame(self, ev) -> None:
        t = time.time()
        try:
            x = getattr(ev, "payload", ev)
            data = bytes(x) if isinstance(x, (bytes, bytearray)) else str(x).encode("utf-8", "surrogateescape")
        except Exception:
            return
        self.last_frame_at = t
        self.frames += 1
        if b"LE=" not in data and b"ET=1" not in data and b"TE;" not in data and b"TE=" not in data:
            return
        try:
            for frame in data.split(b"\x08"):
                if b"|" not in frame:
                    continue
                head, _, body = frame.partition(b"|")
                if len(head) < 2:
                    continue
                mtype = head[0]                                   # 0x14 = snapshot, 0x15 = update
                topic = head[1:].split(b"\x01")[0].decode("latin-1")
                body = body.lstrip(b"|")
                if b"LE=" not in body and b"ET=1" not in body and b"TE;" not in body and b"TE=" not in body:
                    continue
                first = body.split(b";", 1)[0]
                if b"=" in first and b"LE=GO" in body and self._mine("", topic):
                    _plog("UNREADABLE goal-looking update frame: " + topic + " | " + body[:300].decode("latin-1"))
                for rtype, f in _pitch_records(body):
                    it = f.get("IT") or ""
                    if not self._mine(it, topic):
                        if f.get("LE", "").startswith("GO"):
                            _plog("DROPPED goal record (not this match): " + it + " | " + topic)
                        continue
                    if not self.first_rec_at:
                        self.first_rec_at = t
                    if rtype == "TE":
                        if f.get("NA"):
                            self.team[f.get("ID", "")] = f["NA"]
                    elif rtype == "ST":
                        if f.get("LE", "").startswith("GO"):
                            self._goal(f, t, mtype, topic)
                        elif f.get("ET") == "1":
                            _plog("ticker line (log only): " + ";".join(f"{k}={v}" for k, v in f.items())[:300])
        except Exception as e:
            logger.warning(f"[PITCH] parse: {type(e).__name__}: {e}")

    def _note(self, src: str, minute: str, tid: str, what: str) -> None:
        try:
            _dlog(f"DECISION {src} min={minute} team={tid} -> {what}")
        except Exception:
            pass
        self.log.append(f"{time.strftime('%H:%M:%S')} {src} {minute or '?'}' team {tid or '?'} -> {what}")

    def _signal(self, src: str, f: Dict[str, str], t: float) -> None:
        tid = f.get("TE") or f.get("TI") or ""
        minute = _pitch_minute(f)
        try:
            _dlog(f"SIGNAL {src} min={minute} team={tid} id={f.get('ID')} in_bot_ms={(time.time() - t) * 1000:.1f}")
        except Exception:
            pass
        rec = (src, tid, minute, tuple(sorted(f.items())))
        if rec in self._goal_seen:                                   # the exact same record again
            self.dupes += 1
            return
        self._goal_seen.add(rec)
        self._goal_q.append(rec)
        if len(self._goal_q) > 3000:
            self._goal_seen.discard(self._goal_q.popleft())
        if t - self.first_rec_at < Config.PITCH_QUIET_SECS:          # the history bet365 replays when the page opens
            self.ignored += 1
            self._note(src, minute, tid, "history (page just opened)")
            return
        if minute.isdigit() and self.fresh_cb is not None and not self.fresh_cb(int(minute)):
            self.ignored += 1                                        # an old goal that arrived late
            self._note(src, minute, tid, "old goal (history)")
            return
        if t - self._last_fire.get(tid, 0.0) < Config.PITCH_DEBOUNCE or t - self.last_fire < 3.0:
            self.dupes += 1                                          # the other source's signal for the same goal
            self._note(src, minute, tid, "same goal (other source)")
            return
        self._last_fire[tid] = self.last_fire = t
        self.fired += 1
        self._note(src, minute, tid, "FIRED")
        cb = self.cb
        if cb:
            cb({"kind": "goal", "src": src, "tid": tid, "ts": t, "minute": minute, "xy": f.get("XY", ""),
                "le": f.get("LE", "") or "ticker", "team": self.team.get(tid, ""),
                "raw": ";".join(f"{k}={v}" for k, v in f.items())})

    def _mine(self, it: str, topic: str) -> bool:
        """A record belongs to this match if it carries the long number of the match link (EV) OR the fixture number (FI)."""
        keys = [k for k in (self.ev, self.fi) if k]
        if not keys:
            return True
        return any(k in it or k in topic for k in keys)

    def _goal(self, f: Dict[str, str], t: float, mtype: int, topic: str) -> None:
        """One goal record (LE=GO). No decision here: it goes straight to the bot with its goal number.
        From the logs: every REPLAYED goal arrived in a 0x14 (snapshot) frame and the live goal in a 0x15 (update) frame,
        so 0x14 = history candidate, 0x15 = live candidate. (The bot still checks the goal number against the score.)"""
        n = _goal_n(f)
        tid = f.get("TE") or f.get("TI") or ""
        hist = (mtype == 0x14)
        raw = ";".join(f"{k}={v}" for k, v in f.items())
        _plog(f"GOAL record type=0x{mtype:02x} history={hist} n={n} team={tid} topic={topic} | {raw[:300]}")
        cb = self.cb
        if cb:
            cb({"kind": "goal", "src": "pitch", "gid": f.get("ID", ""), "n": n, "tid": tid, "ts": t,
                "minute": _pitch_minute(f), "hist": hist, "mtype": mtype,
                "team": self.team.get(tid, ""), "raw": raw})


# =====================================================================
# TELEGRAM
# =====================================================================
class TelegramAlerter:
    def __init__(self):
        self.token = Config.TELEGRAM_BOT_TOKEN
        self.chat_id = Config.TELEGRAM_CHAT_ID
        self.base_url = f"https://api.telegram.org/bot{self.token}"
        self.total_bets = 0
        self.total_staked = 0.0
        self._lock = asyncio.Lock()
        self._last = 0.0
        self._gap = 1.0
        self._session: Optional[aiohttp.ClientSession] = None

    async def _sess(self) -> aiohttp.ClientSession:
        if self._session is None or self._session.closed:
            self._session = aiohttp.ClientSession()
        return self._session

    async def close(self):
        if self._session and not self._session.closed:
            await self._session.close()

    async def send(self, message: str, parse_mode: Optional[str] = "HTML", urgent: bool = False):
        """Sends one message. Failures are LOGGED (they used to vanish silently):
        429 -> wait and retry; 400 (bad HTML) -> retry once as plain text.
        urgent=True (goal alerts / bet results) skips the 1-message-per-second queue."""
        if urgent:
            self._last = asyncio.get_running_loop().time()
        else:
            async with self._lock:
                now = asyncio.get_running_loop().time()
                wait = self._gap - (now - self._last)
                if wait > 0:
                    await asyncio.sleep(wait)
                self._last = asyncio.get_running_loop().time()
        text = message[:4000]
        for _ in range(3):
            payload: Dict[str, Any] = {"chat_id": self.chat_id, "text": text,
                                       "disable_web_page_preview": True}
            if parse_mode:
                payload["parse_mode"] = parse_mode
            try:
                s = await self._sess()
                async with s.post(f"{self.base_url}/sendMessage", json=payload) as r:
                    if r.status == 200:
                        return
                    body = await r.text()
                    logger.warning(f"TG send {r.status}: {body[:200]}")
                    if r.status == 429:
                        try:
                            ra = float(json.loads(body).get("parameters", {}).get("retry_after", 5))
                        except Exception:
                            ra = 5.0
                        await asyncio.sleep(ra + 0.5)
                        continue
                    if r.status == 400 and parse_mode:
                        parse_mode = None
                        text = html.unescape(re.sub(r"<[^>]+>", "", text))
                        continue
                    return
            except Exception as e:
                logger.warning(f"TG send: {type(e).__name__}: {e}")
                return

    async def delete_message(self, message_id):
        """Best effort: removes a message that contains a password from the chat."""
        try:
            s = await self._sess()
            async with s.post(f"{self.base_url}/deleteMessage",
                              json={"chat_id": self.chat_id, "message_id": message_id}) as r:
                await r.read()
        except Exception as e:
            logger.debug(f"TG delete: {e!r}")

    async def notify_startup(self, balance: float):
        await self.send(
            f"💰 <b>LOGGED IN</b>\nBalance: <b>₦{balance:,.2f}</b>\n"
            f"Hard cap: <b>₦{Config.MAX_PROFIT_PER_BET:,.0f}</b>\n\n"
            f"<code>/startbot</code>  <code>/stopbot</code>  <code>/clear</code>\n"
            f"<code>/matches</code>  <code>/login PHONE PASS</code>  <code>/balance N</code>\n"
            f"<code>/switch</code>  <code>/status</code>  <code>/pitch</code>  <code>/shutdown</code>")

    async def notify_ready(self, teams, fi, ss, event_id, next_goal, arms, dom_ok, extra="", dom_note=""):
        h, a = arms.get("home"), arms.get("away")
        mk = (h or a)
        market = html.escape(mk.market_name) if mk else "—"
        await self.send(
            f"🎯 <b>SLOW LOCKED</b>\n⚽ {html.escape(teams)}\n🆔 FI=<code>{fi}</code>  ({ss})\n"
            f"{event_id}\nNext goal #{next_goal}\nMarket: {market}\n"
            f"Headless page: {'OPEN' if dom_ok else 'FAILED'}{dom_note}\n"
            + (extra + "\n" if extra else "")
            + f"Cap ₦{Config.MAX_PROFIT_PER_BET:,.0f}")

    async def notify_bet(self, teams, side, stake, odds, ok, total):
        self.total_bets += 1
        self.total_staked += stake * ok
        await self.send(
            f"{'✅' if ok else '❌'} <b>BET {'SUCCESS' if ok else 'FAIL'}</b> {ok}/{total}\n"
            f"⚽ {html.escape(teams)}\n🎯 {html.escape(side)}\n💵 ₦{stake:,.2f} @ {odds}", urgent=True)

    async def notify_error(self, msg: str):
        await self.send(f"❌ {html.escape(str(msg))}")


class TelegramCommandHandler:
    def __init__(self, bot, alerter: TelegramAlerter):
        self.bot = bot
        self.alerter = alerter
        self._last_id = 0
        self._awaiting_switch = False

    async def start_polling(self):
        await self._reset_webhook()
        logger.info("[TG] polling")
        while True:
            try:
                await self._poll()
                await asyncio.sleep(0.7)
            except Exception as e:
                logger.error(f"[TG] {e}")
                await asyncio.sleep(4)

    async def _reset_webhook(self):
        try:
            s = await self.alerter._sess()
            async with s.post(f"https://api.telegram.org/bot{Config.TELEGRAM_BOT_TOKEN}/deleteWebhook",
                              params={"drop_pending_updates": "true"}) as r:
                logger.info(f"[TG] webhook reset: {(await r.json()).get('ok')}")
        except Exception as e:
            logger.warning(f"[TG] webhook: {e}")

    async def _poll(self):
        s = await self.alerter._sess()
        params = {"offset": self._last_id + 1, "limit": 10, "timeout": 20}
        async with s.get(f"https://api.telegram.org/bot{Config.TELEGRAM_BOT_TOKEN}/getUpdates",
                         params=params) as r:
            if r.status != 200:
                logger.warning(f"[TG] getUpdates {r.status}: {(await r.text())[:150]}")
                return
            data = await r.json()
            if not data.get("ok"):
                return
            for u in data.get("result", []):
                self._last_id = max(self._last_id, u["update_id"])
                await self._handle(u)

    async def _safe(self, fn, *a):
        try:
            await fn(*a)
        except Exception as e:
            logger.exception(f"{getattr(fn, '__name__', 'task')} failed")
            await self.alerter.notify_error(f"{getattr(fn,'__name__','task')}: {type(e).__name__}: {e}")

    async def _handle(self, u: dict):
        m = u.get("message") or {}
        text = (m.get("text") or "").strip()
        chat = m.get("chat", {}).get("id")
        mid = m.get("message_id")
        if str(chat) != str(Config.TELEGRAM_CHAT_ID) or not text:
            return
        text = re.sub(r"^(/\w+)@\w+", r"\1", text)            # /clear@MyBot -> /clear
        low = text.lower().strip()
        logger.info(f"[TG] cmd: {low.split()[0]!r}")           # never log passwords
        pending_switch, self._awaiting_switch = self._awaiting_switch, False

        # reply to a bare /switch:  PHONE PASSWORD [BALANCE]
        if pending_switch and re.fullmatch(r"\+?\d[\d\-]{5,}", low.split()[0]):
            asyncio.create_task(self._safe(self.bot.switch_account, text.split(), mid))
            return

        if low in ("/start", "start", "/help", "help"):
            await self.alerter.send(
                "🟢 <b>Courtside</b>\n"
                f"Hard cap ₦{Config.MAX_PROFIT_PER_BET:,.0f}\n\n"
                "<code>/startbot</code> start\n<code>/stopbot</code> stop\n"
                "<code>/clear</code> clear slow\n<code>/matches</code> all live: FI + score + names\n"
                "<code>/slow</code> then lines: <code>SportyBet- URL</code>  <code>Bet365URL- bet365 match link</code>  "
                "<code>Home- team</code>  <code>Away- team</code>  (<code>Bet365- FI</code> only if the match is not found by names)\n"
                "<code>/pitch</code> goal feed status + last decisions · <code>/pitch off</code> / <code>/pitch on</code>\n"
                "<code>/switch</code> new SportyBet account  (or <code>/switch PHONE PASS BALANCE</code>)\n"
                "<code>/status</code> what is running\n"
                "<code>/raw FI</code> then <code>/raw</code> raw bet365 frames (diagnostic)\n"
                "<code>/shutdown</code> stop the whole bot process for good")
            return
        if low in ("/stop", "stop", "/stopbot", "stopbot", "stop bot"):
            asyncio.create_task(self._safe(self.bot.stop_bot)); return
        if low in ("/startbot", "startbot", "start bot"):
            asyncio.create_task(self._safe(self.bot.start_bot)); return
        if low in ("/clear", "clear"):
            asyncio.create_task(self._safe(self.bot.clear_slow)); return
        if low in ("/matches", "matches", "/list", "list"):
            asyncio.create_task(self._safe(self.bot.bet365.send_full_list)); return
        if low == "/raw" or low.startswith("/raw "):
            p = text.split()
            if len(p) >= 2:
                self.bot.bet365.raw_start(p[1])
                await self.alerter.send(f"Capturing raw frames for FI {p[1]} — send /raw again in a minute")
            else:
                asyncio.create_task(self._safe(self.bot.bet365.raw_dump))
            return
        if low in ("/status", "status"):
            asyncio.create_task(self._safe(self.bot.status_report)); return
        if low in ("/pitch", "/pitch on", "/pitch off"):
            asyncio.create_task(self._safe(self.bot.pitch_cmd, low)); return
        if low in ("/shutdown", "shutdown"):
            asyncio.create_task(self._safe(self.bot.request_shutdown)); return
        if low in ("/switch", "switch"):
            self._awaiting_switch = True
            await self.alerter.send(
                "🔁 <b>Switch account</b>\nSend the new account as:\n"
                "<code>PHONE PASSWORD BALANCE</code>\n(balance is optional)")
            return
        if low.startswith("/switch ") or low.startswith("switch "):
            asyncio.create_task(self._safe(self.bot.switch_account, text.split()[1:], mid))
            return
        if low.startswith("/login ") or low.startswith("login "):
            p = text.split(maxsplit=2)
            if len(p) >= 3:
                asyncio.create_task(self._safe(self.bot.telegram_login, p[1], p[2], mid))
            else:
                await self.alerter.notify_error("/login PHONE PASS")
            return
        if low.startswith("/balance ") or low.startswith("balance "):
            try:
                asyncio.create_task(self._safe(self.bot.handle_balance, float(text.split()[1])))
            except Exception:
                await self.alerter.notify_error("/balance 5000")
            return
        if (low.startswith("/slow") or low.startswith("slow") or "/slow" in low
                or ("sr:match:" in low and "bet365" in low)):
            asyncio.create_task(self._safe(self._handle_slow, text))
            return
        await self.alerter.send("❓ I did not understand that message. Send /help to see the commands.")

    async def _handle_slow(self, text: str):
        logger.info("[TG] /slow received")
        await self.alerter.send("📥 /slow received — locking…")
        url = fi = teams = home = away = b365_url = None
        for line in text.splitlines():
            m = re.match(r"^\s*(?:/slow\s+)?(sporty\w*|bet365url|b365url|bet365link|pitch|bet365|b365|teams?|home|away)\s*[-:–—]\s*(.*)$",
                         line.strip(), re.I)
            if not m:
                continue
            key, body = m.group(1).lower(), m.group(2).strip()
            if key.startswith("sporty"):
                url = body
            elif key in ("bet365url", "b365url", "bet365link", "pitch"):
                b365_url = body
            elif key in ("bet365", "b365"):
                if re.match(r"https?://", body, re.I):
                    b365_url = body
                else:
                    fi = body
            elif key == "home":
                home = body
            elif key == "away":
                away = body
            else:
                teams = body
        if not url:
            mu = re.search(r"https?://\S*sr:match:\d+\S*", text)
            url = mu.group(0) if mu else None
        if not b365_url:
            mb = re.search(r"https?://\S*bet365\S*", text, re.I)
            b365_url = mb.group(0) if mb else None
        if not url or not re.search(r"sr:match:\d+", url):
            await self.alerter.notify_error("SportyBet- line must contain a URL with sr:match:ID")
            return
        if not b365_url or not re.search(r"/EV(\d{6,})", b365_url):
            await self.alerter.notify_error(
                "Bet365URL- must be the bet365 MATCH link (it contains /EV and a number), "
                "e.g.  Bet365URL- https://www.bet365.nl/#/IP/EV15213894932C1")
            return
        mfi = re.search(r"(\d{6,})", fi or "")
        if bool(home) != bool(away):
            await self.alerter.notify_error("give BOTH  Home-  and  Away-  (or neither)")
            return
        await self.bot.handle_slow_game(url, mfi.group(1) if mfi else "", teams or "",
                                        home=home or "", away=away or "", b365_url=b365_url)


# =====================================================================
# BOT
# =====================================================================
class ArbitrageBot:
    def __init__(self):
        self.alerter = TelegramAlerter()
        self.bet365 = Bet365Feed()
        self.bet365.set_alerter(self.alerter)
        self.pitch = PitchFeed(self.bet365)
        self.pitch.cb = self._on_pitch_event
        self.pitch.fresh_cb = self._minute_fresh
        self._goals = 0                                    # goals played so far in the locked game (pitch + score feed)
        self._score: List[int] = [0, 0]                    # [home, away] by bet365 slot
        self._ss_ahead: List[Tuple[float, str]] = []       # goals the score feed counted before the goal feed signalled them
        self._last_pitch_fire = 0.0
        self._pitch_bet = True
        self._side_map: Dict[str, str] = {}
        self._clock: Optional[Tuple[float, float]] = None  # (match minutes, when read) from the SportyBet API
        self.sb = SportyBetClient()
        self.dom = SportyBetDom()
        self.dom.on_price = self._on_price     # the page pushes every price change straight into the cache
        # orders get their OWN threads: they can never queue behind polling work
        self._bet_pool = ThreadPoolExecutor(max_workers=8, thread_name_prefix="bet")
        self._bg_pool = ThreadPoolExecutor(max_workers=6, thread_name_prefix="bg")
        self._slow = None
        self._logged_in = False
        self._active = False
        self._has_open_bet = False
        self._processing = False
        self._arms: Dict[str, ArmedSelection] = {}
        self._armed_goal = 0
        self._arm_ready = asyncio.Event()
        self.balance = 0.0
        self._next_goal_no = 1
        self._keep_task = None
        self._prep_task = None
        self._rearm_task = None
        self._arm_task = None
        self._alts: Dict[str, List[ArmedSelection]] = {}   # fallbacks per side (1st-half, full-time)
        self._price: Dict[str, Tuple[float, str, float]] = {}   # side -> (odds, page header, read at)
        self._price_task = None
        self._half: Optional[int] = None                    # half being played — from the SportyBet API only
        self._half_task = None
        self._arms_half: Optional[int] = None               # half the current arms were built for
        self._pipe = None                     # link to the supervisor (state backup)
        self._creds: Optional[Tuple[str, str]] = None
        self._shutdown = asyncio.Event()
        self._tg = None
        self._poll_task = None

    # ---------- state backup: the supervisor keeps this so a crash restarts where we left off ----------
    @staticmethod
    def _mask(phone: str) -> str:
        d = "".join(c for c in str(phone) if c.isdigit())
        return f"…{d[-4:]}" if len(d) >= 4 else "account"

    def _sync(self):
        if not self._pipe:
            return
        st: Dict[str, Any] = {
            "balance": self.balance, "active": self._active,
            "open_bet": self._has_open_bet,
            "slow": ({"url": self._slow["url"], "fi": self._slow["fi"], "b365_url": self._slow.get("b365_url", ""),
                      "teams": self._slow.get("teams_arg", ""),
                      "home": self._slow.get("home_arg", ""),
                      "away": self._slow.get("away_arg", "")} if self._slow else None)}
        if self._creds:
            st["phone"], st["password"] = self._creds
        try:
            self._pipe.send(st)
        except Exception as e:
            logger.warning(f"[SYNC] {e!r}")

    # ---------- login ----------
    async def _new_login(self, phone: str, password: str) -> Optional[SportyBetClient]:
        sb = SportyBetClient()
        loop = asyncio.get_running_loop()
        try:
            ok = await asyncio.wait_for(
                loop.run_in_executor(self._bg_pool, lambda: sb.login(phone, password)), timeout=90)
        except Exception as e:
            logger.error(f"[LOGIN] {type(e).__name__}: {e}")
            return None
        return sb if ok else None

    async def telegram_login(self, phone: str, password: str, msg_id=None):
        if msg_id:
            await self.alerter.delete_message(msg_id)      # keep the password out of the chat
        await self.alerter.send("Logging in…")
        sb = await self._new_login(phone, password)
        if sb:
            self.sb = sb
            self._creds = (phone, password)
            self._sync()
        await self.alerter.send("Login OK — send /balance AMOUNT then /startbot" if sb else "Login failed")

    async def switch_account(self, args: List[str], msg_id=None):
        """/switch PHONE PASS [BALANCE] — log in with a new SportyBet account and swap to it.
        The old account stays active if the new login fails."""
        if msg_id:
            await self.alerter.delete_message(msg_id)
        if len(args) < 2:
            await self.alerter.notify_error("/switch PHONE PASSWORD [BALANCE]"); return
        if self._processing:
            await self.alerter.notify_error("a bet is being placed — send /switch again in a few seconds")
            return
        phone, password = args[0], args[1]
        bal = None
        if len(args) >= 3:
            try:
                bal = float(args[2].replace(",", ""))
            except ValueError:
                await self.alerter.notify_error("balance must be a number: /switch PHONE PASS 5000")
                return
        await self.alerter.send(f"🔁 Switching to {self._mask(phone)}…")
        sb = await self._new_login(phone, password)
        if not sb:
            await self.alerter.send("❌ Switch failed — still on the previous account")
            return
        had_open = self._has_open_bet
        self.sb = sb
        self._creds = (phone, password)
        self._logged_in = True
        self._has_open_bet = False            # open bets belong to the old account
        if bal is not None:
            self.balance = bal
        self._sync()
        msg = f"✅ Now using {self._mask(phone)}"
        if bal is not None:
            msg += f"\nBalance ₦{self.balance:,.2f}"
        else:
            msg += (f"\n⚠️ Balance still shows the OLD account (₦{self.balance:,.2f}) — "
                    f"send <code>/balance N</code>")
        if had_open:
            msg += "\n⚠️ Bets already open on the old account will NOT be cashed out automatically."
        if self._slow:
            msg += "\nThe locked game stays locked — bets now go to this account."
        await self.alerter.send(msg)

    async def _finish(self, balance: float):
        self.balance = float(balance)
        self._logged_in = True
        self._sync()
        await self.alerter.notify_startup(balance)

    async def handle_balance(self, amount: float):
        if self._logged_in:
            self.balance = float(amount)
            self._sync()
            await self.alerter.send(f"Balance set ₦{amount:,.2f}")
        elif self.sb.logged_in:
            await self._finish(amount)
        else:
            await self.alerter.notify_error("login first:  /login PHONE PASS")

    async def status_report(self):
        s = self._slow
        game = (f"{html.escape(s['teams'] or '?')} (FI {s['fi']})" if s else "none")
        half = {1: "1st", 2: "2nd"}.get(self._half or 0, "?")
        await self.alerter.send(
            "📊 <b>Status</b>\n"
            f"Account: {self._mask(self._creds[0]) if self._creds else 'not logged in'}\n"
            f"Balance: ₦{self.balance:,.2f}\n"
            f"Bot: {'ON' if self._active else 'OFF'}   Bet365 score feed: {'UP' if self.bet365.running else 'down'}\n"
            f"Goal feed: {html.escape(self.pitch.state)}\n"
            f"Slow game: {game}\n"
            f"Next goal #{self._next_goal_no}   Half (API): {half}   Open bets: {'yes' if self._has_open_bet else 'no'}\n"
            f"Headless page: {'open' if self.dom.alive else 'closed'}")

    async def request_shutdown(self):
        await self.alerter.send("🛑 Shutting the bot process down for good (no auto-restart).\n"
                                "Start it again from the terminal with <code>python3 betbot.py</code>")
        self._shutdown.set()

    # ---------- process life-cycle ----------
    def _start_polling(self):
        if self._tg is None:
            self._tg = TelegramCommandHandler(self, self.alerter)
        self._poll_task = asyncio.create_task(self._tg.start_polling())

    async def _restore(self, st: dict, restarts: int):
        """Log in again and put the bot back in the state the supervisor remembers."""
        phone, pw = st["phone"], st.get("password", "")
        sb = await self._new_login(phone, pw)
        if not sb:
            await self.alerter.send(
                "♻️ Bot restarted but auto-login FAILED.\n"
                "Send <code>/login PHONE PASS</code> then <code>/balance N</code> then <code>/startbot</code>")
            return
        self.sb, self._creds = sb, (phone, pw)
        self.balance = float(st.get("balance") or 0)
        self._logged_in = True
        if restarts == 0:
            await self.alerter.notify_startup(self.balance)
        else:
            await self.alerter.send(
                f"♻️ <b>Bot restarted</b> (#{restarts}, last exit code {st.get('last_exit')})\n"
                f"Logged back in. Balance ₦{self.balance:,.2f}")
        self._sync()
        if st.get("active"):
            await self.start_bot(quiet=True)
            slow = st.get("slow")
            if slow:
                await self.handle_slow_game(slow["url"], slow["fi"], slow.get("teams", ""),
                                            feed_wait=150.0, home=slow.get("home", ""),
                                            away=slow.get("away", ""), b365_url=slow.get("b365_url", ""))
                self._has_open_bet = bool(st.get("open_bet"))
                self._sync()

    async def run(self, state: dict):
        loop = asyncio.get_running_loop()
        loop.set_exception_handler(
            lambda l, c: logger.error(f"[ASYNC] {c.get('message')} {c.get('exception')!r}"))
        self._start_polling()
        restarts = int(state.get("restarts") or 0)
        if state.get("phone"):
            await self._restore(state, restarts)
        else:
            await self.alerter.send(
                "♻️ <b>Bot process started</b> — not logged in yet.\n"
                "Send <code>/login PHONE PASS</code> then <code>/balance N</code> then <code>/startbot</code>")
        logger.info("[BOT] ready — control it from Telegram")
        saved_n = -1
        while not self._shutdown.is_set():
            try:
                await asyncio.wait_for(self._shutdown.wait(), timeout=10)
            except asyncio.TimeoutError:
                pass
            if len(self.bet365._announced) != saved_n:         # remember announced FIs on disk
                saved_n = len(self.bet365._announced)
                self.bet365.save_announced()
            if self._poll_task and self._poll_task.done() and not self._shutdown.is_set():
                logger.error("[TG] polling task died — restarting it")
                self._start_polling()
        await self._graceful_stop()

    async def _graceful_stop(self):
        self._active = False
        try:
            self.bet365.save_announced()
        except Exception:
            pass
        self._cancel_prep()
        for step in (self._stop_tasks, self.bet365.stop, self.dom.close):
            try:
                await step()
            except (Exception, asyncio.CancelledError):
                pass
        try:
            self.pitch.reset()
        except Exception:
            pass
        try:
            await self.alerter.send("🛑 Bot process stopped.")
            await self.alerter.close()
        except Exception:
            pass
        for pool in (self._bet_pool, self._bg_pool):
            pool.shutdown(wait=False, cancel_futures=True)

    # ---------- start / stop ----------
    async def start_bot(self, quiet: bool = False):
        if not self._logged_in:
            await self.alerter.notify_error("login + balance first"); return
        if self._active:
            await self.alerter.send("already running — /stopbot first"); return
        self._active = True

        def on_feed(evt: dict):                  # score feed: keeps the goal count right, CASHES OUT when a score goes down
            if not self._active or not self._slow:
                return
            if evt.get("event") == "goal":
                asyncio.ensure_future(self._on_ss_goal(evt))
            elif evt.get("event") == "disallowed":
                asyncio.ensure_future(self._on_disallowed(evt))

        self.bet365.set_callback(on_feed)
        await self.bet365.start()
        self._sync()
        if not quiet:
            await self.alerter.send("BOT STARTED — feed is coming up, list follows.\n"
                                    "Send /slow with SportyBet- / Bet365URL- / Home- / Away- lines")

    def _cancel_prep(self):
        if self._prep_task and not self._prep_task.done():
            self._prep_task.cancel()
        self._prep_task = None
        if self._rearm_task and not self._rearm_task.done():
            self._rearm_task.cancel()
        self._rearm_task = None

    def _reset_game(self):
        self.pitch.reset()
        self._goals, self._score, self._ss_ahead = 0, [0, 0], []
        self._last_pitch_fire = 0.0
        self._pitch_bet = True
        self._side_map = {}
        self._clock = None
        self._arms = {}
        self._alts = {}
        self._price = {}
        self._half = None
        self._arms_half = None
        self._armed_goal = 0
        self._has_open_bet = False
        self._processing = False
        self._seen_ids = set()          # goal ids (1003-N) already handled in this match
        self._gid_of = {}               # goal number -> goal id
        self._ss_goal_at = {}           # goal number -> when the score feed counted it
        self._pitch_goal_at = {}        # goal number -> when the goal feed delivered it
        self._pitch_got = set()         # goal numbers the goal feed delivered
        self._bets = []                 # bets placed in this match (for cash-out)

    async def stop_bot(self):
        self._active = False
        self._cancel_prep()
        await self._stop_tasks()
        try:
            self.bet365.unwatch()
            await self.bet365.stop()
        except (Exception, asyncio.CancelledError) as e:
            logger.error(f"stop feed: {e!r}")
        await self.dom.close()
        self._slow = None
        self._reset_game()
        self._sync()
        await self.alerter.send("BOT STOPPED")

    async def clear_slow(self):
        self._cancel_prep()
        await self._stop_tasks()
        try:
            self.bet365.unwatch()
        except Exception:
            pass
        await self.dom.close()
        self._slow = None
        self._reset_game()
        self._next_goal_no = 1
        self._sync()
        await self.alerter.send("Slow cleared")

    # ---------- /slow ----------
    async def _resolve_fi(self, sporty_url: str, home: str, away: str, wait: float = 30.0) -> Optional[str]:
        """The bet365 fixture id (FI) of this match, found by TEAM NAMES in the score feed - so you never type it.
        Tries your Home-/Away- names first, then the team names the match page itself reports, then SportyBet's."""
        end = time.time() + wait
        while True:
            pairs: List[Tuple[str, str]] = []
            if home and away:
                pairs.append((home, away))
            t1, t2 = self.pitch.team.get("1", ""), self.pitch.team.get("2", "")
            if t1 and t2:
                pairs.append((t1, t2))
            sbp = _sb_pair_from_url(sporty_url)
            if sbp[0] and sbp[1]:
                pairs.append(sbp)
            for want in pairs:
                hits = []
                for fi, st in list(self.bet365.tracker.state.items()):
                    a, b, _ = _split_teams(st.get("name") or "")
                    if b and _pair_match((a, b), want) is not None:
                        hits.append(fi)
                if len(hits) == 1:
                    return hits[0]
            if time.time() >= end:
                return None
            await asyncio.sleep(1.0)

    async def handle_slow_game(self, sporty_url: str, fi: str, teams: str,
                               feed_wait: Optional[float] = None,
                               home: str = "", away: str = "", b365_url: str = ""):
        """Locks the game IMMEDIATELY and replies, then does the slow work
        (feed baseline, API arming, headless page) in the background."""
        if not self._logged_in:
            await self.alerter.notify_error("login first"); return
        if not self._active:
            await self.alerter.notify_error("send /startbot first"); return

        m = re.search(r"(sr:match:\d+)", sporty_url or "")
        if not m:
            await self.alerter.notify_error("SportyBet URL must contain sr:match:ID"); return
        event_id = m.group(1)

        # drop any previous game
        self._cancel_prep()
        await self._stop_tasks()
        await self.dom.close()
        self._reset_game()
        self._arm_ready = asyncio.Event()

        # the GOAL SIGNAL: open the bet365 match page you pasted (a second tab of the bot's Chrome)
        if b365_url:
            self.pitch.open(b365_url, fi)
        if not fi:
            fi = await self._resolve_fi(sporty_url, home, away)
            if not fi:
                self.pitch.reset()
                await self.alerter.notify_error(
                    "Could not find this match in the score feed by team names. "
                    "Add a line  Bet365- <FI>  (the FI from /matches) and send /slow again.")
                return

        self._slow = {"url": sporty_url, "fi": fi, "event_id": event_id, "b365_url": b365_url,
                      "teams": teams.strip(), "teams_arg": teams.strip(),
                      "home_arg": home.strip(), "away_arg": away.strip(),
                      "home": "", "away": ""}
        self.bet365.watch(fi)            # the score is tracked from this moment on (keeps the count right, cashes out)
        rec0 = self.bet365.get_match(fi)
        if rec0:
            self._goals = rec0["home_score"] + rec0["away_score"]
            self._score = [rec0["home_score"], rec0["away_score"]]

        await self.alerter.send(
            f"🔒 <b>LOCKED</b>  Bet365 FI=<code>{fi}</code>\n{event_id}\n"
            f"Goal feed: opening the bet365 match page…  Score feed tracking FI {fi}.\n"
            f"Verifying home/away, then preparing SportyBet page + market…")
        self._prep_task = asyncio.create_task(
            self._prepare_slow(sporty_url, fi, event_id, teams, feed_wait))
        self._sync()

    async def _tell_blocked(self, why: str):
        await self.alerter.send("🚫 <b>BETTING BLOCKED</b> for this game: " + html.escape(why)
                                + "\nGoals are still reported. Fix the names, then /clear and /slow again.")

    def _set_arms(self, arms_all: Dict[str, List[ArmedSelection]]):
        """Best market per side for the status line, plus the fallbacks (1st-half, then
        full-time) so the right one can be picked at goal time without an API call."""
        self._alts = {s: list(v) for s, v in (arms_all or {}).items() if v}
        self._arms = {s: v[0] for s, v in self._alts.items()}

    def _usable(self, side: str) -> List[ArmedSelection]:
        """Candidate markets for this side. 1st-half markets are dead in the 2nd half; 2nd-half
        markets are only used once the API says it is the 2nd half."""
        cands = list(self._alts.get(side) or [])
        if not cands and self._arms.get(side):
            cands = [self._arms[side]]
        half = self._half
        return [c for c in cands
                if not ((half == 2 and c.period_rank == 0) or (half != 2 and c.period_rank == 2))]

    @staticmethod
    def _labels(cands: List[ArmedSelection]) -> Tuple[List[str], Dict[str, ArmedSelection]]:
        """Page headers to look for (1st-half next goal first, then full-time) and which
        market each header belongs to."""
        owner: Dict[str, ArmedSelection] = {}
        labels: List[str] = []
        for c in cands:
            for lb in c.dom_labels:
                k = _label_key(lb)
                if k not in owner:
                    owner[k] = c
                    labels.append(lb)
        return labels, owner

    async def _prepare_slow(self, sporty_url: str, fi: str, event_id: str, teams: str,
                            feed_wait: Optional[float] = None):
        loop = asyncio.get_running_loop()
        try:
            wait = Config.FEED_WAIT if feed_wait is None else feed_wait
            rec = await self.bet365.wait_match(fi, wait)
            if not rec:
                await self.alerter.notify_error(
                    f"FI {fi} is not in the Bet365 feed (waited {int(wait)}s). "
                    f"Check the number with /matches, then /clear and /slow again.")
                return
            ss = rec.get("ss") or "0-0"
            self._goals = rec["home_score"] + rec["away_score"]
            self._score = [rec["home_score"], rec["away_score"]]
            self._next_goal_no = self._goals + 1
            n365 = rec.get("name") or ""

            # 1) WHICH bet365 team is which SportyBet outcome — settled before any goal can fire
            sb_pair = _sb_pair_from_url(sporty_url)
            user = None
            if self._slow and self._slow.get("home_arg") and self._slow.get("away_arg"):
                user = (self._slow["home_arg"], self._slow["away_arg"])
            res = _resolve_sides(n365, sb_pair, user)
            if self._slow:
                first, second = res["t365"]
                self._slow.update(map=res["map"], blocked=res["blocked"], t365=res["t365"],
                                  sb_pair=sb_pair)
                self._slow["home"], self._slow["away"] = sb_pair if sb_pair[0] else (first, second)
                self._slow["teams"] = (f"{user[0]} v {user[1]}" if user
                                       else (teams.strip() or n365))

            # 2) ONE API read gives the half being played, the match clock AND the markets — capped
            try:
                data = await asyncio.wait_for(
                    loop.run_in_executor(self._bg_pool, self.sb.fetch_event, event_id),
                    timeout=Config.API_TIMEOUT)
            except Exception as e:
                data = {}
                await self.alerter.notify_error(f"SportyBet API: {type(e).__name__} {e}")
            phase = _api_phase(data) if data else ""
            if phase in ("1", "2"):
                self._half = int(phase)
            self._note_clock(data)
            arms_all = (self.sb.arms_from_data(data, event_id, self._next_goal_no, self._half)
                        if data else {})
            self._set_arms(arms_all)
            self._armed_goal = self._next_goal_no
            self._arms_half = self._half
            self._arm_ready.set()          # goals no longer have to wait
            if not self._arms:
                await self.alerter.send(
                    "⏳ No open next-goal market right now (probably suspended after a goal). "
                    "Game is LOCKED and I keep checking every 1.5 s — I will tell you when it is armed.")
                self._ensure_arm_retry()
            if res["blocked"]:
                await self._tell_blocked(res["blocked"])

            # 3) headless SportyBet page (must load with HTTP 200) + cross-checks
            dom_ok = await self.dom.open(sporty_url)
            nmk = await self.dom.market_count() if dom_ok else 0
            dom_note = (f" (HTTP {self.dom.http_status}, {nmk} markets)" if dom_ok
                        else f" (HTTP {self.dom.http_status or 'no response'})")
            info = await self.dom.info() if dom_ok else {}
            checks: List[str] = []
            if info.get("teams") and self._slow:
                res2 = _resolve_sides(n365, info["teams"], user)
                if res2["map"] != res["map"] or bool(res2["blocked"]) != bool(res["blocked"]):
                    checks.append("⚠️ the SportyBet page lists the teams differently from its URL — mapping updated")
                    res = res2
                    self._slow.update(map=res["map"], blocked=res["blocked"])
                    if res["blocked"]:
                        await self._tell_blocked(res["blocked"])
                sb_pair = info["teams"]
                self._slow["sb_pair"] = sb_pair
                self._slow["home"], self._slow["away"] = sb_pair
            sbscore = info.get("score")
            if sbscore:
                h365, a365 = rec["home_score"], rec["away_score"]
                mapped = (h365, a365) if res["map"]["home"] == "home" else (a365, h365)
                if tuple(sbscore) == mapped:
                    checks.append(f"✅ score check: bet365 {ss} = SportyBet {sbscore[0]}-{sbscore[1]}")
                elif tuple(sbscore) == mapped[::-1] and sbscore[0] != sbscore[1]:
                    checks.append(f"⚠️ SportyBet shows {sbscore[0]}-{sbscore[1]} but bet365 {ss} maps to "
                                  f"{mapped[0]}-{mapped[1]} — SWAPPED, or SportyBet is lagging. Check before the next goal")
                else:
                    checks.append(f"ℹ️ SportyBet shows {sbscore[0]}-{sbscore[1]}, bet365 {ss} "
                                  f"(SportyBet is often a few seconds behind)")
            checks.append("Half (API): " + {"1": "1st", "2": "2nd", "HT": "half time", "FT": "full time"}
                          .get(phase, "not readable yet"))

            missing = False
            for sd in ("home", "away"):
                a = self._arms.get(sd)
                if a:
                    det = None
                    for _try in range(2):                    # the page may still be filling in
                        det = await self.dom.odds_detail(a.dom_labels, sd) if dom_ok else None
                        if det or not dom_ok:
                            break
                        await asyncio.sleep(0.6)
                    if det:
                        checks.append(f"{sd.title()}: API {a.odds} | page {det[0]} ✓ ({det[1]})")
                    else:
                        missing = True
                        checks.append(f"{sd.title()}: API {a.odds} | page not found ⚠️ "
                                      f"(looked for: {', '.join(a.dom_labels) or '—'})")
                        if dom_ok:                           # show what the page block REALLY contains
                            blk = await self.dom.probe(a.dom_labels)
                            checks.append("Page block: " + (" ; ".join(blk)[:500] if blk
                                                            else "no block with that header on the page"))
            alts = [a for a in (self._alts.get("home") or [])[1:2]]
            if alts:
                checks.append("Fallback market: " + ", ".join(alts[0].dom_labels[:1] or [alts[0].market_name]))
            if missing and dom_ok:
                hdrs = (await self.dom.headers())[:14]
                checks.append("Page markets: " + (" · ".join(hdrs) if hdrs else "none loaded yet"))

            f1, f2 = res["t365"]
            sbh, sba = (self._slow.get("sb_pair") if self._slow else None) or ("?", "?")
            esc = html.escape
            extra = [f"bet365: <b>{esc(f1)}</b> v <b>{esc(f2)}</b>",
                     f"SportyBet: <b>{esc(sbh)}</b> (Home) vs <b>{esc(sba)}</b> (Away)",
                     f"Goal by {esc(f1)} → bet SportyBet <b>{res['map']['home'].upper()}</b>",
                     f"Goal by {esc(f2)} → bet SportyBet <b>{res['map']['away'].upper()}</b>"]
            extra += [esc(n) for n in res["notes"]] + [esc(c) for c in checks]

            await self.alerter.notify_ready(self._slow["teams"] if self._slow else teams,
                                            fi, ss, event_id, self._next_goal_no,
                                            self._arms, dom_ok, "\n".join(extra), dom_note)
            if self._slow:
                self._keep_task = asyncio.create_task(self._keep_loop())
                self._half_task = asyncio.create_task(self._half_loop())
                self._price_task = asyncio.create_task(self._price_loop())
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.exception("prepare_slow failed")
            await self.alerter.notify_error(f"prepare: {type(e).__name__}: {e}")
        finally:
            self._arm_ready.set()

    async def _rearm(self, quiet: bool = False):
        """Re-arm the markets for self._next_goal_no (1st-half next goal first, then full-time
        next goal — see _period_rank). Closed markets and the half that is not being played
        are skipped, so in the 2nd half it is the full-time market."""
        if not self._slow:
            return
        loop = asyncio.get_running_loop()
        event_id = self._slow["event_id"]
        goal_no = self._next_goal_no
        half = self._half
        arms_all: Dict[str, List[ArmedSelection]] = {}
        for _try in range(1 if quiet else 6):
            try:
                arms_all = await asyncio.wait_for(
                    loop.run_in_executor(
                        self._bg_pool, lambda: self.sb.arm_all(event_id, goal_no=goal_no, half=half)),
                    timeout=Config.API_TIMEOUT)
            except Exception as e:
                arms_all = {}
                await self.alerter.notify_error(f"re-arm: {type(e).__name__} {e}")
                break
            if arms_all or not self._slow or self._next_goal_no != goal_no:
                break
            await asyncio.sleep(2.0)     # SportyBet has not opened this goal's market yet — look again
        if not self._slow or self._next_goal_no != goal_no:
            return                       # cleared, or a newer goal already moved on
        self._set_arms(arms_all)         # replace, never keep a stale settled market
        self._armed_goal = goal_no
        self._arms_half = half
        if quiet:
            return
        h, a = self._arms.get("home"), self._arms.get("away")
        mk = h or a
        if mk:
            await self.alerter.send(
                f"Armed goal #{goal_no}: {html.escape((mk.dom_labels or [mk.market_name])[0])}  "
                f"Home@{h.odds if h else '—'}  Away@{a.odds if a else '—'}")
        else:
            await self.alerter.send(f"⚠️ No open market found for goal #{goal_no} — still checking every 1.5 s")
            self._ensure_arm_retry()

    def _ensure_arm_retry(self):
        t = getattr(self, "_arm_task", None)
        if self._slow and not (t and not t.done()):
            self._arm_task = asyncio.create_task(self._arm_retry_loop())

    async def _arm_retry_loop(self):
        """No open next-goal market (suspended after a goal)? Keep looking until one opens,
        then arm it. The game stays locked the whole time, so /clear is never needed."""
        loop = asyncio.get_running_loop()
        try:
            while self._slow and not self._arms:
                await asyncio.sleep(1.5)
                slow = self._slow
                if not slow or self._processing:
                    continue
                goal_no = self._goals + 1
                try:
                    data = await asyncio.wait_for(
                        loop.run_in_executor(self._bg_pool, self.sb.fetch_event, slow["event_id"]),
                        timeout=Config.API_TIMEOUT)
                except asyncio.CancelledError:
                    raise
                except Exception:
                    continue
                if not data or not self._slow:
                    continue
                ph = _api_phase(data)
                if ph in ("1", "2") and int(ph) >= (self._half or 0):
                    self._half = int(ph)
                arms_all = self.sb.arms_from_data(data, slow["event_id"], goal_no, self._half)
                if not arms_all or self._arms or not self._slow:
                    continue
                self._next_goal_no = goal_no
                self._set_arms(arms_all)
                self._armed_goal = goal_no
                self._arms_half = self._half
                self._arm_ready.set()
                self._sync()
                h, a = self._arms.get("home"), self._arms.get("away")
                mk = h or a
                await self.alerter.send(
                    f"✅ <b>Market open — ARMED</b> goal #{goal_no}: "
                    f"{html.escape((mk.dom_labels or [mk.market_name])[0])}  "
                    f"Home@{h.odds if h else '—'}  Away@{a.odds if a else '—'}", urgent=True)
        except asyncio.CancelledError:
            pass

    def _refresh_arms(self, data: dict):
        """Every API poll also refreshes the armed market's probability and odds, so the probability sent
        with a bet is never older than one poll. A market that is closed for a moment KEEPS its old entry
        (it is never dropped from the list)."""
        slow = self._slow
        if not slow or self._processing or not self._arms:
            return
        rt = self._rearm_task
        if rt and not rt.done():
            return
        if self._armed_goal != self._next_goal_no or self._arms_half != self._half:
            return
        fresh = self.sb.arms_from_data(data, slow["event_id"], self._armed_goal, self._half)
        if not fresh:
            return
        key = lambda a: (a.market_id, a.specifier, a.outcome_id)          # noqa: E731
        merged: Dict[str, List[ArmedSelection]] = {}
        for sd, old_list in self._alts.items():
            newer = {key(a): a for a in fresh.get(sd, [])}
            merged[sd] = [newer.pop(key(a), a) for a in old_list] + list(newer.values())
        for sd, lst in fresh.items():
            merged.setdefault(sd, list(lst))
        self._set_arms(merged)

    # ---------- page price: the ONLY odds source for a bet ----------
    def _on_price(self, side: str, odds: float, label: str):
        """Called by the SportyBet page the instant a Home / Away price changes."""
        if odds > 1.01 and side in ("home", "away"):
            self._price[side] = (float(odds), str(label), time.time())

    async def _price_loop(self):
        """Keeps the in-page watcher pointed at the right market headers (it pushes every price
        change into _on_price by itself) and, as a safety net, also reads the price every
        PRICE_POLL seconds. The last good price is kept until PRICE_MAX_AGE even if the market
        is suspended in between."""
        sig: Any = None
        watched_at = 0.0
        try:
            while self._slow:
                await asyncio.sleep(Config.PRICE_POLL)
                if not self._slow or not self.dom.alive:
                    continue
                lh, _ = self._labels(self._usable("home"))
                la, _ = self._labels(self._usable("away"))
                if not lh and not la:
                    continue
                now = time.time()
                s = (tuple(lh), tuple(la))
                if s != sig or now - watched_at > 2.0:      # new market, or re-attach after a page reload
                    sig, watched_at = s, now
                    await self.dom.watch(lh, la)
                res = await self.dom.odds_pair(lh, la)
                now = time.time()
                _trk_market(res, now)
                for sd, det in zip(("home", "away"), res):
                    if det and det[0] > 1.01:
                        self._price[sd] = (det[0], det[1], now)
        except asyncio.CancelledError:
            pass

    # ---------- GOAL SIGNAL (bet365 match page) = bets. The score feed (SS) only keeps the count right and cashes out. ----------
    def _note_clock(self, data: Any):
        c = _api_clock(data)
        if c is not None:
            self._clock = (c, time.time())

    def _now_minute(self) -> Optional[float]:
        if not self._clock:
            return None
        m, t = self._clock
        el = time.time() - t
        return None if el > 180 else m + el / 60.0

    def _minute_fresh(self, minute: int) -> bool:
        """A goal of this match minute is recent (not old history replayed late). Unknown clock = accept."""
        nm = self._now_minute()
        return True if nm is None else minute >= nm - Config.PITCH_FRESH_MINUTES

    def _on_pitch_event(self, e: dict):
        if e.get("kind") == "goal":
            asyncio.ensure_future(self._pitch_goal(e))

    def _pitch_side(self, tid: str, slow: dict) -> str:
        """bet365 score slot ('home' = first-listed team) of the team that scored: by team NAME when the feed
        gives the names, else by team id (1 = home, 2 = away)."""
        sd = self._side_map.get(tid)
        if sd:
            return sd
        nm = self.pitch.team.get(tid, "")
        first, second = slow.get("t365") or ("", "")
        if nm and first and second:
            a, b = _sim(nm, first), _sim(nm, second)
            if a >= b + 0.25 and a >= 0.5:
                sd = "home"
            elif b >= a + 0.25 and b >= 0.5:
                sd = "away"
            if sd:
                self._side_map[tid] = sd
                return sd
        return {"1": "home", "2": "away"}.get(tid, "")

    async def _pitch_goal(self, e: dict):
        """A goal record from the match page. Memory only - nothing here waits for any request.
        replay -> skip | already counted by the score feed -> old | the NEXT goal -> LIVE, even when it arrives
        inside a history window (a replay can never be the next goal: the score feed already counts every played goal)."""
        slow = self._slow
        p = self.pitch
        if not slow or not self._active:
            return
        now = float(e["ts"])
        n, gid = e.get("n"), str(e.get("gid") or "")

        def note(what: str):
            line = f"{time.strftime('%H:%M:%S')} {gid or '?'} {e.get('minute') or '?'}' team {e.get('tid') or '?'} -> {what}"
            p.log.append(line)
            _plog("DECISION " + line)

        if n is None:
            note("no goal number in the record - NOT betting")
            await self.alerter.send(
                f"🎬 goal record without a goal number - NOT betting\nRAW: {html.escape(str(e.get('raw')))[:300]}",
                urgent=True)
            return
        goal_no = int(n) + 1
        self._pitch_got.add(goal_no)
        side = self._pitch_side(e.get("tid", ""), slow)
        rec = self.bet365.get_match(slow["fi"])
        ss_tot = (rec["home_score"] + rec["away_score"]) if rec else None
        known = max(self._goals, ss_tot or 0)                    # goals the bot / the score feed already count
        t_ss = self._ss_goal_at.get(goal_no)
        ss_just_ahead = t_ss is not None and now - t_ss <= Config.SS_AHEAD_SECS

        if gid in self._seen_ids:                                 # 1) replay of a goal we already handled
            p.dupes += 1
            note("replay (id already seen)")
            return
        if e.get("hist"):                                         # 2) inside a history window
            is_next = ss_tot is not None and goal_no == known + 1
            if not (is_next or ss_just_ahead):
                self._seen_ids.add(gid)
                p.ignored += 1
                if goal_no > known:                               # a goal nobody counted and not the next one: do not bet, say so
                    self._goals = goal_no
                    self._next_goal_no = goal_no + 1
                    self._rearm_task = asyncio.create_task(self._rearm(quiet=True))
                    note(f"history shows goal #{goal_no} but the score feed counts {known} - NOT betting")
                    await self.alerter.send(
                        f"⚠️ history shows goal #{goal_no} ({e.get('minute') or '?'}') but the score feed counts {known}. "
                        f"NOT betting. Check the match.", urgent=True)
                else:
                    note(f"history - old goal #{goal_no} (already counted: {known})")
                return
            note(f"inside the history window but goal #{goal_no} is the NEXT goal (counted: {known}) - treating as LIVE")
        elif goal_no <= known and not ss_just_ahead:              # 3) already counted
            self._seen_ids.add(gid)
            p.ignored += 1
            note(f"already counted (goal #{goal_no} <= {known})")
            return
        # 4) LIVE goal
        self._seen_ids.add(gid)
        self._gid_of[goal_no] = gid
        h, a = self._score
        prev = f"{h}-{a}"
        gap = goal_no > known + 1
        if goal_no > self._goals:
            self._goals = goal_no
            if side == "home":
                h += 1
            elif side == "away":
                a += 1
            miss = self._goals - (h + a)
            if miss > 0 and side in ("home", "away"):
                if side == "home":
                    h += miss
                else:
                    a += miss
            self._score = [h, a]
            asyncio.create_task(self._later(Config.CONFIRM_SECS, self._check_confirm(slow, goal_no, gid)))
        self._pitch_goal_at[goal_no] = now
        self._last_pitch_fire = now
        p.fired += 1
        note(f"LIVE goal #{goal_no}" + (" (a goal number was skipped!)" if gap else ""))
        if side not in ("home", "away") or not self._pitch_bet:
            why = "the team is unclear" if side not in ("home", "away") else "betting from the goal feed is OFF (/pitch on)"
            await self.alerter.send(
                f"🎬 NEW GOAL #{goal_no} {e.get('minute') or ''}' - NOT betting: {why}\n"
                f"RAW: {html.escape(str(e.get('raw')))[:300]}", urgent=True)
            return
        await self._on_goal({
            "event": "goal", "src": "pitch", "match_id": slow["fi"], "scorer": side, "ts": now,
            "name": f"{slow['teams']}  🎬 pitch {e.get('minute') or ''}'" + ("  ⚠️ goal number skipped" if gap else ""),
            "prev_ss": prev, "ss": f"{h}-{a}", "home_score": h, "away_score": a,
            "goal_no": goal_no, "goals_added": 1})

    async def _on_ss_goal(self, evt: dict):
        """The score feed counted a goal. It NEVER bets. It keeps the count right, confirms a pitch goal AFTER the bet,
        and warns when the goal feed missed a goal."""
        slow = self._slow
        if not slow or str(evt.get("match_id")) != str(slow["fi"]):
            return
        h, a = int(evt.get("home_score") or 0), int(evt.get("away_score") or 0)
        tot = h + a
        ts = float(evt.get("ts") or time.time())
        self._ss_goal_at[tot] = ts
        pt = self._pitch_goal_at.get(tot)
        if tot > self._goals:
            self._goals, self._score = tot, [h, a]
            self._next_goal_no = tot + 1
            self._rearm_task = asyncio.create_task(self._rearm())
            asyncio.create_task(self.alerter.send(
                f"🥅 <b>SCORE FEED goal #{tot}</b>  {html.escape(str(evt.get('name') or slow['teams']))}\n"
                f"⚽ {evt.get('prev_ss')} → {evt.get('ss')}  🕐 {_wat(ts)}\n"
                f"(information only - bets come from the goal feed)", urgent=True))
            asyncio.create_task(self._later(Config.MISSED_GOAL_SECS, self._check_missed(slow, tot)))
        elif tot == self._goals:
            if pt is not None:
                d = ts - pt
                how = f"goal feed {abs(d):.1f}s {'AHEAD of' if d >= 0 else 'BEHIND'} the score feed"
            else:
                how = "goal came from history"
            asyncio.create_task(self.alerter.send(f"✅ score feed confirms goal #{tot}  ({how})", urgent=True))
            _plog(f"SS confirms goal #{tot}: {how}")

    def _reconcile_goals(self):
        """Replaced by _check_confirm (40 s after a pitch goal the score feed must have confirmed it)."""
        return

    async def pitch_cmd(self, low: str):
        if low.endswith(" on"):
            self._pitch_bet = True
        elif low.endswith(" off"):
            self._pitch_bet = False
        p = self.pitch
        age = f"{int(time.time() - p.last_frame_at)} s ago" if p.last_frame_at else "never"
        nm = self._now_minute()
        await self.alerter.send(
            "🎬 <b>Goal feed</b>\n"
            f"match page: {html.escape(p.url or '-')}\nEV: {p.ev or '-'} · state: {html.escape(p.state)}\n"
            f"frames: {p.frames} · last frame: {age} · match clock: {('%.0f min' % nm) if nm is not None else 'unknown'}\n"
            f"goals fired: {p.fired} · history/old ignored: {p.ignored} · duplicates ignored: {p.dupes}\n"
            f"goal count: {self._goals}  (score feed {self._score[0]}-{self._score[1]})\n"
            f"betting from the goal feed: <b>{'ON' if self._pitch_bet else 'OFF'}</b>\n"
            + ("<b>last decisions</b>\n" + "\n".join(html.escape(x) for x in p.log) if p.log else "no goal records yet"))

    async def _no_price_note(self, sb_side: str, p, t0: float) -> str:
        """Why there was no page price: when the page last showed one, and what the page lists now."""
        try:
            if p:
                d = int((p[2] - t0) * 1000)
                age = (f"SportyBet page last showed a price for {sb_side.upper()} {abs(d)} ms "
                       f"{'AFTER' if d > 0 else 'BEFORE'} the goal signal ({p[1]})")
            else:
                age = f"the page never showed a price for {sb_side.upper()} since this game was locked"
            hdrs = (await self.dom.headers())[:12]
            return f"\n{age}\nPage titles now: " + (" · ".join(hdrs) if hdrs else "none")
        except Exception:
            return ""

    # ---------- goal ----------
    def _place_timed(self, arm: ArmedSelection, stake: float, odds: float,
                     t_dispatch: float) -> dict:
        """Runs in a bet thread. Fresh connection + fresh channel (see place_fresh).
        Adds timestamps so the Telegram timing line shows where time went."""
        t_a = time.time()
        r = self.sb.place_fresh(arm, stake, odds)
        r["_t_d"], r["_t_a"], r["_t_b"] = t_dispatch, t_a, time.time()
        return r

    async def _on_goal(self, evt: dict):
        slow = self._slow
        if not slow or str(evt.get("match_id")) != str(slow["fi"]):
            return
        side = (evt.get("scorer") or "").lower()          # bet365 score slot: "home" = first number
        first, second = slow.get("t365") or ("", "")
        scoring = (first if side == "home" else second) or side

        # ---- the GOAL ALERT goes to Telegram, whatever happens to the bet afterwards
        asyncio.create_task(self.alerter.send(
            f"🎯 <b>GOAL</b>  FI=<code>{slow['fi']}</code>  "
            f"{html.escape(evt.get('name') or slow['teams'])}\n"
            f"⚽ {html.escape(scoring)}  {evt.get('prev_ss')} → {evt.get('ss')}\n"
            f"🕐 signal received <b>{_wat(evt.get('ts'))}</b>", urgent=True))

        if side not in ("home", "away"):
            await self.alerter.notify_error(f"goal scorer unclear: {evt}"); return
        if self._processing:                              # never silent: say that this goal is not bet
            self._next_goal_no = (int(evt.get("home_score") or 0)
                                  + int(evt.get("away_score") or 0) + 1)
            self._rearm_task = asyncio.create_task(self._rearm())
            asyncio.create_task(self.alerter.send(
                "⚠️ goal arrived while the previous bets were still being sent — NOT betting this one",
                urgent=True))
            return

        self._processing = True
        seq_started = False                               # the bet sequence owns _processing once it starts
        t0 = float(evt.get("ts") or time.time())          # the moment the signal arrived
        t_in = time.time()                                # the moment this handler started
        try:
            if not self._arm_ready.is_set():
                try:
                    await asyncio.wait_for(self._arm_ready.wait(), timeout=10)
                except asyncio.TimeoutError:
                    await self.alerter.notify_error("goal fired but SportyBet market not armed yet")
                    return
            slow = self._slow
            if not slow:
                return
            if slow.get("blocked"):
                asyncio.create_task(self.alerter.send(
                    "🚫 NOT betting: " + html.escape(slow["blocked"]), urgent=True))
                return

            # bet365 slot -> SportyBet outcome, decided by team NAMES when the game was locked
            sb_side = (slow.get("map") or {}).get(side, side)

            goal_no = int(evt.get("goal_no") or self._next_goal_no)
            if goal_no != self._armed_goal:          # armed for a different goal number: one quick API read
                self._next_goal_no = goal_no
                await self._rearm(quiet=True)

            cands = self._usable(sb_side)
            if not cands:
                if self._alts.get(sb_side) or self._arms.get(sb_side):
                    await self.alerter.notify_error(
                        f"no market open in the {'2nd' if self._half == 2 else '1st'} half for goal "
                        f"#{goal_no} — not betting")
                else:
                    await self.alerter.notify_error(f"no armed market for {sb_side}")
                return

            # ---- the price: ONLY from the SportyBet page. The page pushes every change into the
            # ---- cache, so reading it is a dictionary lookup (microseconds) — nothing is awaited.
            # ---- If the cache is empty, ONE page read with a hard time limit.
            # ---- No page price = no bet (never the API price).
            labels, owner = self._labels(cands)
            p = self._price.get(sb_side)
            if p and time.time() - p[2] <= Config.PRICE_MAX_AGE and _label_key(p[1]) in owner:
                det: Optional[Tuple[float, str]] = (p[0], p[1])
            else:
                det = await self.dom.odds_detail(labels, sb_side, Config.PAGE_TIMEOUT)
            if not det or det[0] <= 1.01:
                try:
                    _dlog(f"NO_PRICE side={sb_side} signal_age={(time.time() - t0) * 1000:.0f}ms")
                except Exception:
                    pass
                blk = await self.dom.probe(labels)           # what the page block really holds
                await self.alerter.notify_error(
                    f"no price on the SportyBet page for {sb_side.upper()} "
                    f"(looked for: {', '.join(labels) or '—'}) — NOT betting"
                    + (f"\nPage block: {' ; '.join(blk)[:500]}" if blk else "")
                    + await self._no_price_note(sb_side, p, t0))
                return
            odds, page_label = det
            arm = owner.get(_label_key(page_label)) or cands[0]
            t_px = time.time()

            # ---- BET 1: dispatched right now on its own thread, fresh connection + fresh channel.
            tracked = self.balance > 0
            bal = float(self.balance)
            stake = self.sb.stake_for_odds(odds, bal if tracked else 0.0)
            if stake <= 0:
                await self.alerter.notify_error(
                    f"balance ₦{bal:,.2f} is too low for a bet (minimum ₦10) — NOT betting")
                return
            loop = asyncio.get_running_loop()
            fut1 = loop.run_in_executor(self._bet_pool, self._place_timed, arm, stake, odds, time.time())
            t_sent = time.time()
            try:
                _dlog(f"BET_DISPATCH signal_to_dispatch={(t_sent - t0) * 1000:.0f}ms side={sb_side} odds={odds}")
            except Exception:
                pass
            asyncio.create_task(self.alerter.send(          # bet alert in the BACKGROUND
                f"💸 SportyBet <b>{sb_side.upper()}</b>  {html.escape(page_label)} @ {odds}  "
                f"stake ₦{stake:,.2f}  profit ₦{stake * (odds - 1):,.2f}  cap ₦{Config.MAX_PROFIT_PER_BET:,.0f}",
                urgent=True))
            if tracked:                                     # reserve the money now
                self.balance = max(0.0, bal - stake)

            # ---- the rebet + the answers are handled by the sequence, in the background
            seq_started = True
            asyncio.create_task(self._bet_sequence(slow, arm, scoring, page_label, odds, stake,
                                                   fut1, tracked, (t0, t_in, t_px, t_sent)))
        except Exception as e:
            logger.exception("goal handler failed")
            await self.alerter.notify_error(f"goal handler: {e}")
        finally:
            # The goal happened whether or not the bets landed, so the armed market is settled:
            # move on to the next goal number — in the BACKGROUND, right now (not after the answers).
            self._next_goal_no = (int(evt.get("home_score") or 0)
                                  + int(evt.get("away_score") or 0) + 1)
            self._rearm_task = asyncio.create_task(self._rearm())
            self._sync()
            if not seq_started:
                self._processing = False

    async def _bet_sequence(self, slow: dict, arm: ArmedSelection, scoring: str, label: str,
                            odds: float, stake: float, fut1: Any, tracked: bool, marks: tuple):
        """Bet 1 is already on its way. The rebet is sent only after bet 1 was ANSWERED, at most REBET_GAP (0.25 s)
        later, and its stake comes from the real balance. A 4200 (balance) reply carries the real balance: the order is
        then sent once more with a stake that fits. Any other rejection is NOT rebet."""
        loop = asyncio.get_running_loop()
        plan: List[Tuple[float, float]] = [(odds, stake)]
        futs: List[Any] = [fut1]
        notes: List[str] = []
        credited: set = set()                    # indexes whose stake was already given back

        async def answer(f) -> Optional[dict]:
            try:
                return await asyncio.wait_for(asyncio.shield(f), timeout=Config.BET_WAIT)
            except asyncio.TimeoutError:
                return None
            except Exception as e:
                return {"bizCode": -2, "message": f"{type(e).__name__}: {e}"}

        def give_back(i: int, r: Optional[dict]):
            if tracked and isinstance(r, dict) and r.get("bizCode") != 10000 and i not in credited:
                credited.add(i)
                self.balance += plan[i][1]

        try:
            last = await answer(fut1)
            give_back(0, last)
            for n in range(1, max(0, Config.MAX_REBET) + 1):
                if last is None:
                    notes.append(f"rebet skipped: bet {n} not answered within {Config.BET_WAIT:g}s")
                    break
                code = last.get("bizCode")
                if code == 4200:                                     # not enough balance: the reply has the real one
                    real = _units_balance(last)
                    if real is None:
                        notes.append("no resend: 4200 without a balance in the reply")
                        break
                    self.balance, tracked = real, True
                    credited.add(len(plan) - 1)
                    notes.append(f"4200: real balance ₦{real:,.2f} - resending once with a stake that fits")
                elif code == 4510:
                    fx = _fix_from_4510(last)
                    if not fx:
                        notes.append("rebet skipped: 4510 (market / odds changed)")
                        break
                    arm = replace(arm, probability=fx)
                    notes.append(f"rebet uses the server's current probability {fx}")
                elif code != 10000:
                    notes.append(f"no rebet: bet {n} was rejected ({_brief(last)[:90]})")
                    break
                else:                                                # bet 1 accepted: read the real balance DURING the gap
                    bal_f = loop.run_in_executor(self._bg_pool, self.sb.get_balance)
                    try:
                        fresh = await asyncio.wait_for(asyncio.shield(bal_f), timeout=Config.REBET_GAP)
                    except Exception:
                        fresh = None                                 # not back within the gap: use the tracked balance
                    if fresh is not None:
                        self.balance, tracked = fresh, True
                if self._slow is not slow:
                    break
                if tracked and self.balance < 10.0:
                    notes.append(f"rebet skipped: only ₦{self.balance:,.2f} left")
                    break
                stake_n = self.sb.stake_for_odds(odds, self.balance if tracked else 0.0)
                if stake_n <= 0:
                    notes.append(f"rebet skipped: only ₦{self.balance:,.2f} left")
                    break
                f = loop.run_in_executor(self._bet_pool, self._place_timed, arm, stake_n, odds, time.time())
                futs.append(f)
                plan.append((odds, stake_n))
                if tracked:
                    self.balance = max(0.0, self.balance - stake_n)
                if n < Config.MAX_REBET:
                    last = await answer(f)
                    give_back(len(plan) - 1, last)
        except Exception as e:
            logger.exception("bet sequence failed")
            await self.alerter.notify_error(f"bet sequence: {type(e).__name__}: {e}")

        raw = await asyncio.gather(*futs, return_exceptions=True)
        self._processing = False                 # all answers are in: the bot is free for the next goal
        try:
            self._remember_bets(slow, [r for r in raw if isinstance(r, dict)])
        except Exception as e:
            logger.error(f"remember bets: {e!r}")
        await self._report_bets(slow, scoring, plan, raw, tracked, label, notes, marks, credited)
        asyncio.create_task(self._refresh_balance_once())

    async def _report_bets(self, slow: dict, scoring: str, plan: list, raw: list,
                           tracked: bool, label: str, notes: list, marks: tuple, credited: set):
        """Reports the order answers. A failed bet gets the full server reply and the exact
        request, so it can be diagnosed."""
        t0, t_in, t_px, t_sent = marks
        try:
            results = [r if isinstance(r, dict) else
                       {"bizCode": -2, "message": f"{type(r).__name__}: {r}"} for r in raw]
            good = [r for r in results if r.get("bizCode") == 10000]
            if tracked:                              # give back the stake of every bet that did not land
                self.balance += sum(plan[i][1] for i, r in enumerate(results)
                                    if r.get("bizCode") != 10000 and i not in credited)
            if good and self._slow is slow:
                self._has_open_bet = True
            asyncio.create_task(self.alerter.notify_bet(
                slow["teams"], scoring, plan[0][1], plan[0][0], len(good), len(results)))
            ms = lambda a, b: int((b - a) * 1000)            # noqa: E731
            r0 = results[0]
            try:
                _dlog(f"BET_RESULT codes={[r.get('bizCode') for r in results]} order_round_trip_ms={int((r0['_t_b'] - r0['_t_a']) * 1000) if '_t_b' in r0 else None}")
            except Exception:
                pass
            parts = [f"signal→handler {ms(t0, t_in)}ms", f"page price {ms(t_in, t_px)}ms",
                     f"signal→1st bet dispatched {ms(t0, t_sent)}ms"]
            if "_t_a" in r0:
                parts += [f"thread wait {ms(r0['_t_d'], r0['_t_a'])}ms",
                          f"bet 1 round trip (new connection) {ms(r0['_t_a'], r0['_t_b'])}ms"]
            if len(results) > 1 and "_t_d" in results[1] and "_t_d" in r0:
                parts.append(f"rebet sent {ms(r0['_t_d'], results[1]['_t_d'])}ms after bet 1")
            parts.append(f"all done {ms(t0, time.time())}ms")
            if tracked:
                parts.append(f"balance ₦{self.balance:,.2f}")
            timing = "⏱ " + " · ".join(parts + notes)
            for i, r in enumerate(results):
                if r.get("bizCode") == 10000:
                    continue
                o, st = plan[i]
                resp = {k: v for k, v in r.items() if not k.startswith("_")}
                body = json.dumps({"response": resp, "sent": r.get("_sent")},
                                  ensure_ascii=False, default=str)
                took = (f"{ms(r['_t_a'], r['_t_b'])}ms" if "_t_a" in r else "?")
                asyncio.create_task(self.alerter.send(
                    f"❌ <b>BET {i + 1} FAILED</b> — {html.escape(scoring)}\n"
                    f"{html.escape(label)} @ {o} · stake ₦{st:,.2f} · profit ₦{st * (o - 1):,.2f} "
                    f"· SportyBet took {took}\n"
                    f"why: {html.escape(_brief(r))}\n"
                    f"{html.escape(_diag_4510(r))}\n"
                    f"<pre>{html.escape(body[:2600], quote=False)}</pre>", urgent=True))
            asyncio.create_task(self.alerter.send(timing, urgent=True))
            self._sync()
        except Exception as e:
            logger.exception("report_bets failed")
            await self.alerter.notify_error(f"bet result: {type(e).__name__}: {e}")

    # ---------- disallowed: the SCORE feed went DOWN -> cash out from SportyBet ----------
    async def _on_disallowed(self, evt: dict):
        """The SCORE feed went DOWN: forget that goal, then cash out the bets placed on it - but only when the market
        they were placed on is open again on SportyBet (polled through the SportyBet API)."""
        if not self._slow or str(evt.get("match_id")) != str(self._slow["fi"]):
            return
        try:
            ph, pa = [int(x) for x in str(evt.get("prev_ss")).split("-")]
        except Exception:
            ph, pa = 0, 0
        prev_total = ph + pa
        h, a = int(evt.get("home_score") or 0), int(evt.get("away_score") or 0)
        pending = [b for b in self._bets if b.get("goal_no") in (prev_total, None)]
        await self.alerter.send(
            f"🚫 GOAL CANCELLED  FI=<code>{self._slow['fi']}</code>  "
            f"{html.escape(evt.get('name') or self._slow['teams'])}  "
            f"{evt.get('prev_ss')} → {evt.get('ss')}"
            + (f"\nWaiting for the market to open again, then cashing out {len(pending)} bet(s)…" if pending else ""),
            urgent=True)
        gid = self._gid_of.pop(prev_total, None)               # the cancelled goal is forgotten, so a real goal can reuse its number
        for g in (gid, f"1003-{prev_total - 1}"):
            if g:
                self._seen_ids.discard(g)
        self._pitch_got.discard(prev_total)
        self._ss_goal_at.pop(prev_total, None)
        self._pitch_goal_at.pop(prev_total, None)
        self._goals, self._score, self._ss_ahead = h + a, [h, a], []
        self._next_goal_no = self._goals + 1
        if pending:
            self._cash_task = asyncio.create_task(self._cashout_when_open(pending))
        try:
            await self._rearm()
        except Exception as e:
            logger.error(f"rearm after cancel: {e!r}")
        self._sync()

    # ---------- 2nd-half switch (SportyBet REST API, polled every HALF_POLL seconds) ----------
    async def _switch_to_2nd_half(self, data: dict) -> bool:
        """Re-arms on the next-goal market that is open in the 2nd half (full-time next goal),
        using the SAME API reply that detected the half (no extra request).
        False = no open market yet, try again."""
        slow = self._slow
        if not slow:
            return False
        goal_no = self._goals + 1
        arms_all = self.sb.arms_from_data(data, slow["event_id"], goal_no, 2)
        if not arms_all:
            return False
        self._next_goal_no = goal_no
        self._set_arms(arms_all)
        self._armed_goal = goal_no
        self._arms_half = 2
        self._half = 2
        self._arm_ready.set()
        self._sync()
        h, a = self._arms.get("home"), self._arms.get("away")
        mk = h or a
        label = html.escape((mk.dom_labels or [mk.market_name])[0]) if mk else "—"
        await self.alerter.send(
            f"🔄 <b>2nd HALF — market switched</b>\n⚽ {html.escape(slow['teams'] or '?')}\n"
            f"Now armed: <b>{label}</b>  (goal #{goal_no})\n"
            f"Home@{h.odds if h else '—'}  Away@{a.odds if a else '—'}", urgent=True)
        return True

    async def _half_loop(self):
        """Every HALF_POLL seconds asks the SportyBet event API which part of the match it is and what the clock says.
        Tells you at half time, CLEARS THE GAME AUTOMATICALLY at full time (explicit FT from the API, or the API going
        silent / having no open next-goal market for minutes after minute 85), and switches the armed market to the
        full-time next goal the moment the 2nd half is confirmed."""
        loop = asyncio.get_running_loop()
        last, same, notified = "", 0, ""
        unknown = misses = 0
        warned_unknown = warned_miss = False
        no_data_since: Optional[float] = None
        no_mkt_since: Optional[float] = None
        last_dump = 0.0
        try:
            while self._slow:
                await asyncio.sleep(Config.HALF_POLL)
                slow = self._slow
                if not slow:
                    break
                try:
                    data = await asyncio.wait_for(
                        loop.run_in_executor(self._bg_pool, self.sb.fetch_event, slow["event_id"]),
                        timeout=Config.API_TIMEOUT)
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    logger.warning(f"[HALF] {type(e).__name__}: {e}")
                    continue
                if not data:
                    no_data_since = no_data_since or time.time()
                    if self._ft_guess(no_data_since, Config.FT_SILENCE_SECS):
                        await self._ft_clear(slow, "the SportyBet API returned nothing after minute 85", None)
                        return
                    continue
                no_data_since = None
                self._note_clock(data)
                if self._clock and self._clock[0] >= 85.0 and time.time() - last_dump >= 60:
                    last_dump = time.time()
                    _plog("API fields after minute 85: " + _api_fields(data)[:800])
                self._refresh_arms(data)
                self._reconcile_goals()
                if self.sb.arms_from_data(data, slow["event_id"]):
                    no_mkt_since = None
                else:
                    no_mkt_since = no_mkt_since or time.time()
                    if self._ft_guess(no_mkt_since, Config.FT_NOMARKET_SECS):
                        await self._ft_clear(slow, "no open next-goal market for minutes after minute 85", data)
                        return
                phase = "FT" if _api_ended(data) else _api_phase(data)
                if not phase:
                    unknown += 1
                    if unknown >= 10 and not warned_unknown:
                        warned_unknown = True
                        await self.alerter.send(
                            "⚠️ Could not read the match phase from the SportyBet API. "
                            "Fields seen (send this to me):\n"
                            f"<code>{html.escape(_api_fields(data))}</code>")
                    continue
                unknown = 0
                same = same + 1 if phase == last else 1
                last = phase
                if same < 2:                         # same answer twice in a row = confirmed
                    continue
                if phase in ("HT", "FT"):
                    if phase != notified:
                        notified = phase
                        label = "HALF TIME" if phase == "HT" else "FULL TIME"
                        extra = "" if phase == "HT" else "\nClearing this game automatically."
                        await self.alerter.send(
                            f"⏸ <b>{label}</b> — {html.escape(slow['teams'] or '?')}{extra}")
                        if phase == "FT":
                            asyncio.ensure_future(self._auto_clear())
                            return
                    continue
                notified = ""
                if int(phase) >= (self._half or 0):
                    self._half = int(phase)
                if phase == "2" and self._arms_half != 2:
                    rt = self._rearm_task
                    if self._processing or (rt and not rt.done()):
                        continue                     # a bet / re-arm is running: next tick
                    if await self._switch_to_2nd_half(data):
                        misses, warned_miss = 0, False
                    else:
                        misses += 1
                        if misses >= 10 and not warned_miss:
                            warned_miss = True
                            await self.alerter.send(
                                f"⚠️ 2nd half detected but no open next-goal market for goal "
                                f"#{self._goals + 1} yet — still retrying every {Config.HALF_POLL:g}s")
        except asyncio.CancelledError:
            pass

    # ---------- housekeeping while a game is locked ----------
    async def _keep_loop(self):
        """Brings the headless SportyBet page back if it dies or shows no markets. Also starts the balance reader."""
        bt = getattr(self, "_balance_task", None)
        if not (bt and not bt.done()):
            self._balance_task = asyncio.create_task(self._balance_loop())
        empty = 0
        try:
            while self._slow:
                await asyncio.sleep(Config.STATUS_POLL)
                if not self._slow:
                    break
                try:
                    if not self.dom.alive:
                        ok = await self.dom.open(self._slow["url"])
                        await self.alerter.send(
                            f"♻️ headless SportyBet page {'reopened' if ok else 'could NOT be reopened'} "
                            f"(HTTP {self.dom.http_status or 'no response'})")
                        empty = 0
                    elif await self.dom.market_count() == 0:
                        empty += 1
                        if empty >= 3:                      # ~15 s with no market tables: reload the page
                            empty = 0
                            await self.dom.reload()
                            logger.warning("[KEEP] page had no markets - reloaded")
                    else:
                        empty = 0
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    logger.error(f"[KEEP] {e!r}")
        except asyncio.CancelledError:
            pass

    async def _stop_tasks(self):
        for attr in ("_keep_task", "_half_task", "_price_task", "_arm_task", "_balance_task"):
            t = getattr(self, attr, None)
            if t and not t.done():
                t.cancel()
                try:
                    await asyncio.wait_for(asyncio.shield(t), timeout=2.0)
                except (Exception, asyncio.CancelledError):
                    pass
            setattr(self, attr, None)

    def stop(self):
        self._active = False
        self.bet365._want_run = False
        self.bet365.running = False

    async def _later(self, delay: float, coro) -> None:
        try:
            await asyncio.sleep(delay)
            await coro
        except asyncio.CancelledError:
            coro.close()
        except Exception as e:
            logger.error(f"[LATER] {e!r}")

    async def _check_missed(self, slow: dict, goal_no: int):
        """The score feed counted a goal. If the goal feed never delivered it, say so."""
        if slow is not self._slow or goal_no in self._pitch_got:
            return
        _plog(f"MISSED goal #{goal_no}: the score feed counted it, the goal feed never delivered it")
        await self.alerter.send(
            f"⚠️ goal feed MISSED goal #{goal_no} (the score feed counted it). No bet was placed on it.", urgent=True)

    async def _check_confirm(self, slow: dict, goal_no: int, gid: str):
        """A pitch goal the score feed has still not confirmed after CONFIRM_SECS: warn and take it back."""
        if slow is not self._slow:
            return
        rec = self.bet365.get_match(slow["fi"])
        tot = (rec["home_score"] + rec["away_score"]) if rec else 0
        if tot >= goal_no or self._goals != goal_no:
            return
        self._goals = tot
        if rec:
            self._score = [rec["home_score"], rec["away_score"]]
        self._seen_ids.discard(gid)
        self._pitch_got.discard(goal_no)
        self._pitch_goal_at.pop(goal_no, None)
        self._next_goal_no = tot + 1
        self._rearm_task = asyncio.create_task(self._rearm(quiet=True))
        _plog(f"UNCONFIRMED goal #{goal_no} ({gid}): score feed still at {tot} after {Config.CONFIRM_SECS:g}s")
        await self.alerter.send(
            f"⚠️ pitch goal #{goal_no} NOT confirmed by the score feed after {Config.CONFIRM_SECS:g}s "
            f"(score feed total {tot}). Goal count set back. If a bet was placed, check it in SportyBet.", urgent=True)

    def _remember_bets(self, slow: dict, results: list):
        """Keeps the order id of every accepted bet (and its market) so that bet can be cashed out later."""
        for r in results:
            if not isinstance(r, dict) or r.get("bizCode") != 10000:
                continue
            sent = (r.get("_sent") or {}).get("selection") or {}
            parts = str(sent.get("id", "")).split("/")
            spec = str(sent.get("specifier") or "")
            mg = re.search(r"goalnr=(\d+)", spec)
            self._bets.append({"order_id": str((r.get("data") or {}).get("orderId") or ""),
                               "event_id": slow["event_id"],
                               "market_id": parts[-2] if len(parts) >= 2 else "",
                               "specifier": spec,
                               "goal_no": int(mg.group(1)) if mg else None,
                               "bet_id": "", "stake": float(r.get("_stake") or 0)})

    async def _refresh_balance_once(self):
        v = await asyncio.get_running_loop().run_in_executor(self._bg_pool, self.sb.get_balance)
        if v is not None and not self._processing:
            self.balance = v

    async def _balance_loop(self):
        """Reads the real SportyBet balance in the background, so a bet never waits for it."""
        try:
            while self._slow:
                if not self._processing:
                    await self._refresh_balance_once()
                await asyncio.sleep(Config.BALANCE_POLL)
        except asyncio.CancelledError:
            pass

    async def _cashout_when_open(self, bets: List[dict]):
        """Cashes out THESE bets (found by their order id), each only when the market it was placed on
        is open again on SportyBet. Polls the SportyBet API until then (or CASHOUT_MAX_SECS)."""
        loop = asyncio.get_running_loop()
        total = len(bets)
        end = time.time() + Config.CASHOUT_MAX_SECS
        pending, claimed, done, why = list(bets), set(), 0, ""
        try:
            while pending and time.time() < end and self._slow:
                await asyncio.sleep(Config.CASHOUT_POLL)
                for b in list(pending):
                    try:
                        data = await asyncio.wait_for(
                            loop.run_in_executor(self._bg_pool, self.sb.fetch_event, b["event_id"]),
                            timeout=Config.API_TIMEOUT)
                    except Exception:
                        continue
                    if not data or not self.sb.market_open(data, b):
                        continue
                    res = await loop.run_in_executor(self._bg_pool, self.sb.cashout_one, b, claimed)
                    if res.get("ok"):
                        pending.remove(b)
                        done += 1
                        if b in self._bets:
                            self._bets.remove(b)
                        await self.alerter.send(f"💰 cashed out bet {b.get('bet_id')} for ₦{res.get('amount', 0):,.2f}", urgent=True)
                    else:
                        why = res.get("why", "")
        except asyncio.CancelledError:
            pass
        self._has_open_bet = bool(self._bets)
        self._sync()
        await self.alerter.send(
            f"CASHOUT done={done}/{total}" + (f"\nnot cashed out: {html.escape(why)}" if pending else ""), urgent=True)
        asyncio.create_task(self._refresh_balance_once())

    async def _auto_clear(self):
        """Full time: the locked game clears itself."""
        await asyncio.sleep(2.0)
        if self._slow:
            await self.clear_slow()
            await self.alerter.send("🏁 Full time - the locked game was cleared automatically. Send /slow for the next one.")

    def _ft_guess(self, since: Optional[float], secs: float) -> bool:
        """Full time without a clear FT answer: the last known match clock is 85+ min, the API has been silent (or has had
        no open next-goal market) for `secs` seconds, and no bet is waiting to be cashed out."""
        if since is None or time.time() - since < secs or self._bets:
            return False
        return self._clock is not None and self._clock[0] >= 85.0

    async def _ft_clear(self, slow: dict, why: str, data: Any = None):
        fields = _api_fields(data) if data else "no data"
        _plog(f"FULL TIME assumed ({why}); API fields: {fields[:600]}")
        await self.alerter.send(
            f"⏸ <b>FULL TIME</b> (assumed: {html.escape(why)}) — {html.escape(slow['teams'] or '?')}\n"
            f"Clearing this game automatically.\nAPI fields (send these to me so the exact full-time field can be added):\n"
            f"<code>{html.escape(fields[:700])}</code>")
        asyncio.ensure_future(self._auto_clear())


# =====================================================================
# PROCESS: terminal login -> background daemon -> supervisor -> worker (the bot)
# =====================================================================
def _first_run_setup():
    if Config.TELEGRAM_BOT_TOKEN:
        return
    print("First run: Telegram setup (saved to ~/.betbot_config.json, readable only by you)",
          flush=True)
    tok = getpass.getpass("Telegram bot token: ").strip()
    chat = input(f"Telegram chat id [{Config.TELEGRAM_CHAT_ID}]: ").strip() or Config.TELEGRAM_CHAT_ID
    if not tok:
        sys.exit("No Telegram token.")
    Config.TELEGRAM_BOT_TOKEN, Config.TELEGRAM_CHAT_ID = tok, chat
    CONFIG_FILE.write_text(json.dumps({"token": tok, "chat_id": chat}))
    os.chmod(CONFIG_FILE, 0o600)


def _terminal_login() -> dict:
    """Plain blocking prompts BEFORE anything async or networked, so they always show at once."""
    print("SPORTYBET LOGIN (memory only)", flush=True)
    print(f"Hard cap: ₦{Config.MAX_PROFIT_PER_BET:,.0f}", flush=True)
    sb = SportyBetClient()
    try:
        while True:
            phone = input("Phone: ").strip()
            password = getpass.getpass("Password: ").strip()
            print("Logging in…", flush=True)
            try:
                ok = sb.login(phone, password)
            except Exception as e:
                print(f"Login error: {type(e).__name__}: {e}", flush=True)
                ok = False
            if ok:
                break
            print("Login failed — try again.\n", flush=True)
        while True:
            try:
                bal = float(input("Balance (NGN): ").strip().replace(",", "") or "0")
                break
            except ValueError:
                print("Enter a number.", flush=True)
    except EOFError:
        print("No terminal input — log in over Telegram with /login PHONE PASS", flush=True)
        return {}
    return {"phone": phone, "password": password, "balance": bal}


def _read_pid() -> Optional[int]:
    try:
        return int(PID_FILE.read_text().strip())
    except Exception:
        return None


def _is_bot_pid(pid: Optional[int]) -> bool:
    if not pid:
        return False
    try:
        os.kill(pid, 0)
        cmd = Path(f"/proc/{pid}/cmdline").read_bytes().decode("utf-8", "ignore")
        return Path(__file__).name in cmd
    except Exception:
        return False


def _kill_stale_chrome():
    try:
        subprocess.run(["pkill", "-f", "user-data-dir=/tmp/b365-chrome-"], timeout=5)
    except Exception:
        pass


def _stop_running():
    pid = _read_pid()
    if not _is_bot_pid(pid):
        print("Bot is not running.")
        PID_FILE.unlink(missing_ok=True)
        return
    try:
        pgid = os.getpgid(pid)
        os.killpg(pgid, signal.SIGTERM)
        for _ in range(40):
            if not _is_bot_pid(pid):
                break
            time.sleep(0.25)
        if _is_bot_pid(pid):
            os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    _kill_stale_chrome()
    PID_FILE.unlink(missing_ok=True)
    print("Bot stopped.")


def _daemonize():
    """Classic double-fork: the bot no longer belongs to the terminal, so closing the
    SSH window (or tmux, or the phone app) cannot kill it. All output goes to the log."""
    sys.stdout.flush()
    sys.stderr.flush()
    if os.fork() > 0:
        os._exit(0)
    os.setsid()
    if os.fork() > 0:
        os._exit(0)
    devnull = os.open(os.devnull, os.O_RDWR)
    logfd = os.open(str(LOG_FILE), os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    os.dup2(devnull, 0)
    os.dup2(logfd, 1)
    os.dup2(logfd, 2)
    try:
        sys.stdout.reconfigure(line_buffering=True)
        sys.stderr.reconfigure(line_buffering=True)
    except Exception:
        pass
    logger.remove()
    logger.add(sys.stderr, level="INFO", colorize=False,
               format="{time:YYYY-MM-DD HH:mm:ss} | {level: <7} | {message}")


def _worker(tx, state: dict):
    """Runs in its own process. Any crash (even a hard kill) is handled by the supervisor."""
    try:
        signal.signal(signal.SIGHUP, signal.SIG_IGN)
    except Exception:
        pass
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))
    bot = ArbitrageBot()
    bot._pipe = tx
    code = 0
    try:
        asyncio.run(bot.run(state))
    except (KeyboardInterrupt, SystemExit):
        pass
    except BaseException:
        logger.exception("[WORKER] crashed")
        code = 1
    try:
        bot.bet365._kill()
    except Exception:
        pass
    sys.exit(code)


def _supervise(state: dict):
    """Restarts the worker whenever it dies, handing it the last known state."""
    ctx = multiprocessing.get_context("fork")
    flag = {"stop": False, "proc": None}

    def _term(*_):
        flag["stop"] = True
        p = flag["proc"]
        if p is not None and p.is_alive():
            p.terminate()

    signal.signal(signal.SIGTERM, _term)
    try:
        signal.signal(signal.SIGHUP, signal.SIG_IGN)
    except Exception:
        pass
    restarts, backoff = 0, 3.0
    while not flag["stop"]:
        rx, tx = ctx.Pipe(duplex=False)
        state["restarts"] = restarts
        p = ctx.Process(target=_worker, args=(tx, dict(state)))
        t0 = time.time()
        p.start()
        flag["proc"] = p
        tx.close()
        while p.is_alive():
            try:
                if rx.poll(1.0):
                    state.update(rx.recv())
            except (EOFError, OSError):
                time.sleep(0.5)
        try:
            while rx.poll(0):
                state.update(rx.recv())
        except (EOFError, OSError):
            pass
        p.join()
        rx.close()
        code = p.exitcode
        _kill_stale_chrome()
        if flag["stop"] or code == 0:
            logger.info(f"[SUP] worker stopped (code {code}) — supervisor exiting")
            break
        restarts += 1
        state["last_exit"] = code
        backoff = 3.0 if time.time() - t0 > 120 else min(backoff * 2, 60.0)
        logger.error(f"[SUP] worker died (code {code}) — restart #{restarts} in {backoff:.0f}s")
        time.sleep(backoff)


def main():
    print("== betbot ==", flush=True)
    cmd = sys.argv[1].lower() if len(sys.argv) > 1 else ""
    if cmd in ("stop", "kill"):
        _stop_running(); return
    if cmd == "status":
        pid = _read_pid()
        print(f"RUNNING (pid {pid}), log: {LOG_FILE}" if _is_bot_pid(pid) else "NOT running")
        return
    pid = _read_pid()
    if _is_bot_pid(pid):
        print(f"Already running (pid {pid}). Use:  python3 betbot.py stop   then start again.")
        return
    _first_run_setup()
    state = _terminal_login()
    try:
        if LOG_FILE.exists() and LOG_FILE.stat().st_size > 20_000_000:
            LOG_FILE.replace(LOG_FILE.with_suffix(".log.1"))
    except Exception:
        pass
    if cmd == "fg":
        try:
            signal.signal(signal.SIGHUP, signal.SIG_IGN)
        except Exception:
            pass
        PID_FILE.write_text(str(os.getpid()))
        try:
            _supervise(state)
        except KeyboardInterrupt:
            pass
        finally:
            PID_FILE.unlink(missing_ok=True)
        return
    print(f"Starting in the background. You can close this terminal now.\n"
          f"Telegram will confirm.  Logs: {LOG_FILE}   Stop: python3 betbot.py stop", flush=True)
    _daemonize()
    PID_FILE.write_text(str(os.getpid()))
    try:
        _supervise(state)
    finally:
        PID_FILE.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
