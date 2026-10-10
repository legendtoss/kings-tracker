#!/usr/bin/env python3
"""
King's Resort Rozvadov - cash game tracker
==========================================
Runs on GitHub Actions about every 10 minutes. Each run:
  1. reads the running cash tables from King's own data feed (the one their live page uses);
     if that ever fails, it opens the live page in a headless browser and reads it like a visitor,
  2. also reads King's tournament clocks, to see how many tournament players are in action,
  3. adds one line to data/YYYY-MM.csv (Czech local time),
  4. rebuilds README.md with statistics per game and a cash-vs-tournament comparison,
  5. also reads Card Casino Šamorín's live list (data/cardcasino/ + CARD_CASINO.md), Grand Casino
     Aš's cash games and tournaments (data/grandcasinoas/ + GRAND_CASINO_AS.md) and Banco Casino
     Bratislava's website (data/banco/ + BANCO.md). Those are kept fully separate, so a problem
     with their websites can never affect the King's data.

Games are named the way the poker room's own system names them (NLH, PLO5, ...), so different
games are never mixed together. If checks keep failing, the run reports an error and GitHub
emails you (after about an hour, then once a day). Nothing here needs editing.
"""

import csv
import gzip
import json
import os
import re
import subprocess
import sys
import time
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from functools import lru_cache
from html import unescape
from datetime import datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

# ---------------------------------------------------------------- settings

PAGE_URL = os.environ.get("KINGS_URL", "https://kings-resort.com/poker/live")
FEED_URL = os.environ.get("KINGS_FEED_URL", "https://admin.kings-resort.com/zeus/?data=cash_games_by_venue")
CLOCKS_URL = os.environ.get("KINGS_CLOCKS_URL", "https://admin.kings-resort.com/zeus/?data=poker_clocks&venue=1")
VENUE = "1"                     # Rozvadov's number in the feed (Prague has another one)
TZ = ZoneInfo("Europe/Prague")  # Rozvadov time = Warsaw time
ALERT_AFTER = 6                 # failed checks in a row before GitHub emails you (about 1 hour)

DATA_DIR = Path("data")
SITE_FIELDS = ["time", "weekday", "hour", "status", "cash_text", "tournament_text"]
# Slovak rooms read from their web pages: (folder name, display name, page address, results page)
# Slovak rooms read from their websites with a browser. "reader" says where the list is on the page.
SITES = (
    {"key": "banco", "name": "Banco Casino Bratislava", "url": os.environ.get("BANCO_URL", "https://bancocasino.sk/ba/en"),
     "page": Path("BANCO.md"), "age_button": "Confirm", "reader": "banco-popup"},
)
# Card Casino Šamorín: its page loads the live list from a small file, which is read directly.
# The page itself (in a browser) is only the backup if that ever fails.
CARD_SITE = {"key": "cardcasino", "name": "Card Casino Šamorín",
             "url": os.environ.get("CARD_URL", "https://www.cardcasino.sk/en/cashgames/"),
             "page": Path("CARD_CASINO.md"), "age_button": "I am over 18 years old", "reader": "section"}
CARD_FEED_URL = os.environ.get("CARD_FEED_URL", "https://www.cardcasino.sk/ajax/cashgames.php?lang=EN")
CARD_DIR = DATA_DIR / "cardcasino"
CARD_FIELDS = ["time", "weekday", "hour", "status", "source", "tables", "players", "games", "raw"]
CARD_SOURCES = {"feed": "live list", "page table": "page, via browser"}
# Grand Casino Aš: both pages are plain HTML. The tournament page is big (full schedule), so it's
# read every 30 minutes rather than every 10, to go easy on their website.
GAS_CASH_URL = os.environ.get("GAS_CASH_URL", "https://www.grandcasinoas.eu/en/poker/poker-live")
GAS_TOURNEY_URL = os.environ.get("GAS_TOURNEY_URL", "https://www.grandcasinoas.eu/en/poker")
GAS_DIR = DATA_DIR / "grandcasinoas"
GAS_FIELDS = ["time", "weekday", "hour", "status", "tables", "waiting", "games",
              "tourneys", "tourney_players", "tourney_details", "raw"]
GAS_PAGE = Path("GRAND_CASINO_AS.md")
RETIRED_SITES = (("samorin", Path("SAMORIN.md")),)  # an earlier attempt via Banco's site, which had no live data
# Tracking/advertising services skipped during browser visits. Exact domains on purpose: matching
# just "google" would also block Google's code-library servers, which many sites need to work.
TRACKER_DOMAINS = ("google-analytics.com", "googletagmanager.com", "doubleclick.net", "googleadservices.com",
                   "googlesyndication.com", "facebook.net", "facebook.com", "hotjar.com", "clarity.ms",
                   "bing.com", "tiktok.com", "instagram.com", "youtube.com", "ytimg.com", "twitch.tv", "smartlook.com")


def is_tracker(host):
    host = (host or "").lower()
    return any(host == domain or host.endswith("." + domain) for domain in TRACKER_DOMAINS)
README = Path("README.md")
PROBLEM_FILE = Path("debug/last_problem.json")
OLD_DEBUG_FILE = Path("debug/last_page.json")  # written by earlier versions

FIELDS = ["time", "weekday", "hour", "status", "source", "tables", "players", "games",
          "tourneys", "tourney_players", "tourney_list", "tourney_details", "page_text"]
DAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/141.0.0.0 Safari/537.36")
GAME_NAMES = {"NLH": "No-Limit Hold'em (NLH)", "PLO": "Pot-Limit Omaha (PLO)",
              "PLO5": "5-card Pot-Limit Omaha (PLO5)", "PLO6": "6-card Pot-Limit Omaha (PLO6)"}
SOURCES = {"feed": "data feed", "browser feed": "data feed, via browser", "page table": "page table, via browser"}


# ---------------------------------------------------------------- understanding the data
# Every table is stored as an "entry" like  NLH €2/4 7/8  (game, stakes, seated/seats),
# sometimes followed by the room's status, e.g. [WAITING]. One check = entries joined by "; ".

ENTRY_RE = re.compile(r"^(.+?) €([\d/.]+) (\d+)/(\d+)(?: \[[A-Z_]+\])?$")
UNSAFE = re.compile(r"[^\w\s'’()+\-/.,:&]")
STAKES_IN_NAME = re.compile(r"\d+(?:[.,]\d+)?(?:\s*[-/]\s*\d+(?:[.,]\d+)?)+")


def clean(text, limit=40):
    """Plain text that can't break the CSV or the README tables (no | ; [ ] < > ` * #)."""
    return " ".join(UNSAFE.sub(" ", str(text or "")).split())[:limit]


def shown(text, limit=80):
    """Like clean(), but keeps € signs - for text that is only displayed, never parsed."""
    return " ".join(re.sub(r"[^\w\s'’()+\-/.,:&€]", " ", str(text or "")).split())[:limit]


def as_int(value):
    try:
        return max(0, int(float(value)))
    except (TypeError, ValueError, OverflowError):
        return 0


def norm_game(name):
    """One spelling per game, also for data saved by older versions ('MIX NLH /PLO' -> 'MIX NLH/PLO')."""
    return re.sub(r"\s*/\s*", "/", name).strip()


def feed_game(t):
    """The room's own name for a game, minus the stakes:
    'NLH 2-4' -> 'NLH', 'PLO 5-5 5cards' -> 'PLO5', 'SD 25-50' -> 'SD (Short Deck)'."""
    name = STAKES_IN_NAME.sub(" ", str((t.get("gameProfile") or {}).get("name") or ""))
    name = re.sub(r"(?i)\bPLO\s*(\d)[\s-]*cards?\b",
                  lambda m: "PLO" + ("" if m.group(1) == "4" else m.group(1)), name)
    name = norm_game(clean(name))
    gtype = clean((t.get("gameType") or {}).get("name"))
    if name and len(name) <= 4 and name not in GAME_NAMES and gtype and gtype.lower() not in name.lower():
        name = clean(f"{name} ({gtype})")  # spell out short codes
    return name or gtype or "Game"


def feed_stakes(t):
    prof = t.get("gameProfile") or {}
    m = re.search(r"\d+(?:[.,]\d+)?(?:\s*/\s*\d+(?:[.,]\d+)?)+", str(prof.get("blindsFormatted") or ""))
    if m:
        return re.sub(r"\s+", "", m.group(0)).replace(",", ".")
    params = prof.get("params") or {}
    sb, bb = params.get("smallBlind"), params.get("bigBlind")
    if isinstance(sb, (int, float)) and isinstance(bb, (int, float)):
        return f"{sb:g}/{bb:g}"
    return ""


def feed_entries(data):
    """Entries for Rozvadov's tables in the feed, or None if the feed doesn't look right."""
    if not isinstance(data, list):
        return None
    entries = []
    for t in data:
        if not isinstance(t, dict) or str(t.get("venue")) != VENUE:
            continue
        stakes = feed_stakes(t)
        if not stakes:
            continue
        entry = f"{feed_game(t)} €{stakes} {as_int(t.get('playerCount'))}/{as_int(t.get('seatCount'))}"
        status = re.sub(r"[^A-Z_]", "", str(t.get("status") or "").upper())
        entries.append(entry + (f" [{status}]" if status and status != "PLAYING" else ""))
    return entries


@lru_cache(maxsize=None)
def parse_games(games):
    """'NLH €2/4 8/8; PLO5 €5/5 7/8' -> (('NLH', '2/4', 8, 8), ('PLO5', '5/5', 7, 8))"""
    tables = []
    for entry in (games or "").split("; "):
        m = ENTRY_RE.match(entry.strip())
        if m:
            tables.append((norm_game(m.group(1)), m.group(2), int(m.group(3)), int(m.group(4))))
    return tuple(tables)


# Tournaments in play are stored like  Daily Deepstack 40/62  (players still in / entries),
# sometimes followed by the clock's status, e.g. [PAUSED].
TOURNEY_RE = re.compile(r"^(.+?) (\d+)/(\d+)(?: \[[A-Z_]+\])?$")
FINISHED = {"FINISHED", "ENDED", "CLOSED", "CANCELLED", "CANCELED", "COMPLETED"}
LONG_PAUSE = timedelta(hours=2)  # a clock paused longer than this has stopped for the day


def local_time(value):
    try:
        return datetime.fromisoformat(str(value)).replace(tzinfo=None)
    except ValueError:
        return None


def paused_since(t):
    """When the clock's current pause began (the earliest of nested pauses), or None."""
    since, pause = None, t.get("activePause")
    for _ in range(10):
        if not isinstance(pause, dict):
            break
        start = local_time(pause.get("sinceTime"))
        if start and (since is None or start < since):
            since = start
        pause = pause.get("previousPause")
    return since


def number(value):
    try:
        x = float(value)
    except (TypeError, ValueError):
        return None
    return int(x) if x == int(x) else round(x, 2)


def tourney_details(t, name, game, status, active):
    """Everything useful King's clock shows about one tournament, as a small dictionary."""
    level = t.get("currentLevel") or {}
    sb, bb, ante = number(level.get("sb")), number(level.get("bb")), number(level.get("ante"))
    details = {"name": name, "game": game, "status": status or "RUNNING", "left": active,
               "entries": as_int(t.get("totalEntries")), "buyin": number(t.get("entryValue")),
               "fee": number(t.get("serviceFee")), "bounty": number(t.get("bountyValue")),
               "prizepool": number(t.get("effectivePrizePool")), "currency": clean(t.get("currency"), 5),
               "level": number(level.get("number")),
               "blinds": f"{sb}/{bb}" + (f"/{ante}" if ante else "") if sb is not None and bb is not None else None,
               "avg_stack": number(t.get("averageStack")), "start_stack": number(t.get("startingStack")),
               "late_reg_open": bool(t.get("openRegistration")), "late_reg_until_level": number(t.get("lateRegistrationUntilLevel")),
               "reentries": number(t.get("reEntryMaxCount")), "start": str(t.get("start") or "")[:16]}
    return {k: v for k, v in details.items() if v not in (None, "")}


def tournament_entries(data, now, with_details=False):
    """Tournaments in play right now (started, not finished, players still in), or None if
    the clock feed doesn't look right. Scheduled-but-not-started ones are left out.
    with_details=True returns (entries, details) instead."""
    if not isinstance(data, list):
        return None
    local_now = now.replace(tzinfo=None)
    entries, all_details = [], []
    for t in data:
        if not isinstance(t, dict):
            continue
        status = re.sub(r"[^A-Z_]", "", str(t.get("status") or "").upper())
        active = as_int(t.get("activePlayers"))
        start = local_time(t.get("start"))
        if status in FINISHED or active == 0 or (start and start > local_now):
            continue
        since = paused_since(t) if (status == "PAUSED" or t.get("isPaused")) else None
        if since and local_now - since > LONG_PAUSE:
            continue  # e.g. Day 1 finished and chips bagged: nobody is playing
        name = clean(t.get("fullName") or t.get("name") or "Tournament", 60)
        game = tourney_game(" ".join(str(t.get(k) or "") for k in ("fullName", "name", "tournamentName", "subName")))
        entries.append(f"{name} {active}/{as_int(t.get('totalEntries'))}"
                       + (f" [{status}]" if status and status != "RUNNING" else ""))
        all_details.append(tourney_details(t, name, game, status, active))
    return (entries, all_details) if with_details else entries


def tourney_game(name):
    """Which poker game a tournament is. King's data doesn't say it directly, so it's read from the
    tournament's names: King's puts PLO/Omaha, Mix, Short Deck, Pineapple etc. in the title of every
    non-Hold'em event, and everything else is No-Limit Hold'em."""
    n = " ".join(name.lower().replace("’", "'").split())
    if re.search(r"\bmix(ed)?\b|dealer'?s choice|h\.?o\.?r\.?s\.?e|\b8[- ]?game|\bstud\b|\brazz\b|badugi|triple draw", n):
        return "Mixed"
    if "pineapple" in n:
        return "Pineapple"
    if re.search(r"short ?deck|\b6\+|six plus", n):
        return "Short Deck"
    if re.search(r"\bbig o\b", n):
        return "PLO5 Hi-Lo"
    if re.search(r"\bplo\d?\b|omaha", n):
        if re.search(r"hi[ -/]?lo|8 or better|\bo8\b|\bplo8\b", n):
            return "PLO Hi-Lo"
        cards = re.search(r"\bplo\s*([56])\b|\b([56])[ -]?cards?\b", n)
        return "PLO" + (cards.group(1) or cards.group(2) if cards else "")
    return "NLH"


def tourney_family(game):
    return "PLO" if game.startswith("PLO") else "NLH" if game == "NLH" else "Other"


def family(game):
    """Cash game family: NLH, PLO (any Omaha) or Other."""
    return "NLH" if game.startswith("NLH") else "PLO" if game.startswith("PLO") else "Other"


@lru_cache(maxsize=None)
def parse_tourneys(text):
    """'Daily Deepstack 40/62; Day 1 84/565 [PAUSED]' -> (('Daily Deepstack', 40, 62), ('Day 1', 84, 565))"""
    found = []
    for entry in (text or "").split("; "):
        m = TOURNEY_RE.match(entry.strip())
        if m:
            found.append((m.group(1), int(m.group(2)), int(m.group(3))))
    return tuple(found)


# The page's own table, used only when the feed can't be read:
#   NO LIMIT TEXAS HOLD'EM | € 2/4 | 7/8 PLAYERS
BOX_START = "running cash games in rozvadov"
BOX_ENDS = ("running cash games in", "cash game action", "twitch", "youtube")
TABLE_RE = re.compile(r"([^|]*?)\s*\|\s*€\s*([\d/.,]+)\s*\|\s*(\d+)\s*/\s*(\d+)\s*players?", re.I)
EMPTY_BOX = re.compile(r"waiting for more players|no (?:cash )?games", re.I)


def cut_box(text):
    """Text between 'Running Cash Games in Rozvadov' and the next section, lines joined by ' | '."""
    low = text.lower()
    a = low.find(BOX_START)
    if a < 0:
        return None
    a += len(BOX_START)
    end = min([i for i in (low.find(k, a) for k in BOX_ENDS) if i != -1] + [a + 4000])
    lines = (ln.strip() for ln in re.split(r"[\n\t]+", text[a:end]))
    return " | ".join(ln for ln in lines if ln)


def short_game(name):
    """Page names: 'NLH' / 'PLO5' for the two standard games; any other game keeps its own name."""
    words = clean(name)
    n = words.lower().replace("’", "'").replace("-", " ")
    if re.fullmatch(r"no limit (texas )?hold'?em", n):
        return "NLH"
    m = re.fullmatch(r"pot limit omaha(?: (\d) cards?)?", n)
    if m:
        return "PLO" + ("" if m.group(1) in (None, "4") else m.group(1))
    return " ".join(w[:1].upper() + w[1:] for w in words.lower().split()) or "Game"


def box_entries(box):
    """Entries from the page's table: [] if it says nothing is running, None if unreadable."""
    rows = TABLE_RE.findall(box or "")
    if rows:
        return [f"{short_game(g)} €{s.replace(',', '.')} {a}/{b}" for g, s, a, b in rows]
    return [] if not box or EMPTY_BOX.search(box) else None


def strip_tags(fragment):
    return " ".join(unescape(re.sub(r"<[^>]+>", " ", fragment or "")).split())


def card_game(name):
    """Card Casino's game names: 'NLH', 'PLO', 'PLO5'... anything else keeps its own name."""
    n = clean(name).upper().replace(" ", "")
    if n in ("NLH", "NL", "NLHE"):
        return "NLH"
    m = re.fullmatch(r"PLO(\d)?", n)
    if m:
        return "PLO" + ("" if m.group(1) in (None, "4") else m.group(1))
    return norm_game(clean(name)) or "Game"


CARD_STAKES_RE = re.compile(r"\d+(?:[.,]\d+)?(?:\s*/\s*\d+(?:[.,]\d+)?)+")


def card_entry(cells):
    """['NLH', '1/3 €', '8/8'] -> 'NLH €1/3 8/8', or None if the cells don't look like that."""
    if len(cells) < 3:
        return None
    stakes = CARD_STAKES_RE.fullmatch(cells[1].replace("€", "").strip())
    seats = re.fullmatch(r"(\d+)\s*/\s*(\d+)", cells[2].strip())
    if not stakes or not seats or not re.search(r"[A-Za-z]", cells[0]):
        return None
    return f"{card_game(cells[0])} €{re.sub(r'\s+', '', stakes.group(0)).replace(',', '.')} {seats.group(1)}/{seats.group(2)}"


CARD_BLOCK_RE = re.compile(r'<div[^>]*class="[^"]*\bcash-game\b[^"]*"[^>]*>(.*?)</div>', re.S | re.I)
H4_RE = re.compile(r"<h4[^>]*>(.*?)</h4>", re.S | re.I)


def card_entries(fragment):
    """Entries from Card Casino's live list (a small piece of HTML): one per table.
    [] if nothing is running, None if the list doesn't look the way it should."""
    blocks = CARD_BLOCK_RE.findall(fragment or "")
    if not blocks:
        return [] if len(strip_tags(fragment)) < 200 else None
    entries = [card_entry([strip_tags(c) for c in H4_RE.findall(block)]) for block in blocks]
    return None if None in entries else entries


def card_text_entries(text):
    """The same list read from the page's text ('NLH | 1/3 € | 8/8 | PLO | ...')."""
    tokens = [t.strip() for t in (text or "").split(" | ") if t.strip()]
    entries, i = [], 0
    while i + 2 < len(tokens):
        entry = card_entry(tokens[i:i + 3])
        if entry:
            entries.append(entry)
            i += 3
        else:
            i += 1
    return entries


# Grand Casino Aš cash games: a table of Game | Blinds | Buy-in | Status (Running / Waiting).
# Saved per table as an entry like  NLH €1/2 [RUNNING]  (no player counts: the site doesn't show them).
GAS_ENTRY_RE = re.compile(r"^(.+?)(?: €([\d/.]+))? \[([A-Z_]+)\]$")
GAS_BLINDS_RE = re.compile(r"(\d+(?:[.,]\d+)?)\s*€?\s*[-–/]\s*(\d+(?:[.,]\d+)?)(?:\s*€?\s*[-–/]\s*(\d+(?:[.,]\d+)?))?")


def gas_cash_entries(html):
    """Entries from Grand Casino Aš's 'Current cash game' table; None if the table isn't there."""
    start = (html or "").lower().find("current cash game")
    if start < 0:
        return None
    end = html.lower().find("</table>", start)
    if end < 0:
        return None
    entries = []
    for row in re.findall(r"<tr[^>]*>(.*?)</tr>", html[start:end], re.S | re.I):
        cells = [strip_tags(c) for c in re.findall(r"<t[dh][^>]*>(.*?)</t[dh]>", row, re.S | re.I)]
        if len(cells) < 4 or cells[0].lower() == "game":
            continue
        blinds = GAS_BLINDS_RE.search(cells[1])
        stakes = "/".join(x.replace(",", ".") for x in blinds.groups() if x) if blinds else ""
        status = re.sub(r"[^A-Z_]", "", cells[3].upper().replace(" ", "_")) or "UNKNOWN"
        entries.append(f"{card_game(cells[0])}" + (f" €{stakes}" if stakes else "") + f" [{status}]")
    return entries


def parse_gas_games(games):
    """'NLH €1/2 [RUNNING]; PLO/NLH [WAITING]' -> [('NLH', '1/2', 'RUNNING'), ('PLO/NLH', '', 'WAITING')]"""
    found = []
    for entry in (games or "").split("; "):
        m = GAS_ENTRY_RE.match(entry.strip())
        if m:
            found.append((norm_game(m.group(1)), m.group(2) or "", m.group(3)))
    return found


GAS_TOURNEY_RE = re.compile(
    r"Start\s+(?P<date>\d{1,2}\.\d{1,2}\.)\s+(?P<time>\d{1,2}:\d{2})\s+\S+\s+"
    r"(?:LVL\s+(?P<level>\d+)\s+Level\s+(?P<blinds>\d+(?:/\d+)+)|Countdown\s+Level\s+Countdown)\s+"
    r"(?P<buyin>[\d ]+?)\s*€\s*Buy-In\s+(?P<late>\S+)\s+Late Reg\.\s+(?P<sstack>[\d ]+?)\s+Starting Stack\s+"
    r"(?P<avg>[\d ]+?)\s+Average Stack\s+(?P<left>\d+)\s*\((?P<entries>\d+)\)\s*Players\s+"
    r"(?:€\s*(?P<pool>[\d ]+?)|-)\s*Prizepool", re.I)


def gas_tournaments(html, now):
    """Tournaments in play in Grand Casino Aš's 'Current Tournaments' box: (entries, details),
    or None if the box isn't there."""
    text = strip_tags(html).replace("\xa0", " ")
    low = text.lower()
    a = low.find("current tournaments")
    if a < 0:
        return None
    b = low.find("all tournaments", a)
    section = text[a + len("current tournaments"): b if b > 0 else a + 20000]
    entries, details = [], []
    for block in re.split(r"Next level\s+\d+(?:/\d+)+", section):
        m = GAS_TOURNEY_RE.search(block)
        if not m or not m.group("level"):
            continue  # not started yet (still counting down)
        left = as_int(m.group("left"))
        if not left:
            continue
        name = clean(block[:m.start()], 60) or "Tournament"
        late = m.group("late")
        d = {"name": name, "game": tourney_game(name), "status": "RUNNING", "left": left,
             "entries": as_int(m.group("entries")), "buyin": number(m.group("buyin").replace(" ", "")),
             "prizepool": number((m.group("pool") or "").replace(" ", "")), "currency": "EUR",
             "level": number(m.group("level")), "blinds": m.group("blinds"),
             "avg_stack": number(m.group("avg").replace(" ", "")), "start_stack": number(m.group("sstack").replace(" ", "")),
             "late_reg_open": late.lower() != "closed", "start": f"{m.group('date')} {m.group('time')}"}
        details.append({k: v for k, v in d.items() if v not in (None, "")})
        entries.append(f"{name} {left}/{as_int(m.group('entries'))}")
    return entries, details


# ---------------------------------------------------------------- reading King's

def fetch_feed(url=None):
    """King's own data (cash games by default): the small JSON files their live page loads."""
    request = urllib.request.Request(url or FEED_URL, headers={
        "User-Agent": UA, "Accept": "application/json, text/plain, */*",
        "Origin": "https://kings-resort.com", "Referer": "https://kings-resort.com/"})
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.loads(response.read().decode("utf-8"))


def fetch_text(url, referer):
    """A small piece of a casino's web page, fetched the way their page itself fetches it."""
    request = urllib.request.Request(url, headers={
        "User-Agent": UA, "Accept": "text/html, */*; q=0.01", "X-Requested-With": "XMLHttpRequest",
        "Referer": referer, "Accept-Encoding": "gzip"})
    with urllib.request.urlopen(request, timeout=30) as response:
        data = response.read()
        if response.headers.get("Content-Encoding", "").lower() == "gzip":
            data = gzip.decompress(data)
        return data.decode("utf-8", errors="replace")


BOX_READY_JS = """() => {
  const t = (document.body ? document.body.innerText : '').toLowerCase();
  const a = t.indexOf('%s');
  if (a < 0) return false;
  const box = t.slice(a + %d, a + 4000).split('running cash games in')[0];
  return !box.includes('loading');
}""" % (BOX_START, len(BOX_START))

BOX_HTML_JS = r"""() => {
  const re = /running cash games in rozvadov/i;
  const head = Array.from(document.querySelectorAll('body *')).find(
    e => re.test(e.textContent || '') && !Array.from(e.children).some(c => re.test(c.textContent || '')));
  if (!head) return null;
  let box = head;
  for (let i = 0; i < 4 && box.parentElement; i++) {
    if (/running cash games in prague/i.test(box.parentElement.textContent || '')) break;
    box = box.parentElement;
  }
  return box.outerHTML.slice(0, 60000);
}"""


def load_playwright():
    """The browser tools, installed only when they're actually needed."""
    try:
        from playwright.sync_api import sync_playwright, TimeoutError as PWTimeout
    except ImportError:
        subprocess.run([sys.executable, "-m", "pip", "install", "-q", "playwright"], check=True)
        from playwright.sync_api import sync_playwright, TimeoutError as PWTimeout
    return sync_playwright, PWTimeout


def open_browser(p):
    try:
        return p.chromium.launch(channel="chrome")  # GitHub's machines already have Chrome
    except Exception:
        subprocess.run([sys.executable, "-m", "playwright", "install", "--with-deps", "chromium"], check=True)
        return p.chromium.launch()


def skip_extras(page):
    """Don't load pictures, fonts, videos or tracking scripts: faster, and our checks
    don't show up as visits in the casinos' website statistics."""
    def handle(route):
        request = route.request
        host = urllib.parse.urlparse(request.url).hostname or ""
        if request.resource_type in ("image", "media", "font") or is_tracker(host):
            return route.abort()
        return route.continue_()
    page.route("**/*", handle)


def browser_check():
    """Open the live page like a visitor (slow, so only used when the feed fails).
    Returns (entries or None, source, box text, details for debugging)."""
    sync_playwright, PWTimeout = load_playwright()

    responses = []

    def remember_feed(response):
        if "cash_games" in response.url and len(responses) < 5:
            responses.append(response)

    with sync_playwright() as p:
        browser = open_browser(p)
        page = browser.new_page(user_agent=UA, locale="en-US", viewport={"width": 1366, "height": 900})
        skip_extras(page)
        page.on("response", remember_feed)
        for attempt in (1, 2):
            try:
                page.goto(PAGE_URL, wait_until="domcontentloaded", timeout=60_000)
                break
            except Exception:
                if attempt == 2:
                    raise
                page.wait_for_timeout(10_000)
        loaded = True
        try:
            page.wait_for_function(BOX_READY_JS, timeout=45_000, polling=1000)
        except PWTimeout:
            loaded = False
        page.wait_for_timeout(1_500)
        text = page.inner_text("body")
        box_html = page.evaluate(BOX_HTML_JS)
        bodies = []
        for response in responses:
            try:
                bodies.append(response.text())
            except Exception:
                pass
        browser.close()

    box = cut_box(text)
    details = {"page_text_start": text[:4000], "box_html": box_html,
               "feed_seen_by_page": [b[:20000] for b in bodies]}
    for body in reversed(bodies):  # the feed as the page received it, newest first
        try:
            entries = feed_entries(json.loads(body))
        except ValueError:
            continue
        if entries:
            return entries, "browser feed", box, details
    if box is None or not loaded:
        return None, "page table", box, details
    return box_entries(box), "page table", box, details


def page_section(text, start, ends, limit=3000):
    """Text of one section of a page (from a heading to the next one), lines joined by ' | '."""
    low = text.lower()
    a = low.find(start)
    if a < 0:
        return None
    a += len(start)
    end = min([i for i in (low.find(k, a) for k in ends) if i != -1] + [a + limit])
    lines = (ln.strip() for ln in re.split(r"[\n\t]+", text[a:end]))
    return " | ".join(ln for ln in lines if ln)


SECTION_HTML_JS = r"""(title) => {
  const head = Array.from(document.querySelectorAll('h1,h2,h3,h4,h5'))
    .find(e => (e.textContent || '').trim().toLowerCase() === title);
  const box = head && (head.closest('section') || head.parentElement);
  return box ? box.outerHTML.slice(0, 20000) : null;
}"""

# Banco's cash-game list lives in a pop-up window ("Cash games") that is hidden until opened.
# This reads it either way: every table row as a list of cells, plus the plain text and HTML.
CASH_POPUP_JS = r"""() => {
  const title = Array.from(document.querySelectorAll('.modal-title, h1, h2, h3, h4, h5'))
    .find(e => (e.textContent || '').trim().toLowerCase() === 'cash games');
  if (!title) return null;
  const box = title.closest('.modal') || title.closest('.modal-content') || title.parentElement.parentElement;
  const rows = Array.from(box.querySelectorAll('tr'))
    .map(tr => Array.from(tr.children).map(c => (c.textContent || '').replace(/\s+/g, ' ').trim()).filter(Boolean))
    .filter(cells => cells.length);
  const visible = box.offsetParent !== null;
  return {rows, visible, text: ((visible ? box.innerText : box.textContent) || '').slice(0, 5000),
          html: box.outerHTML.slice(0, 20000)};
}"""


def sites_check():
    """Open each Slovak room's page like a visitor and read its live 'Cash games' and 'Poker
    tournaments' boxes. Returns {folder: (cash text, tournament text, details) or an Exception}."""
    sync_playwright, PWTimeout = load_playwright()
    results = {}
    with sync_playwright() as p:
        browser = open_browser(p)
        for site in SITES:
            try:
                results[site["key"]] = read_site(browser, site, PWTimeout)
            except Exception as e:  # one site failing doesn't stop the others
                results[site["key"]] = e
        browser.close()
    return results


def browser_read(site):
    """Open one site in the browser (the backup route for Card Casino)."""
    sync_playwright, PWTimeout = load_playwright()
    with sync_playwright() as p:
        browser = open_browser(p)
        try:
            return read_site(browser, site, PWTimeout)
        finally:
            browser.close()


def read_site(browser, site, PWTimeout):
    responses = []

    def remember(response):
        host = urllib.parse.urlparse(response.url).hostname or ""
        if response.request.resource_type in ("xhr", "fetch") and len(responses) < 10 and not is_tracker(host):
            responses.append(response)

    page = browser.new_page(user_agent=UA, locale="en-US", viewport={"width": 1366, "height": 900})
    try:
        skip_extras(page)
        page.on("response", remember)
        page.goto(site["url"], wait_until="domcontentloaded", timeout=60_000)
        try:
            page.get_by_text(site["age_button"], exact=True).first.click(timeout=3_000)  # the 18+ notice
        except Exception:
            pass
        try:
            page.wait_for_load_state("networkidle", timeout=20_000)
        except PWTimeout:
            pass
        page.wait_for_timeout(2_000)
        popup = section_html = None
        if site["reader"] == "banco-popup":
            try:  # open the "Cash games" pop-up, in case its list is only loaded when opened
                page.get_by_text("Cash Game", exact=True).first.click(timeout=3_000)
                page.wait_for_load_state("networkidle", timeout=10_000)
            except Exception:
                pass
            page.wait_for_timeout(1_500)
            popup = page.evaluate(CASH_POPUP_JS)
        else:
            section_html = page.evaluate(SECTION_HTML_JS, "cash games")
        text = page.inner_text("body")
        bodies = []
        for response in responses:
            try:
                bodies.append({"url": response.url, "status": response.status, "body": response.text()[:10000]})
            except Exception:
                pass
    finally:
        page.close()

    details = {"page_text_start": text[:6000], "data_requests": bodies}
    if site["reader"] == "banco-popup":
        cash = popup_text(popup)
        clock = page_section(text, "cash game", ("cash games", "poker tournaments"), 1500) or ""  # tournament clock
        listed = page_section(text, "poker tournaments", ("banco promotions", "jackpot"), 1500) or ""
        tournaments = " || ".join(part for part in (clock, listed) if part)
        details["cash_popup"] = popup
    else:  # the list sits on the page under a "Cash games" heading
        cash = page_section(text, "cash games", ("current tournaments",), 3000)
        if cash is not None:  # drop the fixed "Game limits" link and rake note, keep the live list
            cash = " | ".join(part for part in cash.split(" | ")
                              if part.lower() != "game limits" and not part.lower().startswith("rake "))
        tournaments = ""
        details["cash_section_html"] = section_html
    return cash, tournaments, details


def popup_text(popup):
    """The cash-game list as text: table rows separated by ' | ', cells by ' ; '.
    None if the pop-up wasn't on the page at all."""
    if not popup:
        return None
    rows = [" ; ".join(cells) for cells in popup.get("rows") or []]
    if rows:
        return " | ".join(rows)
    lines = [" ".join(ln.split()) for ln in (popup.get("text") or "").splitlines()]
    return " | ".join(ln for ln in lines if ln and ln.lower() not in ("cash games", "close", "×", "x"))


def short_error(e):
    return clean(f"{type(e).__name__}: {(str(e).strip().splitlines() or [''])[0]}", 160)


def check():
    """Read the tables now. Returns (status, source, entries or None, page text, problem details)."""
    problem = {}
    for attempt in (1, 2):
        try:
            entries = feed_entries(fetch_feed())
        except Exception as e:
            problem["feed"] = short_error(e)
            time.sleep(5)
            continue
        if entries:
            return "ok", "feed", entries, "", None
        problem["feed"] = "no Rozvadov tables in the feed" if entries == [] else "the feed had an unexpected format"
        break  # an empty answer is double-checked on the page below
    try:
        entries, source, box, details = browser_check()
    except Exception as e:
        problem["browser"] = short_error(e)
        return f"error: {problem['browser']}", "", None, "", problem
    problem.update(details)
    if entries is None:
        return "error: couldn't read the tables on the page", source, None, box or "", problem
    return "ok", source, entries, (box or "") if source == "page table" else "", problem


def check_tournaments(now):
    """(tournaments in play or None, their details, error text). Tournament info is extra: if it
    can't be read, the cash check still counts and the tournament columns are just left empty."""
    error = ""
    for attempt in (1, 2):
        try:
            result = tournament_entries(fetch_feed(CLOCKS_URL), now, with_details=True)
        except Exception as e:
            error = short_error(e)
            time.sleep(3)
            continue
        if result is not None:
            return result[0], result[1], ""
        error = "the tournament feed had an unexpected format"
        break
    return None, [], error


# ---------------------------------------------------------------- saving

def convert_old_row(r):
    """A row written by an earlier version, converted to the current columns."""
    if "games" in r and "source" in r:
        return r
    entries = [e for e in (r.get("tables") or "").split("; ") if ENTRY_RE.match(e)]
    source = "browser feed" if entries else "page table"
    if not entries:
        entries = box_entries(r.get("box_text") or "")
    status = r.get("status") or ""
    if status == "ok" and entries is None:
        status = "error: couldn't read the tables on the page"
    good = status == "ok"
    return {"time": r.get("time", ""), "weekday": r.get("weekday", ""), "hour": r.get("hour", ""),
            "status": status, "source": source if good else "",
            "tables": len(entries) if good else "",
            "players": sum(t[2] for t in parse_games("; ".join(entries))) if good else "",
            "games": "; ".join(entries) if good else "",
            "page_text": (r.get("box_text") or "") if source == "page table" else ""}


def migrate_old_files():
    """Bring CSV files from earlier versions up to date. Nothing is lost: old rows are converted
    and each file is replaced in one step, so a crash can't leave it half-written."""
    for leftover in DATA_DIR.glob("*.tmp"):  # from a run that crashed mid-way
        leftover.unlink()
    for path in sorted(DATA_DIR.glob("*.csv")):
        has_marker = path.read_bytes()[:3] == b"\xef\xbb\xbf"
        with path.open(newline="", encoding="utf-8-sig") as fh:
            reader = csv.DictReader(fh)
            if reader.fieldnames == FIELDS and has_marker:
                continue
            rows = [convert_old_row(r) for r in reader]
        tmp = path.with_suffix(".tmp")
        with tmp.open("w", newline="", encoding="utf-8-sig") as fh:
            writer = csv.DictWriter(fh, fieldnames=FIELDS, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(rows)
        tmp.replace(path)
    OLD_DEBUG_FILE.unlink(missing_ok=True)


def append_row(now, row):
    path = DATA_DIR / f"{now:%Y-%m}.csv"
    new_file = not path.exists()
    with path.open("a", newline="", encoding="utf-8-sig" if new_file else "utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=FIELDS)
        if new_file:
            writer.writeheader()
        writer.writerow(row)


def save_problem(now, row, problem):
    """Details of the latest problem or fallback, for diagnosis. Normal runs write nothing;
    a repeating problem is re-saved at most every 6 hours to keep the history small."""
    if not problem:
        return
    try:
        old = json.loads(PROBLEM_FILE.read_text(encoding="utf-8"))
        same = (old.get("status"), old.get("source")) == (row["status"], row["source"])
        if same and now - datetime.fromisoformat(old["saved_at"]) < timedelta(hours=6):
            return
    except (OSError, ValueError, KeyError):
        pass
    PROBLEM_FILE.parent.mkdir(exist_ok=True)
    payload = {"saved_at": now.isoformat(timespec="seconds"), "status": row["status"],
               "source": row["source"], **problem}
    PROBLEM_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")


def load_csv_rows(folder):
    rows = []
    for path in sorted(folder.glob("*.csv")):
        with path.open(newline="", encoding="utf-8-sig") as fh:
            rows.extend(csv.DictReader(fh))
    return rows


def append_csv(folder, fields, now, row):
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / f"{now:%Y-%m}.csv"
    new_file = not path.exists()
    with path.open("a", newline="", encoding="utf-8-sig" if new_file else "utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        if new_file:
            writer.writeheader()
        writer.writerow(row)


def save_debug_copy(path, now, status, url, details):
    """Raw copy of what a site sent, for diagnosis: first time, then once a day or when the status changes."""
    if not details:
        return
    try:
        old = json.loads(path.read_text(encoding="utf-8"))
        if old.get("status") == status and now - datetime.fromisoformat(old["saved_at"]) < timedelta(hours=24):
            return
    except (OSError, ValueError, KeyError):
        pass
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps({"saved_at": now.isoformat(timespec="seconds"), "status": status, "url": url,
                                **details}, ensure_ascii=False, indent=1), encoding="utf-8")


def check_card():
    """Card Casino's live list. Returns (status, source, entries or None, raw text, details)."""
    problem = {}
    for attempt in (1, 2):
        try:
            fragment = fetch_text(CARD_FEED_URL, CARD_SITE["url"])
        except Exception as e:
            problem["feed"] = short_error(e)
            time.sleep(3)
            continue
        entries = card_entries(fragment)
        if entries is not None:
            return "ok", "feed", entries, "" if entries else shown(strip_tags(fragment), 300), None
        problem.update(feed="the list had an unexpected format", feed_body=fragment[:5000])
        break
    try:  # backup: the cash games page in a browser
        cash, _, details = browser_read(CARD_SITE)
    except Exception as e:
        return f"error: {short_error(e)}", "", None, "", {**problem, "browser": short_error(e)}
    problem.update(details)
    if cash is None:
        return "error: the cash games list wasn't found on the page", "page table", None, "", problem
    entries = card_text_entries(cash)
    if not entries and cash.strip():
        return "error: couldn't read the cash games list", "page table", None, cash[:1000], problem
    return "ok", "page table", entries, "", problem


def record_card(now):
    """One Card Casino check, saved to data/cardcasino/YYYY-MM.csv. Never raises."""
    row = {"time": f"{now:%Y-%m-%d %H:%M}", "weekday": DAYS[now.weekday()], "hour": now.hour,
           "status": "", "source": "", "tables": "", "players": "", "games": "", "raw": ""}
    try:
        status, source, entries, raw, details = check_card()
        row.update(status=status, source=source, raw=raw[:1000])
        if entries is not None:
            row.update(tables=len(entries), players=sum(t[2] for t in parse_games("; ".join(entries))),
                       games="; ".join(entries))
        save_debug_copy(Path("debug/cardcasino_page.json"), now, status, CARD_FEED_URL, details)
    except Exception as e:
        row["status"] = f"error: {short_error(e)}"
    try:
        append_csv(CARD_DIR, CARD_FIELDS, now, row)
        write_card_page(now)
    except Exception as e:
        print(f"Card Casino could not be saved: {short_error(e)}")
    return row


def migrate_card_files():
    """Card Casino rows saved by the previous version (as page text) converted to the current columns."""
    for path in sorted(CARD_DIR.glob("*.csv")):
        with path.open(newline="", encoding="utf-8-sig") as fh:
            reader = csv.DictReader(fh)
            if reader.fieldnames == CARD_FIELDS:
                continue
            rows = []
            for r in reader:
                if "games" in r:
                    rows.append(r)
                    continue
                text = r.get("cash_text") or ""
                entries = card_text_entries(text) if r.get("status") == "ok" else None
                if r.get("status") == "ok" and not entries and text.strip():
                    status, entries = "error: couldn't read the cash games list", None
                else:
                    status = r.get("status", "")
                rows.append({"time": r.get("time", ""), "weekday": r.get("weekday", ""), "hour": r.get("hour", ""),
                             "status": status, "source": "page table" if entries is not None else "",
                             "tables": len(entries) if entries is not None else "",
                             "players": sum(t[2] for t in parse_games("; ".join(entries))) if entries is not None else "",
                             "games": "; ".join(entries or []), "raw": text[:1000] if entries is None else ""})
        tmp = path.with_suffix(".tmp")
        with tmp.open("w", newline="", encoding="utf-8-sig") as fh:
            writer = csv.DictWriter(fh, fieldnames=CARD_FIELDS, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(rows)
        tmp.replace(path)


def write_card_page(now):
    rows = load_csv_rows(CARD_DIR)
    ok = [r for r in rows if r["status"] == "ok" and r["players"] != ""]
    checks = [(r, players_per_game(r)) for r in ok]
    out = ["# 🃏 Card Casino Šamorín — cash game tracker", "",
           f"Reads [Card Casino's live cash-game list]({CARD_SITE['url']}) together with King's, about every 10 minutes. "
           "All times are **Czech time** (same as Poland and Slovakia). Back to [King's](README.md).", ""]
    out += health_lines(rows, now, CARD_SOURCES, "debug/cardcasino_page.json")
    if ok:
        out += snapshot_lines(ok[-1])
    out += busy_sections(ok, checks)
    out += all_games_lines(ok)
    out += ["---", "Raw data: `data/cardcasino` (one CSV file per month). Card Casino lists seated players per table; "
            "it doesn't show waiting lists."]
    CARD_SITE["page"].write_text("\n".join(out) + "\n", encoding="utf-8")


def record_gas(now):
    """One Grand Casino Aš check, saved to data/grandcasinoas/YYYY-MM.csv. Never raises."""
    row = {"time": f"{now:%Y-%m-%d %H:%M}", "weekday": DAYS[now.weekday()], "hour": now.hour, "status": "",
           "tables": "", "waiting": "", "games": "", "tourneys": "", "tourney_players": "", "tourney_details": "", "raw": ""}
    details = {}
    try:
        html = fetch_text(GAS_CASH_URL, "https://www.grandcasinoas.eu/en/poker")
        entries = gas_cash_entries(html)
        if entries is None:
            row["status"] = "error: the 'Current cash game' table wasn't found"
            details["cash_page"] = html[:20000]
        else:
            games = parse_gas_games("; ".join(entries))
            row.update(status="ok", games="; ".join(entries),
                       tables=sum(1 for g in games if g[2] == "RUNNING"), waiting=sum(1 for g in games if g[2] == "WAITING"))
    except Exception as e:
        row["status"] = f"error: {short_error(e)}"
    if now.minute % 30 < 10:  # tournaments every 30 minutes
        try:
            html = fetch_text(GAS_TOURNEY_URL, "https://www.grandcasinoas.eu/en/")
            result = gas_tournaments(html, now)
            if result is None:
                details["tournament_page_start"] = html[:20000]
            else:
                row.update(tourneys=len(result[0]), tourney_players=sum(d["left"] for d in result[1]),
                           tourney_details=json.dumps(result[1], ensure_ascii=False, separators=(",", ":")))
        except Exception as e:
            details["tournaments"] = short_error(e)
    try:
        append_csv(GAS_DIR, GAS_FIELDS, now, row)
        save_debug_copy(Path("debug/grandcasinoas_page.json"), now, row["status"], GAS_CASH_URL, details)
        write_gas_page(now)
    except Exception as e:
        print(f"Grand Casino Aš could not be saved: {short_error(e)}")
    return row


def write_gas_page(now):
    rows = load_csv_rows(GAS_DIR)
    ok = [r for r in rows if r["status"] == "ok"]
    out = ["# 🃏 Grand Casino Aš — cash game tracker", "",
           f"Reads [Grand Casino Aš's live cash games]({GAS_CASH_URL}) every 10 minutes and its "
           f"[current tournaments]({GAS_TOURNEY_URL}) every 30 minutes. All times are **Czech time** (same as Poland). "
           "Back to [King's](README.md).", ""]
    out += health_lines(rows, now, {}, "debug/grandcasinoas_page.json")
    if ok:
        latest = ok[-1]
        games = sorted(parse_gas_games(latest["games"]), key=lambda g: (g[2] != "RUNNING", game_order(g[0]), stake_key(g[1])))
        out += [f"## Cash games at {latest['time']}", ""]
        out += (["```", *(f"{g:<9}{('€' + s) if s else '':<9}{status.lower()}" for g, s, status in games), "```", ""]
                if games else ["No cash games listed.", ""])
    with_t = [r for r in rows if r.get("tourneys", "") != ""]
    if with_t:
        running = tourney_info_of(with_t[-1])
        out += [f"**Tournaments in play at {with_t[-1]['time']}:** "
                + (" · ".join(tourney_text(d) for d in running) if running else "none"), ""]

    # running tables by hour and weekday
    total, count = defaultdict(float), defaultdict(int)
    for r in ok:
        for key in ((int(r["hour"]), r["weekday"]), (int(r["hour"]), "All")):
            total[key] += as_int(r["tables"])
            count[key] += 1
    out += ["## Running cash tables by hour", "",
            "Average number of running tables (Grand Casino Aš shows which games run, not how many players).", "",
            "| Hour | " + " | ".join(DAYS) + " | All days |", "|:--|" + "--:|" * (len(DAYS) + 1)]
    for h in range(24):
        cells = [f"{total[(h, d)] / count[(h, d)]:.1f}" if count[(h, d)] else "·" for d in DAYS + ["All"]]
        out.append(f"| {h:02d}:00 | " + " | ".join(cells) + " |")
    out.append("")

    # how often each game + stake was running
    def running_labels(r):
        return {f"{g} €{s}" if s else g for g, s, status in parse_gas_games(r["games"]) if status == "RUNNING"}
    labelled = [(r, running_labels(r)) for r in ok]
    freq = Counter(label for _, labels in labelled for label in labels)
    top = sorted((label for label, _ in freq.most_common(8)), key=label_key)
    out += ["## How often each game was running, by hour (all days)", ""]
    if top:
        total_h, seen = defaultdict(int), defaultdict(int)
        for r, labels in labelled:
            total_h[int(r["hour"])] += 1
            for label in labels:
                seen[(int(r["hour"]), label)] += 1
        out += ["🟩 most of the time · 🟨 sometimes · 🟥 rarely", "",
                "| Hour | " + " | ".join(top) + " | Checks |", "|:--|" + "--:|" * (len(top) + 1)]
        for h in range(24):
            out.append(f"| {h:02d}:00 | " + " | ".join(pct_cell(seen[(h, label)], total_h[h]) for label in top)
                       + f" | {total_h[h]} |")
    else:
        out.append("No running games seen yet.")
    out.append("")
    out += tournaments_seen_lines(with_t)
    out += ["---", "Raw data: `data/grandcasinoas` (one CSV file per month)."]
    GAS_PAGE.write_text("\n".join(out) + "\n", encoding="utf-8")


def remove_retired_sites():
    for key, page_path in RETIRED_SITES:
        folder = DATA_DIR / key
        rows = []
        for path in folder.glob("*.csv"):
            with path.open(newline="", encoding="utf-8-sig") as fh:
                rows.extend(csv.DictReader(fh))
        if any(r.get("status") == "ok" for r in rows):
            continue  # it did collect something: keep it
        for path in folder.glob("*.csv"):
            path.unlink()
        if folder.exists() and not any(folder.iterdir()):
            folder.rmdir()
        page_path.unlink(missing_ok=True)
        Path(f"debug/{key}_page.json").unlink(missing_ok=True)


def record_sites(now):
    """One check of each Slovak room, each saved to data/<folder>/YYYY-MM.csv.
    Never raises: these sites can't break the King's tracking."""
    try:
        results = sites_check()
    except Exception as e:  # e.g. the browser couldn't start
        results = {site["key"]: e for site in SITES}
    return {site["key"]: record_site(now, site["key"], site["name"], site["url"], site["page"], results.get(site["key"]))
            for site in SITES}


def record_site(now, key, name, url, page_path, result):
    row = {"time": f"{now:%Y-%m-%d %H:%M}", "weekday": DAYS[now.weekday()], "hour": now.hour,
           "status": "", "cash_text": "", "tournament_text": ""}
    details = {}
    if isinstance(result, Exception) or result is None:
        row["status"] = f"error: {short_error(result)}" if result else "error: not checked"
    else:
        cash, tournaments, details = result
        row["status"] = "ok" if cash is not None else "error: the 'Cash games' list wasn't found on the page"
        row["cash_text"] = (cash or "")[:3000]
        row["tournament_text"] = (tournaments or "")[:1500]
    try:
        append_csv(DATA_DIR / key, SITE_FIELDS, now, row)
        save_debug_copy(Path(f"debug/{key}_page.json"), now, row["status"], url, details)
        write_site_page(key, name, url, page_path)
    except Exception as e:
        print(f"{name} could not be saved: {short_error(e)}")
    return row


def write_site_page(key, name, url, page_path):
    rows = load_csv_rows(DATA_DIR / key)
    ok = [r for r in rows if r["status"] == "ok"]
    out = [f"# 🃏 {name} — cash game tracker", "",
           f"Checks [its website]({url}) together with King's, about every 10 minutes. "
           "All times are **Czech time** (same as Poland and Slovakia). Back to [King's](README.md).", ""]
    if rows:
        last = rows[-1]
        state = "✅ OK" if last["status"] == "ok" else f"⚠️ {clean(last['status'], 160)}"
        out += [f"**Last check:** {last['time']} — {state}  ",
                f"**Checks so far:** {len(ok)} successful out of {len(rows)} (since {rows[0]['time'][:10]})", ""]
    if ok:
        latest = ok[-1]
        lines = [shown(x.replace(" ; ", " · ")) for x in latest["cash_text"].split(" | ") if x][:40] \
            or ["(no cash games listed)"]
        out += [f"## Cash games on the site at {latest['time']}", "", "```", *lines, "```", "",
                f"**Tournaments:** {shown(latest['tournament_text'], 300) or 'none listed'}", ""]
    out += ["---", "First version: the lists are saved exactly as the site shows them. Statistics per game "
            "and hour (like on the King's page) are added once a day of data shows the site's format.",
            f"Raw data: `data/{key}` (one CSV file per month)."]
    page_path.write_text("\n".join(out) + "\n", encoding="utf-8")


def load_rows():
    rows = []
    for path in sorted(DATA_DIR.glob("*.csv")):
        with path.open(newline="", encoding="utf-8-sig") as fh:
            rows.extend(csv.DictReader(fh))
    return rows


# ---------------------------------------------------------------- README with statistics

def stake_key(stakes):
    return [float(x) for x in stakes.split("/") if re.fullmatch(r"\d+(?:\.\d+)?", x)][::-1]


def game_order(game):
    """NLH first, then the Omaha games, then everything else."""
    return 0 if game == "NLH" else 1 if game.startswith("PLO") else 2


def label_key(label):
    game, _, stakes = label.rpartition(" €")
    return game_order(game), stake_key(stakes), game


def players_per_game(row):
    count = Counter()
    for game, _, seated, _ in parse_games(row["games"]):
        count[game] += seated
    return count


def labels_of(row):
    return {f"{game} €{stakes}" for game, stakes, _, _ in parse_games(row["games"])}


def main_games(checks):
    """Games that run regularly (in at least 10% of checks), NLH first - at most 4."""
    volume, ran = Counter(), Counter()
    for _, per_game in checks:
        volume.update(per_game)
        ran.update(g for g, n in per_game.items() if n)
    regular = [g for g in volume if ran[g] >= 0.1 * len(checks)]
    return sorted(regular, key=lambda g: (game_order(g), -volume[g]))[:4]


def busiest_slots(checks, game, top=3, min_dates=2):
    total, count, dates = defaultdict(float), defaultdict(int), defaultdict(set)
    for r, per_game in checks:
        slot = (r["weekday"], int(r["hour"]))
        total[slot] += per_game.get(game, 0)
        count[slot] += 1
        dates[slot].add(r["time"][:10])
    slots = sorted(((total[s] / count[s], s) for s in count if len(dates[s]) >= min_dates), key=lambda x: -x[0])
    return [f"{day} {hour:02d}:00 ({avg:.0f})" for avg, (day, hour) in slots[:top] if avg > 0]


def pct_cell(n, total):
    if not total:
        return "·"
    p = round(100 * n / total)
    return f"{'🟩' if p >= 75 else '🟨' if p >= 25 else '🟥'} {p}%"


def count_text(n, word):
    return f"{n} {word}{'s' * (int(n) != 1)}"


def health_lines(rows, now, sources, problem_file):
    if not rows:
        return []
    good = sum(1 for r in rows if r["status"] == "ok" and r.get("players", "x") != "")
    last = rows[-1]
    source = last.get("source") or ""
    state = ((f"✅ OK ({sources.get(source, source)})" if source else "✅ OK") if last["status"] == "ok"
             else f"⚠️ {clean(last['status'], 160)} — details in `{problem_file}`")
    day_ago = (now - timedelta(hours=24)).strftime("%Y-%m-%d %H:%M")
    recent = [r for r in rows if r["time"] >= day_ago]
    times = [datetime.strptime(r["time"], "%Y-%m-%d %H:%M") for r in recent]
    gaps = [b - a for a, b in zip(times, times[1:])] or [timedelta(0)]
    gap_min = int(max(gaps).total_seconds() // 60)
    gap = f"longest gap {gap_min // 60} h {gap_min % 60} min" + (" (GitHub skipped runs)" if gap_min > 60 else "")
    return [f"**Last check:** {last['time']} — {state}  ",
            f"**Last 24 h:** {sum(r['status'] == 'ok' for r in recent)} of {len(recent)} checks OK, {gap} · "
            f"**Collecting since:** {rows[0]['time'][:10]} ({count_text(good, 'good check')})", ""]


def snapshot_lines(latest):
    tables = sorted(parse_games(latest["games"]), key=lambda t: (game_order(t[0]), t[0], stake_key(t[1])))
    out = [f"## Tables running at {latest['time']}", ""]
    if not tables:
        return out + ["No tables were running.", ""]
    width = max(len(t[0]) for t in tables) + 2
    per_game = defaultdict(lambda: [0, 0])
    for game, _, seated, _ in tables:
        per_game[game][0] += seated
        per_game[game][1] += 1
    totals = sorted(per_game.items(), key=lambda kv: (game_order(kv[0]), kv[0]))
    return out + ["```", *(f"{g:<{width}}€{s:<8}{a}/{b} players" for g, s, a, b in tables), "```",
                  " · ".join(f"**{g}:** {p} players at {count_text(n, 'table')}" for g, (p, n) in totals), ""]


def busy_sections(ok, checks):
    """Busiest times, average players by hour per game, and how often each game + stake runs."""
    games = main_games(checks) if checks else []
    out = ["## Busiest times so far", ""]
    lines = [f"- **{g}:** " + " · ".join(slots) for g in games if (slots := busiest_slots(checks, g))]
    out += (["Day, hour and average seated players (only day-hour slots seen on at least 2 different dates).", "", *lines]
            if lines else ["Needs about two weeks of data: each day-and-hour slot must be seen on at least 2 dates."])
    out.append("")

    out += ["## Average players by hour", "",
            "Seated players at each game's tables. 0 = that game wasn't running." if games else "No player data yet.", ""]
    for game in games:
        total, count = defaultdict(float), defaultdict(int)
        for r, per_game in checks:
            for key in ((int(r["hour"]), r["weekday"]), (int(r["hour"]), "All")):
                total[key] += per_game.get(game, 0)
                count[key] += 1
        out += [f"### {GAME_NAMES.get(game, game)}", "",
                "| Hour | " + " | ".join(DAYS) + " | All days |", "|:--|" + "--:|" * (len(DAYS) + 1)]
        for h in range(24):
            cells = [f"{total[(h, d)] / count[(h, d)]:.0f}" if count[(h, d)] else "·" for d in DAYS + ["All"]]
            out.append(f"| {h:02d}:00 | " + " | ".join(cells) + " |")
        out.append("")

    labelled = [(r, labels_of(r)) for r in ok]
    freq = Counter(label for _, labels in labelled for label in labels)
    top = sorted((label for label, _ in freq.most_common(8)), key=label_key)
    out += ["## How often each game was running, by hour (all days)", ""]
    if top:
        total_h, seen = defaultdict(int), defaultdict(int)
        for r, labels in labelled:
            total_h[int(r["hour"])] += 1
            for label in labels:
                seen[(int(r["hour"]), label)] += 1
        out += ["🟩 most of the time · 🟨 sometimes · 🟥 rarely", "",
                "| Hour | " + " | ".join(top) + " | Checks |", "|:--|" + "--:|" * (len(top) + 1)]
        for h in range(24):
            cells = [pct_cell(seen[(h, label)], total_h[h]) for label in top]
            out.append(f"| {h:02d}:00 | " + " | ".join(cells) + f" | {total_h[h]} |")
    else:
        out.append("No games seen yet.")
    out.append("")
    return out


def all_games_lines(ok):
    """Every game + stake ever seen, rare ones included."""
    appearances = defaultdict(list)
    for r in ok:
        for label in labels_of(r):
            appearances[label].append(r)
    if not appearances:
        return []
    out = ["## All games seen", "", "| Game | Running in | Most often | Last seen |", "|:--|--:|:--|:--|"]
    for label in sorted(appearances, key=label_key):
        seen_rows = appearances[label]
        day, hour = Counter((r["weekday"], int(r["hour"])) for r in seen_rows).most_common(1)[0][0]
        out.append(f"| {label} | {round(100 * len(seen_rows) / len(ok))}% of checks "
                   f"| {day} around {hour:02d}:00 | {seen_rows[-1]['time']} |")
    return out + [""]


def tourney_info_of(row):
    """The saved tournament details of one check (older checks only have names: the game is read from those)."""
    try:
        details = json.loads(row.get("tourney_details") or "[]")
    except ValueError:
        details = []
    if details:
        return details
    return [{"name": n, "game": tourney_game(n), "left": a, "entries": e} for n, a, e in parse_tourneys(row.get("tourney_list"))]


def money(value, currency="EUR"):
    sign = {"EUR": "€", "CZK": "CZK ", "USD": "$"}.get(currency or "EUR", f"{currency} ")
    return f"{sign}{value:,.0f}".replace(",", " ") if isinstance(value, (int, float)) else "?"


def tourney_text(d):
    parts = [d.get("game", "?")]
    if d.get("buyin") is not None:
        buyin = money(d["buyin"] + (d.get("fee") or 0), d.get("currency"))
        parts.append(buyin + (f", {money(d['bounty'], d.get('currency'))} bounty" if d.get("bounty") else ""))
    parts.append(f"{d.get('left', '?')} of {d.get('entries', '?')} left")
    if d.get("late_reg_open"):
        parts.append("late reg open")
    if d.get("level") is not None:
        parts.append(f"level {d['level']}" + (f", blinds {d['blinds']}" if d.get("blinds") else ""))
    return f"{shown(d.get('name'), 60)} ({', '.join(parts)})"


def tournaments_seen_lines(rows, limit=15):
    """The tournaments seen most recently: game, buy-in and how big they got."""
    seen = {}
    for r in rows:
        for d in tourney_info_of(r):
            key = d.get("name")
            item = seen.setdefault(key, {"d": d, "first": r["time"], "last": r["time"], "max_entries": 0})
            item.update(d=d, last=r["time"])
            item["max_entries"] = max(item["max_entries"], as_int(d.get("entries")))
    if not seen:
        return []
    recent = sorted(seen.values(), key=lambda item: item["last"], reverse=True)[:limit]
    out = ["## Tournaments seen", "", "The most recent ones. The game is read from the tournament's name.", "",
           "| Tournament | Game | Buy-in | Entries | Seen |", "|:--|:--|--:|--:|:--|"]
    for item in recent:
        d = item["d"]
        buyin = money(d["buyin"] + (d.get("fee") or 0), d.get("currency")) if d.get("buyin") is not None else "·"
        period = item["first"] if item["first"][:13] == item["last"][:13] else f"{item['first']} → {item['last'][5:]}"
        out.append(f"| {shown(d.get('name'), 60)} | {d.get('game', '?')} | {buyin} | {item['max_entries']} | {period} |")
    return out + [""]


def overview_line(kings_row, card_row, banco_row, gas_row=None):
    """One line at the top of the King's page: what's running at all three rooms right now."""
    def cash(row):
        if row and row.get("status") == "ok" and row.get("players", "") != "":
            return f"{count_text(row['tables'], 'table')}, {count_text(row['players'], 'player')}"
        return "couldn't be read"
    parts = [f"King's: {cash(kings_row)}", f"[Card Casino Šamorín](CARD_CASINO.md): {cash(card_row)}"]
    if gas_row:
        gas = ("couldn't be read" if gas_row.get("status") != "ok"
               else f"{count_text(gas_row['tables'], 'table')} running" + (f", {gas_row['waiting']} waiting" if as_int(gas_row["waiting"]) else ""))
        parts.append(f"[Grand Casino Aš](GRAND_CASINO_AS.md): {gas}")
    if banco_row:
        listed = shown((banco_row.get("cash_text") or "").replace(" ; ", " ").replace(" | ", ", "), 70)
        banco = "couldn't be read" if banco_row.get("status") != "ok" else listed or "no games listed"
        parts.append(f"[Banco](BANCO.md): {banco}")
    return "**Right now:** " + " · ".join(parts)


def write_readme(rows, now, overview=""):
    ok = [r for r in rows if r["status"] == "ok" and r["players"] != ""]
    checks = [(r, players_per_game(r)) for r in ok]
    out = ["# 🃏 King's Rozvadov — cash game tracker", "",
           "Checks King's live cash games and tournaments about every 10 minutes and updates this page by itself. "
           "All times are **Czech time** (same as Poland). Also tracking: [Card Casino Šamorín](CARD_CASINO.md) · "
           "[Grand Casino Aš](GRAND_CASINO_AS.md) · [Banco Casino Bratislava](BANCO.md).", ""]
    if overview:
        out += [overview, ""]
    out += health_lines(rows, now, SOURCES, "debug/last_problem.json")

    if ok:
        latest = ok[-1]
        out += snapshot_lines(latest)
        if latest.get("tourneys", "") != "":
            running = tourney_info_of(latest)
            out += ["**Tournaments in play:** " + (" · ".join(tourney_text(d) for d in running) if running else "none"), ""]
        else:
            out += ["**Tournaments:** couldn't be read at this check (cash data is unaffected).", ""]

    out += busy_sections(ok, checks)

    # Do cash games get busier when tournaments are running?
    with_t = [r for r in ok if r.get("tourney_players", "") != ""]
    first_t = datetime.strptime(min(r["time"] for r in with_t), "%Y-%m-%d %H:%M") if with_t else None
    if first_t and now.replace(tzinfo=None) - first_t < timedelta(days=14):
        out += ["## Cash games vs tournaments", "",
                f"Collecting since {first_t:%Y-%m-%d}. Shown from {first_t + timedelta(days=14):%Y-%m-%d}: with fewer "
                "than two weeks, the numbers would mostly reflect which days happened to be recorded.", ""]
        with_t = []
    if with_t:
        by_hour = defaultdict(list)
        for r in ok:
            by_hour[int(r["hour"])].append(int(r["players"]))
        usual = {h: sum(v) / len(v) for h, v in by_hour.items()}
        out += ["## Cash games vs tournaments", "",
                "Cash players grouped by how many players were still in tournaments at the time. "
                "\"vs usual\" compares each check with the average for the same hour of day, so the "
                "normal evening rush doesn't fake a link. It needs a few weeks of data to mean much.", "",
                "| Tournament players in action | Checks | Avg cash players | vs usual for that hour |",
                "|:--|--:|--:|--:|"]
        for label, low, high in (("none", 0, 0), ("1–49", 1, 49), ("50–149", 50, 149), ("150 or more", 150, 10**9)):
            group = [r for r in with_t if low <= int(r["tourney_players"]) <= high]
            if group:
                avg = sum(int(r["players"]) for r in group) / len(group)
                diff = sum(int(r["players"]) - usual[int(r["hour"])] for r in group) / len(group)
                out.append(f"| {label} | {len(group)} | {avg:.0f} | {diff:+.0f} |")
        out.append("")

        # Which cash games run alongside which tournament games?
        cash = {id(r): Counter() for r in ok}
        per_hour = {"NLH": defaultdict(list), "PLO": defaultdict(list)}
        for r in ok:
            for game, _, seated, _ in parse_games(r["games"]):
                cash[id(r)][family(game)] += seated
            for fam in per_hour:
                per_hour[fam][int(r["hour"])].append(cash[id(r)][fam])
        usual_fam = {fam: {h: sum(v) / len(v) for h, v in hours.items()} for fam, hours in per_hour.items()}

        def situation(r):
            families = {tourney_family(d.get("game", "NLH")) for d in tourney_info_of(r) if as_int(d.get("left"))}
            if not families:
                return "none"
            if "PLO" in families:
                return "a PLO tournament"
            return "only NLH tournaments" if families == {"NLH"} else "other tournament games"

        groups = defaultdict(list)
        for r in with_t:
            groups[situation(r)].append(r)
        out += ["### Cash games by tournament type", "",
                "NLH and PLO cash players depending on which tournament games were running. The game of a "
                "tournament is read from its names (PLO/Omaha, Mix, Short Deck... in the title; otherwise NLH).", "",
                "| Tournaments in play | Checks | NLH cash players | vs usual | PLO cash players | vs usual |",
                "|:--|--:|--:|--:|--:|--:|"]
        for label in ("none", "only NLH tournaments", "a PLO tournament", "other tournament games"):
            group = groups.get(label)
            if not group:
                continue
            cells = []
            for fam in ("NLH", "PLO"):
                values = [cash[id(r)][fam] for r in group]
                diffs = [cash[id(r)][fam] - usual_fam[fam][int(r["hour"])] for r in group]
                cells += [f"{sum(values) / len(values):.0f}", f"{sum(diffs) / len(diffs):+.0f}"]
            out.append(f"| {label} | {len(group)} | " + " | ".join(cells) + " |")
        out.append("")

    out += all_games_lines(ok)
    out += tournaments_seen_lines(rows)
    out += ["---", "Raw data: the `data` folder, one CSV file per month. To open one in Excel, use "
            "Data → From Text/CSV (double-clicking puts everything in one column in Polish Excel). "
            "The tracker is `tracker.py`; its schedule is in `.github/workflows/track.yml`."]
    README.write_text("\n".join(out) + "\n", encoding="utf-8")


# ---------------------------------------------------------------- self-test and main

def self_test():
    """Quick checks of the parsing code. If one fails, the run stops before recording anything and
    GitHub emails you - so a broken update can't quietly fill the data with nonsense."""
    def table(prof, gtype, blinds, seated, venue=1, status="PLAYING"):
        return {"gameProfile": {"name": prof, "blindsFormatted": blinds}, "gameType": {"name": gtype},
                "playerCount": seated, "seatCount": 8, "venue": venue, "status": status}
    feed = [table("NLH 2-4", "No Limit Holdem", "€ 2/4", 7), table("PLO 10-10 5cards", "Omaha Poker", "€ 10/10", 8),
            table("SD 25-50", "Short Deck", "€ 25/50", 5, status="WAITING"), table("PLO 5-5", "Omaha Poker", "€ 5/5", "3"),
            table("NLH 1-2", "No Limit Holdem", "€ 1/2", 6, venue=2), table("X|<b>;[Y] 5-10", "", "€ 5/10", None)]
    got = feed_entries(feed)
    assert got == ["NLH €2/4 7/8", "PLO5 €10/10 8/8", "SD (Short Deck) €25/50 5/8 [WAITING]",
                   "PLO €5/5 3/8", "X b Y €5/10 0/8"], got
    assert feed_entries({"error": "x"}) is None and feed_entries([]) == []
    assert list(parse_games("; ".join(got[:3]))) == [("NLH", "2/4", 7, 8), ("PLO5", "10/10", 8, 8),
                                               ("SD (Short Deck)", "25/50", 5, 8)]
    box = "NO LIMIT TEXAS HOLD’EM | € 2/4 | 8/8 PLAYERS | POT-LIMIT OMAHA 5 CARDS | € 5/5 | 7/8 PLAYERS"
    assert box_entries(box) == ["NLH €2/4 8/8", "PLO5 €5/5 7/8"], box_entries(box)
    assert box_entries("CASH GAME TABLES ARE WAITING FOR MORE PLAYERS.") == []
    assert box_entries("SOME NEW LAYOUT 12") is None
    old = convert_old_row({"time": "2026-10-06 04:40", "weekday": "Tue", "hour": "4", "status": "ok", "box_text": box})
    assert (old["source"], old["tables"], old["players"], old["games"]) == \
        ("page table", 2, 15, "NLH €2/4 8/8; PLO5 €5/5 7/8"), old
    clocks = [{"fullName": "Daily | Deepstack", "status": "RUNNING", "start": "2026-10-08T18:00:00", "activePlayers": 40, "totalEntries": 62},
              {"fullName": "Main Event - Final Day", "status": "REGISTRATION_OPEN", "start": "2026-10-08T23:00:00", "activePlayers": 85, "totalEntries": 565},
              {"fullName": "Main Event - Day 1", "status": "PAUSED", "start": "2026-10-07T18:00:00", "activePlayers": 84, "totalEntries": 565},
              {"fullName": "Turbo", "status": "FINISHED", "start": "2026-10-08T12:00:00", "activePlayers": 1, "totalEntries": 30}]
    got = tournament_entries(clocks, datetime(2026, 10, 8, 20, 0, tzinfo=TZ))
    assert got == ["Daily Deepstack 40/62", "Main Event - Day 1 84/565 [PAUSED]"], got
    assert list(parse_tourneys("; ".join(got))) == [("Daily Deepstack", 40, 62), ("Main Event - Day 1", 84, 565)]
    assert tournament_entries({"x": 1}, datetime(2026, 10, 8, tzinfo=TZ)) is None
    bagged = {"fullName": "Day 1", "status": "PAUSED", "start": "2026-10-07T18:00:00", "activePlayers": 84,
              "totalEntries": 565, "activePause": {"sinceTime": "2026-10-08T17:30:00.5",
                                                   "previousPause": {"sinceTime": "2026-10-08T17:00:00"}}}
    assert tournament_entries([bagged], datetime(2026, 10, 8, 18, 30, tzinfo=TZ)) == ["Day 1 84/565 [PAUSED]"]
    assert tournament_entries([bagged], datetime(2026, 10, 8, 19, 30, tzinfo=TZ)) == []
    assert parse_games("MIX NLH /PLO €5/5 6/8") == (("MIX NLH/PLO", "5/5", 6, 8),)
    assert as_int("7.0") == 7 and as_int(None) == 0 and as_int("x") == 0
    names = ("GPD Mystery Bounty - Day 1D", "RENEMASTERMIX Friday Bounty", "PLO5 Bounty", "Pot-Limit Omaha Deepstack",
             "NLH/PLO Mix", "Short Deck Special", "PLO 6-Card Bounty", "Omaha Hi-Lo", "Flip & Go Pineapple", "Big O",
             "GPD NLH Morning Turbo", "6-Max Turbo", "Satellite to PLO Main")
    assert [tourney_game(n) for n in names] == ["NLH", "NLH", "PLO5", "PLO", "Mixed", "Short Deck", "PLO6", "PLO Hi-Lo",
                                               "Pineapple", "PLO5 Hi-Lo", "NLH", "NLH", "PLO"], [tourney_game(n) for n in names]
    clock = {"fullName": "KM EPC Closer - Day 1", "tournamentName": "KM EPC Closer", "subName": "played till ITM",
             "status": "PAUSED", "currency": "EUR", "effectivePrizePool": 240125, "startingStack": 50000,
             "openRegistration": False, "lateRegistrationUntilLevel": 9, "start": "2026-10-05T18:00:03", "totalEntries": 565,
             "activePlayers": 84, "averageStack": 336310, "entryValue": 500, "serviceFee": 0, "bountyValue": None,
             "currentLevel": {"sb": 5000, "bb": 10000, "ante": 10000, "number": 14}}
    entries, details = tournament_entries([clock], datetime(2026, 10, 6, 4, 40, tzinfo=TZ), with_details=True)
    assert entries == ["KM EPC Closer - Day 1 84/565 [PAUSED]"], entries
    assert details[0]["game"] == "NLH" and details[0]["blinds"] == "5000/10000/10000" and details[0]["buyin"] == 500, details
    assert tourney_text(details[0]) == "KM EPC Closer - Day 1 (NLH, €500, 84 of 565 left, level 14, blinds 5000/10000/10000)", \
        tourney_text(details[0])
    assert [family(g) for g in ("NLH", "PLO5", "PLO", "MIX NLH/PLO")] == ["NLH", "PLO", "PLO", "Other"]
    page = "Cash Game\nCash games\nNLH\t1/2\t8\nPLO\t2/2\t6\nPoker tournaments\nCurrently we do not play any tournaments\nBanco promotions"
    assert page_section(page, "cash games", ("poker tournaments",)) == "NLH | 1/2 | 8 | PLO | 2/2 | 6"
    assert page_section(page, "poker tournaments", ("banco promotions",)) == "Currently we do not play any tournaments"
    assert popup_text({"rows": [["Game", "Blinds"], ["NLH", "€1/2"]], "text": ""}) == "Game ; Blinds | NLH ; €1/2"
    assert popup_text({"rows": [], "text": "Cash games\n×\nNo games at the moment"}) == "No games at the moment"
    assert popup_text(None) is None
    card_html = ('<div class="splide__slide"><div class="cash-game aligner flex-start">\r <h4 class="stretch">NLH</h4>\r'
                 ' <h4 class="number">1/3 €</h4>\r <h4>8/8</h4>\r </div><div class="cash-game aligner flex-start">'
                 '<h4 class="stretch">PLO</h4><h4 class="number">100/100 €</h4><h4>5/8</h4></div></div>')
    assert card_entries(card_html) == ["NLH €1/3 8/8", "PLO €100/100 5/8"], card_entries(card_html)
    assert card_entries("") == [] and card_entries("<p>No cash games at the moment</p>") == []
    assert card_entries('<div class="cash-game"><h4>NLH</h4></div>') is None
    assert card_text_entries("NLH | 1/3 € | 8/8 | PLO | 10/10 € | 8/8") == ["NLH €1/3 8/8", "PLO €10/10 8/8"]
    assert [card_game(g) for g in ("nlh", "PLO", "PLO 5", "PLO4", "NLH/PLO")] == ["NLH", "PLO", "PLO5", "PLO", "NLH/PLO"]
    gas_table = ('<h2>Current cash game</h2><table><thead><tr><th>Game</th><th>Blinds</th><th>Buy-in</th><th>Status</th></tr>'
                 '</thead><tr><td><a href="/x/15">NLH</a></td><td>1€-2€</td><td>€50 &ndash; €500</td><td>Running</td></tr>'
                 '<tr><td><a href="/x/16">PLO/NLH</a></td><td></td><td></td><td>Waiting</td></tr></table>')
    assert gas_cash_entries(gas_table) == ["NLH €1/2 [RUNNING]", "PLO/NLH [WAITING]"], gas_cash_entries(gas_table)
    assert gas_cash_entries("<p>nothing</p>") is None
    gas_page = ("<h2>Current Tournaments</h2><div>Crazy Pineapple</div> Start 01.10. 14:00 11:19 LVL 9 Level 1000/1500/1500 "
                "70 € Buy-In Closed Late Reg. 30&nbsp;000 Starting Stack 55&nbsp;500 Average Stack 20 (37) Players "
                "€ 2&nbsp;220 Prizepool Next level 1000/2000/2000 National NLH Championship 1A Start 01.10. 17:00 32:12 Countdown "
                "Level Countdown 150 € Buy-In 05:12:12 Late Reg. 100 000 Starting Stack 100 000 Average Stack 3 (3) Players "
                "€ 100 000 Prizepool Next level 200/500/500 01.10. 12:00 German Team Championship I All Tournaments (126)")
    entries, details = gas_tournaments(gas_page, datetime(2026, 10, 1, 16, 0, tzinfo=TZ))
    assert entries == ["Crazy Pineapple 20/37"], entries
    assert (details[0]["game"], details[0]["prizepool"], details[0]["avg_stack"], details[0]["late_reg_open"]) == \
        ("Pineapple", 2220, 55500, False), details
    assert [is_tracker(h) for h in ("www.googletagmanager.com", "ajax.googleapis.com", "connect.facebook.net",
                                    "admin.kings-resort.com", "bancocasino.sk")] == [True, False, True, False, False]


def should_alert(rows):
    """Email-worthy: the first time ALERT_AFTER checks in a row have failed, then once a day
    (on the first failed check of each new day) for as long as the problem lasts."""
    streak = failure_streak(rows)
    if streak < ALERT_AFTER:
        return False
    return streak == ALERT_AFTER or rows[-1]["time"][:10] != rows[-2]["time"][:10]


def failure_streak(rows):
    streak = 0
    for r in reversed(rows):
        if r["status"] == "ok":
            break
        streak += 1
    return streak


def main():
    try:
        self_test()
    except AssertionError as e:
        print(f"::error::Self-test failed, so nothing was recorded: {e}")
        return 1

    now = datetime.now(TZ)
    DATA_DIR.mkdir(exist_ok=True)
    migrate_old_files()

    status, source, entries, page_text, problem = check()
    tourneys, tourney_info, tourney_error = check_tournaments(now)
    if tourney_error:
        problem = {**(problem or {}), "tournaments": tourney_error}
    row = {"time": f"{now:%Y-%m-%d %H:%M}", "weekday": DAYS[now.weekday()], "hour": now.hour,
           "status": status, "source": source,
           "tables": len(entries) if entries is not None else "",
           "players": sum(t[2] for t in parse_games("; ".join(entries))) if entries is not None else "",
           "games": "; ".join(entries or []),
           "tourneys": len(tourneys) if tourneys is not None else "",
           "tourney_players": sum(a for _, a, _ in parse_tourneys("; ".join(tourneys))) if tourneys is not None else "",
           "tourney_list": "; ".join(tourneys or []),
           "tourney_details": json.dumps(tourney_info, ensure_ascii=False, separators=(",", ":")) if tourneys else "",
           "page_text": page_text[:3000]}
    append_row(now, row)
    save_problem(now, row, problem)

    remove_retired_sites()
    migrate_card_files()
    card_row = record_card(now)
    gas_row = record_gas(now)
    site_rows = record_sites(now)
    rows = load_rows()
    write_readme(rows, now, overview_line(row, card_row, site_rows.get("banco"), gas_row))
    print(json.dumps(row, ensure_ascii=False))
    print("cardcasino:", json.dumps(card_row, ensure_ascii=False)[:200])
    print("grandcasinoas:", json.dumps(gas_row, ensure_ascii=False)[:200])
    for key, site_row in site_rows.items():
        print(f"{key}:", json.dumps(site_row, ensure_ascii=False)[:200])

    if should_alert(rows):
        print(f"::error::{failure_streak(rows)} checks in a row have failed. See README.md and debug/last_problem.json.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
