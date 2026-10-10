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
     Bratislava's website (data/banco/ + BANCO.md), plus Olympic Park Tallinn and Olympic Casino
     Vilnius from OlyBet's poker site (every 30 minutes). Those are kept fully separate, so a
     problem with their websites can never affect the King's data,
  6. marks festival weeks (calendar.csv), the tournament schedule (hendonmob.txt, a copied Hendon
     Mob page) and public holidays in the players' home countries, so the statistics can show
     normal days separately from festivals and holidays.

Games are named the way the poker room's own system names them (NLH, PLO5, ...), so different
games are never mixed together. If checks keep failing, the run reports an error and GitHub
emails you (after about an hour, then once a day). Nothing here needs editing.
"""

import csv
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from functools import lru_cache
from html import unescape
from datetime import date, datetime, timedelta
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
MONTH_FILES = "[0-9][0-9][0-9][0-9]-[0-9][0-9].csv"  # King's data: one file per month, e.g. data/2026-10.csv
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
# Olympic Casino rooms on OlyBet's poker site. That site has bot protection: the tracker only ever
# makes ordinary page requests every 30 minutes, and if the site refuses one it records "blocked"
# instead of trying to get around it.
OLY_SITES = (
    {"key": "olympic-tallinn", "name": "Olympic Park Casino Tallinn", "club": "olympic park",
     "urls": [os.environ.get("OLY_EE_URL", "https://olybetpoker.com/ee/en/cash-games/")],
     "home": os.environ.get("OLY_EE_HOME", "https://olybetpoker.com/ee/en/"), "page": Path("OLYMPIC_TALLINN.md")},
    {"key": "olympic-vilnius", "name": "Olympic Casino Vilnius", "club": "vilni",
     "urls": [os.environ.get("OLY_LT_URL", "https://olybetpoker.com/lt/en/cash-games/"), "https://olybetpoker.com/lt/cash-games/"],
     "home": os.environ.get("OLY_LT_HOME", "https://olybetpoker.com/lt/en/"), "page": Path("OLYMPIC_VILNIUS.md")},
)
OLY_FIELDS = ["time", "weekday", "hour", "status", "club", "tables", "players", "waiting", "games", "listed",
              "tournaments_text", "raw"]
OLY_CLUBS_FILE = DATA_DIR / "olympic_clubs.json"  # remembers each site's club page address

# Festivals, tournament schedule and public holidays (see "festivals, schedule and holidays" below)
CALENDAR_FILE = Path("calendar.csv")          # festival / series / cash-game-event dates, edited by hand
HENDONMOB_FILE = Path("hendonmob.txt")        # a copied Hendon Mob "upcoming events" page
SCHEDULE_FILE = DATA_DIR / "schedule" / "events.csv"  # every event read from it so far (older ones are kept)
SCHEDULE_FIELDS = ["room", "date", "end", "time", "kind", "game", "buyin", "title", "restricted"]
PASTE_STATE = DATA_DIR / "schedule" / "paste.json"  # which copy of hendonmob.txt was read, and from when
HOLIDAY_FILE = DATA_DIR / "holidays.json"     # worked out once a day
SAMPLE_DIR = Path("debug/samples")            # a few raw feed records a day, to spot unused details
FESTIVAL_TYPES = ("festival", "cash event")   # these days are kept apart from normal days in the stats
ROOMS = {  # key: (name, page, the countries most players come from - their public holidays matter)
    "kings": ("King's Rozvadov", "README.md", (("CZ", None, "Czechia"), ("DE", "BY", "Bavaria"))),
    "grandcasinoas": ("Grand Casino Aš", "GRAND_CASINO_AS.md",
                      (("CZ", None, "Czechia"), ("DE", "BY", "Bavaria"), ("DE", "SN", "Saxony"))),
    "cardcasino": ("Card Casino Šamorín", "CARD_CASINO.md",
                   (("SK", None, "Slovakia"), ("AT", None, "Austria"), ("HU", None, "Hungary"))),
    "banco": ("Banco Casino Bratislava", "BANCO.md",
              (("SK", None, "Slovakia"), ("AT", None, "Austria"), ("HU", None, "Hungary"))),
    "olympic-tallinn": ("Olympic Park Tallinn", "OLYMPIC_TALLINN.md", (("EE", None, "Estonia"), ("FI", None, "Finland"))),
    "olympic-vilnius": ("Olympic Casino Vilnius", "OLYMPIC_VILNIUS.md",
                        (("LT", None, "Lithuania"), ("LV", None, "Latvia"), ("PL", None, "Poland"))),
}
HM_ROOMS = (("King's Resort Live, Rozvadov", "kings"), ("Grand Casino Asch ( Aš ), Asch", "grandcasinoas"),
            ("Card Casino Šamorín, Šamorín", "cardcasino"), ("Banco Casino, Bratislava", "banco"),
            ("Olympic Park Casino, Tallinn", "olympic-tallinn"), ("Olympic Casino Vilnius, Vilnius", "olympic-vilnius"))
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


OTHER_GAMES = re.compile(r"\bstud\b|\brazz\b|badugi|baducey|badacey|triple draw|lowball|\b2-7\b|sviten|drawmaha|"
                         r"h\.?o\.?r\.?s\.?e|\b\d+[- ]?game\b|s\.o\.r\.b\.e\.t|t\.o\.r\.s\.e|torses|\bt\.o\.e\b|"
                         r"h\.e\.t\.r\.o\.s|big bet mix|pickem|courchevel")


def tourney_game(name):
    """Which poker game a tournament is, read from its name: rooms put PLO/Omaha, Mix, Short Deck,
    Pineapple etc. in the title of every non-Hold'em event, and everything else is No-Limit Hold'em.
    'PLO mix' = several Omaha variants (PLO4/PLO5/PLO6); 'Mixed' = Omaha mixed with other games."""
    n = " ".join(name.lower().replace("’", "'").split())
    omaha = re.search(r"\bplo\d?\b|omaha|\bbig o\b", n)
    holdem = re.search(r"hold'?em|\bnlh\b", n)
    if OTHER_GAMES.search(n) or (omaha and holdem):
        return "Mixed"
    if re.search(r"dealer'?s choice", n):
        return "PLO mix" if omaha else "Mixed"
    if re.search(r"\bmix(ed)?\b", n) and not omaha:
        return "Mixed"
    if "pineapple" in n:
        return "Pineapple"
    if re.search(r"short ?deck|\b6\+|six plus", n):
        return "Short Deck"
    if not omaha:
        return "NLH"
    if re.search(r"\bbig o\b", n):
        return "PLO5 Hi-Lo"
    if re.search(r"hi[ -/]?lo|8 or better|\bo8\b|\bplo8\b", n):
        return "PLO Hi-Lo"
    sizes = set(re.findall(r"\bplo\s*([456])\b", n)) | set(re.findall(r"\b([56])[ -]?cards?\b", n))
    for group in re.findall(r"\b[456](?:\s*[/-]\s*[456])+\b", n):
        sizes |= set(re.findall(r"[456]", group))
    if len(sizes) > 1 or re.search(r"\bmix\b", n):
        return "PLO mix"
    size = sizes.pop() if sizes else ""
    return "PLO" + (size if size in ("5", "6") else "")


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
    if all("no games" in strip_tags(block).lower() for block in blocks):
        return []  # their list says "No games currently"
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
        return [] if "no cash game table is open" in strip_tags(html).lower() else None
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


# OlyBet cash games: per club a table of Game | Blinds | Buy-in | Tables | Players | Open seats | Waiting,
# read from the page text, e.g. "CLOSED Select NLH 1/3 Tables 0 €1/3 €200.00 0 0/0 (1 waiting) 0 1"
OLY_CLUB_RE = re.compile(r'href="([^"]*cash-games/?\?club=(\d+))"[^>]*>(.*?)</a>', re.S | re.I)
BLOCK_SIGNS = ("cf-chl", "just a moment", "attention required", "cf_chl_opt", "challenge-platform")
STAKES_TOKEN = re.compile(r"\d+(?:[.,]\d+)?(?:/\d+(?:[.,]\d+)?)+")


def oly_cash_rows(html):
    """Every listed game of the club shown on an OlyBet cash games page, read from the page's words:
    '<game> <stakes> Tables N' then €blinds, €buy-in, tables, players/seats, open seats, waiting -
    skipping any extra labels in between. None if the table can't be read (never a guessed zero)."""
    text = strip_tags(html).replace("€ ", "€")
    low = text.lower()
    a = low.find("choose up to two games")
    a = a if a >= 0 else low.find("open seats")
    if a < 0:
        return None
    b = low.find("registration", a)
    tokens = text[a: b if b > 0 else a + 8000].split()
    anchors = [i for i, token in enumerate(tokens)  # "<game> <stakes> Tables N" starts each game's row
               if token.lower() == "tables" and 2 <= i < len(tokens) - 1 and tokens[i + 1].isdigit()
               and STAKES_TOKEN.fullmatch(tokens[i - 1]) and re.search(r"[A-Za-z]", tokens[i - 2])]
    rows = []
    for n, i in enumerate(anchors):
        stop = anchors[n + 1] - 2 if n + 1 < len(anchors) else len(tokens)
        found, j = [], i + 2
        for pattern in (r"€(\d+(?:[.,]\d+)?(?:/\d+(?:[.,]\d+)?)+)", r"€([\d.,]+)", r"(\d+)", r"(\d+)/(\d+)", r"(\d+)", r"(\d+)"):
            while j < stop:
                m = re.fullmatch(pattern, tokens[j])
                j += 1
                if m:
                    found.append(m)
                    break
        if len(found) < 6:
            continue
        status = next((t for t in reversed(tokens[max(0, i - 5): i - 2]) if re.fullmatch(r"[A-Z]{4,15}", t)), "")
        rows.append({"game": card_game(tokens[i - 2]), "stakes": found[0].group(1).replace(",", "."),
                     "buyin": number(found[1].group(1).replace(",", "")), "tables": as_int(found[2].group(1)),
                     "players": as_int(found[3].group(1)), "seats": as_int(found[3].group(2)),
                     "open": as_int(found[4].group(1)), "waiting": as_int(found[5].group(1)), "status": status})
    return rows or None


def oly_tournament_text(html, club):
    """The 'Live' and 'Today' tournament lines on OlyBet's home page for one club (kept as text)."""
    text = strip_tags(html)
    low = text.lower()
    a = low.find("tournaments", low.find("live cash games") if "live cash games" in low else 0)
    if a < 0:
        return ""
    b = min([i for i in (low.find(k, a) for k in ("view more", "latest winners")) if i != -1] + [a + 4000])
    section = text[a:b]
    lines = re.split(r"(?=\b\d{1,2}:\d{2}\b)", section)
    keep = [ln.strip() for ln in lines[1:] if club in ln.lower()] or [ln.strip() for ln in lines[1:]]
    head = lines[0]
    live = "live" if re.search(r"\blive\b", head, re.I) else ""
    return shown(" | ".join(([live] if live else []) + keep), 1500)


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
            data = fetch_feed()
            save_sample("kings_cash_feed", data, lambda t: str(t.get("venue")) == VENUE)
            entries = feed_entries(data)
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
            data = fetch_feed(CLOCKS_URL)
            save_sample("kings_clocks_feed", data)
            result = tournament_entries(data, now, with_details=True)
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
    for path in sorted(DATA_DIR.glob(MONTH_FILES)):
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
    entries = [] if "no games" in cash.lower() else card_text_entries(cash)
    if not entries and cash.strip() and "no games" not in cash.lower():
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
    out += calendar_lines("cardcasino", now)
    out += busy_sections(ok, checks, "cardcasino")
    out += day_type_lines("cardcasino", ok)
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

    out += calendar_lines("grandcasinoas", now)
    all_ok = ok
    ok, note = split_days("grandcasinoas", ok)

    # running tables by hour and weekday
    total, count = defaultdict(float), defaultdict(int)
    for r in ok:
        for key in ((int(r["hour"]), r["weekday"]), (int(r["hour"]), "All")):
            total[key] += as_int(r["tables"])
            count[key] += 1
    out += ["## Running cash tables by hour", "", *([note, ""] if note else []),
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
    out += day_type_lines("grandcasinoas", all_ok, measure="tables")
    out += tournaments_seen_lines(with_t)
    out += ["---", "Raw data: `data/grandcasinoas` (one CSV file per month)."]
    GAS_PAGE.write_text("\n".join(out) + "\n", encoding="utf-8")


def oly_fetch(url, referer):
    """One ordinary page request. Returns (html, None) or (None, reason) - 'blocked' when the
    site's bot protection refuses it. Nothing is done to get around a refusal."""
    try:
        html = fetch_text(url, referer)
    except urllib.error.HTTPError as e:
        return None, "blocked by the site's bot protection" if e.code in (403, 429, 503) else f"HTTP error {e.code}"
    except Exception as e:
        return None, short_error(e)
    if any(sign in html[:20000].lower() for sign in BLOCK_SIGNS):
        return None, "blocked by the site's bot protection"
    return html, None


def record_olympic(now):
    """One check of each Olympic room (every 30 minutes). Never raises. Returns {key: row} for the
    rooms checked in this run (none on the in-between runs)."""
    if now.minute % 30 >= 10:
        return {}
    try:
        clubs = json.loads(OLY_CLUBS_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        clubs = {}
    clubs = {k: v for k, v in clubs.items() if isinstance(v, dict) and "://" in v.get("url", "")}
    results = {}
    for site in OLY_SITES:
        row = {"time": f"{now:%Y-%m-%d %H:%M}", "weekday": DAYS[now.weekday()], "hour": now.hour, "status": "",
               "club": "", "tables": "", "players": "", "waiting": "", "games": "", "listed": "",
               "tournaments_text": "", "raw": ""}
        details = {}
        try:
            known = clubs.get(site["key"])
            urls = ([known["url"]] if known else []) + site["urls"]
            html = rows = None
            for url in urls:
                html, problem = oly_fetch(url, site["home"])
                if html is None:
                    row["status"] = f"error: {problem}"
                    if "blocked" in problem:
                        break  # respect the refusal: no more requests to this site in this run
                    continue
                if not known:  # first time: find the club in the site's list and open its page
                    links = OLY_CLUB_RE.findall(html)
                    match = next(((urllib.parse.urljoin(url, unescape(link)), strip_tags(name))
                                  for link, _, name in links if site["club"] in strip_tags(name).lower()), None)
                    if not match:
                        row["status"] = f"error: no club matching '{site['club']}' on the page"
                        details["page_start"] = html[:20000]
                        break
                    known = clubs[site["key"]] = {"url": match[0], "name": match[1]}
                    html, problem = oly_fetch(known["url"], site["home"])
                    if html is None:
                        row["status"] = f"error: {problem}"
                        break
                shown_club = re.search(r"<h2[^>]*>\s*" + re.escape(known["name"]) + r"\s*</h2>", html, re.I)
                if not shown_club:
                    row["status"] = "error: couldn't confirm the page shows the right club"
                    details["page_start"] = html[:20000]
                    clubs.pop(site["key"], None)  # look it up again next time
                    break
                rows = oly_cash_rows(html)
                if rows is not None:
                    row["club"] = shown(known["name"], 60)
                    break
                details["page_start"] = html[:20000]
                row["status"] = "error: couldn't read the cash games table"
                break
            if rows is not None:
                running = [r for r in rows if r["tables"] > 0]
                entries = []
                for r in running:  # one entry per table; the site gives totals per game, so they're shared out evenly
                    players, seats = divmod(r["players"], r["tables"]), divmod(r["seats"], r["tables"])
                    entries += [f"{r['game']} €{r['stakes']} {players[0] + (i < players[1])}/{seats[0] + (i < seats[1])}"
                                for i in range(r["tables"])]
                row.update(status="ok", tables=sum(r["tables"] for r in rows), players=sum(r["players"] for r in rows),
                           waiting=sum(r["waiting"] for r in rows), games="; ".join(entries),
                           listed="; ".join(f"{r['game']} €{r['stakes']}: {count_text(r['tables'], 'table')}, "
                                            f"{r['players']}/{r['seats']} players, {r['waiting']} waiting" for r in rows))
            if now.minute < 10 and "blocked" not in row["status"]:  # tournaments once an hour
                home, problem = oly_fetch(site["home"], site["home"])
                if home is not None:
                    row["tournaments_text"] = oly_tournament_text(home, site["club"])
                elif problem:
                    details["tournaments"] = problem
        except Exception as e:
            row["status"] = f"error: {short_error(e)}"
        try:
            append_csv(DATA_DIR / site["key"], OLY_FIELDS, now, row)
            save_debug_copy(Path(f"debug/{site['key']}_page.json"), now, row["status"], site["urls"][0], details)
            write_olympic_page(site, now)
        except Exception as e:
            print(f"{site['name']} could not be saved: {short_error(e)}")
        results[site["key"]] = row
    try:
        OLY_CLUBS_FILE.write_text(json.dumps(clubs, indent=1), encoding="utf-8")
    except OSError:
        pass
    return results


def write_olympic_page(site, now):
    rows = load_csv_rows(DATA_DIR / site["key"])
    ok = [r for r in rows if r["status"] == "ok" and r["players"] != ""]
    checks = [(r, players_per_game(r)) for r in ok]
    out = [f"# 🃏 {site['name']} — cash game tracker", "",
           f"Reads [OlyBet's live cash games page]({site['urls'][0]}) every 30 minutes (their site has bot protection, so "
           "the tracker checks gently and simply records it when a check is refused). All times are **Czech time** "
           "(Tallinn and Vilnius are one hour ahead). Back to [King's](README.md).", ""]
    out += health_lines(rows, now, {}, f"debug/{site['key']}_page.json")
    if ok:
        latest = ok[-1]
        out += [f"**Club:** {latest['club']}", ""]
        out += snapshot_lines(latest)
        out += [f"**Waiting lists:** {latest['waiting'] or 0} players · **All games listed:** {shown(latest['listed'], 600)}", ""]
    with_t = [r for r in rows if r.get("tournaments_text")]
    if with_t:
        out += [f"**Tournaments on their site at {with_t[-1]['time']}:** {with_t[-1]['tournaments_text']}", ""]
    out += calendar_lines(site["key"], now)
    out += busy_sections(ok, checks, site["key"])
    out += day_type_lines(site["key"], ok)
    out += all_games_lines(ok)
    out += ["---", f"Raw data: `data/{site['key']}` (one CSV file per month)."]
    site["page"].write_text("\n".join(out) + "\n", encoding="utf-8")


def rewrite_csv(path, fields, rows):
    tmp = path.with_suffix(".tmp")
    with tmp.open("w", newline="", encoding="utf-8-sig") as fh:
        writer = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    tmp.replace(path)


def repair_history():
    """Fix rows earlier versions recorded wrongly. Safe to run every time: it only touches rows
    that match one of the known mistakes, and leaves everything else as it was."""
    fixes = [
        # Card Casino said "No games currently": that's 0 tables, not an error
        (CARD_DIR, CARD_FIELDS, lambda r: r["status"] == "error: couldn't read the cash games list" and "no games" in r["raw"].lower(),
         {"status": "ok", "source": "page table", "tables": 0, "players": 0, "games": "", "raw": ""}),
        # Grand Casino Aš showed "No Cash Game table is open": 0 tables, not an error
        (GAS_DIR, GAS_FIELDS, lambda r: r["status"] == "error: the 'Current cash game' table wasn't found",
         {"status": "ok", "tables": 0, "waiting": 0, "games": ""}),
    ]
    for site in OLY_SITES:  # the first Olympic version reported 0 tables without actually reading the table
        fixes.append((DATA_DIR / site["key"], OLY_FIELDS, lambda r: r["status"] == "ok" and not r["listed"],
                      {"status": "error: table not read (first version)", "tables": "", "players": "", "waiting": "", "games": ""}))
    for folder, fields, is_wrong, correction in fixes:
        for path in sorted(folder.glob("*.csv")):
            with path.open(newline="", encoding="utf-8-sig") as fh:
                rows = list(csv.DictReader(fh))
            changed = False
            for r in rows:
                if is_wrong(r):
                    r.update(correction)
                    changed = True
            if changed:
                rewrite_csv(path, fields, rows)


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
    if key in ROOMS:
        out += calendar_lines(key, datetime.now(TZ))
    out += ["---", "First version: the lists are saved exactly as the site shows them. Statistics per game "
            "and hour (like on the King's page) are added once a day of data shows the site's format.",
            f"Raw data: `data/{key}` (one CSV file per month)."]
    page_path.write_text("\n".join(out) + "\n", encoding="utf-8")


def load_rows():
    rows = []
    for path in sorted(DATA_DIR.glob(MONTH_FILES)):
        with path.open(newline="", encoding="utf-8-sig") as fh:
            rows.extend(csv.DictReader(fh))
    return rows


# ---------------------------------------------------------------- festivals, schedule and holidays

MONTHS = ("Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec")
_WD, _MON = "(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun)", "(?:" + "|".join(MONTHS) + ")"
HM_LINE = re.compile(rf"^(?P<d1>{_WD}) (?P<n1>\d{{1,2}})(?: (?P<m1>{_MON}))?(?: - (?P<d2>{_WD}) (?P<n2>\d{{1,2}}) (?P<m2>{_MON}))?"
                     rf"(?: at (?P<t>\d{{1,2}}:\d{{2}} ?[ap]m))?\s+(?P<rest>\S.*)$", re.I)
HM_ROOM_RES = [(re.compile(r"\s*".join(re.escape(part) for part in name.replace("(", " ( ").replace(")", " ) ")
                                         .replace(",", " , ").split()), re.I), key) for name, key in HM_ROOMS]
BUYIN_RE = re.compile(r"^(?:[A-Z]{2,6} )?€\s*(\d[\d,]*(?:\s*\+\s*\d[\d,]*)*)")
TYPE_ICON = {"festival": "🎪", "cash event": "💵", "series": "🎟️", "nearby": "📍"}
CONTEXT = {"calendar": [], "schedule": [], "holidays": {}}  # filled once per run by setup_context()


def cal_text(text, limit=200):
    """Calendar and schedule text for the pages: only characters that could break a markdown table go."""
    text = " ".join(re.sub(r"[|`<>*\[\]]", " ", str(text or "")).split())
    return text if len(text) <= limit else text[:limit - 1].rsplit(" ", 1)[0] + " …"


def event_name(title):
    """A schedule title without its buy-in prefix ('€ 300 + 40 Pot Limit Omaha - Main Event' -> 'Pot Limit Omaha - Main Event')."""
    buy = BUYIN_RE.match(title)
    return title[buy.end():].strip(" -") if buy else title


def day_icon(room, day):
    for c in CONTEXT["calendar"]:
        if c["room"] == room and c["type"] in FESTIVAL_TYPES and c["start_d"].isoformat() <= day <= c["end_d"].isoformat():
            return TYPE_ICON.get(c["type"], "🎪")
    return "📅"


def hm_day(weekday, day, month, today):
    """The date of e.g. 'Sat 10 Oct': the nearest year in which that day really is a Saturday."""
    options = []
    for year in (today.year - 1, today.year, today.year + 1):
        try:
            d = date(year, month, day)
        except ValueError:
            continue
        options.append((DAYS[d.weekday()] != weekday.title(), abs((d - today).days), d))
    return min(options)[2] if options else None


def hm_kind(title):
    t = title.lower()
    if "cash game challenge" in t:
        return "cash"
    if re.search(r"party|dinner|lunch|slots|blackjack|roulette|sportsbook|chicago|flip finals", t):
        return "other"
    if re.search(r"satell?ite|qualifier|flip\W*(?:n|&)\W*go to", t):
        return "satellite"
    return "tournament"


def parse_hendonmob(text, today):
    """The events at the tracked rooms in a copied Hendon Mob 'upcoming events' page (other lines are ignored)."""
    events = []
    for raw in (text or "").splitlines():
        line = " ".join(raw.replace("’", "'").replace("´", "'").split())
        m = HM_LINE.match(line)
        if not m:
            continue
        rest = m.group("rest")
        found = next(((regex.search(rest), key) for regex, key in HM_ROOM_RES if regex.search(rest)), None)
        if not found:
            continue
        venue, room = found
        title = rest[:venue.start()].rstrip(" ,")
        for country in ("Czech Republic", "Slovakia", "Estonia", "Lithuania"):
            if title.startswith(country + " "):
                title = title[len(country) + 1:].strip()
                break
        month = m.group("m1") or m.group("m2")
        start = hm_day(m.group("d1"), int(m.group("n1")), MONTHS.index(month.title()) + 1, today) if month else None
        if not title or not start:
            continue
        end = start
        if m.group("n2"):
            end = hm_day(m.group("d2"), int(m.group("n2")), MONTHS.index(m.group("m2").title()) + 1, today) or start
            end = end if timedelta(0) <= end - start <= timedelta(days=60) else start
        buy = BUYIN_RE.match(title)
        kind = hm_kind(title)
        clock = datetime.strptime(m.group("t").replace(" ", "").upper(), "%I:%M%p") if m.group("t") else None
        events.append({"room": room, "date": start.isoformat(), "end": end.isoformat() if end != start else "",
                       "time": f"{clock:%H:%M}" if clock else "", "kind": kind,
                       "game": "Other" if kind == "other" else tourney_game(title),
                       "buyin": str(sum(int(x.replace(",", "")) for x in re.findall(r"\d[\d,]*", buy.group(1)))) if buy else "",
                       "title": title[:150], "restricted": "yes" if "restricted" in rest[venue.end():].lower() else ""})
    return events


def hm_last_day(text, today):
    """The last day a copied Hendon Mob page covers (any venue), so events past it are never touched."""
    last = None
    for raw in (text or "").splitlines():
        m = HM_LINE.match(" ".join(raw.split()))
        month = m and (m.group("m1") or m.group("m2"))
        if month:
            d = hm_day(m.group("d1"), int(m.group("n1")), MONTHS.index(month.title()) + 1, today)
            last = max(last, d) if last and d else d or last
    return last


def merge_schedule(known, events, since, last_day):
    """Add a fresh copy's events. For the rooms it lists, it has the final word on the days from
    `since` (when it was pasted) to the last day it covers: anything it no longer lists there was moved
    or cancelled and is dropped. Older days are never touched, so the history stays complete."""
    fresh = {(e["room"], e["date"], e["time"], e["title"]): e for e in events}
    rooms = {e["room"] for e in events}
    for key in list(known):
        if key[0] in rooms and since <= key[1] <= last_day and key not in fresh:
            del known[key]
    known.update(fresh)
    return known


def update_schedule(today):
    """Every event read from hendonmob.txt so far, kept in data/schedule/events.csv: replacing hendonmob.txt with a
    fresh copy adds new events and keeps the old ones, so past days can still be compared."""
    known = {}
    try:
        with SCHEDULE_FILE.open(newline="", encoding="utf-8-sig") as fh:
            for r in csv.DictReader(fh):
                known[(r["room"], r["date"], r["time"], r["title"])] = {k: r.get(k) or "" for k in SCHEDULE_FIELDS}
    except OSError:
        pass
    saved = {k: dict(v) for k, v in known.items()}
    try:
        text = HENDONMOB_FILE.read_text(encoding="utf-8", errors="replace")
    except OSError:
        text = ""
    events = parse_hendonmob(text, today)
    if events:
        try:
            state = json.loads(PASTE_STATE.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            state = {}
        digest = hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]
        if state.get("hash") != digest:  # a new copy: it speaks for the days from today on
            state = {"hash": digest, "from": today.isoformat()}
            PASTE_STATE.parent.mkdir(parents=True, exist_ok=True)
            PASTE_STATE.write_text(json.dumps(state), encoding="utf-8")
        last = hm_last_day(text, today) or today
        merge_schedule(known, events, state.get("from", today.isoformat()), last.isoformat())
    for e in known.values():  # re-read the game of older rows too, in case the reading has improved
        e["kind"] = hm_kind(e["title"])
        e["game"] = "Other" if e["kind"] == "other" else tourney_game(e["title"])
    rows = sorted(known.values(), key=lambda r: (r["date"], r["time"], r["room"], r["title"]))
    if known != saved:
        SCHEDULE_FILE.parent.mkdir(parents=True, exist_ok=True)
        rewrite_csv(SCHEDULE_FILE, SCHEDULE_FIELDS, rows)
    return rows


def calendar_day(text):
    for fmt in ("%Y-%m-%d", "%d.%m.%Y", "%d/%m/%Y"):
        try:
            return datetime.strptime(text.strip(), fmt).date()
        except ValueError:
            continue
    return None


def load_calendar():
    """calendar.csv: one line per festival, series or cash-game event (also if saved by Excel with ';')."""
    try:
        text = CALENDAR_FILE.read_text(encoding="utf-8-sig")
    except OSError:
        return []
    first = text.split("\n", 1)[0]
    out = []
    for r in csv.DictReader(text.splitlines(), delimiter=";" if first.count(";") > first.count(",") else ","):
        r = {str(k).strip().lower(): (v or "").strip() for k, v in r.items() if k}
        start, end = calendar_day(r.get("start", "")), calendar_day(r.get("end", "") or r.get("start", ""))
        if not (start and r.get("room") and r.get("name")):
            continue
        out.append({**r, "type": r.get("type", "").lower() or "festival", "start_d": start, "end_d": max(start, end or start)})
    return sorted(out, key=lambda c: (c["start_d"], c["room"]))


def load_holidays(now):
    """Public holidays in each room's main player countries, worked out once a day with the 'holidays'
    package (installed on first use) and kept in data/holidays.json. If that fails, they're left out."""
    today = f"{now:%Y-%m-%d}"
    cache = {}
    try:
        cache = json.loads(HOLIDAY_FILE.read_text(encoding="utf-8"))
        if cache.get("made") == today:
            return cache.get("rooms", {})
    except (OSError, ValueError, AttributeError):
        cache = {}
    try:
        try:
            import holidays as hol
        except ImportError:
            subprocess.run([sys.executable, "-m", "pip", "install", "-q", "holidays"], check=True, timeout=180)
            import importlib
            importlib.invalidate_caches()
            import holidays as hol
        years = list(range(now.year - 1, now.year + 2))
        rooms = {}
        for room, (_, _, markets) in ROOMS.items():
            days = defaultdict(lambda: defaultdict(list))
            for country, subdiv, label in markets:
                try:
                    found = hol.country_holidays(country, subdiv=subdiv, years=years, language="en_US")
                except Exception:
                    found = hol.country_holidays(country, subdiv=subdiv, years=years)
                for day, names in found.items():
                    for name in str(names).split("; "):
                        days[day.isoformat()][name].append(label)
            rooms[room] = {d: dict(names) for d, names in sorted(days.items())}
        HOLIDAY_FILE.write_text(json.dumps({"made": today, "rooms": rooms}, ensure_ascii=False, indent=1), encoding="utf-8")
        return rooms
    except Exception as e:
        print(f"Public holidays unavailable this run: {short_error(e)}")
        return cache.get("rooms", {})


def setup_context(now):
    CONTEXT["calendar"] = load_calendar()
    CONTEXT["schedule"] = update_schedule(now.date())
    CONTEXT["holidays"] = load_holidays(now)
    day_info.cache_clear()


def holiday_text(names):
    return "; ".join(f"{name} ({', '.join(labels)})" for name, labels in names.items())


@lru_cache(maxsize=None)
def day_info(room, day):
    """What kind of day it was at a room: ('festival', name), ('holiday', names) or ('normal', '')."""
    try:
        d = date.fromisoformat(day)
    except ValueError:
        return "normal", ""
    for c in CONTEXT["calendar"]:
        if c["room"] == room and c["type"] in FESTIVAL_TYPES and c["start_d"] <= d <= c["end_d"]:
            return "festival", c["name"]
    names = CONTEXT["holidays"].get(room, {}).get(day)
    return ("holiday", holiday_text(names)) if names else ("normal", "")


def day_tag(room, day):
    kind, label = day_info(room, day)
    return f" {day_icon(room, day)} {label}" if kind == "festival" else " 📅 public holiday" if kind == "holiday" else ""


def omaha_event(e):
    """An Omaha tournament, or a mix that includes Omaha (satellites and side events left out)."""
    if e["kind"] != "tournament":
        return False
    return tourney_family(e["game"]) == "PLO" or (e["game"] == "Mixed" and bool(re.search(r"\bplo\d?\b|omaha|\bbig o\b", e["title"], re.I)))


def nice_dates(start, end):
    if start == end:
        return f"{start.day} {start:%b}"
    if (start.year, start.month) == (end.year, end.month):
        return f"{start.day}–{end.day} {end:%b}"
    return f"{start.day} {start:%b} – {end.day} {end:%b}"


def uncovered_main_events(room, today):
    """Main-event days on the schedule that no calendar.csv line covers yet - the cue to add a festival."""
    covered = [(c["start_d"], c["end_d"]) for c in CONTEXT["calendar"] if c["room"] == room]
    found = {}
    for e in CONTEXT["schedule"]:
        if e["room"] != room or e["kind"] != "tournament" or not re.search(r"main event|\bme\b", e["title"], re.I):
            continue
        d = date.fromisoformat(e["date"])
        if d >= today and not any(a <= d <= b for a, b in covered):
            found.setdefault(d, e)
    return sorted(found.items())


def calendar_lines(room, now):
    """Festivals now and next, Omaha tournaments in the next two weeks and coming public holidays."""
    today = now.date()
    if not (CONTEXT["calendar"] or CONTEXT["schedule"] or CONTEXT["holidays"]):
        return []
    out = ["## Festivals and schedule", ""]
    cal = [c for c in CONTEXT["calendar"] if c["room"] == room and c["end_d"] >= today]
    shown_rows = [("Now", c) for c in cal if c["start_d"] <= today] + [("Coming up", c) for c in cal if c["start_d"] > today][:4]
    for label, c in shown_rows:
        details = " · ".join(x for x in (cal_text(c.get("notes"), 300),
                                         f"Omaha: {cal_text(c['omaha_events'], 900)}" if c.get("omaha_events") else "") if x)
        out.append(f"- **{label}:** {TYPE_ICON.get(c['type'], '')} **{cal_text(c['name'], 80)}**, "
                   f"{nice_dates(c['start_d'], c['end_d'])} ({c['type']})" + (f" — {details}" if details else ""))
    if not shown_rows:
        out.append("- No festivals listed for this room in `calendar.csv`.")
    missing = uncovered_main_events(room, today)
    if missing:
        days = ", ".join(f"{d.day} {d:%b}" for d, _ in missing[:8]) + (" …" if len(missing) > 8 else "")
        out.append(f"- ⚠️ **Not in `calendar.csv` yet:** Hendon Mob lists main-event days on {days} "
                   f"(e.g. “{cal_text(event_name(missing[0][1]['title']), 70)}”). Add a line for that festival or "
                   "series, so its days are compared separately instead of counting as normal days.")
    soon = [e for e in CONTEXT["schedule"] if e["room"] == room and omaha_event(e)
            and today <= date.fromisoformat(e["date"]) <= today + timedelta(days=14)]
    if soon:
        out += ["", "**Omaha tournaments in the next 14 days** (from `hendonmob.txt`):", "",
                "| Day | Time (local) | Buy-in | Tournament |", "|:--|:--|--:|:--|"]
        for e in soon[:15]:
            d = date.fromisoformat(e["date"])
            when = f"{DAYS[d.weekday()]} {d.day} {d:%b}"
            if e["end"]:
                last = date.fromisoformat(e["end"])
                when += f" – {DAYS[last.weekday()]} {last.day} {last:%b}"
            out.append(f"| {when} | {e['time'] or '·'} | {money(int(e['buyin'])) if e['buyin'] else '·'} "
                       f"| {cal_text(event_name(e['title']), 90)} |")
    elif any(e["room"] == room for e in CONTEXT["schedule"]):
        out += ["", "No Omaha tournaments on the schedule in the next 14 days."]
    holidays = CONTEXT["holidays"].get(room, {})
    if holidays:
        markets = ", ".join(label for _, _, label in ROOMS[room][2])
        last = (today + timedelta(days=30)).isoformat()
        coming = [(d, names) for d, names in holidays.items() if today.isoformat() <= d <= last]
        text = " · ".join(f"{DAYS[date.fromisoformat(d).weekday()]} {date.fromisoformat(d).day} "
                          f"{date.fromisoformat(d):%b}: {holiday_text(names)}" for d, names in coming)
        out += ["", f"**Public holidays in the next 30 days** where most players come from ({markets}): {text or 'none'}."]
    return out + [""]


def all_rooms_calendar_lines(now, limit=30):
    today = now.date()
    rows = [c for c in CONTEXT["calendar"] if c["end_d"] >= today]
    if not rows:
        return []
    out = ["## Coming up at all rooms", "",
           "From `calendar.csv` — open it on GitHub and use the pencil button to add or correct dates. "
           "🎪 festival · 💵 cash-game event · 🎟️ smaller series · 📍 nearby, not tracked.", "",
           "| Dates | Room | Event | Omaha |", "|:--|:--|:--|:--|"]
    gaps = [ROOMS[room][0] for room in ROOMS if uncovered_main_events(room, today)]
    if gaps:
        out[3:3] = [f"⚠️ Main events on the schedule that `calendar.csv` doesn't cover yet: {', '.join(gaps)} "
                    "(details on their pages).", ""]
    for c in rows[:limit]:
        name, page = ROOMS[c["room"]][:2] if c["room"] in ROOMS else (c["room"], "")
        room_cell = f"[{name}]({page})" if page else name
        when = nice_dates(c["start_d"], c["end_d"]) + (" **now**" if c["start_d"] <= today else "")
        out.append(f"| {when} | {room_cell} | {TYPE_ICON.get(c['type'], '')} {cal_text(c['name'], 60)} "
                   f"| {cal_text(c.get('omaha_events'), 500) or '·'} |")
    return out + [""]


def split_days(room, rows):
    """The rows for a page's main statistics: normal days only, once at least two normal days have been
    recorded. Returns (rows, a note saying which days are included)."""
    if not room or not rows:
        return rows, ""
    normal = [r for r in rows if day_info(room, r["time"][:10])[0] == "normal"]
    special = len(rows) - len(normal)
    if not special:
        return rows, ""
    if len({r["time"][:10] for r in normal}) >= 2:
        return normal, (f"*Normal days only: {count_text(special, 'check')} during festivals, cash-game events or "
                        "public holidays are compared separately in “Festivals, holidays and normal days” below.*")
    return rows, ("*All days: fewer than two normal days recorded so far, so these include festival and holiday "
                  "days (compared separately below).*")


def day_type_lines(room, ok, measure="players"):
    """Normal days, each festival and public holidays side by side, adjusted for the hour of day."""
    groups = defaultdict(list)
    for r in ok:
        kind, label = day_info(room, r["time"][:10])
        groups[(kind, label if kind == "festival" else "")].append(r)
    if not groups or set(groups) == {("normal", "")}:
        return []

    def value(r):
        return as_int(r["players"] if measure == "players" else r["tables"])

    def families(r):
        found = Counter()
        if measure == "players":
            for game, _, seated, _ in parse_games(r["games"]):
                found[family(game)] += seated
        else:
            for game, _, status in parse_gas_games(r["games"]):
                found[family(game)] += status == "RUNNING"
        return found

    hours = defaultdict(list)
    for r in groups.get(("normal", ""), []):
        hours[int(r["hour"])].append(value(r))
    usual = {h: sum(v) / len(v) for h, v in hours.items()}
    schedule_days = {e["date"] for e in CONTEXT["schedule"] if e["room"] == room}
    omaha_days = {e["date"] for e in CONTEXT["schedule"] if e["room"] == room and omaha_event(e)}
    first_listed = min(schedule_days) if schedule_days else None

    def line(label, rows):
        dates = sorted({r["time"][:10] for r in rows})
        fam = [families(r) for r in rows]
        diffs = [value(r) - usual[int(r["hour"])] for r in rows if int(r["hour"]) in usual]
        span = f"{nice_dates(date.fromisoformat(dates[0]), date.fromisoformat(dates[-1]))} ({count_text(len(dates), 'day')})"
        return (f"| {label} | {span} | {len(rows)} | {sum(value(r) for r in rows) / len(rows):.1f} "
                f"| {sum(f['NLH'] for f in fam) / len(rows):.1f} | {sum(f['PLO'] for f in fam) / len(rows):.1f} "
                f"| {(f'{sum(diffs) / len(diffs):+.1f}' if diffs else '·')} |")

    markets = ", ".join(label for _, _, label in ROOMS[room][2])
    what = "seated players" if measure == "players" else "running tables"
    out = ["## Festivals, holidays and normal days", "",
           f"Average {what} per check on each kind of day, in total and for NLH and Omaha games. “vs normal” "
           "compares every check with normal days at the same hour, so days that happened to be checked mostly in "
           "the evening don't look busier just because evenings are. Festival dates: `calendar.csv`; public "
           f"holidays: those of the countries most players come from ({markets}).", "",
           f"| Days | Dates | Checks | {'Players' if measure == 'players' else 'Tables'} | NLH | Omaha | vs normal, same hour |",
           "|:--|:--|--:|--:|--:|--:|--:|"]
    for key in sorted(groups, key=lambda g: ({"normal": 0, "festival": 1, "holiday": 2}[g[0]], min(r["time"] for r in groups[g]))):
        rows = groups[key]
        icon = day_icon(room, rows[0]["time"][:10]) if key[0] == "festival" else ""
        out.append(line({"normal": "Normal days", "festival": f"{icon} {cal_text(key[1], 50)}", "holiday": "📅 Public holidays"}[key[0]], rows))
        if key == ("normal", "") and first_listed:
            listed = [r for r in rows if r["time"][:10] >= first_listed]
            with_o = [r for r in listed if r["time"][:10] in omaha_days]
            without = [r for r in listed if r["time"][:10] not in omaha_days]
            if with_o and without:
                out += [line("↳ with an Omaha tournament on the schedule", with_o), line("↳ without one", without)]
    return out + [""]


def save_sample(name, data, keep=None):
    """Once a day, keep a few raw records of a data feed and the list of all its fields - to spot
    details worth recording that the tracker doesn't use yet (debug/samples/)."""
    path = SAMPLE_DIR / f"{name}.json"
    today = f"{datetime.now(TZ):%Y-%m-%d}"
    try:
        if json.loads(path.read_text(encoding="utf-8")).get("saved_on") == today:
            return
    except (OSError, ValueError, AttributeError):
        pass
    try:
        records = data if isinstance(data, list) else [data]
        records = [r for r in records if keep is None or (isinstance(r, dict) and keep(r))] or records
        fields = sorted({str(k) for r in records if isinstance(r, dict) for k in r})
        SAMPLE_DIR.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"saved_on": today, "records": len(records), "fields": fields, "sample": records[:5]},
                                   ensure_ascii=False, indent=1, default=str), encoding="utf-8")
    except Exception:
        pass


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


def busy_sections(ok, checks, room=None):
    """Busiest times, average players by hour per game, and how often each game + stake runs
    (normal days only once there are enough of them - see split_days)."""
    kept, note = split_days(room, ok)
    if kept is not ok:
        ids = {id(r) for r in kept}
        ok, checks = kept, [(r, pg) for r, pg in checks if id(r) in ids]
    games = main_games(checks) if checks else []
    out = ["## Busiest times so far", ""] + ([note, ""] if note else [])
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


def overview_line(kings_row, card_row, banco_row, gas_row=None, oly_rows=None, day=None):
    """One line at the top of the King's page: what's running at every room right now."""
    day = day or f"{datetime.now(TZ):%Y-%m-%d}"
    def cash(row):
        if row and row.get("status") == "ok" and row.get("players", "") != "":
            return f"{count_text(row['tables'], 'table')}, {count_text(row['players'], 'player')}"
        return "couldn't be read"
    parts = [f"King's{day_tag('kings', day)}: {cash(kings_row)}",
             f"[Card Casino Šamorín](CARD_CASINO.md){day_tag('cardcasino', day)}: {cash(card_row)}"]
    if gas_row:
        gas = ("couldn't be read" if gas_row.get("status") != "ok"
               else f"{count_text(gas_row['tables'], 'table')} running" + (f", {gas_row['waiting']} waiting" if as_int(gas_row["waiting"]) else ""))
        parts.append(f"[Grand Casino Aš](GRAND_CASINO_AS.md){day_tag('grandcasinoas', day)}: {gas}")
    for site in OLY_SITES:
        row = (oly_rows or {}).get(site["key"])
        if row:
            text = cash(row) + (f" ({row['waiting']} waiting)" if as_int(row.get("waiting")) else "") \
                if row.get("status") == "ok" else ("blocked" if "blocked" in row.get("status", "") else "couldn't be read")
            parts.append(f"[{site['name'].replace(' Casino', '')}]({site['page'].name}){day_tag(site['key'], day)}: "
                         f"{text} at {row['time'][11:]}")
    if banco_row:
        listed = shown((banco_row.get("cash_text") or "").replace(" ; ", " ").replace(" | ", ", "), 70)
        banco = "couldn't be read" if banco_row.get("status") != "ok" else listed or "no games listed"
        parts.append(f"[Banco](BANCO.md){day_tag('banco', day)}: {banco}")
    return "**Right now:** " + " · ".join(parts)


def write_readme(rows, now, overview=""):
    ok = [r for r in rows if r["status"] == "ok" and r["players"] != ""]
    checks = [(r, players_per_game(r)) for r in ok]
    out = ["# 🃏 King's Rozvadov — cash game tracker", "",
           "Checks King's live cash games and tournaments about every 10 minutes and updates this page by itself. "
           "All times are **Czech time** (same as Poland). Also tracking: [Card Casino Šamorín](CARD_CASINO.md) · "
           "[Grand Casino Aš](GRAND_CASINO_AS.md) · [Banco Casino Bratislava](BANCO.md) · "
           "[Olympic Park Tallinn](OLYMPIC_TALLINN.md) · [Olympic Casino Vilnius](OLYMPIC_VILNIUS.md).", ""]
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

    out += calendar_lines("kings", now)
    out += all_rooms_calendar_lines(now)
    out += busy_sections(ok, checks, "kings")
    out += day_type_lines("kings", ok)

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
            "The tracker is `tracker.py`; its schedule is in `.github/workflows/track.yml`.  ",
            "Festival dates: `calendar.csv` (edit on GitHub). Tournament schedule: `hendonmob.txt` — to refresh it, "
            "copy the Hendon Mob upcoming-events page and paste it over that file's contents; every event read so far "
            "is kept in `data/schedule/events.csv`. Public holidays: `data/holidays.json`."]
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
    more = {"€ 1,100 Pot Limit Omaha - PLO4/PLO5 Championship Day 1 (Event #10)": "PLO mix",
            "€ 85 + 15 Pot Limit Omaha - 4-5-6 in the Mix (PLO4/5/6)": "PLO mix",
            "€ 175 + 25 Omaha Dealers Choice (Event #12)": "PLO mix", "€ 310 + 40 Pot Limit Dealers Choice": "Mixed",
            "€ 350 Pot Limit Sviten - PLO5 & Draw (Event #15)": "Mixed",
            "€ 170 + 30 No Limit Hold'em / Pot Limit Omaha - Half n Half": "Mixed",
            "€ 1,500 WSOPC Big O (Ring Event #3)": "PLO5 Hi-Lo", "€ 350 Pot Limit Omaha - PLO4 HI-LO/PLO5 HI-LO": "PLO Hi-Lo",
            "€ 500 + 50 Pot Limit Omaha - 550er PLO5 Highroller": "PLO5", "€ 250 Pot Limit - 2-7 Triple Draw": "Mixed",
            "€ 125 Pot Limit Omaha": "PLO", "€ 310 + 40 Pot Limit Omaha 4/5/6 (Event #22)": "PLO mix",
            "€ 50 + 10 Pot Limit Omaha - 4/5/6 Masters 7 Max": "PLO mix", "€ 295 No Limit Hold'em - BPC Main Event": "NLH",
            "€ 1,500 No Limit Hold'em - WSOPC Monster Stack (Ring Event #15)": "NLH", "€ 220 + 30 Mixed Games - H.O.R.S.E.": "Mixed"}
    assert {n: tourney_game(n) for n in more} == more, {n: tourney_game(n) for n in more if tourney_game(n) != more[n]}
    paste = ("10-Oct-2026\tSaturday\nSat 10 Oct at 3:00pm\tCzech Republic\t€ 125 Pot Limit Omaha, King's Resort Live, Rozvadov\n"
             "Sat 10 Oct at 2:00pm\tWales\t£ 100 No Limit Hold'em, Les Croupiers, Cardiff\n"
             "Fri 30 Oct - Sun 1 Nov at 2:00pm  Czech Republic  € 500 No Limit Hold'em - WSOPC King's German Championship "
             "(Ring Event #6) Day 1, King’s Resort Live, Rozvadov\n"
             "Sun 11 - Mon 12 Oct at 2:00pm\tEstonia\tKOT € 1,100 + 100 Pot Limit Omaha - PLO4/PLO5 Championship Day 1 (Event #10), "
             "Olympic Park Casino, Tallinn\n"
             "Fri 16 Oct at 3:00pm\tCzech Republic\t€ 120 No Limit Hold'em - DPM Ladies Event, King's Resort Live, Rozvadov Entry restricted\n"
             "Sat 17 Oct at 6:00pm\tCzech Republic\t€ 34 + 6 Flip´n Go Satellite to PLO ME, Grand Casino Asch (Aš), Asch\n"
             "Tue 24 Nov at 8:00pm\tEstonia\t€ 200 Cash Game Challenge (Event #30), Olympic Park Casino, Tallinn\n"
             "Fri 9 - Sun 11 Oct\tEstonia\t€ 250 No Limit Hold'em - Mini-Main (Event #2), Olympic Park Casino, Tallinn\n")
    got = [(e["room"], e["date"], e["end"], e["time"], e["kind"], e["game"], e["buyin"], e["restricted"])
           for e in parse_hendonmob(paste, date(2026, 10, 10))]
    assert got == [("kings", "2026-10-10", "", "15:00", "tournament", "PLO", "125", ""),
                   ("kings", "2026-10-30", "2026-11-01", "14:00", "tournament", "NLH", "500", ""),
                   ("olympic-tallinn", "2026-10-11", "2026-10-12", "14:00", "tournament", "PLO mix", "1200", ""),
                   ("kings", "2026-10-16", "", "15:00", "tournament", "NLH", "120", "yes"),
                   ("grandcasinoas", "2026-10-17", "", "18:00", "satellite", "PLO", "40", ""),
                   ("olympic-tallinn", "2026-11-24", "", "20:00", "cash", "NLH", "200", ""),
                   ("olympic-tallinn", "2026-10-09", "2026-10-11", "", "tournament", "NLH", "250", "")], got
    assert parse_hendonmob(paste, date(2027, 1, 20))[0]["date"] == "2026-10-10"  # the year follows the weekday
    saved = dict(CONTEXT)
    try:
        CONTEXT.update(calendar=[{"room": "kings", "type": "festival", "name": "WSOPC", "start_d": date(2026, 10, 28),
                                  "end_d": date(2026, 11, 11)}],
                       schedule=[], holidays={"kings": {"2026-10-28": {"Independent Czechoslovak State Day": ["Czechia"]},
                                                        "2026-11-17": {"Freedom Day": ["Czechia"]}}})
        day_info.cache_clear()
        assert day_info("kings", "2026-10-28") == ("festival", "WSOPC")  # a festival outranks the holiday
        assert day_info("kings", "2026-11-17") == ("holiday", "Freedom Day (Czechia)")
        assert day_info("kings", "2026-11-12") == ("normal", "") and day_info("cardcasino", "2026-10-30") == ("normal", "")
        rows = [{"time": f"2026-11-{d:02d} 20:00", "hour": "20", "players": "30", "games": "NLH €2/4 8/8"} for d in (12, 13)]
        rows += [{"time": "2026-10-29 20:00", "hour": "20", "players": "50", "games": "PLO5 €5/5 8/8"}]
        kept, note = split_days("kings", rows)
        assert len(kept) == 2 and "Normal days only" in note
        table = "\n".join(day_type_lines("kings", rows))
        assert "| 🎪 WSOPC | 29 Oct (1 day) | 1 | 50.0 | 0.0 | 8.0 | +20.0 |" in table, table
        assert day_tag("kings", "2026-10-30") == " 🎪 WSOPC" and day_tag("kings", "2026-11-17") == " 📅 public holiday"
        assert event_name("€ 300 + 40 Pot Limit Omaha - Main Event") == "Pot Limit Omaha - Main Event"
        old = {("kings", "2026-10-09", "15:00", "Past event"): {}, ("kings", "2026-10-20", "15:00", "Cancelled"): {},
               ("kings", "2026-12-30", "15:00", "Beyond the new copy"): {}, ("banco", "2026-10-20", "18:00", "Other room"): {},
               ("kings", "2026-10-21", "14:00", "Moved"): {}}
        new = [{"room": "kings", "date": "2026-10-21", "time": "16:00", "title": "Moved"}]
        assert sorted(merge_schedule(old, new, "2026-10-11", "2026-12-19")) == [
            ("banco", "2026-10-20", "18:00", "Other room"), ("kings", "2026-10-09", "15:00", "Past event"),
            ("kings", "2026-10-21", "16:00", "Moved"), ("kings", "2026-12-30", "15:00", "Beyond the new copy")]
        CONTEXT["schedule"] = [{"room": "kings", "date": "2026-11-12", "kind": "tournament", "title": "€ 500 NLH - Main Event Day 1A"},
                               {"room": "kings", "date": "2026-11-02", "kind": "tournament", "title": "€ 500 NLH - Main Event Day 1A"},
                               {"room": "kings", "date": "2026-11-13", "kind": "satellite", "title": "Satellite to ME"}]
        assert [d.isoformat() for d, _ in uncovered_main_events("kings", date(2026, 10, 11))] == ["2026-11-12"]
        assert cal_text("€199 main event; €350 high roller 11–12 Oct | x") == "€199 main event; €350 high roller 11–12 Oct x"
    finally:
        CONTEXT.update(saved)
        day_info.cache_clear()
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
    oly_page = ("<h2>Olympic Park Casino</h2><p>Choose up to two games and register</p> REGISTER GAME BLINDS BUY-IN TABLES "
                "PLAYERS OPEN SEATS WAITING CLOSED Select NLH 1/3 Tables 0 €1/3 €200.00 0 0/0 (1 waiting) 0 1 "
                "Select PLO 5/5 Tables 2 €5/5 €300.00 2 15/18 3 4 CLOSED Select NLH 5/5 Tables 0 €5/5 €300.00 0 0/0 0 0 "
                "REGISTER Registration Name Surname")
    rows = oly_cash_rows(oly_page)
    assert [(r["game"], r["stakes"], r["tables"], r["players"], r["seats"], r["waiting"], r["status"]) for r in rows] == \
        [("NLH", "1/3", 0, 0, 0, 1, "CLOSED"), ("PLO", "5/5", 2, 15, 18, 4, ""), ("NLH", "5/5", 0, 0, 0, 0, "CLOSED")], rows
    with_labels = oly_page.replace("€1/3 €200.00", "Blinds € 1/3 Buy-in &euro;200.00").replace("2 15/18 3 4", "Tables 2 Players 15/18 Open 3 Waiting 4")
    assert [(r["game"], r["tables"], r["players"], r["waiting"]) for r in oly_cash_rows(with_labels)] == \
        [("NLH", 0, 0, 1), ("PLO", 2, 15, 4), ("NLH", 0, 0, 0)], oly_cash_rows(with_labels)
    assert oly_cash_rows("<p>nothing here</p>") is None
    assert oly_cash_rows("<p>Choose up to two games and register</p> something else entirely") is None
    assert card_entries('<div class="splide__slide">\r\n <div class="cash-game aligner">\r\n <h4>No games currently</h4>\r\n </div>\r\n</div>') == []
    assert gas_cash_entries("<p>Back to home</p><p>No Cash Game table is open at this time</p>") == []
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
    try:
        setup_context(now)
    except Exception as e:  # the calendar is extra: a problem with it never stops the tracking
        print(f"Festival calendar / schedule / holidays skipped: {short_error(e)}")

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
    repair_history()
    card_row = record_card(now)
    gas_row = record_gas(now)
    record_olympic(now)
    site_rows = record_sites(now)
    latest_oly = {}
    for site in OLY_SITES:
        oly = load_csv_rows(DATA_DIR / site["key"])
        if oly:
            latest_oly[site["key"]] = oly[-1]
    rows = load_rows()
    write_readme(rows, now, overview_line(row, card_row, site_rows.get("banco"), gas_row, latest_oly, f"{now:%Y-%m-%d}"))
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
