#!/usr/bin/env python3
"""
King's Resort Rozvadov - cash game tracker
==========================================
Runs on GitHub Actions about every 15 minutes. Each run:
  1. reads the running cash tables from King's own data feed (the one their live page uses);
     if that ever fails, it opens the live page in a headless browser and reads it like a visitor,
  2. adds one line to data/YYYY-MM.csv (Czech local time),
  3. rebuilds README.md with statistics per game.

Games are named the way the poker room's own system names them (NLH, PLO5, ...), so different
games are never mixed together. If checks keep failing, the run reports an error and GitHub
emails you (after about an hour, then at most once a day). Nothing here needs editing.
"""

import csv
import json
import os
import re
import subprocess
import sys
import time
import urllib.request
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

# ---------------------------------------------------------------- settings

PAGE_URL = os.environ.get("KINGS_URL", "https://kings-resort.com/poker/live")
FEED_URL = os.environ.get("KINGS_FEED_URL", "https://admin.kings-resort.com/zeus/?data=cash_games_by_venue")
VENUE = "1"                     # Rozvadov's number in the feed (Prague has another one)
TZ = ZoneInfo("Europe/Prague")  # Rozvadov time = Warsaw time
ALERT_AFTER = 4                 # failed checks in a row before GitHub emails you (about 1 hour)

DATA_DIR = Path("data")
README = Path("README.md")
PROBLEM_FILE = Path("debug/last_problem.json")
OLD_DEBUG_FILE = Path("debug/last_page.json")  # written by earlier versions

FIELDS = ["time", "weekday", "hour", "status", "source", "tables", "players", "games", "page_text"]
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


def as_int(value):
    try:
        return max(0, int(value))
    except (TypeError, ValueError):
        return 0


def feed_game(t):
    """The room's own name for a game, minus the stakes:
    'NLH 2-4' -> 'NLH', 'PLO 5-5 5cards' -> 'PLO5', 'SD 25-50' -> 'SD (Short Deck)'."""
    name = STAKES_IN_NAME.sub(" ", str((t.get("gameProfile") or {}).get("name") or ""))
    name = re.sub(r"(?i)\bPLO\s*(\d)[\s-]*cards?\b",
                  lambda m: "PLO" + ("" if m.group(1) == "4" else m.group(1)), name)
    name = clean(name)
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


def parse_games(games):
    """'NLH €2/4 8/8; PLO5 €5/5 7/8' -> [('NLH', '2/4', 8, 8), ('PLO5', '5/5', 7, 8)]"""
    tables = []
    for entry in (games or "").split("; "):
        m = ENTRY_RE.match(entry.strip())
        if m:
            tables.append((m.group(1), m.group(2), int(m.group(3)), int(m.group(4))))
    return tables


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


# ---------------------------------------------------------------- reading King's

def fetch_feed():
    """King's own cash-game data: the small JSON file their live page loads."""
    request = urllib.request.Request(FEED_URL, headers={
        "User-Agent": UA, "Accept": "application/json, text/plain, */*",
        "Origin": "https://kings-resort.com", "Referer": "https://kings-resort.com/"})
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.loads(response.read().decode("utf-8"))


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


def browser_check():
    """Open the live page like a visitor (slow, so only used when the feed fails).
    Returns (entries or None, source, box text, details for debugging)."""
    try:
        from playwright.sync_api import sync_playwright, TimeoutError as PWTimeout
    except ImportError:  # installed only when it's actually needed
        subprocess.run([sys.executable, "-m", "pip", "install", "-q", "playwright"], check=True)
        from playwright.sync_api import sync_playwright, TimeoutError as PWTimeout

    responses = []

    def remember_feed(response):
        if "cash_games" in response.url and len(responses) < 5:
            responses.append(response)

    with sync_playwright() as p:
        try:
            browser = p.chromium.launch(channel="chrome")  # GitHub's machines already have Chrome
        except Exception:
            subprocess.run([sys.executable, "-m", "playwright", "install", "--with-deps", "chromium"], check=True)
            browser = p.chromium.launch()
        page = browser.new_page(user_agent=UA, locale="en-US", viewport={"width": 1366, "height": 900})
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
    for path in sorted(DATA_DIR.glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as fh:
            reader = csv.DictReader(fh)
            if reader.fieldnames == FIELDS:
                continue
            rows = [convert_old_row(r) for r in reader]
        tmp = path.with_suffix(".tmp")
        with tmp.open("w", newline="", encoding="utf-8") as fh:
            writer = csv.DictWriter(fh, fieldnames=FIELDS, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(rows)
        tmp.replace(path)
    OLD_DEBUG_FILE.unlink(missing_ok=True)


def append_row(now, row):
    path = DATA_DIR / f"{now:%Y-%m}.csv"
    new_file = not path.exists()
    with path.open("a", newline="", encoding="utf-8") as fh:
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


def load_rows():
    rows = []
    for path in sorted(DATA_DIR.glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as fh:
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


def busiest_slots(checks, game, top=3, min_checks=3):
    total, count = defaultdict(float), defaultdict(int)
    for r, per_game in checks:
        slot = (r["weekday"], int(r["hour"]))
        total[slot] += per_game.get(game, 0)
        count[slot] += 1
    slots = sorted(((total[s] / count[s], s) for s in count if count[s] >= min_checks), key=lambda x: -x[0])
    return [f"{day} {hour:02d}:00 ({avg:.0f})" for avg, (day, hour) in slots[:top] if avg > 0]


def pct_cell(n, total):
    if not total:
        return "·"
    p = round(100 * n / total)
    return f"{'🟩' if p >= 75 else '🟨' if p >= 25 else '🟥'} {p}%"


def write_readme(rows, now):
    ok = [r for r in rows if r["status"] == "ok" and r["players"] != ""]
    checks = [(r, players_per_game(r)) for r in ok]
    out = ["# 🃏 King's Rozvadov — cash game tracker", "",
           "Checks King's live cash games about every 15 minutes and updates this page by itself. "
           "All times are **Czech time** (same as Poland).", ""]

    if rows:
        last = rows[-1]
        state = (f"✅ OK ({SOURCES.get(last['source'], last['source'])})" if last["status"] == "ok"
                 else f"⚠️ {clean(last['status'], 160)} — details in `debug/last_problem.json`")
        day_ago = (now - timedelta(hours=24)).strftime("%Y-%m-%d %H:%M")
        recent = [r for r in rows if r["time"] >= day_ago]
        out += [f"**Last check:** {last['time']} — {state}  ",
                f"**Last 24 h:** {sum(r['status'] == 'ok' for r in recent)} of {len(recent)} checks OK · "
                f"**Collecting since:** {rows[0]['time'][:10]} ({len(ok)} good checks)", ""]

    if ok:
        latest = ok[-1]
        tables = sorted(parse_games(latest["games"]), key=lambda t: (game_order(t[0]), t[0], stake_key(t[1])))
        out += [f"## Tables running at {latest['time']}", ""]
        if tables:
            width = max(len(t[0]) for t in tables) + 2
            per_game = defaultdict(lambda: [0, 0])
            for game, _, seated, _ in tables:
                per_game[game][0] += seated
                per_game[game][1] += 1
            totals = sorted(per_game.items(), key=lambda kv: (game_order(kv[0]), kv[0]))
            out += ["```", *(f"{g:<{width}}€{s:<8}{a}/{b} players" for g, s, a, b in tables), "```",
                    " · ".join(f"**{g}:** {p} players at {n} table{'s' * (n != 1)}" for g, (p, n) in totals), ""]
        else:
            out += ["No tables were running.", ""]

    games = main_games(checks) if checks else []

    # Quick answer first: when is each main game busiest?
    out += ["## Busiest times so far", ""]
    lines = [f"- **{g}:** " + " · ".join(slots) for g in games if (slots := busiest_slots(checks, g))]
    out += (["Day, hour and average seated players (only day-hour slots with at least 3 checks).", "", *lines]
            if lines else ["Needs about a week of data: every day-and-hour slot needs at least 3 checks."])
    out.append("")

    # One table per main game: average seated players by hour and weekday
    out += ["## Average players by hour", "",
            "Seated players at each game's tables. 0 = that game wasn't running." if games
            else "No player data yet.", ""]
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

    # How often each game + stake was running, by hour
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

    # Every game + stake ever seen, rare ones included
    appearances = defaultdict(list)
    for r, labels in labelled:
        for label in labels:
            appearances[label].append(r)
    if appearances:
        out += ["## All games seen", "", "| Game | Running in | Most often | Last seen |", "|:--|--:|:--|:--|"]
        for label in sorted(appearances, key=label_key):
            seen_rows = appearances[label]
            day = Counter(r["weekday"] for r in seen_rows).most_common(1)[0][0]
            hour = Counter(int(r["hour"]) for r in seen_rows).most_common(1)[0][0]
            out.append(f"| {label} | {round(100 * len(seen_rows) / len(ok))}% of checks "
                       f"| {day} around {hour:02d}:00 | {seen_rows[-1]['time']} |")
        out.append("")

    out += ["---", "Raw data: the `data` folder (one CSV file per month, opens in Excel). "
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
    assert parse_games("; ".join(got[:3])) == [("NLH", "2/4", 7, 8), ("PLO5", "10/10", 8, 8),
                                               ("SD (Short Deck)", "25/50", 5, 8)]
    box = "NO LIMIT TEXAS HOLD’EM | € 2/4 | 8/8 PLAYERS | POT-LIMIT OMAHA 5 CARDS | € 5/5 | 7/8 PLAYERS"
    assert box_entries(box) == ["NLH €2/4 8/8", "PLO5 €5/5 7/8"], box_entries(box)
    assert box_entries("CASH GAME TABLES ARE WAITING FOR MORE PLAYERS.") == []
    assert box_entries("SOME NEW LAYOUT 12") is None
    old = convert_old_row({"time": "2026-10-06 04:40", "weekday": "Tue", "hour": "4", "status": "ok", "box_text": box})
    assert (old["source"], old["tables"], old["players"], old["games"]) == \
        ("page table", 2, 15, "NLH €2/4 8/8; PLO5 €5/5 7/8"), old


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
    row = {"time": f"{now:%Y-%m-%d %H:%M}", "weekday": DAYS[now.weekday()], "hour": now.hour,
           "status": status, "source": source,
           "tables": len(entries) if entries is not None else "",
           "players": sum(t[2] for t in parse_games("; ".join(entries))) if entries is not None else "",
           "games": "; ".join(entries or []), "page_text": page_text[:3000]}
    append_row(now, row)
    save_problem(now, row, problem)

    rows = load_rows()
    write_readme(rows, now)
    print(json.dumps(row, ensure_ascii=False))

    streak = failure_streak(rows)
    if streak >= ALERT_AFTER and (streak - ALERT_AFTER) % 96 == 0:  # after ~1 hour, then once a day
        print(f"::error::{streak} checks in a row have failed. See README.md and debug/last_problem.json.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
