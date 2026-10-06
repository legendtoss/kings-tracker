#!/usr/bin/env python3
"""
King's Resort Rozvadov - cash game tracker
==========================================
GitHub Actions runs this about every 15 minutes. Each run it:
  1. opens https://kings-resort.com/poker/live in a headless Chrome browser,
  2. waits until the "Running Cash Games in Rozvadov" box has loaded,
  3. adds one line to data/YYYY-MM.csv (Czech local time),
  4. rebuilds README.md with hour-by-hour statistics.

You don't need to edit anything in this file.
"""

import csv
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

URL = os.environ.get("KINGS_URL", "https://kings-resort.com/poker/live")
TZ = ZoneInfo("Europe/Prague")  # Rozvadov time = Warsaw time
DATA_DIR = Path("data")
DEBUG_FILE = Path("debug/last_page.json")
README = Path("README.md")

FIELDS = ["time", "weekday", "hour", "status", "cash_games", "stakes_running", "box_text"]
DAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
BOX_START = "running cash games in rozvadov"
BOX_ENDS = ("running cash games in", "cash game action", "twitch", "youtube")
BOX_TIMEOUT_MS = 45_000
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/141.0.0.0 Safari/537.36")

# True once the Rozvadov box no longer says "Loading..."
BOX_READY_JS = """() => {
  const t = (document.body ? document.body.innerText : '').toLowerCase();
  const a = t.indexOf('%s');
  if (a < 0) return false;
  const box = t.slice(a + %d, a + 4000).split('running cash games in')[0];
  return !box.includes('loading');
}""" % (BOX_START, len(BOX_START))

# The "Cash Games: N" counter in the site header
COUNTER_JS = r"""() => {
  const m = (document.body.textContent || '').match(/cash games\s*:\s*(\d+)/i);
  return m ? m[1] : null;
}"""

# HTML of the Rozvadov box (kept in debug/ for fine-tuning)
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


# ---------------------------------------------------------------- reading the page

def launch(p):
    """Use the Chrome that GitHub's machines already have; download Chromium only if that fails."""
    try:
        return p.chromium.launch(channel="chrome")
    except Exception as e:
        print(f"System Chrome unavailable ({e}); installing Chromium...", flush=True)
        subprocess.run([sys.executable, "-m", "playwright", "install", "--with-deps", "chromium"], check=True)
        return p.chromium.launch()


def scrape():
    from playwright.sync_api import sync_playwright, TimeoutError as PWTimeout

    responses, ws_frames = [], []

    def on_response(r):
        if r.request.resource_type in ("xhr", "fetch") and len(responses) < 40:
            responses.append(r)

    def on_websocket(ws):
        def on_frame(payload):
            if len(ws_frames) < 30:
                ws_frames.append({"url": ws.url, "data": str(payload)[:3000]})
        ws.on("framereceived", on_frame)

    with sync_playwright() as p:
        browser = launch(p)
        page = browser.new_page(user_agent=UA, locale="en-US",
                                viewport={"width": 1366, "height": 900})
        page.on("response", on_response)
        page.on("websocket", on_websocket)

        for attempt in (1, 2):
            try:
                page.goto(URL, wait_until="domcontentloaded", timeout=60_000)
                break
            except Exception:
                if attempt == 2:
                    raise
                page.wait_for_timeout(10_000)

        status = "ok"
        try:
            page.wait_for_function(BOX_READY_JS, timeout=BOX_TIMEOUT_MS, polling=1000)
        except PWTimeout:
            status = "box did not finish loading"
        page.wait_for_timeout(2_000)  # give the header counter a moment to update

        text = page.inner_text("body")
        counter = page.evaluate(COUNTER_JS)
        box_html = page.evaluate(BOX_HTML_JS)

        network = []
        for r in responses:
            try:
                body = r.text()
            except Exception as e:
                body = f"<could not read: {e}>"
            network.append({"url": r.url, "status": r.status, "body": body[:8000]})
        browser.close()

    return status, text, counter, box_html, network, ws_frames


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


STAKE_RE = re.compile(r"(€\s?)?(?<![\d/.:])(\d{1,4})\s?/\s?(€\s?)?(\d{1,4})"
                      r"(?:\s?/\s?(€\s?)?(\d{1,4}))?(?![\d/:])(\s?€(?!\s?\d))?")


def stake_key(s):
    return [int(x) for x in s.split("/")][::-1]


def find_stakes(box):
    """Stakes like '2/4' or '5/5/10' in the box. If any are written with €, only
    those count, so seat counts like '8/9' are not mistaken for stakes."""
    found = []
    for m in STAKE_RE.finditer(box):
        g = m.groups()
        nums = [int(x) for x in (g[1], g[3], g[5]) if x]
        if any(a > b for a, b in zip(nums, nums[1:])):
            continue
        found.append(("/".join(map(str, nums)), any((g[0], g[2], g[4], g[6]))))
    if any(euro for _, euro in found):
        found = [f for f in found if f[1]]
    return sorted({s for s, _ in found}, key=stake_key)


# ---------------------------------------------------------------- saving

def append_row(now, row):
    DATA_DIR.mkdir(exist_ok=True)
    path = DATA_DIR / f"{now:%Y-%m}.csv"
    is_new = not path.exists()
    with path.open("a", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=FIELDS)
        if is_new:
            writer.writeheader()
        writer.writerow(row)


def save_debug(now, row, debug):
    """Raw copy of what the page sent (refreshed every 6 h or when the status changes)."""
    if not debug:
        return
    try:
        old = json.loads(DEBUG_FILE.read_text(encoding="utf-8"))
        recent = now - datetime.fromisoformat(old["saved_at"]) < timedelta(hours=6)
        if recent and old.get("status") == row["status"]:
            return
    except Exception:
        pass
    DEBUG_FILE.parent.mkdir(exist_ok=True)
    payload = {"saved_at": now.isoformat(timespec="seconds"), "status": row["status"],
               "cash_games": row["cash_games"], "box_text": row["box_text"], **debug}
    DEBUG_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")


# ---------------------------------------------------------------- README with statistics

def load_rows():
    rows = []
    for path in sorted(DATA_DIR.glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as fh:
            rows.extend(csv.DictReader(fh))
    return rows


def pct_cell(n, total):
    if not total:
        return "·"
    p = round(100 * n / total)
    return f"{'🟩' if p >= 75 else '🟨' if p >= 25 else '🟥'} {p}%"


def write_readme():
    rows = load_rows()
    ok = [r for r in rows if r["status"] == "ok"]
    out = ["# 🃏 King's Rozvadov — cash game tracker", "",
           f"Checks [the live page]({URL}) about every 15 minutes and updates this page automatically. "
           "All times are **Czech time** (same as Poland).", ""]

    if rows:
        last = rows[-1]
        state = "✅ OK" if last["status"] == "ok" else f"⚠️ {last['status']}"
        out += [f"**Last check:** {last['time']} — {state}  ",
                f"**Checks so far:** {len(ok)} successful out of {len(rows)} (since {rows[0]['time'][:10]})", ""]

    if ok:
        lr = ok[-1]
        lines = [x for x in lr["box_text"].split(" | ") if x][:40] or ["(nothing listed)"]
        out += [f"## What the page showed at {lr['time']}", "",
                f"Cash Games counter: **{lr['cash_games'] or '?'}**", "", "```", *lines, "```", ""]

    # Table 1: average of the "Cash Games" counter by hour and weekday
    sums, cnts = defaultdict(float), defaultdict(int)
    for r in ok:
        if r["cash_games"]:
            for key in ((int(r["hour"]), r["weekday"]), (int(r["hour"]), "All")):
                sums[key] += float(r["cash_games"])
                cnts[key] += 1
    out += ["## Average number of running cash games, by hour", "",
            "Taken from the *Cash Games* counter on the site. Bigger number = more action.", "",
            "| Hour | " + " | ".join(DAYS) + " | All days |",
            "|:--|" + "--:|" * (len(DAYS) + 1)]
    for h in range(24):
        cells = [f"{sums[(h, d)] / cnts[(h, d)]:.1f}" if cnts[(h, d)] else "·" for d in DAYS + ["All"]]
        out.append(f"| {h:02d}:00 | " + " | ".join(cells) + " |")
    out.append("")

    # Table 2: how often each stake was listed, by hour (all days)
    freq = Counter(s for r in ok for s in set(filter(None, r["stakes_running"].split(";"))))
    stakes = sorted((s for s, _ in freq.most_common(10)), key=stake_key)
    out += ["## How often each stake was running, by hour (all days)", ""]
    if stakes:
        total_h, seen = defaultdict(int), defaultdict(int)
        for r in ok:
            h = int(r["hour"])
            total_h[h] += 1
            for s in set(filter(None, r["stakes_running"].split(";"))):
                seen[(h, s)] += 1
        out += ["🟩 most of the time · 🟨 sometimes · 🟥 rarely", "",
                "| Hour | " + " | ".join(f"€{s}" for s in stakes) + " | Checks |",
                "|:--|" + "--:|" * (len(stakes) + 1)]
        for h in range(24):
            cells = [pct_cell(seen[(h, s)], total_h[h]) for s in stakes]
            out.append(f"| {h:02d}:00 | " + " | ".join(cells) + f" | {total_h[h]} |")
    else:
        out.append("No stakes recognised yet — see the latest check above.")

    out += ["", "---", "Raw data: the `data` folder (one CSV file per month, opens in Excel)."]
    README.write_text("\n".join(out) + "\n", encoding="utf-8")


# ---------------------------------------------------------------- main

def main():
    now = datetime.now(TZ)
    row = {"time": f"{now:%Y-%m-%d %H:%M}", "weekday": DAYS[now.weekday()], "hour": now.hour,
           "status": "", "cash_games": "", "stakes_running": "", "box_text": ""}
    debug = {}
    try:
        status, text, counter, box_html, network, ws_frames = scrape()
        box = cut_box(text)
        if box is None:
            status = "box not found on page"
        else:
            stakes = find_stakes(box)
            row["box_text"] = box[:3000]
            row["stakes_running"] = ";".join(stakes)
            if counter == "0" and stakes:
                counter = None  # counter hasn't refreshed yet - don't record a fake zero
        row["status"] = status
        row["cash_games"] = counter or ""
        debug = {"url": URL, "page_text_start": text[:5000], "box_html": box_html,
                 "network": network, "websocket_frames": ws_frames}
    except Exception as e:
        first_line = (str(e).strip().splitlines() or [""])[0]
        row["status"] = f"error: {type(e).__name__}: {first_line}"[:200]

    append_row(now, row)
    save_debug(now, row, debug)
    write_readme()
    print(json.dumps(row, ensure_ascii=False))


if __name__ == "__main__":
    main()
