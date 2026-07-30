"""Download raw erdosproblems.com data for the Erdős evaluation set.

Fetches, straight from the primary sources, everything needed to join
"which curated list is this problem on?" metadata onto the ``apn_erdos``
samples (keyed by erdosproblems.com problem number, which is the ``<n>`` in
sample ids ``Erdos<n>.erdos_<n>...``), and writes it as JSON close to the
source's own structure:

* **Problem records** -- every problem on the site, scraped from the prize
  bucket pages (``/prizes/<amount>``; every problem appears in exactly one
  bucket, the $0 bucket holding the unprized majority). Each problem-box
  yields ``{number, state, label, prize_usd, statement, sources, tags,
  comment_activity}`` -> ``erdosproblems_problems.jsonl``.

  ``state`` is the site's binary open/solved flag; ``label`` the finer badge
  shown to readers (``OPEN``, ``PROVED``, ``DISPROVED (LEAN)``, ...);
  ``statement`` the problem text with HTML stripped, LaTeX kept;
  ``sources`` the citation list ``[{code, locator}, ...]`` as displayed
  (``[Er61,p.243]`` -> ``{"code": "Er61", "locator": "p.243"}``) -- these are
  the papers the problem appears in, so membership in *any* of Erdős's
  problem-list papers is a join against the lists file, not a fact baked in
  here; ``comment_activity`` the unincorporated-comment-claims widget status
  (``open``/``partial``/``claimed``; only present on open problems).

* **List-paper catalog** -- the ``/lists`` page's table of the 147 problem
  lists Erdős wrote: ``{code, title, reference, year, problems_in_database,
  solved_in_database, completely_checked}`` -> ``erdosproblems_lists.jsonl``.
  Which of these count as "curated" (the favourite/most-wanted lists vs the
  survey compendia) is deliberately left to the consumer.

* **1999 booklet crosswalk** -- Thomas Bloom's forum post (24 Jan 2026)
  mapping all 94 entries of the booklet *Some of Paul's favorite problems*
  (selected by 18 of Erdős's colleagues for the 1999 Budapest conference) to
  database numbers: ``{entry, section, problems, annotation}`` per entry,
  annotation verbatim (``"open (new)"``, ``"solved (in 1960!)"``, ...) ->
  ``booklet_1999_crosswalk.json``.

* **Bloom's Top 10** -- the headline entries of the site's "Top 10 Erdős
  Problems" blog post (16 Apr 2026): ``{heading, problems}`` per entry ->
  ``bloom_top10.json``.

* **Ben Green's 100 Open Problems** -- the erdosproblems.com URLs explicitly
  hyperlinked in the PDF's link annotations (11 of his 100 problems; the
  rest are not mechanically mappable and mostly are not Erdős-database
  problems) -> ``green_open_problems.json``.

The parse is purely mechanical -- no interpretation. Parsed counts are
validated against the site's own self-reported totals (per-bucket problem
counts, the 147-list total, the 94-entry booklet) so a silent layout change
fails loudly instead of producing a short file.

erdosproblems.com rate-limits at 5 requests/minute (Cloudflare returns 429
beyond that), so requests are spaced ``--delay`` seconds apart; a full run is
17 requests, ~4 minutes. ``--cache-dir`` keeps every fetched page on disk and
reuses pages already present, so an interrupted or repeated run only fetches
what is missing.

Usage::

    python scripts/fetch_erdosproblems_data.py
    python scripts/fetch_erdosproblems_data.py --out-dir apn/data/erdos/raw
    python scripts/fetch_erdosproblems_data.py --cache-dir /tmp/ep-cache
"""

from __future__ import annotations

import argparse
import datetime
import html as htmllib
import json
import re
import sys
import zlib
from pathlib import Path

import requests

BASE = "https://www.erdosproblems.com"
PRIZE_AMOUNTS = [0, 10, 24, 25, 44, 50, 78, 100, 250, 500, 1000, 5000, 10000]
BOOKLET_THREAD = f"{BASE}/forum/thread/General%20Erd%C5%91s%20Discussion"
TOP10_THREAD = f"{BASE}/forum/thread/blog:5"
GREEN_PDF = "https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf"
USER_AGENT = (
    "Mozilla/5.0 (compatible; LeanOpenProblems-data-fetch; "
    "https://github.com/epoch-research/LeanOpenProblems)"
)


def fetch(url: str, cache_dir: Path | None, cache_name: str, delay: float,
          binary: bool = False) -> bytes:
    if cache_dir is not None:
        cached = cache_dir / cache_name
        if cached.exists() and cached.stat().st_size > 2000:
            return cached.read_bytes()
    import time

    time.sleep(delay)
    resp = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=120)
    resp.raise_for_status()
    if b"429 Too Many Requests" in resp.content[:500]:
        raise RuntimeError(f"rate-limited fetching {url}; increase --delay")
    if cache_dir is not None:
        cache_dir.mkdir(parents=True, exist_ok=True)
        (cache_dir / cache_name).write_bytes(resp.content)
    return resp.content


def strip_tags(fragment: str) -> str:
    return htmllib.unescape(re.sub(r"<[^>]+>", "", fragment)).strip()


def parse_problem_boxes(page: str, prize_usd: int) -> list[dict]:
    out = []
    for box in page.split('<div class="problem-box">')[1:]:
        pid = re.search(r'<div id="problem_id"><a href="/(\d+)">#\1</a>(.*?)</div>',
                        box, re.S)
        if pid is None:
            continue
        state = re.search(r'<div class="problem-text" id="(\w+)">', box)
        label = re.search(
            r'<span class="tooltip">\s*([A-Z][A-Z() ]*?)\s*<span class="tooltiptext">', box)
        content = re.search(r'<div id="content">(.*?)</div>', box, re.S)
        sources = [
            {"code": code, "locator": disp.partition(",")[2] or None}
            for code, disp in re.findall(
                r"addNewBox\('(\w+)', '\d+', true\);return false;\">\[([^\]]+)\]</a>",
                pid.group(2))
        ]
        tags_div = re.search(r'<div id="tags">(.*?)</div>', box, re.S)
        tags = re.findall(r'<a href="/tags/[^"]*">([^<]+)</a>', tags_div.group(1)) \
            if tags_div else []
        activity = re.search(r'data-current-status="(\w+)"', box)
        out.append({
            "number": int(pid.group(1)),
            "state": state.group(1) if state else None,
            "label": label.group(1).strip() if label else None,
            "prize_usd": prize_usd,
            "statement": strip_tags(content.group(1)) if content else None,
            "sources": sources,
            "tags": tags,
            "comment_activity": activity.group(1) if activity else None,
        })
    return out


def parse_lists_page(page: str) -> list[dict]:
    out = []
    for completed, code, count, solved, title, reference in re.findall(
            r'<tr\s*(class="completed")?\s*>\s*<th>\s*'
            r'<a href="/search_bib/([^?"]+)\?sources_only=1">\s*(\d+) problems?\s*</a>'
            r'\s*<br>\s*\((\d+) solved\)</th>\s*<th><i>(.*?)</i><br/>\s*(.*?)</th>',
            page, re.S):
        reference = re.sub(r"\s+", " ", strip_tags(reference))
        year = re.findall(r"\((\d{4})\)", reference)
        out.append({
            "code": code,
            "title": re.sub(r"\s+", " ", strip_tags(title)),
            "reference": reference,
            "year": int(year[-1]) if year else None,
            "problems_in_database": int(count),
            "solved_in_database": int(solved),
            "completely_checked": bool(completed),
        })
    return out


def parse_booklet_post(page: str) -> tuple[list[dict], str | None]:
    post = page[page.find("1999 booklet"):]
    post = post[:post.find("</div>")]
    posted = re.search(r"(\d\d:\d\d on \d+ \w+ \d{4})", page[page.find("1999 booklet"):])
    entries = []
    section = None
    for chunk in re.split(r"<br\s*/?>", post):
        h3 = re.search(r"<h3>(.*?)</h3>", chunk)
        if h3:
            section = strip_tags(h3.group(1))
            chunk = chunk[h3.end():]
        m = re.match(r"\s*(\d+\.\d+) - (.*)", chunk, re.S)
        if not m:
            continue
        problems = [int(n) for n in re.findall(r'<a href="/(\d+)"', m.group(2))]
        annotation = strip_tags(re.sub(r"<a[^>]*>\[\d+\]</a>(?: and | , |, )?", "",
                                       m.group(2))).strip(" ,")
        entries.append({
            "entry": m.group(1),
            "section": section,
            "problems": problems,
            "annotation": annotation,
        })
    return entries, posted.group(1) if posted else None


def parse_top10_post(page: str) -> list[dict]:
    out = []
    for heading in re.findall(r"<h3[^>]*>(.*?)</h3>", page, re.S):
        text = re.sub(r"\s+", " ", strip_tags(heading))
        problems = [int(n) for n in re.findall(r"\[(\d+)\]", text)]
        if problems:
            out.append({"heading": text, "problems": problems})
    return out


def parse_green_pdf(pdf: bytes) -> dict:
    streams = []
    for m in re.finditer(rb"stream\r?\n(.*?)endstream", pdf, re.S):
        try:
            streams.append(zlib.decompress(m.group(1)))
        except zlib.error:
            pass
    blob = b"\n".join([pdf] + streams)
    uris = sorted({
        u.decode() for u in re.findall(rb"/URI\s*\((.*?)\)\s*>>", blob)
        if b"erdosproblems" in u
    })
    problems = sorted({
        int(m.group(1)) for u in uris
        for m in [re.search(r"erdosproblems\.com/(\d+)", u)] if m
    })
    return {"uris": uris, "problems": problems}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--out-dir", type=Path,
                        default=Path("apn/data/erdos/raw"))
    parser.add_argument("--cache-dir", type=Path, default=None,
                        help="reuse pages already downloaded here; fetch the rest")
    parser.add_argument("--delay", type=float, default=13.0,
                        help="seconds between requests (site limit: 5/minute)")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    retrieved = datetime.date.today().isoformat()

    def get(url: str, name: str, binary: bool = False) -> bytes:
        return fetch(url, args.cache_dir, name, args.delay, binary)

    lists = parse_lists_page(get(f"{BASE}/lists", "lists.html").decode())
    total = re.search(r"There are (\d+) lists",
                      get(f"{BASE}/lists", "lists.html").decode())
    assert total and len(lists) == int(total.group(1)), \
        f"parsed {len(lists)} lists, page reports {total and total.group(1)}"

    summary = get(f"{BASE}/prizes", "prizes.html").decode()
    expected = {int(a): int(t) for a, t in re.findall(
        r"\$(\d+)</a> : \d+ solved out of (\d+)", summary)}
    problems: list[dict] = []
    for amount in PRIZE_AMOUNTS:
        page = get(f"{BASE}/prizes/{amount}", f"prize_{amount}.html").decode()
        rows = parse_problem_boxes(page, amount)
        assert len(rows) == expected[amount], \
            f"${amount}: parsed {len(rows)}, summary says {expected[amount]}"
        problems.extend(rows)
    problems.sort(key=lambda r: r["number"])
    numbers = [r["number"] for r in problems]
    assert len(set(numbers)) == len(numbers), "duplicate problem numbers"

    booklet_page = get(BOOKLET_THREAD, "forum_general.html").decode()
    booklet, posted = parse_booklet_post(booklet_page)
    assert len(booklet) == 94, f"parsed {len(booklet)} booklet entries, expected 94"

    top10 = parse_top10_post(get(TOP10_THREAD, "forum_top10.html").decode())
    assert len(top10) == 10, f"parsed {len(top10)} top-10 headings, expected 10"

    green = parse_green_pdf(get(GREEN_PDF, "green-open-problems.pdf", binary=True))

    with open(args.out_dir / "erdosproblems_problems.jsonl", "w") as f:
        for row in problems:
            f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    with open(args.out_dir / "erdosproblems_lists.jsonl", "w") as f:
        for row in lists:
            f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    json.dump({
        "_meta": {
            "source": BOOKLET_THREAD,
            "description": "Thomas Bloom's crosswalk of the 1999 booklet 'Some of "
                           "Paul's favorite problems' (94 entries selected by 18 of "
                           "Erdős's colleagues) to database problem numbers",
            "posted": posted,
            "retrieved": retrieved,
        },
        "entries": booklet,
    }, open(args.out_dir / "booklet_1999_crosswalk.json", "w"),
        ensure_ascii=False, indent=1)
    json.dump({
        "_meta": {
            "source": TOP10_THREAD,
            "description": "Headline entries of Thomas Bloom's 'Top 10 Erdős "
                           "Problems' blog post",
            "posted": "16 April 2026",
            "retrieved": retrieved,
        },
        "entries": top10,
    }, open(args.out_dir / "bloom_top10.json", "w"), ensure_ascii=False, indent=1)
    json.dump({
        "_meta": {
            "source": GREEN_PDF,
            "description": "erdosproblems.com URLs hyperlinked in Ben Green's "
                           "'100 Open Problems' PDF; most of his problems carry no "
                           "such link and are not mechanically mappable",
            "retrieved": retrieved,
        },
        **green,
    }, open(args.out_dir / "green_open_problems.json", "w"),
        ensure_ascii=False, indent=1)

    print(f"{len(problems)} problems, {len(lists)} lists, {len(booklet)} booklet "
          f"entries, {len(top10)} top-10 entries, {len(green['problems'])} Green links "
          f"-> {args.out_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
