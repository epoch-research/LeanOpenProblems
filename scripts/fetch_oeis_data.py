"""Download raw OEIS data for the 492-conjecture evaluation set.

For every unique OEIS sequence referenced by the dataset manifest (444 of
them; some sequences contribute more than one conjecture), this fetches two
artifacts straight from oeis.org and writes them as JSON Lines:

* **Sequence record** -- the full structured entry from the JSON API
  (``/search?q=id:A<num>&fmt=json``): ``name``, ``comment``, ``keyword``,
  ``author``, ``data``, ``created``, etc. -> ``oeis_records.jsonl``.

* **Revision history** -- the entry's revision log, parsed from the history page
  (``/history?seq=A<num>``) into compact structured revisions ->
  ``oeis_history.jsonl``. OEIS exposes history *only* as HTML (``fmt=json`` is
  ignored; the per-revision text view requires login), so we scrape it, but we
  do not store the 30 KB page -- ~80% is boilerplate. The parse mirrors the
  page's structure: each revision becomes ``{v, user, time, changes,
  discussion}``, where the two content fields map to the HTML's two per-revision
  regions. ``changes`` (from ``<div class=entry>``) lists, per OEIS section
  (COMMENTS, NAME, KEYWORD, ...), the inline diff text with additions marked
  ``{+...}`` and deletions ``{-...}`` -- so the text a revision *added* (e.g. a
  conjecture comment) is recoverable. ``discussion`` (from ``<div
  class=discussbar>``) lists the revision's editor notes as ``{date, time, user,
  note}``. Together these record *when* each piece of text entered the database
  and *which user* typed the edit. (The editing user is not necessarily the
  conjecture's proposer -- that attribution lives in the comment prose -- so both
  artifacts feed the later provenance-extraction pass.) History paginates 10
  revisions per page; we follow the "older changes" links to capture them all.

This is the download step: a raw fetch of the JSON records, plus a purely
mechanical parse of the history HTML into structured revisions (no
interpretation -- proposer attribution is a later LLM pass). Each line is
``{"oeis_id": "A...", ...}``; records carry ``"record"`` (the API object) and
histories carry ``"revisions"``. Both files are keyed by ``oeis_id`` and the
script is resumable -- ids already present in an output file are skipped -- so
an interrupted run can simply be re-invoked.

OEIS is a free public resource with no official API rate limit; we stay polite
with a default 1 request/second delay and a descriptive User-Agent. A full run
is ~900+ requests (history adds an extra page request per heavily-revised
sequence), roughly 15-20 min.

Usage::

    python scripts/fetch_oeis_data.py
    python scripts/fetch_oeis_data.py --out-dir apn/data/oeis/metadata/snapshots --delay 1.0
    python scripts/fetch_oeis_data.py --limit 5            # smoke test
    python scripts/fetch_oeis_data.py --ids A129365 A268597
"""

from __future__ import annotations

import argparse
import html as htmllib
import json
import re
import sys
import time
from pathlib import Path

import requests

OEIS_DIR = Path(__file__).parent.parent / "apn" / "data" / "oeis"
DEFAULT_OUT_DIR = Path(__file__).parent.parent / "apn" / "data" / "oeis" / "metadata" / "snapshots"

RECORD_URL = "https://oeis.org/search?q=id:{oeis_id}&fmt=json"
# History paginates 10 revisions per page (newest first); &start=N walks older
# ones. The last page omits the "older changes" link, which is our stop signal.
HISTORY_URL = "https://oeis.org/history?seq={oeis_id}&start={start}"
USER_AGENT = "tsoukalas-lean-oeis-metadata/1.0 (research; contact tom@epochai.org)"

def unique_oeis_ids(dataset_dir: Path) -> list[str]:
    """Sorted unique A-numbers from the dataset's ``samples.jsonl`` manifest
    (each row's ``oeis_id`` field)."""
    from apn.dataset import load_manifest

    return sorted({r.extra["oeis_id"] for r in load_manifest(dataset_dir)})


_REVBAR_RE = re.compile(r"<div class=\"?revbar\"?>")
_HEADER_RE = re.compile(
    r"history/view\?seq=\w+&v=(\d+)\">#\d+</a> by "
    r"<a href=\"[^\"]*\">([^<]+)</a> at (.+?)\s*</div>",
    re.S,
)
# The HTML splits each revision into two regions: a <div class=entry> holding the
# section diffs, then a separate <div class=discussbar> holding revision-level
# discussion notes. We partition on the discussbar so neither bleeds into the
# other (an earlier version let the last section swallow the discussbar).
_DISCUSSBAR_RE = re.compile(r"<div class=discussbar>")
_SECTION_RE = re.compile(r"<div class=sectname>(.*?)</div>(.*?)(?=<div class=sectname>|\Z)", re.S)
_DIFF_RE = re.compile(r"<p class=\"diffs\"><tt>(.*?)</tt></p>", re.S)
_DISCUSSNOTE_RE = re.compile(
    r"<div class=discussnote>\s*"
    r"(?:<div class=date>(.*?)</div>\s*)?"
    r"(?:<div class=time>(.*?)</div>\s*)?"
    r"<pre class=note>(.*?)</pre>",
    re.S,
)
_NOTE_USER_RE = re.compile(r"\s*<span class=user>(.*?)</span>\s*:?\s*(.*)", re.S)
_INS_RE = re.compile(r"<ins>(.*?)</ins>", re.S)
_DEL_RE = re.compile(r"<del>(.*?)</del>", re.S)
_TAG_RE = re.compile(r"<[^>]+>")
# "older changes" link on a non-final history page; its start= is the next page.
_OLDER_RE = re.compile(r"history\?seq=\w+&amp;start=(\d+)\">\s*older changes")


def _strip_tags(text: str) -> str:
    """Drop HTML tags and unescape entities, returning trimmed plain text."""
    return htmllib.unescape(_TAG_RE.sub("", text)).strip()


def _parse_changes(entry_region: str) -> list[dict[str, object]]:
    """Section diffs from the ``<div class=entry>`` region of one revision.

    Each ``<div class=sectname>`` (COMMENTS, NAME, KEYWORD, STATUS, ...) yields a
    ``{section, diffs}`` entry whose ``diffs`` are the inline diff fragments with
    additions rendered ``{+...}`` and deletions ``{-...}`` (so the text a revision
    *added* -- e.g. a conjecture comment -- is recoverable).
    """
    changes: list[dict[str, object]] = []
    for section in _SECTION_RE.finditer(entry_region):
        name = _strip_tags(section.group(1))
        diffs: list[str] = []
        for diff in _DIFF_RE.finditer(section.group(2)):
            marked = _INS_RE.sub(r"{+\1}", diff.group(1))
            marked = _DEL_RE.sub(r"{-\1}", marked)
            text = _strip_tags(marked)
            if text:
                diffs.append(text)
        if diffs:
            changes.append({"section": name, "diffs": diffs})
    return changes


def _parse_discussion(discuss_region: str) -> list[dict[str, object]]:
    """Discussion notes from the ``<div class=discussbar>`` region of a revision.

    Each ``<div class=discussnote>`` yields ``{date, time, user, note}`` mirroring
    the page's ``<div class=date>``/``<div class=time>``/``<pre class=note>``
    (the note's leading ``<span class=user>`` is split out as ``user``). These are
    revision-level, not attached to any section.
    """
    notes: list[dict[str, object]] = []
    for date, time_, body in _DISCUSSNOTE_RE.findall(discuss_region):
        user_match = _NOTE_USER_RE.match(body)
        if user_match:
            user, note = _strip_tags(user_match.group(1)), _strip_tags(user_match.group(2))
        else:
            user, note = None, _strip_tags(body)
        notes.append({"date": date.strip(), "time": time_.strip(), "user": user, "note": note})
    return notes


def parse_history(page: str) -> list[dict[str, object]]:
    """Reduce a ``/history?seq=`` page to a list of structured revisions.

    Returns newest-first ``{v, user, time, changes, discussion}`` dicts (matching
    the page's order), mirroring the HTML's two per-revision regions: ``changes``
    from ``<div class=entry>`` (see :func:`_parse_changes`) and ``discussion``
    from ``<div class=discussbar>`` (see :func:`_parse_discussion`). ``user`` is
    who *typed* the revision -- not necessarily the conjecture's proposer.

    Purely mechanical: it preserves what the page says without judging who
    proposed anything (that is the downstream LLM pass). A page with no revisions
    (unexpected) yields ``[]``.
    """
    revisions: list[dict[str, object]] = []
    for block in _REVBAR_RE.split(page)[1:]:
        header = _HEADER_RE.search(block)
        if not header:
            continue
        version, user, timestamp = int(header.group(1)), _strip_tags(header.group(2)), header.group(3).strip()
        entry_region, _, discuss_region = block.partition("<div class=discussbar>")
        revisions.append(
            {
                "v": version,
                "user": user,
                "time": timestamp,
                "changes": _parse_changes(entry_region),
                "discussion": _parse_discussion(discuss_region),
            }
        )
    return revisions


def existing_ids(path: Path) -> set[str]:
    """The ``oeis_id`` values already written to a JSONL output (for resuming)."""
    if not path.is_file():
        return set()
    done: set[str] = set()
    for line in path.read_text().splitlines():
        if line.strip():
            done.add(json.loads(line)["oeis_id"])
    return done


def fetch(session: requests.Session, url: str, *, retries: int = 4, timeout: float = 30.0) -> str:
    """GET ``url`` and return the body text, retrying with backoff on failure.

    Retries transient errors (timeouts, 5xx, connection resets, 429) with
    exponential backoff; other 4xx responses won't fix themselves and are raised
    immediately since every id here is known to exist.
    """
    last_error: Exception | None = None
    for attempt in range(retries):
        try:
            response = session.get(url, timeout=timeout)
            if 400 <= response.status_code < 500 and response.status_code != 429:
                response.raise_for_status()
            if response.status_code >= 500 or response.status_code == 429:
                raise requests.HTTPError(f"{response.status_code} for {url}")
            return response.text
        except requests.RequestException as error:
            last_error = error
            backoff = 2.0**attempt
            print(f"    retry {attempt + 1}/{retries} after {error} (sleep {backoff}s)", file=sys.stderr)
            time.sleep(backoff)
    raise RuntimeError(f"failed to fetch {url}: {last_error}")


def fetch_all_revisions(session: requests.Session, oeis_id: str, *, delay: float) -> list[dict[str, object]]:
    """All revisions of a sequence, following history pagination to the end.

    The history page shows 10 revisions (newest first); ``&start=N`` walks to
    older ones, and the absence of an "older changes" link marks the last page.
    We fetch successive pages -- sleeping ``delay`` between requests -- and
    concatenate their parsed revisions into one newest-first list. The next
    page's ``start`` is read from the "older changes" link rather than assumed,
    and a non-increasing ``start`` (or a page that adds no new revision numbers)
    breaks the loop as a guard against an infinite fetch.
    """
    revisions: list[dict[str, object]] = []
    seen: set[object] = set()
    start = 0
    while True:
        html = fetch(session, HISTORY_URL.format(oeis_id=oeis_id, start=start))
        for revision in parse_history(html):
            if revision["v"] not in seen:
                seen.add(revision["v"])
                revisions.append(revision)
        older = _OLDER_RE.search(html)
        if not older:
            break
        next_start = int(older.group(1))
        if next_start <= start:  # malformed/looping pagination -- stop rather than spin
            break
        start = next_start
        time.sleep(delay)
    return revisions


def append_jsonl(path: Path, obj: dict[str, object]) -> None:
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(obj, ensure_ascii=False) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR, help="output directory for the JSONL files")
    parser.add_argument("--dataset-dir", type=Path, default=OEIS_DIR, help="dataset dir whose samples.jsonl enumerates the sequences")
    parser.add_argument("--delay", type=float, default=1.0, help="seconds to sleep between HTTP requests (politeness)")
    parser.add_argument("--limit", type=int, default=None, help="only fetch the first N (not-yet-downloaded) sequences")
    parser.add_argument("--ids", nargs="+", default=None, help="fetch only these A-numbers (e.g. A129365), ignoring the manifest")
    parser.add_argument("--records-only", action="store_true", help="skip the history pages, fetch only the JSON records")
    parser.add_argument("--history-only", action="store_true", help="skip the JSON records, fetch only the history pages")
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    records_path = args.out_dir / "oeis_records.jsonl"
    history_path = args.out_dir / "oeis_history.jsonl"

    ids = args.ids if args.ids is not None else unique_oeis_ids(args.dataset_dir)
    want_records = not args.history_only
    want_history = not args.records_only

    done_records = existing_ids(records_path) if want_records else set()
    done_history = existing_ids(history_path) if want_history else set()

    # A sequence still needs work if either artifact we want is missing.
    todo = [aid for aid in ids if (want_records and aid not in done_records) or (want_history and aid not in done_history)]
    if args.limit is not None:
        todo = todo[: args.limit]

    print(
        f"{len(ids)} sequences; {len(todo)} need fetching "
        f"(records done: {len(done_records)}, history done: {len(done_history)})",
        file=sys.stderr,
    )

    session = requests.Session()
    session.headers["User-Agent"] = USER_AGENT

    for index, oeis_id in enumerate(todo, 1):
        print(f"[{index}/{len(todo)}] {oeis_id}", file=sys.stderr)
        if want_records and oeis_id not in done_records:
            body = fetch(session, RECORD_URL.format(oeis_id=oeis_id))
            results = json.loads(body)
            record = results[0] if results else None
            if record is None:
                print(f"    WARNING: no JSON record returned for {oeis_id}", file=sys.stderr)
            append_jsonl(records_path, {"oeis_id": oeis_id, "record": record})
            time.sleep(args.delay)
        if want_history and oeis_id not in done_history:
            revisions = fetch_all_revisions(session, oeis_id, delay=args.delay)
            if not revisions:
                print(f"    WARNING: parsed 0 revisions for {oeis_id}", file=sys.stderr)
            append_jsonl(history_path, {"oeis_id": oeis_id, "revisions": revisions})
            time.sleep(args.delay)

    print("done", file=sys.stderr)


if __name__ == "__main__":
    main()
