"""LLM-structure the OEIS-native bibliography (link[]/reference[] strings).

PROTOTYPE / exploratory: runs on a sample and prints structured output beside the
raw strings so extraction quality can be checked before a full run.

The OEIS record gives bibliography as strings: link[] are HTML-anchor-bearing
('Author, <a href="URL">Title</a>, Venue Vol (Year), pages') and reference[] are
free-text citations. We deterministically drop OEIS-internal links (b-files,
index, self-refs) and hand the rest to GPT-5.5, which parses each into structured
fields (title, authors, venue, year, url, doi, arxiv_id) and classifies kind --
recovering the author/venue/year we'd otherwise discard and surfacing doi/arxiv_id
for later dedup against the OpenAlex (external) records.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
import time
from collections import defaultdict
from pathlib import Path

import openai

ROOT = Path(__file__).parent.parent
RAW = ROOT / "apn" / "data" / "oeis" / "raw"
MAPPING = ROOT / "apn" / "data" / "oeis" / "THEOREM_MAPPING.txt"
MODEL = "gpt-5.5"
_NUM_RE = re.compile(r"^(\d+)_")
_INTERNAL = re.compile(r"(^/|oeis\.org/(A\d|wiki|search)|/b\d+\.txt|/a\d+\.|/wiki/)", re.I)
_SELF_REF = re.compile(r"alphaproof|alphaproof-nexus-results|2605\.22763|AI-Driven Formal Proof Search", re.I)
_HREF_RE = re.compile(r'href="([^"]+)"')


def load_env() -> None:
    for line in (ROOT / ".env").read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            os.environ.setdefault(k, v.strip().strip('"').strip("'"))


def load_records() -> dict[str, dict]:
    out: dict[str, dict] = {}
    for line in (RAW / "oeis_records.jsonl").read_text().splitlines():
        if line.strip():
            o = json.loads(line)
            out[o["oeis_id"]] = o["record"] or {}
    return out


def group_conjectures() -> dict[str, list[str]]:
    by_seq: dict[str, list[str]] = defaultdict(list)
    for line in MAPPING.read_text().splitlines():
        parts = line.split()
        if len(parts) >= 2:
            m = _NUM_RE.match(parts[1])
            if m:
                by_seq[f"A{int(m.group(1)):06d}"].append(parts[0])
    return dict(by_seq)


def candidate_entries(record: dict) -> list[dict]:
    """Bibliography strings worth structuring: external links + all references."""
    entries: list[dict] = []
    for s in record.get("link", []) or []:
        href = _HREF_RE.search(s)
        if href and (_INTERNAL.search(href.group(1)) or _SELF_REF.search(s)):
            continue  # b-file / index / self-ref
        if _SELF_REF.search(s):
            continue
        entries.append({"source": "link", "raw": s})
    for s in record.get("reference", []) or []:
        if not _SELF_REF.search(s):
            entries.append({"source": "reference", "raw": s})
    return entries


SCHEMA = {
    "type": "object", "additionalProperties": False,
    "properties": {"entries": {"type": "array", "items": {
        "type": "object", "additionalProperties": False,
        "properties": {
            "i": {"type": "integer"},
            "kind": {"type": "string", "enum": ["journal_article", "preprint", "book", "thesis", "conference", "webpage", "software", "dataset", "other"]},
            "title": {"type": ["string", "null"]},
            "authors": {"type": "array", "items": {"type": "string"}},
            "venue": {"type": ["string", "null"]},
            "year": {"type": ["integer", "null"]},
            "url": {"type": ["string", "null"]},
            "doi": {"type": ["string", "null"]},
            "arxiv_id": {"type": ["string", "null"]},
        },
        "required": ["i", "kind", "title", "authors", "venue", "year", "url", "doi", "arxiv_id"],
    }}}, "required": ["entries"],
}

SYSTEM = ("Parse each OEIS bibliography entry into structured fields. Entries come from an OEIS sequence's "
          "'link' section (HTML, the URL is in the href attribute) or 'reference' section (free-text citation). "
          "For each, by its index i, extract: title; authors (list, in order; [] if none); venue (journal/publisher/site); "
          "year (4-digit int or null); url (from href, or null); doi (bare 10.xxxx/... if present in url or text, else null); "
          "arxiv_id (e.g. 1203.5413, from an arxiv URL or text, else null); and kind. Use null/[] for absent fields; "
          "do not invent values. Classify kind by what the entry actually is (a journal_article, preprint (e.g. arXiv), "
          "book, thesis, conference paper, webpage, software, dataset, or other).")


CHUNK = 40  # bound entries per LLM call; a few famous sequences have 100+ (A000040 has 152)


def extract(client: openai.OpenAI, oeis_id: str, entries: list[dict], effort: str) -> list[dict]:
    """Parsed citation records for one sequence, with `source` mapped back from index `i`.

    Entries are chunked so a huge bibliography (the primes, Catalan, ...) doesn't
    become one oversized high-effort call that stalls or truncates.
    """
    out: list[dict] = []
    for start in range(0, len(entries), CHUNK):
        batch = entries[start:start + CHUNK]
        if len(entries) > CHUNK:
            print(f"{time.strftime('%H:%M:%S')}   {oeis_id} chunk {start}-{start+len(batch)}/{len(entries)}", flush=True)
        listing = "\n".join(f"[{i}] ({e['source']}) {e['raw']}" for i, e in enumerate(batch))
        resp = client.chat.completions.create(
            model=MODEL, reasoning_effort=effort,
            response_format={"type": "json_schema", "json_schema": {"name": "bib", "schema": SCHEMA, "strict": True}},
            messages=[{"role": "system", "content": SYSTEM},
                      {"role": "user", "content": f"OEIS {oeis_id} bibliography entries:\n{listing}"}],
        )
        for p in json.loads(resp.choices[0].message.content)["entries"]:
            i = p.pop("i")
            p["source"] = batch[i]["source"] if 0 <= i < len(batch) else None
            out.append(p)
    return out


def done_ids(path: Path) -> set[str]:
    if not path.is_file():
        return set()
    return {json.loads(l)["oeis_id"] for l in path.read_text().splitlines() if l.strip()}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=ROOT / "apn" / "data" / "oeis" / "oeis_native_citations.jsonl")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--ids", nargs="+", default=None)
    ap.add_argument("--n", type=int, default=10)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--effort", default="high")
    args = ap.parse_args()

    load_env()
    client = openai.OpenAI(timeout=300.0, max_retries=2)
    records = load_records()
    by_seq = group_conjectures()

    if args.ids:
        targets = list(args.ids)
    elif args.all:
        targets = sorted(by_seq)
    else:
        targets = random.Random(args.seed).sample(sorted(by_seq), args.n)

    done = done_ids(args.out)
    todo = [s for s in targets if s not in done]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    print(f"{len(targets)} targeted; {len(todo)} to do ({len(done)} done)", flush=True)

    for i, oeis_id in enumerate(todo, 1):
        entries = candidate_entries(records.get(oeis_id, {}))
        try:
            citations = extract(client, oeis_id, entries, args.effort) if entries else []
        except Exception as error:  # noqa: BLE001 -- resumable rerun retries
            print(f"{time.strftime('%H:%M:%S')} [{i}/{len(todo)}] {oeis_id} FAILED: {error}", flush=True)
            continue
        with args.out.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps({"oeis_id": oeis_id, "citations": citations}, ensure_ascii=False) + "\n")
        kinds = ",".join(sorted({c["kind"] for c in citations})) or "-"
        print(f"{time.strftime('%H:%M:%S')} [{i}/{len(todo)}] {oeis_id} "
              f"{len(entries)} entries -> {len(citations)} citations [{kinds}]", flush=True)


if __name__ == "__main__":
    main()
