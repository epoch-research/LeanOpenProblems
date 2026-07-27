"""OpenAlex pipeline: papers referencing each OEIS sequence (deduped within OpenAlex).

Per sequence, union three OpenAlex full-text queries:
  B. A-number, subfield-constrained -- ``fulltext.search:A#####`` with
     ``primary_topic.subfield.id`` in the core math set (Algebra & Number Theory,
     Discrete Math & Combinatorics, Theoretical CS, Computational Math).
  C. URL-anchored, any field -- ``fulltext.search:"oeis.org/A#####"`` (quoted phrase).
  D. OEIS co-occurrence, any field -- ``fulltext.search:OEIS A#####`` (unquoted = both
     tokens anywhere). The "OEIS" token kills cross-field collisions without a
     subfield filter; dominates B on recall but isn't a strict superset of C, so we
     union all three.

Counts are ``meta.count`` (exact totals); the citation list is the deduped union of
B/C/D, fetched in full via cursor pagination. Self-references to this project are
excluded. This is the OpenAlex pipeline only -- the OEIS-native bibliography (the
entry's own link[]/reference[]) is a separate pipeline (scripts/extract_bibliography.py).

Output: JSONL keyed by ``oeis_id``, resumable (ids already written are skipped).
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

import requests

ROOT = Path(__file__).parent.parent
MAPPING = ROOT / "apn" / "data" / "oeis" / "THEOREM_MAPPING.txt"

OPENALEX = "https://api.openalex.org/works"
SUBFIELDS = "primary_topic.subfield.id:subfields/2602|subfields/2607|subfields/2614|subfields/2605"
SELECT = "id,doi,title,publication_year,authorships,primary_location,cited_by_count"
PAGE_CAP = 2000  # runaway guard on full-text fetch; logged if hit (no silent truncation)
PACE = 0.2  # seconds between requests -- the full run is ~1300 requests; pace to avoid a rate-limit block
_NUM_RE = re.compile(r"^(\d+)_")
_SELF_REF = re.compile(r"alphaproof|alphaproof-nexus-results|2605\.22763|AI-Driven Formal Proof Search", re.I)


def load_env() -> None:
    for line in (ROOT / ".env").read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            os.environ.setdefault(k, v.strip().strip('"').strip("'"))


def group_conjectures() -> dict[str, list[str]]:
    by_seq: dict[str, list[str]] = defaultdict(list)
    for line in MAPPING.read_text().splitlines():
        parts = line.split()
        if len(parts) >= 2:
            m = _NUM_RE.match(parts[1])
            if m:
                by_seq[f"A{int(m.group(1)):06d}"].append(parts[0])
    return dict(by_seq)


def get_with_backoff(session: requests.Session, params: dict, *, retries: int = 5) -> requests.Response:
    """GET with 429 handling: short transient backoff, but ABORT on a long block."""
    for attempt in range(retries):
        r = session.get(OPENALEX, params=params, timeout=60)
        if r.status_code == 429:
            ra = float(r.headers.get("retry-after", 2.0**attempt))
            if ra > 120:
                raise SystemExit(f"OpenAlex hard rate-limit block: retry-after={ra:.0f}s. "
                                 f"Aborting (resumable: rerun later).")
            time.sleep(ra)
            continue
        r.raise_for_status()
        time.sleep(PACE)  # polite spacing between requests
        return r
    raise RuntimeError("429 retries exhausted")


def fetch_all(session: requests.Session, filt: str) -> tuple[int, list[dict]]:
    """Full result set for a filter via cursor pagination. Returns (meta.count, papers)."""
    cursor, results, count = "*", [], 0
    while cursor:
        params = {"filter": filt, "select": SELECT, "per_page": 200, "cursor": cursor,
                  "api_key": os.environ["OPENALEX_API_KEY"], "mailto": "tom@epochai.org"}
        j = get_with_backoff(session, params).json()
        count = j["meta"]["count"]
        page = j.get("results", [])
        for w in page:
            loc = w.get("primary_location") or {}
            src = loc.get("source") or {}
            results.append({
                "title": w.get("title"),
                "year": w.get("publication_year"),
                "doi": (w.get("doi") or "").replace("https://doi.org/", "") or None,
                "openalex_id": (w.get("id") or "").split("/")[-1],
                "venue": src.get("display_name"),
                "authors": [a["author"]["display_name"] for a in w.get("authorships", [])[:8]],
                "cited_by": w.get("cited_by_count"),
            })
        cursor = j["meta"].get("next_cursor")
        if not page or len(results) >= PAGE_CAP:
            if len(results) < count:
                print(f"  WARNING {filt}: fetched {len(results)}/{count} (cap)", file=sys.stderr)
            break
    return count, results


def dedup_key(p: dict) -> str:
    if p.get("doi"):
        return "doi:" + p["doi"].lower()
    return "title:" + re.sub(r"\W+", "", (p.get("title") or "").lower())[:60]


def openalex_citations(session: requests.Session, oeis_id: str) -> dict:
    queries = {
        "subfield": f"fulltext.search:{oeis_id},{SUBFIELDS}",
        "url": f'fulltext.search:"oeis.org/{oeis_id}"',
        "oeis": f"fulltext.search:OEIS {oeis_id}",
    }
    counts: dict[str, int] = {}
    seen: dict[str, dict] = {}
    for name, filt in queries.items():
        counts[name], papers = fetch_all(session, filt)
        for p in papers:
            if _SELF_REF.search(p.get("title") or ""):
                continue
            k = dedup_key(p)
            if k in seen:
                seen[k]["sources"].append(name)
            else:
                p["sources"] = [name]
                seen[k] = p
    return {"oeis_id": oeis_id, "counts": counts, "citations": list(seen.values())}


def done_ids(path: Path) -> set[str]:
    if not path.is_file():
        return set()
    return {json.loads(l)["oeis_id"] for l in path.read_text().splitlines() if l.strip()}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=ROOT / "apn" / "data" / "oeis" / "openalex_citations.jsonl")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--n", type=int, default=100)
    ap.add_argument("--ids", nargs="+", default=None)
    ap.add_argument("--seed", type=int, default=7)
    args = ap.parse_args()

    load_env()
    by_seq = group_conjectures()
    session = requests.Session()

    if args.ids:
        targets = list(args.ids)
    elif args.all:
        targets = sorted(by_seq)
    else:
        targets = random.Random(args.seed).sample(sorted(by_seq), args.n)

    done = done_ids(args.out)
    todo = [s for s in targets if s not in done]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    print(f"{len(targets)} targeted; {len(todo)} to fetch ({len(done)} done)", flush=True)

    start = time.monotonic()
    agg = defaultdict(int)
    for i, oeis_id in enumerate(todo, 1):
        res = openalex_citations(session, oeis_id)
        with args.out.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(res, ensure_ascii=False) + "\n")
        c, n_cit = res["counts"], len(res["citations"])
        agg["cit"] += n_cit
        agg["zero"] += n_cit == 0
        eta = (time.monotonic() - start) / i * (len(todo) - i) / 60
        print(f"[{i}/{len(todo)}] {oeis_id} subf={c['subfield']} url={c['url']} oeis={c['oeis']} "
              f"union={n_cit} (ETA {eta:.0f}m)", flush=True)
    print(f"\nSUMMARY: citations={agg['cit']} zero={agg['zero']}/{len(todo)}", flush=True)


if __name__ == "__main__":
    main()
