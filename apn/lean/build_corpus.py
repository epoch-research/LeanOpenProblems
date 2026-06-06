#!/usr/bin/env python3
"""Processing stage of the corpus build: join the downloaded data into /corpus.

Reads the proof-pile shards and metadata parquet that the two fetch stages
already downloaded (``--shards-dir`` / ``--meta-dir``, populated by fetch.py) and
writes the final artifacts -- no network here, so editing this never re-runs the
downloads:

    out/src/<id>/<file>.tex   per-paper LaTeX source trees (latest version),
                              preserving each paper's \\input/\\include files
                              rather than flattening them into one blob.
    out/metadata.jsonl        one JSON record per src/ paper: every field from
                              the metadata dump, plus a synthetic `file` pointing
                              at the paper's src/ dir.

The agent greps the result with plain ``rg``/``cat``: grep ``metadata.jsonl`` to
find papers by topic, then read their ``src/<id>/`` directory. The 2022
proof-pile snapshot is leak-safe by construction (it predates the benchmark
paper), so we don't top it up with newer papers.

Local eyeball (after fetch.py populated ./shards and ./meta)::

    uv run --with pyarrow python apn/lean/build_corpus.py \\
        --shards-dir ./shards --meta-dir ./meta --out ./corpus
"""

from __future__ import annotations

import argparse
import gzip
import json
import re
import shutil
import sys
from collections.abc import Iterator
from pathlib import Path

# Benchmark paper's month; the corpus must predate it. The 2022 snapshot is
# already safely below this -- the check is a cheap tripwire, not the defense.
CUTOFF_DATE = "2026-05-01"


def parse_arxiv_path(file_field: str) -> tuple[str, int, str] | None:
    """Parse a proof-pile arxiv ``meta.file`` into ``(canonical_id, version, rest)``.

    Paths look like ``1812.02537/v5 arxiv/sections/5_interpolation.tex`` (modern)
    or ``math0211159/v2 arxiv/main.tex`` (pre-2007 scheme, slash dropped). Returns
    ``None`` for anything we can't confidently identify.
    """
    parts = file_field.split("/")
    if len(parts) < 2:
        return None
    raw_id = parts[0].strip()
    vm = re.search(r"v(\d+)", parts[1])
    version = int(vm.group(1)) if vm else 1
    rest = "/".join(parts[2:]) if len(parts) > 2 else parts[1]

    if re.fullmatch(r"\d{4}\.\d{4,5}", raw_id):
        canonical = raw_id  # modern: 1812.02537
    elif re.fullmatch(r"[a-z-]+(\.[A-Z]{2})?\d{7}", raw_id):
        # pre-2007: reinsert the slash arXiv (and the metadata dump) use, e.g.
        # math0211159 -> math/0211159, math.AG0501001 -> math.AG/0501001.
        canonical = re.sub(r"(\d{7})$", r"/\1", raw_id)
    else:
        return None
    return canonical, version, rest


def safe_id(canonical: str) -> str:
    """Filesystem-safe form of an arXiv id (the src/<id> directory name)."""
    return canonical.replace("/", "_")


def safe_rest(rest: str) -> str | None:
    """Sanitize a paper-relative path; reject traversal/absolute paths."""
    parts = [p for p in rest.split("/") if p not in ("", ".")]
    if not parts or any(p == ".." for p in parts):
        return None
    return "/".join(parts)


def iter_arxiv_rows(shard_paths: list[Path]) -> Iterator[tuple[str, int, str, str]]:
    """Yield ``(canonical_id, version, rest, text)`` for every arxiv .tex row."""
    for shard in shard_paths:
        with gzip.open(shard, "rt", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    row = json.loads(line)
                except json.JSONDecodeError:
                    continue
                meta = row.get("meta") or {}
                if meta.get("config") != "arxiv":
                    continue
                parsed = parse_arxiv_path(str(meta.get("file", "")))
                if parsed is None:
                    continue
                canonical, version, rest = parsed
                yield canonical, version, rest, row.get("text", "")


def build_source(shard_paths: list[Path], out: Path, max_papers: int | None) -> dict[str, str]:
    """Explode arxiv rows into ``out/src/<id>/<original-path>.tex``.

    Each proof-pile row is one source file, written back at its original path
    under a per-paper directory. Only the latest version of each paper is kept.
    Returns ``{canonical_id: "src/<dir>"}`` to drive the metadata join.

    Pass 1 finds the latest version per id (small: id -> int). Pass 2 streams the
    rows again and writes each chosen-version file -- bounded memory.
    """
    print("pass 1/2: resolving latest version per paper", flush=True)
    best: dict[str, int] = {}
    for canonical, version, _rest, _text in iter_arxiv_rows(shard_paths):
        if version > best.get(canonical, 0):
            best[canonical] = version
    print(f"  {len(best)} distinct papers", flush=True)

    keep = set(best)
    if max_papers is not None:
        keep = set(sorted(best)[:max_papers])
        print(f"  --max-papers: keeping {len(keep)}", flush=True)

    src_dir = out / "src"
    if src_dir.exists():
        shutil.rmtree(src_dir)
    src_dir.mkdir(parents=True)

    print("pass 2/2: writing src/<id>/<file>.tex", flush=True)
    written: dict[str, str] = {}
    files = 0
    for canonical, version, rest, text in iter_arxiv_rows(shard_paths):
        if canonical not in keep or version != best[canonical]:
            continue
        rel_rest = safe_rest(rest)
        if rel_rest is None:
            continue
        sid = safe_id(canonical)
        dest = src_dir / sid / rel_rest
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text, encoding="utf-8")
        written[canonical] = f"src/{sid}"
        files += 1
    print(f"  wrote {files} files across {len(written)} papers to {src_dir}", flush=True)
    return written


def build_metadata(meta_paths: list[Path], written: dict[str, str], out: Path) -> None:
    """Join the metadata dump against ``written`` and emit ``out/metadata.jsonl``."""
    import pyarrow.parquet as pq  # type: ignore[import-not-found]

    wanted = set(written)
    records: dict[str, dict[str, object]] = {}
    late = 0
    for shard in meta_paths:
        print(f"  scanning {shard.name}", flush=True)
        pf = pq.ParquetFile(shard)
        # No `columns=` filter: keep every field from the dump verbatim and let
        # the agent make sense of them. We only add a synthetic `file` pointing
        # at the paper's src/ dir.
        for batch in pf.iter_batches(batch_size=65536):
            cols = batch.to_pydict()
            for i, aid in enumerate(cols["id"]):
                if aid not in wanted or aid in records:
                    continue
                record = {key: col[i] for key, col in cols.items()}
                record["file"] = written[aid]
                records[aid] = record
                upd = cols["update_date"][i]
                upd_s = upd.isoformat()[:10] if hasattr(upd, "isoformat") else str(upd)[:10]
                if upd_s >= CUTOFF_DATE:
                    late += 1  # a later metadata revision; the paper itself is 2022

    path = out / "metadata.jsonl"
    with path.open("w", encoding="utf-8") as fh:
        for aid in sorted(records):
            # default=str stringifies non-JSON types (e.g. the update_date
            # timestamp) so every record stays one grep-friendly line.
            fh.write(json.dumps(records[aid], ensure_ascii=False, default=str) + "\n")
    missing = len(wanted) - len(records)
    print(
        f"  wrote {len(records)} records to {path} "
        f"({missing} src papers had no metadata match; "
        f"{late} have a post-{CUTOFF_DATE} update_date)",
        flush=True,
    )


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--shards-dir", type=Path, required=True, help="dir of proof-pile .jsonl.gz")
    ap.add_argument("--meta-dir", type=Path, required=True, help="dir of metadata .parquet")
    ap.add_argument("--out", type=Path, default=Path("corpus"), help="output directory")
    ap.add_argument("--max-papers", type=int, default=None, help="cap papers written (smoke test)")
    args = ap.parse_args()

    shard_paths = sorted(args.shards_dir.rglob("*.jsonl.gz"))
    if not shard_paths:
        print(f"no .jsonl.gz under {args.shards_dir} -- run fetch.py --repo proofpile", file=sys.stderr)
        return 1
    args.out.mkdir(parents=True, exist_ok=True)
    print(f"=== source: {len(shard_paths)} shard(s) ===", flush=True)
    written = build_source(shard_paths, args.out, args.max_papers)
    if not written:
        print("no papers written", file=sys.stderr)
        return 1

    meta_paths = sorted(args.meta_dir.rglob("*.parquet"))
    if not meta_paths:
        print(f"no .parquet under {args.meta_dir} -- run fetch.py --repo metadata", file=sys.stderr)
        return 1
    print(f"=== metadata: {len(meta_paths)} shard(s) ===", flush=True)
    build_metadata(meta_paths, written, args.out)
    print("done.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
