#!/usr/bin/env python3
"""Build the offline arXiv-math grep corpus baked into the agent-corpus image.

The agent's sandbox has no network, so the literature it can consult must be on
disk. This script produces that on-disk corpus from two public, pinned sources:

  * hoskinson-center/proof-pile -- a 2022 snapshot whose ``arxiv`` subset is
    pure-math arXiv LaTeX *source*, filtered to .tex, English-only, junk
    dropped. Being a 2022 snapshot makes it leak-safe by construction: it
    physically cannot contain a solution to a conjecture that is still open as
    of the benchmark paper (arXiv:2605.22763, May 2026). We deliberately do NOT
    top it up with newer papers -- that would reintroduce the leak risk.
  * librarian-bots/arxiv-metadata-snapshot -- a CC0 mirror of the Cornell/Kaggle
    arXiv metadata dump (title, authors, abstract, categories, dates), joined on
    arXiv id to give the agent a topic-search surface the .tex bodies lack.

Output layout (``--out``)::

    corpus/
      src/<id>.tex      one file per paper (latest version, sections concat'd)
      metadata.jsonl    one JSON record per paper present in src/

The agent greps this with plain ``rg``/``cat`` in its bash shell -- there are no
bespoke tools. Two-stage search: grep ``metadata.jsonl`` to find papers by
topic/category, then grep their ``src/<id>.tex`` for the actual mathematics.

Both source revisions are pinned below for reproducible image builds. Run inside
the Dockerfile ``corpus`` stage; for a local eyeball::

    uv run --with huggingface_hub --with pyarrow \\
        python apn/lean/build_corpus.py --out ./corpus --shards 1 --no-metadata
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

# Pinned source revisions (see module docstring). Bump deliberately; the image
# tag is keyed on apn.__version__, so a corpus change rides a version bump.
PROOF_PILE_REPO = "hoskinson-center/proof-pile"
PROOF_PILE_REV = "490b980249446f2f3bd2df3a8cf085d0f2de240a"
METADATA_REPO = "librarian-bots/arxiv-metadata-snapshot"
METADATA_REV = "489d966b008f003cb3a5d3482041b7ed1946cd58"

# proof-pile ships a single "default" config split across these gzipped JSONL
# shards; the arxiv subset is interleaved (rows where meta.config == "arxiv").
PROOF_PILE_SHARDS = (
    [f"train/proofpile_train_{i}.jsonl.gz" for i in range(21)]
    + ["dev/proofpile_dev.jsonl.gz", "test/proofpile_test.jsonl.gz"]
)
METADATA_SHARDS = [f"data/train-{i:05d}-of-00010.parquet" for i in range(10)]

# Benchmark paper's month; the corpus must predate it. The 2022 snapshot is
# already safely below this -- the check is a cheap tripwire, not the defense.
_CUTOFF_DATE = "2026-05-01"


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
    """Filesystem-safe form of an arXiv id (the src/ filename stem)."""
    return canonical.replace("/", "_")


def _iter_arxiv_rows(shard_paths: list[Path]) -> Iterator[tuple[str, int, str, str]]:
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


def download_shards(repo: str, rev: str, names: list[str], cache_dir: str | None) -> list[Path]:
    from huggingface_hub import hf_hub_download  # type: ignore[import-not-found]

    paths = []
    for name in names:
        print(f"  downloading {repo}@{rev[:8]} {name}", flush=True)
        paths.append(
            Path(
                hf_hub_download(
                    repo_id=repo,
                    filename=name,
                    revision=rev,
                    repo_type="dataset",
                    cache_dir=cache_dir,
                )
            )
        )
    return paths


def _safe_rest(rest: str) -> str | None:
    """Sanitize a paper-relative path; reject traversal/absolute paths."""
    parts = [p for p in rest.split("/") if p not in ("", ".")]
    if not parts or any(p == ".." for p in parts):
        return None
    return "/".join(parts)


def build_source(shard_paths: list[Path], out: Path, max_papers: int | None) -> dict[str, str]:
    """Explode arxiv rows into ``out/src/<id>/<original-path>.tex``.

    Each proof-pile row is one source file, written back at its original path
    under a per-paper directory -- so a paper's ``\\input``/``\\include`` tree is
    preserved as real sibling files, not flattened into one blob. Only the latest
    version of each paper is kept. Returns ``{canonical_id: relative_paper_dir}``
    for the papers written, to drive the metadata join.

    Pass 1 finds the latest version per id (small: id -> int). Pass 2 streams the
    rows again and writes each chosen-version file -- bounded memory, no
    full-corpus buffering.
    """
    print("pass 1/2: resolving latest version per paper", flush=True)
    best: dict[str, int] = {}
    for canonical, version, _rest, _text in _iter_arxiv_rows(shard_paths):
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
    for canonical, version, rest, text in _iter_arxiv_rows(shard_paths):
        if canonical not in keep or version != best[canonical]:
            continue
        rel_rest = _safe_rest(rest)
        if rel_rest is None:
            continue
        sid = safe_id(canonical)
        paper_dir = src_dir / sid
        dest = paper_dir / rel_rest
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
                if upd_s >= _CUTOFF_DATE:
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
        f"{late} have a post-{_CUTOFF_DATE} update_date)",
        flush=True,
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, default=Path("corpus"), help="output directory")
    ap.add_argument("--cache-dir", default=None, help="HF download cache dir")
    ap.add_argument(
        "--shards", type=int, default=None,
        help="limit to the first N proof-pile shards (smoke test; yields partial "
        "papers since a paper's sections may span shards)",
    )
    ap.add_argument("--max-papers", type=int, default=None, help="cap papers written (smoke test)")
    ap.add_argument("--no-metadata", action="store_true", help="skip the metadata join")
    args = ap.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)

    shard_names = PROOF_PILE_SHARDS[: args.shards] if args.shards else PROOF_PILE_SHARDS
    print(f"=== proof-pile: {len(shard_names)} shard(s) ===", flush=True)
    shard_paths = download_shards(PROOF_PILE_REPO, PROOF_PILE_REV, shard_names, args.cache_dir)
    written = build_source(shard_paths, args.out, args.max_papers)
    if not written:
        print("no papers written", file=sys.stderr)
        return 1

    if args.no_metadata:
        print("skipping metadata (--no-metadata)", flush=True)
    else:
        print(f"=== metadata: {len(METADATA_SHARDS)} shard(s) ===", flush=True)
        meta_paths = download_shards(METADATA_REPO, METADATA_REV, METADATA_SHARDS, args.cache_dir)
        build_metadata(meta_paths, written, args.out)

    print("done.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
