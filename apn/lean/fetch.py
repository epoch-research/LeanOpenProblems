#!/usr/bin/env python3
"""Download-only stages of the corpus build: fetch a pinned HF dataset to disk.

Used by the two ``corpus_fetch_*`` Docker stages -- one per source -- which do
nothing but pull files from the HF Hub at a pinned revision into ``--dest``.
Keeping download separate from processing (build_corpus.py) means editing the
join logic never re-downloads these ~9 GB. This script has no dependency on the
processing code, so editing that never busts these stages either.

Sources (both public, no auth):
  * hoskinson-center/proof-pile -- a 2022 snapshot; its ``arxiv`` subset is the
    pure-math LaTeX source. A 2022 snapshot is leak-safe by construction.
  * librarian-bots/arxiv-metadata-snapshot -- CC0 mirror of the Cornell/Kaggle
    arXiv metadata dump.

Revisions are pinned for reproducible builds; bump deliberately (a corpus change
rides an apn.__version__ bump, which keys the image tag).
"""

from __future__ import annotations

import argparse
import shutil
import sys
from pathlib import Path

# repo -> (repo_id, revision, [files]).
SOURCES: dict[str, tuple[str, str, list[str]]] = {
    "proofpile": (
        "hoskinson-center/proof-pile",
        "490b980249446f2f3bd2df3a8cf085d0f2de240a",
        [f"train/proofpile_train_{i}.jsonl.gz" for i in range(21)]
        + ["dev/proofpile_dev.jsonl.gz", "test/proofpile_test.jsonl.gz"],
    ),
    "metadata": (
        "librarian-bots/arxiv-metadata-snapshot",
        "489d966b008f003cb3a5d3482041b7ed1946cd58",
        [f"data/train-{i:05d}-of-00010.parquet" for i in range(10)],
    ),
}


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--repo", choices=sorted(SOURCES), required=True)
    ap.add_argument("--dest", type=Path, required=True, help="directory to download into")
    ap.add_argument("--cache-dir", default=None, help="HF download cache (delete after)")
    ap.add_argument("--limit", type=int, default=None, help="first N files only (smoke test)")
    args = ap.parse_args()

    from huggingface_hub import hf_hub_download  # type: ignore[import-not-found]

    repo, rev, names = SOURCES[args.repo]
    if args.limit is not None:
        names = names[: args.limit]
    args.dest.mkdir(parents=True, exist_ok=True)
    for name in names:
        print(f"  downloading {repo}@{rev[:8]} {name}", flush=True)
        # Download to the cache, then copy to dest as a real file (not a cache
        # symlink) so the COPY --from into the build stage carries actual data.
        cached = hf_hub_download(
            repo_id=repo, filename=name, revision=rev, repo_type="dataset", cache_dir=args.cache_dir
        )
        out = args.dest / name
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(cached, out)
    print(f"fetched {len(names)} files to {args.dest}", flush=True)
    if not names:
        print("no files fetched", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
