# type: ignore
"""Generate the per-conjecture isolated OEIS specs in ``apn/data/oeis/Isolated/``.

Our harness scores one OEIS *conjecture* per sample, but each upstream
``Sources/*.lean`` file bundles the sequence definitions, sanity "test" lemmas, and
**one or more** conjecture theorems. SafeVerify requires every theorem in the
target file to be discharged, so a sample about conjecture *T* was only marked
correct if *all* conjectures in its file were settled. This script reconstructs
the AlphaProof Nexus paper's per-conjecture challenge files: for each mapped
conjecture it keeps the file's definitions + the single target theorem and drops
every other ``theorem``/``lemma`` (sibling conjectures *and* test lemmas), exactly
reproducing ``reference_sources/alphaproof-nexus-results/APNOutputs/OEIS/*``. The
sequence ``def`` is pinned by value in SafeVerify, so the test lemmas were never
the anti-cheat guard and can be dropped.

This is a *vendor-time* dev tool (like ``scripts/bump_version.py``), not imported
at runtime. ``apn/dataset.py`` reads the committed ``Isolated/`` files directly.

This script only *generates*. The committed ``Isolated/`` files are validated by
``tests/test_oeis_isolation.py`` -- re-extraction structural checks, the
authoritative ``lake env lean -o`` compile gate, and the paper oracle
cross-check -- all of which run the Lean toolchain in a container (the shared cut
logic and Docker plumbing live in ``scripts/isolation.py``; the OEIS data
locations in ``scripts/oeis_isolation.py``). After regenerating, run those
tests to confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean container
with the repo mounted and build the extractor in-tree:

    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-scorer:latest sleep infinity
    docker exec apn-isolate-dev bash -lc \\
        'cd /repo/apn/lean/extract_ranges && lake build extract_ranges'

Then generate (defaults target that container and in-tree exe):

    python scripts/generate_oeis_isolated.py

(The committed ``apn/lean/Dockerfile`` ``generate`` stage bakes the same extractor
to ``/opt/apn/extract_ranges/...`` for a from-image regen; pass ``--exe`` to use it.)
"""

from __future__ import annotations

import argparse
import sys

from apn.dataset import load_manifest
from scripts.isolation import (
    DEFAULT_CONTAINER,
    DEV_EXE,
    dependency_closure,
    isolate,
    kept_flags,
    resolve_target,
    run_extractor,
    tidy,
)
from scripts.oeis_isolation import OEIS_DIR, ISOLATED_DIR, SOURCES_DIR


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=DEV_EXE, help="extractor path in container (default: dev in-tree)")
    args = ap.parse_args()

    rows = load_manifest(OEIS_DIR)
    source_files = sorted({r.source for r in rows})
    print(f"Extracting decl ranges from {len(source_files)} source files...", flush=True)
    ranges = run_extractor([OEIS_DIR / s for s in source_files], args.container, args.exe)
    by_file = {fr["file"].rsplit("/", 1)[-1]: fr for fr in ranges}

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    written: dict[str, str] = {}
    for row in rows:
        filerec = by_file[row.source.rsplit("/", 1)[-1]]
        target = resolve_target(row.id, filerec)  # the unique target theorem
        closure = dependency_closure(filerec, target["name"])
        flags = kept_flags(filerec, closure)
        iso = tidy(isolate((OEIS_DIR / row.source).read_bytes(), filerec, flags))
        out = ISOLATED_DIR / f"{row.id}.lean"
        # No filename collisions, casefolded: the repo must check out intact
        # on case-insensitive filesystems.
        if out.name.casefold() in written:
            raise SystemExit(f"isolated-filename collision: {out.name}")
        written[out.name.casefold()] = row.id
        out.write_bytes(iso)

    print(
        f"Wrote {len(written)} isolated files to {ISOLATED_DIR}.\n"
        "Validate with: pytest tests/test_oeis_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
