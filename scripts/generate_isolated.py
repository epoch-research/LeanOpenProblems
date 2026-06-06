# type: ignore
"""Generate the per-conjecture isolated OEIS specs in ``apn/data/oeis/Isolated/``.

Our harness scores one OEIS *conjecture* per sample, but each upstream
``Auto/*.lean`` file bundles the sequence definitions, sanity "test" lemmas, and
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
logic and Docker plumbing live in ``scripts/oeis_isolation.py``). After
regenerating, run those tests to confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean container
with the repo mounted and build the extractor in-tree:

    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-scorer:latest sleep infinity
    docker exec apn-isolate-dev bash -lc \\
        'cd /repo/apn/lean/extract_ranges && lake build extract_ranges'

Then generate (defaults target that container and in-tree exe):

    python scripts/generate_isolated.py

(The committed ``apn/lean/Dockerfile`` ``generate`` stage bakes the same extractor
to ``/opt/apn/extract_ranges/...`` for a from-image regen; pass ``--exe`` to use it.)
"""

from __future__ import annotations

import argparse
import sys

from oeis_isolation import (
    AUTO_DIR,
    DEFAULT_CONTAINER,
    DEV_EXE,
    ISOLATED_DIR,
    MAPPING_FILE,
    dependency_closure,
    isolate,
    kept_flags,
    parse_mapping,
    resolve_target,
    run_extractor,
    tidy,
)


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=DEV_EXE, help="extractor path in container (default: dev in-tree)")
    args = ap.parse_args()

    mapping = parse_mapping(MAPPING_FILE.read_text())
    source_files = sorted({files[0] for _, files in mapping})
    print(f"Extracting decl ranges from {len(source_files)} source files...", flush=True)
    ranges = run_extractor([AUTO_DIR / f for f in source_files], args.container, args.exe)
    by_file = {fr["file"].rsplit("/", 1)[-1]: fr for fr in ranges}

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    written: dict[str, str] = {}
    for name, files in mapping:
        filerec = by_file[files[0]]
        target = resolve_target(name, filerec)  # the unique target theorem
        closure = dependency_closure(filerec, target["name"])
        flags = kept_flags(filerec, closure)
        iso = tidy(isolate((AUTO_DIR / files[0]).read_bytes(), filerec, flags))
        out = ISOLATED_DIR / f"{name}.lean"
        if out.name in written:  # no filename collisions
            raise SystemExit(f"isolated-filename collision: {out.name}")
        written[out.name] = name
        out.write_bytes(iso)

    print(
        f"Wrote {len(written)} isolated files to {ISOLATED_DIR}.\n"
        "Validate with: pytest tests/test_oeis_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
