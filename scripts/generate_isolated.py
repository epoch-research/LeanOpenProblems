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

Mechanism. Lean 4's surface syntax is environment-extensible, so the cut is
driven by Lean's own parser/elaborator, not a regex. The companion Lean exe
``apn/lean/extract_ranges`` parses + elaborates each file through the frontend
and emits, per top-level command, its byte span plus the source-ranged
declarations it introduced (fully-qualified name, kind, and -- for theorems --
the elaborated statement as a stable raw-``Expr`` string). We delete the spans of
the ``theorem`` commands whose declaration is not the target and keep everything
else verbatim. There is no local Lean toolchain, so the extractor runs in the
Lean Docker image; this script drives it over ``docker exec``.

Validation gates (all hard unless noted):
  1. Every mapped conjecture name resolves to exactly one ``theorem`` decl.
  2. Re-extracting each isolated file shows exactly one ``theorem`` and it is the
     target -- and the file elaborates with no error-severity messages (this
     subsumes a compile check; ``sorry`` is a warning, not an error).
  3. The isolated target's elaborated type equals the source target's type
     (isolation never edits the statement).
  4. No isolated-filename collisions.
  5. Oracle cross-check (confidence, non-fatal): for the paper's solved problems,
     our isolated target's type matches that file's ``target_theorem_0`` type.

Setup (one-time, since there is no local Lean toolchain). Start a Lean container
with the repo mounted and build the extractor in-tree:

    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-scorer:latest sleep infinity
    docker exec apn-isolate-dev bash -lc \\
        'cd /repo/apn/lean/extract_ranges && lake build extract_ranges'

Then generate + validate (defaults target that container and in-tree exe):

    python scripts/generate_isolated.py

(The committed ``apn/lean/Dockerfile`` ``generate`` stage bakes the same extractor
to ``/opt/apn/extract_ranges/...`` for a from-image regen; pass ``--exe`` to use it.)
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
OEIS_DIR = REPO / "apn" / "data" / "oeis"
AUTO_DIR = OEIS_DIR / "Auto"
ISOLATED_DIR = OEIS_DIR / "Isolated"
MAPPING_FILE = OEIS_DIR / "THEOREM_MAPPING.txt"
REF_DIR = REPO / "reference_sources" / "alphaproof-nexus-results" / "APNOutputs" / "OEIS"

# Paths/identifiers inside the Lean container.
CONTAINER_REPO = "/repo"
CONTAINER_PROJECT = "/workspace/leanproject"
DEFAULT_CONTAINER = "apn-isolate-dev"
# Where the extractor exe lives in the container. The dev container mounts the
# repo at /repo and builds in-tree; the baked scorer image installs it under
# /opt (see apn/lean/Dockerfile).
DEV_EXE = f"{CONTAINER_REPO}/apn/lean/extract_ranges/.lake/build/bin/extract_ranges"
BAKED_EXE = "/opt/apn/extract_ranges/.lake/build/bin/extract_ranges"


# --------------------------------------------------------------------------- #
# Pure helpers (no Docker): the cut + matching logic, unit-testable.           #
# --------------------------------------------------------------------------- #
def parse_mapping(text: str) -> list[tuple[str, list[str]]]:
    """``THEOREM_MAPPING.txt`` -> ``[(conjecture_name, [file, ...]), ...]``."""
    entries: list[tuple[str, list[str]]] = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) >= 2:
            entries.append((parts[0], parts[1:]))
    return entries


def theorem_decls(filerec: dict) -> list[dict]:
    """The ``theorem``-kind declarations of a file's extractor record."""
    return [d for c in filerec["commands"] for d in c["decls"] if d["kind"] == "theorem"]


def is_theorem_command(cmd: dict) -> bool:
    """Whether a command is a standalone ``theorem``/``lemma`` declaration -- i.e.
    a cut candidate. Two kinds of declaration look like a theorem but are part of
    the spec's *definitions* and must be kept, so they are excluded:

    * A ``def``/``structure``/``inductive`` command introduces a non-theorem decl
      (the def, or the inductive + its constructor/recursor/projections), so it
      is not all-theorem. A ``structure`` that bundles several conjectures as
      Prop-valued fields emits a *theorem* projection per field (A092243), yet the
      structure is a definition -- caught by the all-theorem test.
    * A ``Prop``-valued class ``instance`` (e.g. ``instance : Fact (Nat.Prime 3)``)
      has kind "theorem" but ``isInstance`` -- caught by the no-instance test
      (A341685)."""
    return (
        bool(cmd["decls"])
        and all(d["kind"] == "theorem" for d in cmd["decls"])
        and not any(d["isInstance"] for d in cmd["decls"])
    )


def theorem_command_decls(filerec: dict) -> list[dict]:
    """The decls of the file's standalone theorem/lemma commands (the ones the
    cut operates on). Excludes theorem-kind projections of a kept structure."""
    return [d for c in filerec["commands"] if is_theorem_command(c) for d in c["decls"]]


def matches_name(decl_name: str, mapped: str) -> bool:
    """A theorem matches a mapped name if it is that name or has it as its final
    namespace component(s) -- the mapping uses short names while a few targets
    live inside a ``namespace`` (so the env name is ``Ns.short``)."""
    return decl_name == mapped or decl_name.endswith("." + mapped)


def resolve_target(name: str, filerec: dict) -> dict:
    """The unique ``theorem`` decl for mapped ``name`` (gate 1)."""
    thms = theorem_decls(filerec)
    hits = [d for d in thms if matches_name(d["name"], name)]
    if len(hits) != 1:
        raise SystemExit(
            f"{name}: expected exactly one matching theorem in "
            f"{Path(filerec['file']).name}, found {[d['name'] for d in hits]} "
            f"(all theorems: {[d['name'] for d in thms]})"
        )
    return hits[0]


def isolate(src: bytes, filerec: dict, target_decl_name: str) -> bytes:
    """Drop the source spans of every standalone theorem command except the target's.

    The extractor's command spans cleanly partition the post-header region (each
    command's end == the next command's start, leading doc-comment included), so
    we reconstruct = header + the kept commands' spans concatenated. A command is
    dropped iff it is a standalone theorem/lemma declaration (:func:`is_theorem_command`)
    whose decl is not the target; everything else (defs, structures, axioms,
    ``open``/``namespace``, comments) is kept verbatim.
    """
    commands = filerec["commands"]
    if not commands:
        return src
    kept = [
        c
        for c in commands
        if not (is_theorem_command(c) and all(d["name"] != target_decl_name for d in c["decls"]))
    ]
    out = bytearray(src[: commands[0]["startByte"]])
    for c in kept:
        out += src[c["startByte"] : c["endByte"]]
    return bytes(out)


def tidy(text: bytes) -> bytes:
    """Collapse the blank-line runs left where siblings were cut; one final NL."""
    s = text.decode("utf-8")
    s = re.sub(r"\n{3,}", "\n\n", s)
    return (s.rstrip() + "\n").encode("utf-8")


# --------------------------------------------------------------------------- #
# Docker orchestration: run the Lean extractor.                               #
# --------------------------------------------------------------------------- #
def host_to_container(path: Path) -> str:
    return f"{CONTAINER_REPO}/{path.resolve().relative_to(REPO)}"


def run_extractor(files: list[Path], container: str, exe: str) -> list[dict]:
    """Run ``extract_ranges`` over ``files`` (under ``lake env``) and parse JSON."""
    cpaths = [host_to_container(p) for p in files]
    cmd = ["docker", "exec", "-w", CONTAINER_PROJECT, container, "lake", "env", exe, *cpaths]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"extractor failed (rc={proc.returncode}).\n"
            f"STDERR tail:\n{proc.stderr[-3000:]}"
        )
    # The exe prints one compact JSON line to stdout; take the last '['-line.
    for line in reversed(proc.stdout.splitlines()):
        line = line.strip()
        if line.startswith("["):
            return json.loads(line)
    raise RuntimeError(f"no JSON in extractor stdout:\n{proc.stdout[-2000:]}")


# --------------------------------------------------------------------------- #
# Driver.                                                                      #
# --------------------------------------------------------------------------- #
def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=None, help="extractor path in container (default: dev in-tree)")
    ap.add_argument("--skip-oracle", action="store_true", help="skip the APNOutputs cross-check")
    args = ap.parse_args()
    exe = args.exe or DEV_EXE

    mapping = parse_mapping(MAPPING_FILE.read_text())
    source_files = sorted({files[0] for _, files in mapping})
    print(f"Extracting decl ranges from {len(source_files)} source files...", flush=True)
    ranges = run_extractor([AUTO_DIR / f for f in source_files], args.container, exe)
    by_file = {Path(fr["file"]).name: fr for fr in ranges}
    for fr in ranges:
        if fr["errors"]:
            print(f"  WARN source {Path(fr['file']).name} elaboration errors:")
            for e in fr["errors"][:3]:
                print("    " + e.splitlines()[0])

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    written: dict[str, str] = {}
    src_types: dict[str, str] = {}
    for name, files in mapping:
        filerec = by_file[files[0]]
        target = resolve_target(name, filerec)
        src_types[name] = target["type"]
        iso = tidy(isolate((AUTO_DIR / files[0]).read_bytes(), filerec, target["name"]))
        out = ISOLATED_DIR / f"{name}.lean"
        if out.name in written:  # gate 4
            raise SystemExit(f"isolated-filename collision: {out.name}")
        written[out.name] = name
        out.write_bytes(iso)
    print(f"Wrote {len(written)} isolated files. Validating (re-extraction)...", flush=True)

    iso_ranges = run_extractor(sorted(ISOLATED_DIR.glob("*.lean")), args.container, exe)
    iso_types: dict[str, str] = {}
    failures = 0
    for fr in iso_ranges:
        name = Path(fr["file"]).stem
        if fr["errors"]:  # gate 2 (elaboration)
            failures += 1
            print(f"  FAIL {name}: elaboration errors:\n    " + "\n    ".join(fr["errors"][:2]))
            continue
        thms = theorem_command_decls(fr)
        if len(thms) != 1:  # gate 2 (single theorem command)
            failures += 1
            print(f"  FAIL {name}: {len(thms)} theorem commands remain: {[d['name'] for d in thms]}")
            continue
        if not matches_name(thms[0]["name"], name):  # gate 2 (it is the target)
            failures += 1
            print(f"  FAIL {name}: remaining theorem {thms[0]['name']} is not the target")
            continue
        if thms[0]["type"] != src_types[name]:  # gate 3 (statement preserved)
            failures += 1
            print(f"  FAIL {name}: target type changed during isolation")
            continue
        iso_types[name] = thms[0]["type"]
    if failures:
        raise SystemExit(f"{failures} isolated file(s) failed validation.")
    print(f"All {len(iso_types)} isolated files valid: one target theorem, clean elaboration, statement preserved.")

    if not args.skip_oracle:
        oracle_cross_check(iso_types, args.container, exe)


def oracle_cross_check(iso_types: dict[str, str], container: str, exe: str) -> None:
    """Compare our isolated target statement to the paper's published challenge
    file for each solved problem (matched by elaborated type, since the paper
    renames the theorem to ``target_theorem_0``). Non-fatal: reports a summary."""
    ref_files = sorted(REF_DIR.glob("*.lean"))
    if not ref_files:
        print("Oracle: no reference files found; skipping.")
        return
    print(f"Oracle cross-check against {len(ref_files)} solved reference files...", flush=True)
    try:
        ref_ranges = run_extractor(ref_files, container, exe)
    except RuntimeError as exc:
        print(f"Oracle: reference extraction failed, inconclusive:\n{exc}")
        return
    match = mismatch = missing = 0
    for fr in ref_ranges:
        name = Path(fr["file"]).stem
        if name not in iso_types:
            missing += 1
            print(f"  ? {name}: no isolated file for this reference")
            continue
        # The paper renames the conjecture to `target_theorem_0`; the file's other
        # theorems are the published solution's helper lemmas, which we ignore.
        tgt = [d for d in theorem_decls(fr) if matches_name(d["name"], "target_theorem_0")]
        if len(tgt) != 1:
            print(f"  ? {name}: reference has {len(tgt)} `target_theorem_0` decls; skipping")
            continue
        if tgt[0]["type"] == iso_types[name]:
            match += 1
        else:
            mismatch += 1
            print(f"  MISMATCH {name}: isolated target type != reference target_theorem_0 type")
    print(f"Oracle: {match} match, {mismatch} mismatch, {missing} unmatched (of {len(ref_files)}).")


if __name__ == "__main__":
    sys.exit(main())
