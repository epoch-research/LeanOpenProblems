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

A ``theorem``/``lemma`` is kept iff it is the target *or* a definitional
dependency: a kept ``def`` may pass a ``lemma`` as a proof term (e.g. a
nonemptiness proof to ``Finset.min'``), so such lemmas are pulled in via a
dependency closure and survive. Only theorems nothing kept depends on (sibling
conjectures, sanity/test lemmas) are cut.

Validation gates (all hard unless noted):
  1. Every mapped conjecture name resolves to exactly one ``theorem`` decl.
  2. Re-extracting each isolated file shows the target theorem present, and the
     surviving theorem/lemma commands are exactly those planned (target + its
     dependency lemmas) -- no leftover sibling conjecture or test lemma.
  3. The isolated target's elaborated type equals the source target's type
     (isolation never edits the statement).
  4. No isolated-filename collisions.
  5. **Compile gate (authoritative):** every isolated file compiles with the
     scorer's exact ``lake env lean -o`` command, in parallel in the container.
  6. Oracle cross-check (confidence, non-fatal): for the paper's solved problems,
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


def dependency_closure(filerec: dict, target_decl_name: str) -> set[str]:
    """Names that must be kept: the spec's definitions + the target, plus every
    declaration any of those transitively depends on.

    The seed is every declaration of a non-theorem command (defs, structures and
    their projections/recursors, ``instance``s, axioms) together with the target
    theorem. We then follow ``deps`` (file-local references) to a fixed point, so
    a ``theorem``/``lemma`` that a kept definition uses -- e.g. a nonemptiness
    proof passed to ``Finset.min'`` -- is pulled in and survives. Only theorems
    nothing kept depends on (sibling conjectures, sanity/test lemmas) are cut.
    """
    deps = {d["name"]: d["deps"] for c in filerec["commands"] for d in c["decls"]}
    seed: set[str] = {
        d["name"]
        for c in filerec["commands"]
        if not is_theorem_command(c)
        for d in c["decls"]
    }
    seed |= {d["name"] for d in theorem_decls(filerec) if matches_name(d["name"], target_decl_name)}
    closure = set(seed)
    stack = list(seed)
    while stack:
        for dep in deps.get(stack.pop(), []):
            if dep not in closure:
                closure.add(dep)
                stack.append(dep)
    return closure


def kept_flags(filerec: dict, closure: set[str]) -> list[bool]:
    """Per-command keep decision: every non-theorem command is kept; a theorem
    command is kept iff one of its declarations is in the dependency closure
    (the target, or a definitional-dependency lemma)."""
    return [
        (not is_theorem_command(c)) or any(d["name"] in closure for d in c["decls"])
        for c in filerec["commands"]
    ]


def _line_starts(src: bytes) -> list[int]:
    """Byte offset of the start of each line in ``src``."""
    starts = [0]
    for i, b in enumerate(src):
        if b == 0x0A:
            starts.append(i + 1)
    return starts


def _attached_start(src: bytes, line_starts: list[int], decl_start: int, gap_start: int) -> int:
    """Byte offset where the comment block *attached* to a declaration begins.

    A contiguous run of ``--`` comment lines immediately above the declaration
    (no blank line between them and it, and not crossing into the previous
    declaration's text at ``gap_start``) documents that declaration and travels
    with it. Returns ``decl_start`` when there is no such block.
    """
    import bisect

    li = bisect.bisect_right(line_starts, decl_start) - 1
    attached = decl_start
    li -= 1
    while li >= 0 and line_starts[li] >= gap_start:
        end = line_starts[li + 1] if li + 1 < len(line_starts) else len(src)
        line = src[line_starts[li] : end].decode("utf-8", "replace").strip()
        if line == "" or not line.startswith("--"):
            break
        attached = line_starts[li]
        li -= 1
    return attached


def isolate(src: bytes, filerec: dict, flags: list[bool]) -> bytes:
    """Reconstruct the file keeping only the commands flagged ``True``.

    Each command spans ``[declStart, declEnd)`` for its own text (doc-comment
    included) plus the inter-command *gap* trivia. A command's *unit* is its
    attached leading comment block + its text; cutting a command drops its unit
    (so a comment documenting a removed theorem goes with it) while the free
    trivia between units -- blank lines, detached comments -- is always kept (so
    a comment documenting a *kept* definition is never lost). :func:`tidy` then
    collapses the blank-line runs left behind.
    """
    commands = filerec["commands"]
    if not commands:
        return src
    line_starts = _line_starts(src)
    attached = []
    for i, c in enumerate(commands):
        gap_start = commands[i - 1]["declEnd"] if i > 0 else 0
        attached.append(_attached_start(src, line_starts, c["declStart"], gap_start))

    out = bytearray(src[: attached[0]])  # preamble (license, imports, ...)
    n = len(commands)
    for i, c in enumerate(commands):
        if flags[i]:
            out += src[attached[i] : c["declEnd"]]  # the kept unit (comments + decl)
        next_unit = attached[i + 1] if i + 1 < n else len(src)
        out += src[c["declEnd"] : next_unit]  # free trivia (always kept)
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


# Compiles each isolated file with the scorer's exact command
# (``lake env lean -o``) in parallel; echoes the stem of any that fail. This is
# the authoritative correctness gate -- it is the same elaboration the scorer
# runs on every target at eval time.
_COMPILE_SCRIPT = r"""
set -u
PROJ=/workspace/leanproject
WORK="$PROJ/_apn_gen"
rm -rf "$WORK"; mkdir -p "$WORK"
cd "$PROJ"
compile_one() {
  local f="$1" stem
  stem=$(basename "$f" .lean)
  cp "$f" "$WORK/$stem.lean"
  if ! lake env lean -o "$WORK/$stem.olean" "$WORK/$stem.lean" >/dev/null 2>&1; then
    echo "$stem"
  fi
  rm -f "$WORK/$stem.lean" "$WORK/$stem.olean" "$WORK/$stem.ilean"
}
export -f compile_one
export WORK PROJ
xargs -P "${APN_COMPILE_JOBS:-4}" -I{} bash -c 'compile_one "{}"' < "$1"
rm -rf "$WORK"
"""


def compile_all(files: list[Path], container: str) -> list[str]:
    """Compile every isolated file in the container; return the failing stems."""
    list_path = REPO / "_audit" / "_compile_list.txt"
    script_path = REPO / "_audit" / "_compile_all.sh"
    list_path.parent.mkdir(exist_ok=True)
    list_path.write_text("\n".join(host_to_container(p) for p in files) + "\n")
    script_path.write_text(_COMPILE_SCRIPT)
    cmd = [
        "docker", "exec", container, "bash",
        host_to_container(script_path), host_to_container(list_path),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"compile driver failed (rc={proc.returncode}):\n{proc.stderr[-3000:]}")
    return sorted(s for s in proc.stdout.split() if s)


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

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    written: dict[str, str] = {}
    src_types: dict[str, str] = {}
    planned_thms: dict[str, list[str]] = {}  # theorem-command decls expected to survive
    for name, files in mapping:
        filerec = by_file[files[0]]
        target = resolve_target(name, filerec)  # gate 1: unique target theorem
        closure = dependency_closure(filerec, target["name"])
        flags = kept_flags(filerec, closure)
        src_types[name] = target["type"]
        planned_thms[name] = sorted(
            d["name"]
            for c, keep in zip(filerec["commands"], flags)
            if keep and is_theorem_command(c)
            for d in c["decls"]
        )
        iso = tidy(isolate((AUTO_DIR / files[0]).read_bytes(), filerec, flags))
        out = ISOLATED_DIR / f"{name}.lean"
        if out.name in written:  # gate 4: no filename collisions
            raise SystemExit(f"isolated-filename collision: {out.name}")
        written[out.name] = name
        out.write_bytes(iso)
    print(f"Wrote {len(written)} isolated files. Validating (re-extraction)...", flush=True)

    iso_ranges = run_extractor(sorted(ISOLATED_DIR.glob("*.lean")), args.container, exe)
    iso_types: dict[str, str] = {}
    failures = 0
    for fr in iso_ranges:
        name = Path(fr["file"]).stem
        thms = theorem_command_decls(fr)
        target_hits = [d for d in thms if matches_name(d["name"], name)]
        if len(target_hits) != 1:  # gate 2a: target present exactly once
            failures += 1
            print(f"  FAIL {name}: target appears {len(target_hits)}x among {[d['name'] for d in thms]}")
            continue
        remaining = sorted(d["name"] for d in thms)
        if remaining != planned_thms[name]:  # gate 2b: only target (+ dep lemmas) survive
            failures += 1
            print(f"  FAIL {name}: theorem commands {remaining} != planned {planned_thms[name]}")
            continue
        if target_hits[0]["type"] != src_types[name]:  # gate 3: statement preserved
            failures += 1
            print(f"  FAIL {name}: target statement changed during isolation")
            continue
        iso_types[name] = target_hits[0]["type"]
    if failures:
        raise SystemExit(f"{failures} isolated file(s) failed structural validation.")
    print(f"Structural checks passed for all {len(iso_types)} files. Compiling (authoritative gate)...", flush=True)

    failed = compile_all(sorted(ISOLATED_DIR.glob("*.lean")), args.container)
    if failed:
        print(f"  {len(failed)} isolated file(s) FAILED to compile:")
        for stem in failed:
            print(f"    {stem}")
        raise SystemExit(f"{len(failed)} isolated file(s) failed the compile gate.")
    print(f"All {len(written)} isolated files compile cleanly.")

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
