"""Dataset-neutral machinery for the per-target isolation pipeline.

Each benchmark dataset here presents one *target* theorem per sample, but the
upstream Lean files bundle definitions, sanity "test" lemmas, and one or more
target theorems per file. SafeVerify requires every theorem in the scored file
to be discharged, so each dataset derives per-target *isolated* specs: keep the
file's definitions plus the single target theorem, cut every other standalone
``theorem``/``lemma`` command. This module is the shared engine; the
dataset-specific frontends (``scripts/oeis_isolation.py``,
``scripts/fc100_isolation.py``) own the data locations, membership parsing, and
any dataset-specific cuts, and are imported by the matching ``generate_*.py``
vendor-time scripts and ``tests/test_*_isolation.py`` validation suites.

Generation and validation are deliberately separate: the scripts only write
files, the tests only check them. Both share the cut logic (so the tests
re-derive independently what *should* survive) and the Docker plumbing that
drives the Lean declaration-range extractor (``apn/lean/extract_ranges``), since
there is no local Lean toolchain -- everything Lean runs in a container.

Mechanism. Lean 4's surface syntax is environment-extensible, so the cut is
driven by Lean's own parser/elaborator, not a regex. The extractor parses +
elaborates each file through the frontend and emits, per top-level command, its
byte span plus the source-ranged declarations it introduced (fully-qualified
name, kind, ``isInstance``, file-local ``deps``, and -- for theorems -- the
elaborated statement as a stable raw-``Expr`` string). We delete the spans of
the ``theorem`` commands whose declaration is not the target (nor a definitional
dependency of a kept ``def``) and keep everything else verbatim.
"""

from __future__ import annotations

import bisect
import json
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Paths/identifiers inside the Lean container.
CONTAINER_REPO = "/repo"
CONTAINER_PROJECT = "/workspace/leanproject"
DEFAULT_CONTAINER = "apn-isolate-dev"
# Where the extractor exe lives in the container. The dev container mounts the
# repo at /repo and builds in-tree; the baked image installs it under /opt (the
# `generate` stage of apn/lean/Dockerfile).
DEV_EXE = f"{CONTAINER_REPO}/apn/lean/extract_ranges/.lake/build/bin/extract_ranges"
BAKED_EXE = "/opt/apn/extract_ranges/.lake/build/bin/extract_ranges"


# --------------------------------------------------------------------------- #
# Pure helpers (no Docker): the cut + matching logic, unit-testable.           #
# --------------------------------------------------------------------------- #
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
    """The unique ``theorem`` decl for mapped ``name``. Raises if not exactly one
    matches -- the target must be identifiable to produce the spec at all."""
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


def planned_survivors(filerec: dict, name: str) -> tuple[str, list[str]]:
    """For mapped conjecture ``name`` in ``filerec``, the (target elaborated type,
    sorted names of the theorem-command decls that should survive isolation).
    This is the cut's *prediction*; the test compares it to what re-extracting
    the committed isolated file actually shows."""
    target = resolve_target(name, filerec)
    flags = kept_flags(filerec, dependency_closure(filerec, target["name"]))
    survivors = sorted(
        d["name"]
        for c, keep in zip(filerec["commands"], flags)
        if keep and is_theorem_command(c)
        for d in c["decls"]
    )
    return target["type"], survivors


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


def _trailing_comment_end(
    src: bytes, line_starts: list[int], decl_end: int, region_end: int
) -> int:
    """Byte offset up to which line-comment trivia hanging *directly off* a cut
    declaration extends: its same-line ``-- ...`` comment plus any immediately
    following ``--`` comment lines, stopping at the first blank or non-comment
    line, and never past ``region_end`` (the start of the next unit).

    Returns ``decl_end`` when nothing abuts -- so cutting a declaration with no
    trailing comment changes nothing (the bare gap is preserved exactly as
    before). The ``region_end`` bound guarantees we never consume a comment the
    leading-attachment pass already gave to the next kept declaration, and
    stopping at the first blank line preserves blank-separated/floating comments
    (which may document the next kept decl). Only plain ``--`` comments are
    stripped; ``/- ... -/`` and ``/-- ... -/`` blocks are left untouched.
    """
    n = len(src)
    li = bisect.bisect_right(line_starts, decl_end) - 1
    line_end = line_starts[li + 1] if li + 1 < len(line_starts) else n
    tail = src[decl_end:line_end].decode("utf-8", "replace").strip()
    if tail and not tail.startswith("--"):
        return decl_end  # code (not a line comment) follows on the decl's line
    consumed = min(line_end, region_end) if tail else decl_end
    idx = li + 1
    while idx < len(line_starts) and line_starts[idx] < region_end:
        start = line_starts[idx]
        end = line_starts[idx + 1] if idx + 1 < len(line_starts) else n
        text = src[start:end].decode("utf-8", "replace").strip()
        if text == "" or not text.startswith("--"):
            break
        consumed = min(end, region_end)
        idx += 1
    return consumed


def isolate(src: bytes, filerec: dict, flags: list[bool]) -> bytes:
    """Reconstruct the file keeping only the commands flagged ``True``.

    Each command spans ``[declStart, declEnd)`` for its own text (doc-comment
    included) plus the inter-command *gap* trivia. A command's *unit* is its
    attached leading comment block + its text; cutting a command drops its unit
    (so a comment documenting a removed theorem goes with it) *and* the line
    comments hanging directly off its tail (a same-line ``-- ...`` after the
    proof, plus following ``--`` lines up to the first blank line -- see
    :func:`_trailing_comment_end`). The remaining gap trivia -- blank lines and
    blank-separated/floating comments -- is always kept, so a comment documenting
    a *kept* definition is never lost. :func:`tidy` then collapses the blank-line
    runs left behind.
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
        decl_end = c["declEnd"]
        next_unit = attached[i + 1] if i + 1 < n else len(src)
        if flags[i]:
            out += src[attached[i] : decl_end]  # the kept unit (comments + decl)
            out += src[decl_end:next_unit]  # its trailing trivia travels with it
        else:
            # Cut: also drop the line comments hanging off this decl's tail; keep
            # the rest of the gap (blanks / floating comments) verbatim.
            out += src[_trailing_comment_end(src, line_starts, decl_end, next_unit) : next_unit]
    return bytes(out)


def tidy(text: bytes) -> bytes:
    """Collapse the blank-line runs left where siblings were cut; one final NL."""
    s = text.decode("utf-8")
    s = re.sub(r"\n{3,}", "\n\n", s)
    return (s.rstrip() + "\n").encode("utf-8")


# --------------------------------------------------------------------------- #
# The appended disproof declaration (comparator-migration-plan.md §4).         #
#                                                                              #
# Every isolated spec ends with one mechanically derived declaration           #
#                                                                              #
#   theorem <target>.disproof : ¬ (type_of% @<target>) := sorry               #
#                                                                              #
# so one committed file is simultaneously the agent's sketch, the proof        #
# challenge and the disproof challenge. `type_of%` is a Lean-core term         #
# elaborator returning the referenced constant's *elaborated* type, so the     #
# declaration's type is exactly `Not <target's statement>` -- no source-level  #
# negation of binders. The declaration is appended at top level under the      #
# target's fully-qualified name; the few specs whose isolation cut dropped a   #
# trailing `end` (the upstream file closes its namespaces after content the    #
# cut removed) first get those `end` lines restored. Certification that the    #
# appended declaration's type is BEq-identical to `mkNot` of the target's is   #
# independent (apn/lean/extract_ranges/CertifyDisproof.lean, driven by the     #
# isolation suites); the helpers here are deliberately *syntactic* and fail    #
# loudly on anything they cannot account for.                                  #
# --------------------------------------------------------------------------- #
def strip_comments_and_strings(text: str) -> str:
    """Blank out Lean comments and string literals (preserving newlines and
    offsets) so line-anchored scans below never match commented-out or quoted
    text. Handles nested ``/- -/`` blocks (doc comments included), ``--`` line
    comments, and ``"..."`` strings with escapes."""
    out = list(text)
    i, n = 0, len(text)
    block_depth = 0
    while i < n:
        ch = text[i]
        pair = text[i : i + 2]
        if block_depth > 0:
            if pair == "/-":
                block_depth += 1
                out[i] = out[i + 1] = " "
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
            else:
                if ch != "\n":
                    out[i] = " "
                i += 1
        elif pair == "/-":
            block_depth = 1
            out[i] = out[i + 1] = " "
            i += 2
        elif pair == "--":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif ch == '"':
            out[i] = " "
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out[i] = out[i + 1] = " "
                    i += 2
                    continue
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
        else:
            i += 1
    return "".join(out)


def split_name_components(ident: str) -> list[str]:
    """Split a Lean hierarchical identifier on dots, respecting ``«...»``
    segments (whose contents may themselves contain dots)."""
    parts: list[str] = []
    cur = ""
    depth = 0
    for ch in ident:
        if ch == "«":
            depth += 1
            cur += ch
        elif ch == "»":
            depth -= 1
            cur += ch
        elif ch == "." and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    if any(not p for p in parts) or depth != 0:
        raise ValueError(f"malformed hierarchical identifier: {ident!r}")
    return parts


_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)\s*$")
_SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
_END_RE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
_THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\s+([^\s:({\[⦃]+)"
)

# A scope-stack entry: ("namespace", component) or ("section", name-or-None).
_Scope = tuple[str, "str | None"]


def _pop_end(stack: list[_Scope], name: str | None, where: str) -> None:
    if name is None:
        if not stack:
            raise ValueError(f"{where}: 'end' with no open scope")
        kind, top = stack.pop()
        if kind == "namespace":
            raise ValueError(f"{where}: anonymous 'end' closing namespace {top}")
        return
    components = split_name_components(name)
    # `end A.B` pops one entry per component; a single component may instead
    # close the like-named section.
    if len(components) == 1 and stack and stack[-1] == ("section", components[0]):
        stack.pop()
        return
    for comp in reversed(components):
        if not stack:
            raise ValueError(f"{where}: 'end {name}' with no open scope")
        kind, top = stack.pop()
        if kind != "namespace" or top != comp:
            raise ValueError(f"{where}: 'end {name}' does not match open scope {kind} {top}")


def scan_scopes(text: str, target_id: str | None = None) -> tuple[list[str], str | None]:
    """Statically scan a spec's scope structure.

    Returns ``(open_namespaces, target_fq_name)``: the namespace components
    still open at EOF (outermost first), and -- when ``target_id`` is given --
    the fully-qualified name of the unique ``theorem``/``lemma`` whose
    environment name is ``target_id`` or ends with ``.<target_id>``. Raises on
    anything unaccounted for (ambiguous target, mismatched ``end``); the
    container-side certification and compile gates back this scan up.
    """
    stack: list[_Scope] = []
    hits: list[str] = []
    for lineno, line in enumerate(strip_comments_and_strings(text).splitlines(), 1):
        where = f"line {lineno}"
        if m := _NAMESPACE_RE.match(line):
            for comp in split_name_components(m.group(1)):
                stack.append(("namespace", comp))
        elif m := _SECTION_RE.match(line):
            stack.append(("section", m.group(1)))
        elif m := _END_RE.match(line):
            _pop_end(stack, m.group(1), where)
        elif target_id is not None and (m := _THEOREM_RE.match(line)):
            prefix = [comp for kind, comp in stack if kind == "namespace" and comp]
            fq = ".".join([*prefix, m.group(1)])
            if fq == target_id or fq.endswith("." + target_id):
                hits.append(fq)
    open_namespaces = [comp for kind, comp in stack if kind == "namespace" and comp]
    if target_id is None:
        return open_namespaces, None
    if len(hits) != 1:
        raise ValueError(f"expected exactly one declaration matching {target_id!r}, found {hits}")
    return open_namespaces, hits[0]


def disproof_declaration(decl_name: str) -> str:
    """The derived disproof declaration for a target's fully-qualified name."""
    return f"theorem {decl_name}.disproof : ¬ (type_of% @{decl_name}) := sorry"


def append_disproof(text: str, target_id: str, decl_name: str | None = None) -> tuple[str, str]:
    """Append the derived disproof declaration to an isolated spec.

    Restores any ``end`` lines the isolation cut dropped (specs that end inside
    an open ``namespace``), then appends :func:`disproof_declaration` for the
    target's fully-qualified name at top level. ``decl_name`` supplies that
    name when the caller has it authoritatively (the generators take it from
    the extractor); otherwise it is derived by :func:`scan_scopes` -- and when
    both are available they must agree. Returns ``(new_text, decl_name)``.
    """
    open_namespaces, scanned = scan_scopes(text, target_id)
    if decl_name is None:
        assert scanned is not None
        decl_name = scanned
    elif scanned != decl_name:
        raise ValueError(
            f"static scan resolved target {target_id!r} to {scanned!r}, "
            f"but the extractor says {decl_name!r}"
        )
    parts = [text.rstrip() + "\n"]
    if open_namespaces:
        closers = "".join(f"end {comp}\n" for comp in reversed(open_namespaces))
        parts.append("\n" + closers)
    parts.append("\n" + disproof_declaration(decl_name) + "\n")
    return "".join(parts), decl_name


# --------------------------------------------------------------------------- #
# Docker orchestration: run the Lean extractor / compile gate in a container.  #
# --------------------------------------------------------------------------- #
def host_to_container(path: Path) -> str:
    """Map a host repo path to its location inside the (``-v $REPO:/repo``) container."""
    return f"{CONTAINER_REPO}/{path.resolve().relative_to(REPO)}"


def parse_extractor_output(stdout: str) -> list[dict]:
    """Parse the extractor's JSON array from its stdout.

    ``extract_ranges`` prints one compact JSON line (after any ``lake`` build
    noise); take the last line that starts with ``[``. Pure -- shared by the
    subprocess caller below (the generation scripts) and the Inspect-sandbox
    caller (``tests/test_*_isolation.py``), which differ only in how they run
    the exe in a container.
    """
    for line in reversed(stdout.splitlines()):
        line = line.strip()
        if line.startswith("["):
            return json.loads(line)
    raise RuntimeError(f"no JSON in extractor stdout:\n{stdout[-2000:]}")


def run_extractor(files: list[Path], container: str, exe: str) -> list[dict]:
    """Run ``extract_ranges`` over ``files`` (under ``lake env``) and parse JSON."""
    cpaths = [host_to_container(p) for p in files]
    cmd = ["docker", "exec", "-w", CONTAINER_PROJECT, container, "lake", "env", exe, *cpaths]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"extractor failed (rc={proc.returncode}).\nSTDERR tail:\n{proc.stderr[-3000:]}"
        )
    return parse_extractor_output(proc.stdout)


# Compiles each isolated file with the scorer's exact command (``lake env lean
# -o``) in parallel; echoes the stem of any that fail. The script is fed on
# stdin and the file list as positional args, so no host scratch files are
# needed. This is the authoritative correctness gate -- the same elaboration the
# scorer runs on every target at eval time. Exported (not ``_``-private) because
# the tests drive it through the Inspect sandbox; the subprocess caller below
# (the generation scripts) and the tests share this one script verbatim.
COMPILE_SCRIPT = r"""
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
printf '%s\n' "$@" | xargs -P "${APN_COMPILE_JOBS:-4}" -I{} bash -c 'compile_one "{}"'
rm -rf "$WORK"
"""


def compile_all(files: list[Path], container: str) -> list[str]:
    """Compile every isolated file in the container; return the failing stems."""
    cpaths = [host_to_container(p) for p in files]
    cmd = ["docker", "exec", "-i", container, "bash", "-s", "--", *cpaths]
    proc = subprocess.run(cmd, input=COMPILE_SCRIPT, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"compile driver failed (rc={proc.returncode}):\n{proc.stderr[-3000:]}")
    return sorted(s for s in proc.stdout.split() if s)
