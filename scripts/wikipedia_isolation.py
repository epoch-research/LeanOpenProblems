"""Wikipedia-dataset frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions in
``scripts/fc_statements.py``; this module owns what is Wikipedia-specific --
the data locations under ``apn/data/wikipedia/``, the universe census, and the
de-modulization of the vendored sources.

Membership is *defined* by the vendored sources: every ``theorem``/``lemma``
declaration carrying a ``@[category research open ...]`` attribute in
``Sources/`` (every ``FormalConjectures/Wikipedia`` file with at least one such
statement at the pinned FC commit -- see ``apn/data/wikipedia/NOTICE.md``) is a
universe member. Value-typed ``answer(sorry)`` members and members carrying a
complete in-file proof become ``excluded`` rows.

De-modulization. The pin postdates upstream's switch to the Lean module system
(``module`` header, ``public import``, ``@[expose] public section``). The
sandbox images build only the util-module closure, and the scorer compiles
specs as ordinary (non-module) files, so every isolated spec is derived from
the *de-modulized* source (:func:`extraction_source`): the module header and
the ``public section`` line are dropped and ``public import`` becomes
``import``. A handful of files import sibling FC problem files the images do
not build; :data:`SIBLING_IMPORT_PATCHES` removes those imports and inlines
the one statement that referenced a sibling declaration.

Two callers import this module: ``scripts/generate_wikipedia_isolated.py``
(the vendor-time tool) and ``tests/test_wikipedia_isolation.py`` (the
authoritative validation of the committed files).
"""

from __future__ import annotations

import re

from scripts.isolation import REPO, is_theorem_command

WIKIPEDIA_DIR = REPO / "apn" / "data" / "wikipedia"
SOURCES_DIR = WIKIPEDIA_DIR / "Sources"
ISOLATED_DIR = WIKIPEDIA_DIR / "Isolated"

VALUE_TYPED_REASON = (
    "value-typed answer(sorry): the placeholder elaborates to a position-labeled "
    "sorryAx in the statement's type, so the statement cannot be closed (or even "
    "stated) without a chosen answer value"
)

PROVED_IN_FILE_REASON = (
    "complete formal proof in the source file at the pin: the statement is not "
    "an open task, and shipping it would leak the proof text"
)

# Files whose isolated specs may carry a `sorry` outside the target theorem
# (a kept def whose dependency closure pulls in a sorry'd helper theorem).
SORRY_ALLOWLIST_FILES: set[str] = set()

RESEARCH_OPEN_ATTR_RE = re.compile(r"^@\[category research open[,\]]", re.MULTILINE)
ANY_RESEARCH_ATTR_RE = re.compile(r"^@\[category research (open|solved)[^\]]*\]", re.MULTILINE)

# Exact (old, new) replacements applied to a file's de-modulized text. Each
# `old` must occur exactly once. The images build only the FC util closure,
# so imports of sibling problem files cannot resolve at scoring time.
SIBLING_IMPORT_PATCHES: dict[str, list[tuple[str, str]]] = {
    "AmicableNumbers.lean": [
        ("import FormalConjectures.ErdosProblems.«830»\n", ""),
        # `type_of% Erdos830.erdos_830.parts.i`, inlined: Erdős 830 part (i)
        # at the pin is `{(a, b) | IsAmicable a b}.Infinite`.
        (
            "theorem infinitely_many_amicable : type_of% Erdos830.erdos_830.parts.i := by",
            "theorem infinitely_many_amicable : {(a, b) | IsAmicable a b}.Infinite := by",
        ),
    ],
    "SparseRuler.lean": [
        ("import FormalConjectures.ErdosProblems.«170»\n", ""),
    ],
    "ArtinPrimitiveRootsConjecture.lean": [
        ("import FormalConjectures.Millennium.RiemannHypothesis\n", ""),
        # The namespace is declared by the dropped import; nothing in the file
        # uses a name from it.
        ("open GRH\n", ""),
    ],
}

_MODULE_HEADER_RE = re.compile(r"^module[ \t]*\n", re.MULTILINE)
_PUBLIC_IMPORT_RE = re.compile(r"^public import ", re.MULTILINE)
_PUBLIC_SECTION_RE = re.compile(r"^@\[expose\] public section\n", re.MULTILINE)


def demodulize(text: str) -> str:
    """Rewrite a module-system FC problem file as an ordinary Lean file."""
    first_import = text.index("public import ")
    header, n_module = _MODULE_HEADER_RE.subn("", text[:first_import])
    if n_module != 1:
        raise ValueError(f"expected one `module` header line, found {n_module}")
    text = header + text[first_import:]
    text = _PUBLIC_IMPORT_RE.sub("import ", text)
    text, n_section = _PUBLIC_SECTION_RE.subn("", text)
    if n_section != 1:
        raise ValueError(f"expected one `@[expose] public section` line, found {n_section}")
    return text


def extraction_source(rel: str) -> str:
    """The text every isolated spec of ``Sources/<rel>`` is cut from: the
    vendored file de-modulized, with any sibling-import patches applied."""
    text = demodulize((SOURCES_DIR / rel).read_text())
    for old, new in SIBLING_IMPORT_PATCHES.get(rel, []):
        if text.count(old) != 1:
            raise ValueError(f"{rel}: patch anchor {old!r} found {text.count(old)}x")
        text = text.replace(old, new)
    if re.search(r"^import FormalConjectures\.", text, re.MULTILINE):
        raise ValueError(f"{rel}: unpatched sibling import")
    return text


def universe_members(src: bytes, filerec: dict) -> list[dict]:
    """The file's ``research open`` theorem/lemma declarations."""
    members: list[dict] = []
    for cmd in filerec["commands"]:
        span = src[cmd["declStart"] : cmd["declEnd"]].decode("utf-8", "replace")
        n_open = len(RESEARCH_OPEN_ATTR_RE.findall(span))
        if not n_open or not cmd["decls"]:
            continue
        if not is_theorem_command(cmd) or len(cmd["decls"]) != 1 or n_open != 1:
            raise SystemExit(
                f"{filerec['file']}: research-open command with unexpected "
                f"shape: decls={[d['name'] for d in cmd['decls']]}"
            )
        members.append(cmd["decls"][0])
    return members
