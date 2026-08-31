"""Erdős-universe frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates, the research-category census) in
``scripts/fc_statements.py``; this module owns what is Erdős-specific -- the
data locations under ``apn/data/erdos/`` and the exclusion/allowlist
constants. Membership is *defined* by the vendored sources: every
``theorem``/``lemma`` declaration carrying a ``@[category research ...]``
attribute in ``Sources/`` (the Bloom statement selection's 48
``FormalConjectures/ErdosProblems`` files at the pinned FC commit -- see
``apn/data/erdos/NOTICE.md`` and
``ERDOS_PROBLEM_STATEMENT_SELECTION.md`` next to it) is a universe member,
resolution status notwithstanding. Value-typed ``answer(sorry)`` members (a ``sorryAx``
in the elaborated statement type, unscoreable by the verifier) and members
carrying a complete in-file proof become ``excluded`` rows.

Two callers import this module: ``scripts/generate_erdos_isolated.py`` (the
vendor-time tool that produces ``samples.jsonl`` + ``Isolated/``) and
``tests/test_erdos_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

import re

from scripts.fc_statements import (  # noqa: F401  (re-exported for this dataset's callers)
    RESEARCH_ATTR_RE,
    research_categories,
    strip_category_attrs,
    universe_members,
)
from scripts.isolation import (
    REPO,
    append_disproof,
    strip_private,
    tidy,
)

ERDOS_DIR = REPO / "apn" / "data" / "erdos"
SOURCES_DIR = ERDOS_DIR / "Sources"
ISOLATED_DIR = ERDOS_DIR / "Isolated"

# The reason recorded on value-typed answer(sorry) rows (mirrors fc100open's).
VALUE_TYPED_REASON = (
    "value-typed answer(sorry): the placeholder elaborates to a position-labeled "
    "sorryAx in the statement's type, so the statement cannot be closed (or even "
    'stated) without the paper\'s google.answer "with_auxiliary" machinery, and '
    "SafeVerify cannot score it"
)

# The reason recorded on rows whose declaration carries a complete formal
# proof in the source file itself (no `sorry` anywhere in the command): the
# statement is not an open task, and no spec can ship without either leaking
# the proof text verbatim or inventing un-filling surgery for arbitrary proof
# terms. Members merely *recorded* solved (category flip, formal_proof URL)
# whose in-file proof is still `sorry` stay included -- re-deriving those is
# exactly the task, as for the recorded-verdict answer literals.
PROVED_IN_FILE_REASON = (
    "complete formal proof in the source file at the pin: the statement is not "
    "an open task, and shipping it would leak the proof text"
)

# Files whose isolated specs may carry a `sorry` outside the target theorem:
# a kept ``def``/``abbrev`` whose dependency closure pulls in a sorry'd helper
# theorem, which therefore survives the cut (such samples implicitly also
# require proving the helper).
SORRY_ALLOWLIST_FILES: set[str] = set()

# All statements ship with recorded verdicts un-filled: FC records a
# resolution as a `research solved` category flip, a `formal_proof` URL
# attribute pointing at a complete proof, and doc-comment prose -- crediting
# the DeepMind prover agent, other AI provers, or human authors, sometimes
# stating the direction or even describing the counterexample, plus module-doc
# reference lines linking the solution papers/formalisations. Un-filling the
# answer literal removes the machine-readable key; these annotations are the
# same key in human-readable form, so generation strips them back to
# resolution-free text: every kept declaration's `@[category ...]` list is
# dropped whole (see ``scripts.fc_statements.strip_category_attrs``; that
# takes any formal_proof clause with it), and the free prose is removed via
# the exact snippets in VERDICT_PROSE (assembled from the generation census
# plus an agentic audit of every member against its source). Every application
# is counted and the totals asserted, so upstream drift at regeneration fails
# loudly instead of leaking. tests/test_erdos.py asserts the markers are
# absent from every shipped sketch.
VERDICT_PROSE = [
    # 138.variants.difference: a recorded-verdict answer(True) member shipped
    # un-filled; this sentence is that verdict in prose.
    "\n\nThe DeepMind prover agent has found a formal proof of this statement.\n",
]


# --------------------------------------------------------------------------- #
# The Hadwiger–Nelson special case (Problem 508).                              #
# --------------------------------------------------------------------------- #
# 508's only research-open statement, `HadwigerNelsonProblem`, is value-typed
# (`χ(ℝ²) = answer(sorry)`) and ships as an excluded manifest row. χ(ℝ²) is
# known to lie in {5, 6, 7} (de Grey's lower bound, Isbell's hexagonal upper
# bound), so the benchmark carries three derived prove-or-disprove samples in
# its place, one per candidate value -- Greg Burnham's proposal, adopted by
# Thomas Bloom (2026-08-25). Each spec is the source file cut down to the
# target theorem with the `answer(sorry)` placeholder replaced by the literal
# and the theorem renamed to `HadwigerNelsonProblem.eqN` -- so the three
# statements carry distinct names and the id-is-the-declaration-name
# convention holds.
#
# The derivation is pure text over the vendored source (no extractor run), so
# generation and the fast suite (tests/test_erdos.py, byte-level re-derivation)
# both recompute it, and the container gates (compile, disproof certification)
# cover the derived specs like every other spec in
# tests/test_erdos_isolation.py -- which skips only the answer-form
# certificate for them (the source statement is value-typed; there is no
# rewrite form to certify) and asserts the derived statement's elaborated type
# is sorryAx-free instead.
HN_DECL = "Erdos508.HadwigerNelsonProblem"
HN_VALUES = (5, 6, 7)
HN_SAMPLE_IDS = tuple(f"{HN_DECL}.eq{v}" for v in HN_VALUES)

# The target command's exact source text at the pin. Anchoring on the full
# span keeps the derivation honest: if the pinned file drifts, generation and
# the tests fail loudly here instead of silently deriving from something else.
_HN_TARGET_COMMAND = """/--
The Hadwiger–Nelson problem asks: How many colors are required to color the plane
such that no two points at distance 1 from each other have the same color?
-/
@[category research open, AMS 52]
theorem HadwigerNelsonProblem :
    χ(ℝ²) = answer(sorry) := by
  sorry
"""

_HN_ANSWER_SORRY_RE = re.compile(r"answer\(\s*sorry\s*\)")


def derive_hadwiger_nelson_specs() -> dict[str, str]:
    """The three derived Hadwiger–Nelson isolated specs, ``{sample id: text}``."""
    src = (SOURCES_DIR / "508.lean").read_text()
    idx = src.index(_HN_TARGET_COMMAND)
    preamble = src[:idx]
    # The target is the file's first theorem, so the preamble is exactly the
    # header/module doc/opens/notation and everything after the target (the
    # solved/textbook siblings) is dropped whole.
    assert "theorem" not in preamble and "@[category" not in preamble
    base, n_attrs = strip_category_attrs(preamble + _HN_TARGET_COMMAND)
    assert n_attrs == 1
    base = strip_private(tidy(base.encode()).decode())
    specs: dict[str, str] = {}
    for value, sample_id in zip(HN_VALUES, HN_SAMPLE_IDS):
        text, n = _HN_ANSWER_SORRY_RE.subn(str(value), base)
        assert n == 1, f"{sample_id}: {n} answer(sorry) substitutions"
        old_header = "theorem HadwigerNelsonProblem :"
        new_header = f"theorem HadwigerNelsonProblem.eq{value} :"
        assert text.count(old_header) == 1, sample_id
        text = text.replace(old_header, new_header)
        specs[sample_id], _ = append_disproof(text, sample_id, sample_id)
    return specs


def hn_manifest_rows() -> list[dict]:
    """Manifest rows for the three derived Hadwiger–Nelson samples."""
    return [
        {
            "id": sample_id,
            "source": "Sources/508.lean",
            "erdos_number": 508,
            "category_at_pin": "research open",
            "answer_form": None,
        }
        for sample_id in HN_SAMPLE_IDS
    ]


def strip_fc_annotations(text: str) -> tuple[str, dict[str, int]]:
    """Remove FC's catalogue/verdict annotations from an isolated spec's text,
    returning the stripped text and per-kind application counts (summed and
    asserted by generation). Elaboration-neutral by construction -- the
    attributes never reach the statement's type, prose is prose -- and the
    certificate + compile gates re-check the result."""
    counts = {"category": 0, "prose": 0}
    text, counts["category"] = strip_category_attrs(text)
    for snippet in VERDICT_PROSE:
        if snippet in text:
            counts["prose"] += text.count(snippet)
            newline = "\n" if snippet.startswith("\n") else ""
            text = text.replace(snippet, newline)
    return text, counts
