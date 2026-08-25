"""Erdős-universe frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates) in ``scripts/fc_statements.py``; this module owns
what is Erdős-specific -- the data locations under ``apn/data/erdos/`` and the
universe census. Membership is *defined* by the vendored sources: every
``theorem``/``lemma`` declaration carrying a ``@[category research ...]``
attribute in ``Sources/`` (the Bloom statement selection's 48
``FormalConjectures/ErdosProblems`` files at the pinned FC commit -- see
``apn/data/erdos/NOTICE.md`` and ``metadata/
ERDOS_PROBLEM_STATEMENT_SELECTION.md``) is a universe member, resolution
status notwithstanding. Value-typed ``answer(sorry)`` members (a ``sorryAx``
in the elaborated statement type, unscoreable by the verifier) and members
carrying a complete in-file proof become ``excluded`` rows.

Two callers import this module: ``scripts/generate_erdos_isolated.py`` (the
vendor-time tool that produces ``samples.jsonl`` + ``Isolated/``) and
``tests/test_erdos_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

import re

from scripts.fc_statements import strip_category_attrs
from scripts.isolation import REPO, is_theorem_command

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
# require proving the helper). Each entry is a task-addition-time decision;
# generation reports allowlisted extras instead of failing, and fails loudly
# on any file not listed here. None of the Bloom-selection files needs one
# (the Tsoukalas-era entries -- 295/633/697/961/1055 -- all left with that
# set); re-add only what generation reports.
SORRY_ALLOWLIST_FILES: set[str] = set()

# A research-category classification attribute and its status field. Matched
# against a *command's* source span (the extractor includes the attribute list
# and doc comment in the span), so each hit attaches to a known declaration.
# Anchored to line starts like ``strip_category_attrs``'s pattern -- prose may
# quote the attribute mid-line and must not be counted.
RESEARCH_ATTR_RE = re.compile(r"^@\[category research (open|solved)[^\]]*\]", re.MULTILINE)


def research_categories(span: bytes) -> list[str]:
    """The research-category statuses (``"research open"``/``"research
    solved"``) declared in one command's source span, in order."""
    text = span.decode("utf-8", "replace")
    return [f"research {m.group(1)}" for m in RESEARCH_ATTR_RE.finditer(text)]


def universe_members(src: bytes, filerec: dict) -> list[tuple[dict, str]]:
    """The file's universe members: ``(theorem_decl, category)`` for every
    standalone theorem/lemma command carrying a research-category attribute.

    Anonymous ``example`` commands may carry the attribute too (387.lean's
    sanity check does); they introduce no declaration and are not members.
    The caller cross-checks that no research attribute was silently skipped by
    comparing the file-total against the per-command sum.
    """
    members: list[tuple[dict, str]] = []
    for cmd in filerec["commands"]:
        cats = research_categories(src[cmd["declStart"] : cmd["declEnd"]])
        if not cats or not cmd["decls"]:
            continue
        if not is_theorem_command(cmd) or len(cmd["decls"]) != 1 or len(cats) != 1:
            raise SystemExit(
                f"{filerec['file']}: research-category command with unexpected "
                f"shape: decls={[d['name'] for d in cmd['decls']]}, cats={cats}"
            )
        members.append((cmd["decls"][0], cats[0]))
    return members


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
