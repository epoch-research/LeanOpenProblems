# type: ignore
"""Erdős-attempted-set frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates) in ``scripts/fc_statements.py``; this module owns
what is Erdős-specific -- the data locations under ``apn/data/erdos/`` and
their parsers. Membership comes from the vendored ``ATTEMPTED.txt`` (the 353
ErdosProblems statements the Tsoukalas paper's agent attempted, arXiv
2605.22763) minus ``EXCLUDED.txt`` (3 names with no statement at the vendored
FC commit), with ``RENAMED.txt`` tracking upstream renames -- 350 kept
targets. Unlike FC100's fully qualified subset names, the attempted names are
*short* (``erdos_741.parts.i``); resolution against the vendored sources uses
``matches_name`` suffix semantics and ``MAPPING.txt`` records the resolved
fully qualified declaration names.

Two callers import this module: ``scripts/generate_erdos_isolated.py`` (the
vendor-time tool that produces ``Isolated/`` + ``MAPPING.txt``) and
``tests/test_erdos_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

import re

from apn.dataset import parse_decl_mapping as parse_mapping  # re-exported
from scripts.fc_statements import strip_category_attrs
from scripts.isolation import REPO

ERDOS_DIR = REPO / "apn" / "data" / "erdos"
SOURCES_DIR = ERDOS_DIR / "Sources"
ISOLATED_DIR = ERDOS_DIR / "Isolated"
ATTEMPTED_FILE = ERDOS_DIR / "ATTEMPTED.txt"
EXCLUDED_FILE = ERDOS_DIR / "EXCLUDED.txt"
RENAMED_FILE = ERDOS_DIR / "RENAMED.txt"
MAPPING_FILE = ERDOS_DIR / "MAPPING.txt"

# Targets whose isolated spec may carry a `sorry` outside the target theorem.
# 1055.lean's kept `noncomputable def p := Nat.find (exists_p r)` depends on
# the sorry'd textbook theorem `exists_p`, which therefore survives the cut;
# it is deliberately kept as-is (decided at task-addition time, mirroring
# FC100's EllipticCurveRank instance), so that sample implicitly also requires
# proving `exists_p` -- a strict weakening of the target itself (infinitude of
# primes in each class implies existence). Generation reports it instead of
# failing.
SORRY_ALLOWLIST = {
    "Erdos1055.erdos_1055",
}

# The dataset's answer(...)-form census (short name -> expected count), pinned
# at task-addition time; see ``scripts/fc_statements.py`` for the form labels.
# Any drift means the membership files or vendored sources changed.
FORM_CENSUS = {
    None: 85,  # plain propositions
    "lhs_sorry": 249,  # answer(sorry) ↔ P
    "lhs_true": 7,  # answer(True) ↔ P   (recorded verdict, un-filled)
    "lhs_false": 6,  # answer(False) ↔ P  (recorded verdict, un-filled)
    "rhs_sorry": 3,  # P ↔ answer(sorry)
}

# All 353 statements were unresolved when the paper's agent attempted them; FC
# has since recorded verdicts on 14 members: a `research solved` category
# flip, for 10 of them a `formal_proof` URL attribute pointing at a complete
# proof, and prose crediting the prover agent (one line of which states the
# direction outright). Un-filling the answer literal removes the
# machine-readable key; these annotations are the same key in human-readable
# form, so generation strips them back to the attempt-time text: every kept
# declaration's `@[category ...]` list is dropped whole (see
# ``scripts.fc_statements.strip_category_attrs``; that takes any formal_proof
# clause with it), and the free prose is removed via the exact snippets in
# VERDICT_PROSE. Every application is counted and the totals asserted, so
# upstream drift at regeneration fails loudly instead of leaking.
# tests/test_erdos.py asserts the markers are absent from every shipped sketch.
VERDICT_PROSE = [
    "\n\nThis was disproved by the DeepMind prover agent.\n",
    "\n\nThis was proved by DeepMind prover agent.\n",
    "\n\nThe DeepMind prover agent has found a formal proof of this statement.\n",
    " - [DM26a] DeepMind prover agent, [formal proof of Erdős problem 152]"
    "(https://github.com/mo271/formal-conjectures/blob/"
    "29c60aa79729701905cf9e92517af23f588971f2/FormalConjectures/ErdosProblems/152.lean#L485)"
    " (2026)\n",
    " - [DM26b] DeepMind prover agent, [formal proof of the quadratic variant of Erdős problem 152]"
    "(https://github.com/mo271/formal-conjectures/blob/"
    "ff58c933d53bb807bf85d98a47402703f9f14ed3/FormalConjectures/ErdosProblems/152.lean#L496)"
    " (2026)\n",
    "\n\nThis stronger quadratic variant was also proved formally by the DeepMind prover agent"
    " [DM26b].\n",
]
# 351 category lists (one per kept declaration: the 350 targets + 1055's kept
# `exists_p`) and the 6 verdict-prose lines.
ANNOTATION_TOTALS = {"category": 351, "prose": 6}


def strip_fc_annotations(text: str) -> tuple[str, dict[str, int]]:
    """Remove FC's catalogue/verdict annotations from an isolated spec's text,
    returning the stripped text and per-kind application counts (summed and
    asserted against ``ANNOTATION_TOTALS`` by generation). Elaboration-neutral
    by construction -- the attributes never reach the statement's type, prose
    is prose -- and the certificate + compile gates re-check the result."""
    counts = {"category": 0, "prose": 0}
    text, counts["category"] = strip_category_attrs(text)
    for snippet in VERDICT_PROSE:
        if snippet in text:
            counts["prose"] += text.count(snippet)
            newline = "\n" if snippet.startswith("\n") else ""
            text = text.replace(snippet, newline)
    return text, counts


def parse_names(text: str) -> list[str]:
    """Names one per line; blank lines and ``#`` comments ignored."""
    names: list[str] = []
    for line in text.splitlines():
        entry = line.split("#", 1)[0].strip()
        if entry:
            names.append(entry)
    return names


def parse_renamed(text: str) -> dict[str, str]:
    """``RENAMED.txt`` as ``{attempt_time_name: name_at_vendored_commit}``
    (one whitespace-separated pair per line; ``#`` comments ignored)."""
    renames: dict[str, str] = {}
    for line in text.splitlines():
        entry = line.split("#", 1)[0].strip()
        if entry:
            old, new = entry.split()
            renames[old] = new
    return renames


def kept_names() -> list[str]:
    """The 350 kept short names: ``ATTEMPTED.txt``'s 353 minus
    ``EXCLUDED.txt``'s 3, with ``RENAMED.txt`` applied, in attempt-list order.
    Fails loudly if the membership arithmetic is off (a vendoring or
    exclusion-list error, never something to paper over)."""
    attempted = parse_names(ATTEMPTED_FILE.read_text())
    if len(attempted) != 353 or len(set(attempted)) != 353:
        raise SystemExit(f"expected 353 distinct attempted names, found {len(attempted)}")
    excluded = parse_names(EXCLUDED_FILE.read_text())
    if len(excluded) != 3:
        raise SystemExit(f"expected 3 excluded names, found {len(excluded)}")
    unknown = sorted(set(excluded) - set(attempted))
    if unknown:
        raise SystemExit(f"EXCLUDED.txt names not in the attempted list: {unknown}")
    renames = parse_renamed(RENAMED_FILE.read_text())
    stale = sorted((set(renames) - set(attempted)) | (set(renames.values()) & set(attempted)))
    if stale:
        raise SystemExit(f"RENAMED.txt entries inconsistent with the attempted list: {stale}")
    kept = [renames.get(n, n) for n in attempted if n not in set(excluded)]
    assert len(kept) == 350 and len(set(kept)) == 350
    return kept
