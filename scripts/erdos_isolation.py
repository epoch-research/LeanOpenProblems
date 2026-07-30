"""Erdős-attempted-set frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates) in ``scripts/fc_statements.py``; this module owns
what is Erdős-specific -- the data locations under ``apn/data/erdos/`` and
their parsers. ``Sources/`` is the whole FC ErdosProblems directory at the
vendored commit, so which statements belong to an evaluation set is not a
property of the corpus: it comes from a file under ``subsets/``. Generation
currently covers ``subsets/tsoukalas.json`` -- the 353 ErdosProblems statements
the Tsoukalas paper's agent attempted (arXiv 2605.22763) minus its 3 excluded
names, with its 1 rename applied, for 350 kept targets. Unlike FC100's fully
qualified subset names, the attempted names are *short* (``erdos_741.parts.i``);
resolution against the vendored sources uses ``matches_name`` suffix semantics
and ``MAPPING.json`` records the resolved fully qualified declaration names.

Two callers import this module: ``scripts/generate_erdos_isolated.py`` (the
vendor-time tool that produces ``Isolated/`` + ``MAPPING.json``) and
``tests/test_erdos_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

import hashlib
import json
import re

from apn.dataset import parse_decl_mapping
from scripts.fc_statements import strip_category_attrs
from scripts.isolation import REPO

parse_mapping = parse_decl_mapping  # re-exported under the dataset-neutral name

ERDOS_DIR = REPO / "apn" / "data" / "erdos"
SOURCES_DIR = ERDOS_DIR / "Sources"
ISOLATED_DIR = ERDOS_DIR / "Isolated"
MAPPING_FILE = ERDOS_DIR / "MAPPING.json"
SUBSETS_DIR = ERDOS_DIR / "subsets"
# The evaluation set generation covers. Sources/ is set-free, so this is the
# only place the generated universe is scoped to a particular set; widening it
# means generating specs for further subsets, not editing the corpus.
GENERATED_SUBSET = "tsoukalas"

# The FC commit Sources/ is vendored at (see SOURCES.json).
FC_COMMIT = "67338a157bbb8d87e9a349d662f82a868bda6327"

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
# proof, and doc-comment prose recording the resolution -- crediting the
# DeepMind prover agent, other AI provers, or human authors, sometimes stating
# the direction or even describing the counterexample, plus module-doc
# reference lines linking the solution papers/formalisations. Un-filling the
# answer literal removes the machine-readable key; these annotations are the
# same key in human-readable form, so generation strips them back to the
# attempt-time text: every kept declaration's `@[category ...]` list is
# dropped whole (see ``scripts.fc_statements.strip_category_attrs``; that
# takes any formal_proof clause with it), and the free prose is removed via
# the exact snippets in VERDICT_PROSE (assembled from the shipped generation
# plus a full agentic audit of all 350 members against their sources). Every
# application is counted and the totals asserted, so upstream drift at
# regeneration fails loudly instead of leaking. tests/test_erdos.py asserts
# the markers are absent from every shipped sketch.
VERDICT_PROSE = [
    # -- resolutions by the paper's own agent -------------------------------
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
    # -- resolutions recorded from other provers/authors --------------------
    "\nSolved affirmatively by [Fo99], who gave an explicit construction.\n\n"
    "This was formalized in Lean by Alexeev using Aristotle and ChatGPT.\n",  # 1071.parts.ii
    "\n\nThis was proved affirmatively by Chojecki [Ch26], using a Duke-type equidistribution"
    " theorem.\nA Lean formalisation of the reduction (conditional on a Duke-type equidistribution"
    " theorem) exists;\nsee the [forum discussion]"
    "(https://www.erdosproblems.com/forum/thread/1148#post-4849).\n",  # 1148
    "- [Ch26] P. Chojecki, [Bounded Representations by $x^2 + y^2 - z^2$]"
    "(https://www.ulam.ai/research/erdos1148-full.pdf) (2026)\n",  # 1148 module-doc reference
    "\n\nThis has been falsified.\n",  # 125.variants.positive_lower_density
    "\n\nThe answer is yes, by [APSSV26, Section 4]; a Lean formalisation is available"
    " in [Mo26].\n",  # 997
    "- [Mo26] P. Monticone, [Lean formalisation of Erdős problem 997]"
    "(https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https://gist.githubusercontent.com/"
    "pitmonticone/016f2ed66b4cd1c4c4b9998095170e60/raw/"
    "b7dfc05c525ae385b5835f89f1ada721443e4305/Erdos997.lean) (2026)\n",  # 997 module-doc reference
    "\n\nThis question has been answered negatively by Xichuan in the\n[comments]"
    "(https://www.erdosproblems.com/forum/thread/1082), who gave a set of $42$ points in\n"
    "$\\mathbb{R}^2$, with no three on a line, such that each point determines only $20$ distinct"
    " distances.\n\nA smaller counterexample has been formalised here: it comprised of $8$ points,"
    " where each point only\ndetermines $3$ distances.\n\n"
    "This counterexample has originally been found by Heiko Harborth.\n",  # 1082.parts.ii
    "\n\nA positive [solution](https://github.com/spicylemonade/erdos-38) was given by GPT 5.5 Pro\n"
    "(prompted by gebyjaff, cleanup by Liam Price); in fact a sparse random set $B$ has this"
    " property,\nwith $f(\\alpha)\\gg \\alpha (1-\\alpha)^2$.\n",  # 38
    "\n\nLarsen and Larsen [LaLa26] answered this in the negative.\n",  # 868.parts.i
    "\n\nLarsen and Larsen [LaLa26] constructed a counterexample with $f(n) > c \\log n$ for all"
    " large $n$.\n",  # 868.parts.ii
    "- [LaLa26] Larsen and Larsen, [Erdős problem 868]"
    "(https://github.com/Larsen-Daniel/Erdos-868/blob/main/868.pdf) (2026)\n",  # 868 module-doc ref
]
# 351 category lists (one per kept declaration: the 350 targets + 1055's kept
# `exists_p`) and 18 verdict-prose applications: each snippet applies once,
# except the 868 module-doc reference line, which lands in both of that file's
# derived specs (parts.i and parts.ii).
ANNOTATION_TOTALS = {"category": 351, "prose": 18}


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


def kept_names() -> list[str]:
    """The kept short names of the generated subset, in its own order:
    ``subsets/tsoukalas.json``'s 353 attempted names minus its 3 excluded ones,
    with its 1 rename applied -> 350. Fails loudly if the membership arithmetic
    is off (a vendoring or exclusion-list error, never something to paper
    over)."""
    subset = json.loads((SUBSETS_DIR / f"{GENERATED_SUBSET}.json").read_text())
    counts = subset["_meta"]["counts"]
    attempted = subset["attempted"]
    if len(attempted) != counts["attempted"] or len(set(attempted)) != counts["attempted"]:
        raise SystemExit(
            f"expected {counts['attempted']} distinct attempted names, "
            f"found {len(attempted)}"
        )
    upstream = subset["_meta"]["upstream"]
    digest = hashlib.sha256("\n".join(attempted).encode()).hexdigest()
    if digest != upstream["sha256"]:
        raise SystemExit(
            f"attempted list hashes to {digest}, expected {upstream['sha256']} "
            f"({upstream['path']} at {upstream['commit'][:7]})"
        )
    excluded = {row["target"] for row in subset["excluded"]}
    if len(excluded) != counts["excluded"]:
        raise SystemExit(f"expected {counts['excluded']} excluded names, found {len(excluded)}")
    unknown = sorted(excluded - set(attempted))
    if unknown:
        raise SystemExit(f"excluded names not in the attempted list: {unknown}")
    renames = {row["attempted"]: row["at_fc_commit"] for row in subset["renamed"]}
    stale = sorted((set(renames) - set(attempted)) | (set(renames.values()) & set(attempted)))
    if stale:
        raise SystemExit(f"renamed entries inconsistent with the attempted list: {stale}")
    kept = [renames.get(n, n) for n in attempted if n not in excluded]
    assert len(kept) == counts["samples"] and len(set(kept)) == counts["samples"]
    return kept
