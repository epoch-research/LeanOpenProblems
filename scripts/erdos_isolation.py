"""Erdős-universe frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates) in ``scripts/fc_statements.py``; this module owns
what is Erdős-specific -- the data locations under ``apn/data/erdos/`` and the
universe census. Membership is *defined* by the vendored sources: every
``theorem``/``lemma`` declaration carrying a ``@[category research ...]``
attribute in ``Sources/`` (``FormalConjectures/ErdosProblems`` files at the
pinned FC commit) is a universe member, resolution status notwithstanding;
the committed ``samples.jsonl`` is curated down to the paper's attempted set
(see ``apn/data/erdos/NOTICE.md``). Value-typed ``answer(sorry)`` members (a
``sorryAx`` in the elaborated statement type, unscoreable by SafeVerify)
become ``excluded`` rows.

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
# each has a kept ``def``/``abbrev`` whose dependency closure pulls in a
# sorry'd helper theorem, which therefore survives the cut -- 1055's
# `def p := Nat.find (exists_p r)` on the textbook `exists_p` (the precedent,
# decided at task-addition time, mirroring FC100's EllipticCurveRank
# instance), 295's `abbrev k := Nat.find (exists_k N)` likewise, 633's
# `IsCuttable.sq` API lemma, 697's `def δ := (density_exists m α).choose`,
# and 961's `def f := Nat.find (well_defined k hk)` whose proof uses the
# sorry'd Sylvester-Schur statement. Those samples implicitly also require
# proving the helper -- in each case an established result, so a strict
# weakening of the target. Generation reports these instead of failing.
SORRY_ALLOWLIST_FILES = {
    "295.lean",
    "633.lean",
    "697.lean",
    "961.lean",
    "1055.lean",
}

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
    # -- resolutions by the paper's own agent -------------------------------
    "\n\nThis was disproved by the DeepMind prover agent.\n",
    "\n\nThis was proved by DeepMind prover agent.\n",
    "\n\nThe DeepMind prover agent has found a formal proof of this statement.\n",
    "\n\nThe DeepMind prover agent has found a formal disproof of this statement.\n",  # 12.parts.ii, 26.tenenbaum
    "\n\nThis was proved formally by the DeepMind prover agent [DM26a].\n",  # 152
    "\n\nThe DeepMind prover agent found a formal proof for this statement\n",  # 741.variants.upper (no period upstream)
    "\n\nFormal proof linked here provided by AlphaProof.\n",  # 1052, 233.lower_bound, 1074.EHSNumbers_infinite
    "\n\nFormal proof provided by AlphaProof\n",  # 267.specialization_pow_two
    "\nThis was found be AlphaProof for the specific instance $X^2 - X + 1$ and then generalised.\n",  # 477
    "\n\nThis was found and proved by AlphaProof.\n\nIt also found $(n + 1)! + n$.\n",  # 198.concrete
    "\n\nAlphaProof has found the following explicit construction: $A = \\{ (n+1)!+n : n\\geq 0\\}$. This is a\n"
    "Sidon set, and intersects every arithmetic progression, since for any $a,d\\in \\mathbb{N}$,\n"
    "$(a+d+1)!+(a+d)\\in A$, and $d$ divides $(a+d+1)!+d$.\n",  # 198
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
