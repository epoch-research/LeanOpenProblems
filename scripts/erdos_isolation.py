"""Erdős-universe frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates) in ``scripts/fc_statements.py``; this module owns
what is Erdős-specific -- the data locations under ``apn/data/erdos/`` and the
universe census. Membership is *defined* by the vendored sources: every
``theorem``/``lemma`` declaration carrying a ``@[category research ...]``
attribute in ``Sources/`` (the full ``FormalConjectures/ErdosProblems``
directory at the pinned FC commit) is a universe member, resolution status
notwithstanding; the committed ``samples.jsonl`` is the census's output.
Value-typed ``answer(sorry)`` members (a ``sorryAx`` in the elaborated
statement type, unscoreable by SafeVerify) ship as ``excluded`` rows.

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

# Hand-isolation for the few members the generic cut cannot handle -- exact
# (old, new) text replacements applied to the isolated spec, each asserted to
# apply exactly once, and all re-checked by the certificate + compile gates
# (an inlined type must elaborate to exactly the source's spliced type, binder
# names included, or tests/test_erdos_isolation.py fails):
#
# * 11.lean / 392.lean state bridge variants via `type_of% <sibling>`, which
#   splices the sibling's elaborated *type* -- so the sibling never appears in
#   the extractor's `deps`, the cut removes it, and the isolated spec cannot
#   elaborate. The sibling *statements* are inlined verbatim in its place
#   (keeping them as sorry'd theorems instead would make SafeVerify demand
#   their proofs -- wrong task; they are hypotheses here).
# * 683.lean / 1145.lean import another problem file. Problem-module oleans
#   are not built into the sandbox images, so a shipped spec must not import
#   one; the imports are dead weight for every kept declaration (683's specs
#   only `open` the namespace, and 1145's user is its `@[category test]`
#   sibling -- cross-file references also make that command invisible to the
#   extractor, so the cut engine never saw it and it must be dropped by text).
_ERDOS_392_STMT = (
    "∀ (A : ℕ → ℕ) (h : ∀ n > 0, IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, "
    "(n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)), "
    "((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)"
)
_ERDOS_392_LOWER_STMT = (
    "∀ (A : ℕ → ℕ) (hA : ∀ n > 0, IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, "
    "(n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n) } (A n)), "
    "(fun (n : ℕ) => (A n - n + n / Real.log n : ℝ)) =o[atTop] fun n => n / Real.log n"
)
_STRIP_961_IMPORT = [
    ("import FormalConjectures.ErdosProblems.«961»\n", ""),
    ("open Filter Real Erdos961\n", "open Filter Real\n"),
]
HARDCODED_ISOLATION: dict[str, list[tuple[str, str]]] = {
    "Erdos11.erdos_11.variants.granville_soundararajan": [
        (
            "(H : type_of% erdos_11)",
            "(H : ∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l)",
        ),
    ],
    "Erdos392.erdos_392.variants.implication": [
        ("(h : type_of% erdos_392)", f"(h : {_ERDOS_392_STMT})"),
        ("type_of% erdos_392.variants.lower", _ERDOS_392_LOWER_STMT),
    ],
    "Erdos683.erdos_683": _STRIP_961_IMPORT,
    "Erdos683.erdos_683.variant.exp_sqrt": _STRIP_961_IMPORT,
    "Erdos683.erdos_683.variant.erdos_log": _STRIP_961_IMPORT,
    "Erdos683.erdos_683.variant.sylvester_schur": _STRIP_961_IMPORT,
    "Erdos1145.erdos_1145": [
        ("import FormalConjectures.ErdosProblems.«28»\n", ""),
        (
            "/--\nA stronger form of [erdosproblems.com/28].\n-/\n"
            "@[category test, AMS 11]\n"
            "theorem erdos_1145.test_implies_erdos_28 : Erdos1145Prop → type_of% Erdos28.erdos_28 := by\n"
            "  delta sumRep\n"
            "  intro h1145 s hs\n"
            "  rcases hs.exists_le with ⟨m, hm⟩\n"
            "  by_cases hfin : s.Finite\n"
            "  · exact absurd hs (hfin.add hfin).infinite_compl\n"
            "  · have hinf : s.Infinite := hfin\n"
            "    refine h1145 hinf hinf ?_ ?_\n"
            "    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds\n"
            "      filter_upwards [Filter.eventually_gt_atTop 0] with n hn\n"
            "      rw [div_self]\n"
            "      exact mod_cast Nat.pos_iff_ne_zero.mp <|\n"
            "        lt_of_lt_of_le hn (Nat.nth_strictMono hinf).le_apply\n"
            "    · filter_upwards [Filter.eventually_gt_atTop m] with n hn\n"
            "      by_contra hns\n"
            "      exact not_le_of_gt hn (hm n hns)\n",
            "",
        ),
    ],
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
