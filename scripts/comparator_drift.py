"""Module-sensitive closure drift analysis (comparator-migration-plan.md §3.3, §7.5).

Comparator builds the ``Challenge`` and ``Solution`` modules under different
module names and compares the configured target's closure by exact exported
names. Lean bakes the *source module name* into ``private`` declaration names
and some compiler-generated names (notably anonymous ``instance``s), so
byte-identical source can elaborate to different closures and a faithful
submission can be **falsely rejected**. This is fail-closed (invalid proofs are
never accepted), but it must not appear silently.

This module identifies, purely from the committed specs (no container), the
*candidate* set: specs whose already-isolated source contains one of the
module-derived name sources --

* a spec-local ``private`` declaration: its exported name is
  ``_private.<Module>.0.<name>``, unconditionally module-embedded. The *OEIS*
  generator strips ``private`` at generation (``scripts.isolation.strip_private``;
  privacy has no semantic effect beyond name visibility/mangling), so this
  reason firing on an OEIS spec means a regenerate skipped the strip; the
  erdos/fc100open private cases are kept as documented fail-closed limitations;
* an anonymous ``instance`` (with or without binders, ``instance :`` /
  ``instance (n : N) :`` / ``instance {..} [..] :``): Lean derives a name from
  the type and, *only when that name collides* with an existing constant,
  disambiguates by appending the module name (``instInhabitedNat_challenge`` vs
  ``instInhabitedNat_solution`` -- comparator#58);
* a ``deriving`` clause: the derived instances get the same generated names as
  anonymous instances, so the same collision rule applies.

Because isolation keeps only the target plus its dependency closure, a
surviving module-embedded name is normally in the compared closure, so such a
spec is a drift candidate.

The candidate set is a static over-approximation (collision-conditional
mechanisms usually do NOT fire): the *confirmed* affected set is determined
empirically by compiling each candidate once as module ``Challenge`` in the
comparator image and checking for module-embedded constant names reachable
from the target/`.disproof` closure -- byte-identical source compiled as
``Solution`` differs in exactly those names. ``tests/test_comparator_drift.py``
pins ``CANDIDATE_IDS`` so a dataset / Lean / exporter / Comparator bump that
introduces or removes a candidate fails CI loudly, prompting that scan to be
re-run.

History: before the strip, 20 specs (19 ``private``, 1 instance-collision)
were confirmed false-rejects -- ``oeis_A258667_conjecture_0``'s published gold
proof was rejected live with "Const does not match between challenge and
target 'A258667'". The OEIS-only strip fixed that dataset's 14 ``private``
cases; that gold proof now passes and serves as the fix's regression guard
(``tests/test_gold_proofs.py``). Of the 5 erdos/fc100open ``private`` rejects,
3 left the erdos corpus with the Bloom statement selection; the remaining 2
and the 1 OEIS instance-collision persist (see ``CONFIRMED_REJECT_IDS``).
"""

from __future__ import annotations

import re
from pathlib import Path

from apn.dataset import ERDOS_DIR, FC100_DIR, OEIS_DIR, load_manifest
from scripts.isolation import strip_comments_and_strings

# A spec-local `private` declaration (any form) -- its name mangles to
# `_private.<module>.0.<name>`, unconditionally differing between Challenge
# and Solution.
_PRIVATE_RE = re.compile(r"(?m)^\s*private\b")
# An anonymous `instance` (no name; `instance :` or binder forms such as
# `instance (n : N) :` / `instance {..} [..] :`). Its type-derived generated
# name gains a module-derived suffix only when it collides with an existing
# constant (comparator#58). A *named* `instance foo :` never does.
_ANON_INSTANCE_RE = re.compile(r"(?m)^\s*(?:noncomputable\s+)?instance\s*(?:$|[:(\[{⦃])")
# A `deriving` clause generates instances under the same naming scheme, so the
# same collision rule applies.
_DERIVING_RE = re.compile(r"\bderiving\b")

DATASETS = (OEIS_DIR, ERDOS_DIR, FC100_DIR)


def drift_reasons(spec_text: str) -> list[str]:
    """The module-derived-name triggers present in a committed spec (empty if
    none). Comment/string-aware so a ``private`` mentioned in prose or a quoted
    string never counts."""
    code = strip_comments_and_strings(spec_text)
    reasons: list[str] = []
    if _PRIVATE_RE.search(code):
        reasons.append("private-decl")
    if _ANON_INSTANCE_RE.search(code):
        reasons.append("anon-instance")
    if _DERIVING_RE.search(code):
        reasons.append("deriving")
    return reasons


def drift_candidates() -> dict[str, list[str]]:
    """Every committed spec that is a module-sensitive drift candidate, mapped to
    its trigger reasons."""
    out: dict[str, list[str]] = {}
    for dataset_dir in DATASETS:
        for row in load_manifest(dataset_dir):
            if row.excluded is not None:
                continue
            reasons = drift_reasons((Path(dataset_dir) / row.statement_path).read_text())
            if reasons:
                out[row.id] = reasons
    return out


# Pinned candidate set (static over-approximation; guarded by
# tests/test_comparator_drift.py): 1 fc100open spec with a spec-local
# `private` declaration (the OEIS and erdos ones are stripped at generation;
# the Bloom statement selection dropped the old erdos corpus's other `private`
# carriers), 11 with an anonymous `instance` (7 of those also `deriving`), and
# 1 `deriving`-only.
CANDIDATE_IDS: frozenset[str] = frozenset({
    "A379240_conjecture_equality",
    "EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic",
    "Erdos340.erdos_340.variants.co_density_zero_sub",
    "MonochromaticQuantumGraph.eqSystem10_no_solution_d3",
    "MonochromaticQuantumGraph.eqSystem10_no_solution_d3_trinary_int",
    "MonochromaticQuantumGraph.eqSystem10_no_solution_d4",
    "MonochromaticQuantumGraph.eqSystem12_no_solution_d3",
    "MonochromaticQuantumGraph.eqSystem16_no_solution_d3",
    "MonochromaticQuantumGraph.eqSystem6_no_solution_d4",
    "MonochromaticQuantumGraph.eqSystem_no_solution_ge6_ge3_real",
    "OpenQuantumProblem23.hasSICPOVM_60",
    "oeis_341685_conjecture_0",
    "oeis_a122589_conjecture_0",
})

# Empirically CONFIRMED false-reject set (2026-08-25 scan, re-run after the
# OEIS `private` strip: each candidate compiled once as module `Challenge` in
# the comparator image; a spec is confirmed iff a module-embedded constant
# name is reachable from the target/`.disproof` dependency closure -- the
# byte-identical `Solution` build differs in exactly those names, so
# comparator's compare step must reject a faithful submission). These specs
# are unwinnable as shipped (fail-closed: invalid proofs are still never
# accepted):
#
# * 1 fc100open spec with a `private` def in the target closure (deliberately
#   left unstripped; the OEIS and erdos generators strip at generation --
#   Erdos101.erdos_101 left this set when the erdos strip was adopted.
#   Confirmed as 5 in the 2026-08-25 scan, of which 3 left the erdos corpus
#   with the Bloom statement selection);
# * oeis_341685_conjecture_0, an anonymous instance whose generated name
#   collides (`Fact (Nat.Prime 3)` -> `instFactPrimeOfNatNat_challenge`)
#   inside the statement itself; verified end-to-end by an identical-file
#   comparator probe ("Challenge and solution theorem statement do not
#   match"). Fixing it would mean naming the instance in the committed spec.
#
# The other candidates are clean: their generated instance names are
# namespaced or collision-free, so both modules produce identical names --
# except specs that DO carry module-embedded names which sit outside the
# compared closure and are therefore benign, all verified end-to-end by
# identical-file comparator probes that pass the compare step and reject only
# at the sorryAx axiom check: oeis_a122589_conjecture_0
# (`instCoeNatReal_challenge`), the EllipticCurveRank spec
# (`inst..._challenge`), and A381358_limit_exists /
# general_supercongruence_conjecture (Lean auto-generates *private* match
# equation lemmas -- `<def>.match_1.eq_N`/`.splitter`/`._arg_pusher` -- even
# for the now-public defs; they are elaboration-time artifacts outside the
# exported target closure). Erdos1148.erdos_1148, benign in the 2026-08-25
# scan (a `private` instance the statement never references), has since left
# the erdos corpus.
CONFIRMED_REJECT_IDS: frozenset[str] = frozenset({
    "Erdos340.erdos_340.variants.co_density_zero_sub",
    "oeis_341685_conjecture_0",
})


def main() -> None:
    cands = drift_candidates()
    print(f"{len(cands)} drift candidates:")
    for cid, reasons in sorted(cands.items()):
        print(f"  {cid}: {','.join(reasons)}")


if __name__ == "__main__":
    main()
