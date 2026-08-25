"""Module-sensitive closure drift analysis (comparator-migration-plan.md §3.3, §7.5).

Comparator builds the ``Challenge`` and ``Solution`` modules under different
module names and compares the configured target's closure by exact exported
names. Lean bakes the *source module name* into ``private`` declaration names
and some compiler-generated names (notably anonymous ``instance``s), so
byte-identical source can elaborate to different closures and a faithful
submission can be **falsely rejected**. This is fail-closed (invalid proofs are
never accepted), but it must not appear silently.

This module identifies, purely from the committed specs (no container), the
*candidate* set: specs whose already-isolated source contains a spec-local
``private`` declaration or an anonymous ``instance :`` -- the two module-derived
name sources. Because isolation keeps only the target plus its dependency
closure, such a surviving declaration is in the compared closure, so it is a
drift candidate.

The candidate set is a static over-approximation: the *confirmed* affected set
(the subset an actual identical-source Challenge/Solution comparator run rejects
at the compare step) is a subset of these, determined by the §7.5 pre-cutover
sweep -- not run here. ``tests/test_comparator_drift.py`` pins ``CANDIDATE_IDS``
so a dataset / Lean / exporter / Comparator bump that introduces or removes a
candidate fails CI loudly, prompting that sweep to be re-run.
"""

from __future__ import annotations

import re
from pathlib import Path

from apn.dataset import ERDOS_DIR, FC100_DIR, OEIS_DIR, load_manifest
from scripts.isolation import strip_comments_and_strings

# A spec-local `private` declaration (any decl kind) -- its name mangles to
# `_private.<module>.<hash>.<name>`, differing between Challenge and Solution.
_PRIVATE_RE = re.compile(
    r"(?m)^\s*private\s+(?:noncomputable\s+)?"
    r"(?:def|theorem|lemma|abbrev|instance|structure|inductive)\b"
)
# An anonymous `instance :` (no name) receives a module-derived generated name
# (comparator#58). A *named* `instance foo :` does not.
_ANON_INSTANCE_RE = re.compile(r"(?m)^\s*(?:noncomputable\s+)?instance\s*:")

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
# tests/test_comparator_drift.py): 20 specs with a spec-local `private`
# declaration + 3 with an anonymous `instance :`. The precise reject subset is
# confirmed by the §7.5 pre-cutover sweep (not run here).
CANDIDATE_IDS: frozenset[str] = frozenset({
    "A253187.universal_sum_conjecture",
    "A277223_conjecture",
    "A381358_limit_exists",
    "EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic",
    "Erdos101.erdos_101",
    "Erdos1148.erdos_1148",
    "Erdos340.erdos_340",
    "Erdos340.erdos_340.variants._33_mem_sub",
    "Erdos340.erdos_340.variants.co_density_zero_sub",
    "Erdos340.erdos_340.variants.sub_hasPosDensity",
    "general_supercongruence_conjecture",
    "oeis_145062_conjecture_0",
    "oeis_253187_conjecture_1",
    "oeis_341685_conjecture_0",
    "oeis_354766_conjecture_1_multiplicative",
    "oeis_60957_conjecture_0",
    "oeis_A078590_conjecture",
    "oeis_A258667_conjecture_0",
    "oeis_A262781_conjecture",
    "oeis_a103885_conjecture_0",
    "oeis_a122589_conjecture_0",
    "oeis_a279612_conjecture_i",
    "poincare_series_conjecture",
})


def main() -> None:
    cands = drift_candidates()
    print(f"{len(cands)} drift candidates:")
    for cid, reasons in sorted(cands.items()):
        print(f"  {cid}: {','.join(reasons)}")


if __name__ == "__main__":
    main()
