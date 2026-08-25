"""Pin the module-sensitive drift-candidate set (comparator-migration-plan.md §3.3).

Fast, pure-Python (no container): it recomputes the candidate set from the
committed specs and asserts it equals the pinned ``CANDIDATE_IDS``. Comparator
can falsely reject a faithful submission when the target's closure contains a
spec-local ``private`` or anonymous-``instance`` declaration (a module-derived
name that differs between the Challenge and Solution modules). This test makes a
dataset / Lean / exporter / Comparator bump that adds or removes such a spec fail
loudly, so the §7.5 comparator sweep is re-run and the confirmed affected list
kept current rather than drifting silently.
"""

from __future__ import annotations

from scripts.comparator_drift import CANDIDATE_IDS, drift_candidates


def test_drift_candidate_set_is_pinned() -> None:
    found = set(drift_candidates())
    assert found == set(CANDIDATE_IDS), (
        "module-sensitive drift-candidate set changed; re-run the §7.5 comparator "
        "sweep and update CANDIDATE_IDS.\n"
        f"  newly appeared: {sorted(found - set(CANDIDATE_IDS))}\n"
        f"  disappeared:    {sorted(set(CANDIDATE_IDS) - found)}"
    )
