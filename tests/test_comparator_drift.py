"""Pin the module-sensitive drift sets (comparator-migration-plan.md §3.3).

Fast, pure-Python (no container): it recomputes the candidate set from the
committed specs and asserts it equals the pinned ``CANDIDATE_IDS``. Comparator
can falsely reject a faithful submission when the target's closure contains a
module-embedded generated name -- a spec-local ``private`` declaration
(unconditional) or an anonymous/derived instance whose generated name collides
with an existing constant (comparator#58). This test makes a dataset / Lean /
exporter / Comparator bump that adds or removes such a spec fail loudly, so
the empirical compile-as-Challenge scan is re-run and the confirmed
``CONFIRMED_REJECT_IDS`` kept current rather than drifting silently.
"""

from __future__ import annotations

from scripts.comparator_drift import CANDIDATE_IDS, CONFIRMED_REJECT_IDS, drift_candidates


def test_drift_candidate_set_is_pinned() -> None:
    found = set(drift_candidates())
    assert found == set(CANDIDATE_IDS), (
        "module-sensitive drift-candidate set changed; re-run the empirical "
        "compile-as-Challenge scan and update CANDIDATE_IDS/CONFIRMED_REJECT_IDS.\n"
        f"  newly appeared: {sorted(found - set(CANDIDATE_IDS))}\n"
        f"  disappeared:    {sorted(set(CANDIDATE_IDS) - found)}"
    )


def test_confirmed_rejects_are_candidates() -> None:
    # The empirically confirmed false-reject set is a subset of the static
    # over-approximation by construction; a violation means one of the lists
    # was edited by hand inconsistently.
    assert CONFIRMED_REJECT_IDS <= CANDIDATE_IDS
