"""FC100OpenSet1 frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates) in ``scripts/fc_statements.py``; this module owns
what is FC100-specific -- the data locations under ``apn/data/fc100open/``.
Membership is the committed ``samples.jsonl`` manifest (one row per member of
the paper's frozen 100-problem open set, arXiv 2605.13171, transcribed at
vendor time from upstream's ``FC100OpenSet1.lean``; the 14 value-typed
``answer(sorry)`` members, unscorable by SafeVerify, are its ``excluded``
rows -- see the dataset's ``NOTICE.md``).

Two callers import this module: ``scripts/generate_fc100_isolated.py`` (the
vendor-time tool that produces ``Isolated/``) and
``tests/test_fc100_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

from scripts.isolation import REPO

FC100_DIR = REPO / "apn" / "data" / "fc100open"
SOURCES_DIR = FC100_DIR / "Sources"
ISOLATED_DIR = FC100_DIR / "Isolated"

# Targets whose isolated spec may carry a `sorry` outside the target theorem.
# Wikipedia/EllipticCurveRank.lean declares its Mordell-Weil `Module.Finite`
# instance with `:= sorry` in FC itself; it is deliberately kept as-is (decided
# at task-addition time), so that sample implicitly also requires proving the
# instance. Generation reports it instead of failing.
SORRY_ALLOWLIST = {
    "EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic",
}
