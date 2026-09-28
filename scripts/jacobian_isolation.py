"""Jacobian-conjecture frontend for the per-target isolation pipeline.

The dataset-neutral cut logic lives in ``scripts/isolation.py``; this module
owns the data locations under ``apn/data/jacobian/``. The one vendored source
restates formal-conjectures' Jacobian conjecture over ``ℂ`` with the known
resolution withheld (see the dataset's ``NOTICE.md``), in FC's conventions, so
membership uses the same census as the Erdős universe
(``scripts.erdos_isolation``): every standalone ``theorem``/``lemma``
declaration carrying a research-category attribute is a member.

As for ``personal_corresp`` there is nothing to un-record: the source ships no
``answer(...)`` forms, no recorded verdicts, no in-file proofs of members, and
no anonymous ``example`` sanity checks -- generation *asserts* those absences
instead of rewriting/excluding, so drift at regeneration fails loudly.

Two callers import this module: ``scripts/generate_jacobian_isolated.py`` (the
vendor-time tool that produces ``samples.jsonl`` + ``Isolated/``) and
``tests/test_jacobian_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

from scripts.isolation import REPO

JACOBIAN_DIR = REPO / "apn" / "data" / "jacobian"
SOURCES_DIR = JACOBIAN_DIR / "Sources"
ISOLATED_DIR = JACOBIAN_DIR / "Isolated"
