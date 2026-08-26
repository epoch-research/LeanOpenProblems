"""Erdős-autoformalized frontend for the per-target isolation pipeline.

The dataset-neutral cut logic lives in ``scripts/isolation.py``; this module
owns the data locations under ``apn/data/erdos_autoformalized/``. The vendored
sources are our own autoformalization pipeline's output, not upstream
Formal-Conjectures files (see the dataset's ``NOTICE.md``) -- but they state
problems in FC's conventions (the ``FormalConjecturesUtil`` import,
``@[category research ...]`` attributes), so membership uses the same census
as the Erdős universe (``scripts.erdos_isolation``): every standalone
``theorem``/``lemma`` declaration carrying a research-category attribute is a
member.

Unlike the FC-derived datasets there is nothing to un-record: the sources ship
no ``answer(...)`` forms, no recorded verdicts, no in-file proofs, and no
anonymous ``example`` sanity checks -- generation *asserts* those absences
instead of rewriting/excluding, so upstream drift at regeneration fails loudly
(a member that trips one of them needs a curation decision, not a silent
exclusion row).

Two callers import this module:
``scripts/generate_erdos_autoformalized_isolated.py`` (the vendor-time tool
that produces ``samples.jsonl`` + ``Isolated/``) and
``tests/test_erdos_autoformalized_isolation.py`` (the authoritative validation
of the committed files).
"""

from __future__ import annotations

from scripts.isolation import REPO

ERDOS_AUTOFORMALIZED_DIR = REPO / "apn" / "data" / "erdos_autoformalized"
SOURCES_DIR = ERDOS_AUTOFORMALIZED_DIR / "Sources"
ISOLATED_DIR = ERDOS_AUTOFORMALIZED_DIR / "Isolated"
