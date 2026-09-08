"""Marczinzik–Böhmler ring-theory frontend for the per-target isolation pipeline.

The dataset-neutral cut logic lives in ``scripts/isolation.py``; this module
owns the data locations under ``apn/data/marczinzik/``. The vendored sources
are hand-curated formalizations of two homological conjectures for
finite-dimensional algebras contributed by René Marczinzik and Bernhard
Böhmler, restated in FC's conventions (the ``FormalConjecturesUtil`` import,
``@[category research ...]`` attributes) -- see the dataset's ``NOTICE.md`` --
so membership uses the same census as the Erdős universe
(``scripts.erdos_isolation``): every standalone ``theorem``/``lemma``
declaration carrying a research-category attribute is a member.

As for ``erdos_autoformalized`` there is nothing to un-record: the sources ship
no ``answer(...)`` forms, no recorded verdicts, no in-file proofs of members,
and no anonymous ``example`` sanity checks -- generation *asserts* those
absences instead of rewriting/excluding, so drift at regeneration fails loudly.

Two callers import this module: ``scripts/generate_marczinzik_isolated.py``
(the vendor-time tool that produces ``samples.jsonl`` + ``Isolated/``) and
``tests/test_marczinzik_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

from scripts.isolation import REPO

MARCZINZIK_DIR = REPO / "apn" / "data" / "marczinzik"
SOURCES_DIR = MARCZINZIK_DIR / "Sources"
ISOLATED_DIR = MARCZINZIK_DIR / "Isolated"
