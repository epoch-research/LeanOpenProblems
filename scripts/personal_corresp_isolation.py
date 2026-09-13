"""Personal-correspondence frontend for the per-target isolation pipeline.

The dataset-neutral cut logic lives in ``scripts/isolation.py``; this module
owns the data locations under ``apn/data/personal_corresp/``. The vendored
sources are hand-curated formalizations of open conjectures sent to us by
mathematicians in personal correspondence (see the dataset's ``NOTICE.md`` for
the contributors), restated in FC's conventions (the ``FormalConjecturesUtil``
import, ``@[category research ...]`` attributes), so membership uses the same
census as the Erdős universe
(``scripts.erdos_isolation``): every standalone ``theorem``/``lemma``
declaration carrying a research-category attribute is a member.

As for ``erdos_autoformalized`` there is nothing to un-record: the sources ship
no ``answer(...)`` forms, no recorded verdicts, no in-file proofs of members,
and no anonymous ``example`` sanity checks -- generation *asserts* those
absences instead of rewriting/excluding, so drift at regeneration fails loudly.

Two callers import this module: ``scripts/generate_personal_corresp_isolated.py``
(the vendor-time tool that produces ``samples.jsonl`` + ``Isolated/``) and
``tests/test_personal_corresp_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

from scripts.isolation import REPO

PERSONAL_CORRESP_DIR = REPO / "apn" / "data" / "personal_corresp"
SOURCES_DIR = PERSONAL_CORRESP_DIR / "Sources"
ISOLATED_DIR = PERSONAL_CORRESP_DIR / "Isolated"
