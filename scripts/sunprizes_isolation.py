"""Sun-prizes frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, category-attribute stripping) in
``scripts/fc_statements.py``; this module owns what is Sun-prizes-specific --
the data locations under ``apn/data/sunprizes/``. Membership is the committed
``samples.jsonl`` manifest: the Zhi-Wei Sun conjectures carrying cash prizes
on his homepage that are formalized in FC at the pinned commit (8 of the
page's 11; see the dataset's ``NOTICE.md``), transcribed at vendor time. All
8 are plain ``research open`` statements -- no ``answer(...)`` forms, no
excluded rows.

Two callers import this module: ``scripts/generate_sunprizes_isolated.py``
(the vendor-time tool that produces ``Isolated/``) and
``tests/test_sunprizes_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

from scripts.isolation import REPO

SUNPRIZES_DIR = REPO / "apn" / "data" / "sunprizes"
SOURCES_DIR = SUNPRIZES_DIR / "Sources"
ISOLATED_DIR = SUNPRIZES_DIR / "Isolated"
