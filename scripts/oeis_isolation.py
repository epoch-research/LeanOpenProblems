"""OEIS frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``; this module owns what is OEIS-specific -- the data
locations under ``apn/data/oeis/``. Membership is the committed
``samples.jsonl`` manifest (one row per conjecture, transcribed at vendor time
from upstream's ``THEOREM_MAPPING.txt``; see the dataset's ``NOTICE.md``).

Two callers import this module:

* ``scripts/generate_oeis_isolated.py`` -- the vendor-time tool that *produces*
  ``apn/data/oeis/Isolated/`` from ``Sources/`` + the manifest.
* ``tests/test_oeis_isolation.py`` -- the authoritative *validation* of the
  committed ``Isolated/`` files (re-extraction structural check, the
  ``lake env lean -o`` compile gate, and the paper oracle cross-check).
"""

from __future__ import annotations

from scripts.isolation import REPO

OEIS_DIR = REPO / "apn" / "data" / "oeis"
SOURCES_DIR = OEIS_DIR / "Sources"
ISOLATED_DIR = OEIS_DIR / "Isolated"
