# type: ignore
"""OEIS frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``; this module owns what is OEIS-specific -- the data
locations under ``apn/data/oeis/`` and the ``THEOREM_MAPPING.txt`` parser.

Two callers import this module:

* ``scripts/generate_oeis_isolated.py`` -- the vendor-time tool that *produces*
  ``apn/data/oeis/Isolated/`` from ``Auto/`` + ``THEOREM_MAPPING.txt``.
* ``tests/test_oeis_isolation.py`` -- the authoritative *validation* of the
  committed ``Isolated/`` files (re-extraction structural check, the
  ``lake env lean -o`` compile gate, and the paper oracle cross-check).
"""

from __future__ import annotations

from apn.dataset import parse_oeis_mapping as parse_mapping  # re-exported
from scripts.isolation import REPO

OEIS_DIR = REPO / "apn" / "data" / "oeis"
AUTO_DIR = OEIS_DIR / "Auto"
ISOLATED_DIR = OEIS_DIR / "Isolated"
MAPPING_FILE = OEIS_DIR / "THEOREM_MAPPING.txt"
