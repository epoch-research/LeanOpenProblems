#!/usr/bin/env python3
"""Regenerate ``lite.txt`` -- a seeded random subset of the 492 OEIS conjectures.

The committed ``lite.txt`` is the output of this script; rerunning it reproduces
that file byte-for-byte. Run from the repo root::

    python3 apn/data/oeis/subsets/_gen_lite.py

Why a lite subset: each OEIS sample is a long agent run, so the full 492 is
expensive to sweep. A random subset estimates the full-set pass rate at a
fraction of the cost. At a true rate of ~20% (mid of the observed 10-30%), n=100
gives a 95% CI of about +/-7% after the finite-population correction -- enough to
rank models in that band. Below ~50 the estimate gets too noisy to compare
models; to detect small gaps between similar models, run the full 492.

Reproducibility: the universe is the sorted set of conjecture theorem names, so
the draw does not depend on ``THEOREM_MAPPING.txt`` line order; ``random.Random``
is seeded with a fixed constant. Bump ``SEED`` (not the data) if you ever need a
fresh independent draw, and say so in the header.
"""

from __future__ import annotations

import random
from pathlib import Path

SEED = 42
N = 100

_HERE = Path(__file__).resolve().parent
MAPPING = _HERE.parent / "THEOREM_MAPPING.txt"
OUT = _HERE / "lite.txt"

HEADER = f"""\
# lite -- a randomly drawn {N}-conjecture subset of the 492 OEIS Open Problems,
# for cheaper runs that still estimate the full-set pass rate. One conjecture
# theorem name per line; blank lines and #-comments are ignored (see
# apn.dataset.load_subset). Referenced by name, e.g. `apn_oeis(subset="lite")`.
#
# At a true pass rate of ~20% (mid of the observed 10-30%), n={N} gives a 95%
# CI of about +/-7% after the finite-population correction -- enough to rank
# models in that band at ~1/5 the cost of the full run. Below ~50 the estimate
# gets too noisy to compare models; for detecting small gaps, run the full 492.
#
# Reproducible pipeline (regenerates this file byte-for-byte):
#   universe = sorted(first-token of every non-blank line in THEOREM_MAPPING.txt)
#   assert len(universe) == 492
#   chosen   = sorted(random.Random({SEED}).sample(universe, {N}))
# Sorting the universe first makes the draw independent of mapping line order.
# Seed = {SEED}. To regenerate: python3 apn/data/oeis/subsets/_gen_lite.py
"""


def main() -> None:
    universe = sorted(
        line.split()[0] for line in MAPPING.read_text().splitlines() if line.split()
    )
    assert len(universe) == 492, f"expected 492 conjectures, found {len(universe)}"
    assert len(set(universe)) == 492, "duplicate theorem names in mapping"

    chosen = sorted(random.Random(SEED).sample(universe, N))
    OUT.write_text(HEADER + "\n" + "\n".join(chosen) + "\n")
    print(f"wrote {OUT} with {len(chosen)} names (seed={SEED})")


if __name__ == "__main__":
    main()
