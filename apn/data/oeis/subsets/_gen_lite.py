#!/usr/bin/env python3
"""Regenerate ``lite.json`` -- a seeded random subset of the 492 OEIS conjectures.

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
the draw does not depend on ``THEOREM_MAPPING.json`` row order; ``random.Random``
is seeded with a fixed constant. Bump ``SEED`` (not the data) if you ever need a
fresh independent draw, and say so in the header.
"""

from __future__ import annotations

import json
import random
from pathlib import Path

from apn.dataset import parse_oeis_mapping

SEED = 42
N = 100

_HERE = Path(__file__).resolve().parent
MAPPING = _HERE.parent / "THEOREM_MAPPING.json"
OUT = _HERE / "lite.json"

DESCRIPTION = (
    f"A randomly drawn {N}-conjecture subset of the 492 OEIS Open Problems, for "
    f"cheaper runs that still estimate the full-set pass rate. At a true pass rate "
    f"of ~20% (mid of the observed 10-30%), n={N} gives a 95% CI of about +/-7% "
    f"after the finite-population correction -- enough to rank models in that band "
    f"at ~1/5 the cost of the full run. Below ~50 the estimate gets too noisy to "
    f"compare models; for detecting small gaps, run the full 492."
)
DERIVATION = (
    f"universe = sorted(target of every THEOREM_MAPPING.json row); "
    f"assert len(universe) == 492; "
    f"chosen = sorted(random.Random({SEED}).sample(universe, {N})). "
    f"Sorting the universe first makes the draw independent of mapping row order."
)


def main() -> None:
    universe = sorted(name for name, _ in parse_oeis_mapping(MAPPING.read_text()))
    assert len(universe) == 492, f"expected 492 conjectures, found {len(universe)}"
    assert len(set(universe)) == 492, "duplicate theorem names in mapping"

    chosen = sorted(random.Random(SEED).sample(universe, N))
    payload = {
        "_meta": {
            "name": "lite",
            "description": DESCRIPTION,
            "generator": "apn/data/oeis/subsets/_gen_lite.py",
            "derivation": DERIVATION,
            "seed": SEED,
        },
        "samples": chosen,
    }
    OUT.write_text(json.dumps(payload, indent=1, ensure_ascii=False) + "\n")
    print(f"wrote {OUT} with {len(chosen)} names (seed={SEED})")


if __name__ == "__main__":
    main()
