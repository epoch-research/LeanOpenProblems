# type: ignore
"""FC100OpenSet1 frontend for the per-target isolation pipeline.

The dataset-neutral cut logic and Docker plumbing live in
``scripts/isolation.py``, and the Formal-Conjectures statement conventions
(the ``example``-command cut, the ``answer(...) ↔`` rewrite and its
re-elaboration certificates) in ``scripts/fc_statements.py``; this module owns
what is FC100-specific -- the data locations under ``apn/data/fc100open/`` and
their parsers. Membership comes from the vendored subset file
``FC100OpenSet1.lean`` (the paper's frozen 100-problem open set, arXiv
2605.13171) minus ``EXCLUDED.txt`` (the 14 value-typed ``answer(sorry)``
members, unscorable by SafeVerify).

Two callers import this module: ``scripts/generate_fc100_isolated.py`` (the
vendor-time tool that produces ``Isolated/`` + ``MAPPING.txt``) and
``tests/test_fc100_isolation.py`` (the authoritative validation of the
committed files).
"""

from __future__ import annotations

import re

from apn.dataset import parse_decl_mapping as parse_mapping  # re-exported
from scripts.isolation import REPO

FC100_DIR = REPO / "apn" / "data" / "fc100open"
SOURCES_DIR = FC100_DIR / "Sources"
ISOLATED_DIR = FC100_DIR / "Isolated"
SUBSET_FILE = FC100_DIR / "FC100OpenSet1.lean"
EXCLUDED_FILE = FC100_DIR / "EXCLUDED.txt"
MAPPING_FILE = FC100_DIR / "MAPPING.txt"

# Targets whose isolated spec may carry a `sorry` outside the target theorem.
# Wikipedia/EllipticCurveRank.lean declares its Mordell-Weil `Module.Finite`
# instance with `:= sorry` in FC itself; it is deliberately kept as-is (decided
# at task-addition time), so that sample implicitly also requires proving the
# instance. Generation reports it instead of failing.
SORRY_ALLOWLIST = {
    "EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic",
}

_DECL_NAME_RE = re.compile(r"decl_name%\s+([^\s,\]]+)")


def parse_subset_names(text: str) -> list[str]:
    """The member names listed in ``FC100OpenSet1.lean`` (its ``problems`` list
    of ``decl_name% <Name>`` entries), in file order."""
    return _DECL_NAME_RE.findall(text)


def parse_excluded(text: str) -> list[str]:
    """The excluded member names in ``EXCLUDED.txt`` (one per line; blank lines
    and ``#`` comments ignored)."""
    names: list[str] = []
    for line in text.splitlines():
        entry = line.split("#", 1)[0].strip()
        if entry:
            names.append(entry)
    return names


def kept_names() -> list[str]:
    """The 86 kept member names: the subset file's 100 minus ``EXCLUDED.txt``'s
    14, in subset-file order. Fails loudly if the membership arithmetic is off
    (a vendoring or exclusion-list error, never something to paper over)."""
    members = parse_subset_names(SUBSET_FILE.read_text())
    if len(members) != 100 or len(set(members)) != 100:
        raise SystemExit(f"expected 100 distinct subset members, found {len(members)}")
    excluded = parse_excluded(EXCLUDED_FILE.read_text())
    if len(excluded) != 14:
        raise SystemExit(f"expected 14 excluded members, found {len(excluded)}")
    unknown = sorted(set(excluded) - set(members))
    if unknown:
        raise SystemExit(f"EXCLUDED.txt names not in the subset: {unknown}")
    kept = [n for n in members if n not in set(excluded)]
    assert len(kept) == 86
    return kept
