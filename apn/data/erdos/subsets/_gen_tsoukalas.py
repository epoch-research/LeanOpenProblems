#!/usr/bin/env python3
"""Regenerate ``tsoukalas.json`` -- the Tsoukalas paper's Erdős attempted set.

The committed file is this script's output; rerunning it reproduces that file
byte-for-byte. Run from the repo root::

    python3 apn/data/erdos/subsets/_gen_tsoukalas.py

The set is defined by reconciling the paper's attempted list against the
vendored FC commit, and the committed JSON records both the inputs and the
result:

* ``attempted`` -- the 353 names of ``erdos_problems_attempted.txt`` from the
  AlphaProof Nexus results repository, in upstream order. ``_meta.upstream``
  pins that file's repo, commit and SHA-256, so the list is auditable against
  the source without vendoring a second copy of it.
* ``excluded`` / ``renamed`` -- the reconciliation, one documented reason per
  entry: 3 attempted names have no statement at the vendored FC commit, and 1
  was renamed upstream between the paper's attempt and that commit.
* ``samples`` -- the resulting 350 sample ids (fully qualified declaration
  names), which is what ``apn.dataset.load_subset`` returns.

``samples`` is derived from the short kept names via the committed
``MAPPING.json``, so regeneration is a two-step dance whenever membership
changes: run ``scripts/generate_erdos_isolated.py`` first (it reads the
membership fields here and rewrites MAPPING.json and Isolated/), then this
script to refresh ``samples``. Membership itself is hand-maintained -- it
encodes upstream facts, not a computation.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from apn.dataset import ERDOS_MAPPING_FILE, parse_decl_mapping
from scripts.isolation import matches_name

_HERE = Path(__file__).resolve().parent
OUT = _HERE / "tsoukalas.json"

UPSTREAM = {
    "repo": "https://github.com/google-deepmind/alphaproof-nexus-results",
    "commit": "c58c3cd01dd8cb5705606565ac23bfd81d432ae5",
    "path": "erdos_problems_attempted.txt",
    "license": "CC-BY 4.0, © 2026 Google LLC",
    # The upstream file is exactly the `attempted` names below, newline-separated
    # with no trailing newline; `verify_attempted_digest` re-derives this from
    # them, so a hand-edit of the list fails instead of silently redefining the
    # paper's set.
    "sha256": "144046c754a6ba494944bbd9378d26e23355fb0298ef4e78ca821ded44d4f6a3",
}
FC_COMMIT = "67338a157bbb8d87e9a349d662f82a868bda6327"

_NEVER_PUBLIC = (
    "never existed in the public FC repository: a full-history "
    "`git log -S <name> --all` finds nothing, and the live main (checked "
    "2026-07-27, including renamed variants.* forms) has no such statement -- "
    "presumably attempted against a Google-internal FC state never upstreamed"
)
EXCLUDED = [
    {"target": "erdos_677_stronger", "reason": _NEVER_PUBLIC},
    {"target": "erdos_7.variant.autoformalized", "reason": _NEVER_PUBLIC},
    {
        "target": "erdos_729",
        "reason": (
            "exists on FC main only after the vendored commit (upstreamed ~July "
            "2026). Including it would need special-cased statement adaptation "
            "against a different FC state than everything else; provenance purity "
            "won over the +1 sample. Revisit if the sandbox images move past its "
            "upstreaming"
        ),
    },
]
RENAMED = [
    {
        "attempted": "erdos_1082b",
        "at_fc_commit": "erdos_1082.parts.ii",
        "reason": (
            "upstream rename between the paper's attempt and the vendored FC commit"
        ),
    }
]

DESCRIPTION = (
    "The Tsoukalas paper's canonical Erdős attempted set (arXiv 2605.22763): the "
    "353 FC ErdosProblems statements the paper's agent attempted -- every FC "
    "ErdosProblems statement as of early Feb 2026 -- minus 3 that cannot be "
    "reconciled with the vendored FC commit, with 1 upstream rename applied. "
    "Membership ignores resolution status: it is the paper's attempted set, "
    "regardless of what has been resolved since."
)


def verify_attempted_digest(attempted: list[str]) -> None:
    """Check the ``attempted`` list still hashes to the vendored upstream file."""
    digest = hashlib.sha256("\n".join(attempted).encode()).hexdigest()
    if digest != UPSTREAM["sha256"]:
        raise SystemExit(
            f"attempted list hashes to {digest}, expected {UPSTREAM['sha256']} "
            f"({UPSTREAM['path']} at {UPSTREAM['commit'][:7]})"
        )


def kept_short_names(attempted: list[str]) -> list[str]:
    """The 350 kept short names: ``attempted`` minus ``EXCLUDED``, with
    ``RENAMED`` applied, in attempt-list order."""
    excluded = {row["target"] for row in EXCLUDED}
    renames = {row["attempted"]: row["at_fc_commit"] for row in RENAMED}
    return [renames.get(n, n) for n in attempted if n not in excluded]


def main() -> None:
    attempted = json.loads(OUT.read_text())["attempted"]
    if len(attempted) != 353 or len(set(attempted)) != 353:
        raise SystemExit(f"expected 353 distinct attempted names, got {len(attempted)}")
    verify_attempted_digest(attempted)
    unknown = sorted({row["target"] for row in EXCLUDED} - set(attempted))
    if unknown:
        raise SystemExit(f"excluded names not in the attempted list: {unknown}")

    kept = kept_short_names(attempted)
    mapped = parse_decl_mapping(ERDOS_MAPPING_FILE.read_text())
    by_short = {short: full for (full, _), short in zip(mapped, kept)}
    for short, full in by_short.items():
        if not matches_name(full, short):
            raise SystemExit(f"MAPPING.json entry {full} does not resolve {short}")
    if len(by_short) != len(kept):
        raise SystemExit("MAPPING.json does not cover the kept names one-to-one")

    payload = {
        "_meta": {
            "name": "tsoukalas",
            "description": DESCRIPTION,
            "generator": "apn/data/erdos/subsets/_gen_tsoukalas.py",
            "upstream": UPSTREAM,
            "fc_commit": FC_COMMIT,
            "counts": {
                "attempted": len(attempted),
                "excluded": len(EXCLUDED),
                "renamed": len(RENAMED),
                "samples": len(kept),
            },
        },
        "attempted": attempted,
        "excluded": EXCLUDED,
        "renamed": RENAMED,
        "samples": [by_short[short] for short in kept],
    }
    OUT.write_text(json.dumps(payload, indent=1, ensure_ascii=False) + "\n")
    print(f"wrote {OUT} with {len(kept)} samples")


if __name__ == "__main__":
    main()
