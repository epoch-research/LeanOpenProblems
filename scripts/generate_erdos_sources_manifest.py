"""Regenerate ``apn/data/erdos/SOURCES.json`` -- the vendored-corpus manifest.

``Sources/`` is the complete ``FormalConjectures/ErdosProblems/`` directory of
the Formal Conjectures repository at the commit the sandbox images bake. The
manifest records that provenance plus a SHA-256 per file, so
``tests/test_erdos.py`` can assert the corpus is complete and unmodified
without reaching for the (gitignored) local FC clone.

Run from the repo root, with the clone present::

    python scripts/generate_erdos_sources_manifest.py
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SOURCES_DIR = REPO / "apn" / "data" / "erdos" / "Sources"
MANIFEST_FILE = REPO / "apn" / "data" / "erdos" / "SOURCES.json"
FC_COMMIT = "67338a157bbb8d87e9a349d662f82a868bda6327"


def main() -> None:
    files = sorted(SOURCES_DIR.glob("*.lean"), key=lambda p: p.name)
    manifest = {
        "_meta": {
            "description": (
                "Complete FormalConjectures/ErdosProblems/ directory vendored "
                "verbatim from the Formal Conjectures repository. Corpus only: "
                "which statements belong to which evaluation set is defined by "
                "the files under subsets/, and which are runnable by MAPPING.json."
            ),
            "repo": "https://github.com/google-deepmind/formal-conjectures",
            "commit": FC_COMMIT,
            "path": "FormalConjectures/ErdosProblems",
            "license": "Apache-2.0, © 2026 The Formal Conjectures Authors",
            "generator": "scripts/generate_erdos_sources_manifest.py",
        },
        "files": {
            p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files
        },
    }
    MANIFEST_FILE.write_text(json.dumps(manifest, indent=1, sort_keys=False) + "\n")
    print(f"{len(files)} files -> {MANIFEST_FILE.relative_to(REPO)}")


if __name__ == "__main__":
    main()
