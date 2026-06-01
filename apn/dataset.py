"""Datasets of Lean proof sketches.

A *sketch* is a Lean file containing one or more theorems whose proof bodies are
``sorry``. Each becomes an Inspect :class:`Sample` whose input is the file text
and whose metadata records the target theorem name(s) and the original sketch
text (so the scorer can check the statement was preserved).

Currently this loads the autoformalized OEIS conjectures from Formal Conjectures
(the paper's 44/492 evaluation).
"""

from __future__ import annotations

import re
from pathlib import Path

from inspect_ai.dataset import MemoryDataset, Sample

OEIS_DIR = Path(__file__).parent / "data" / "oeis"
OEIS_AUTO_DIR = OEIS_DIR / "Auto"
OEIS_MAPPING_FILE = OEIS_DIR / "THEOREM_MAPPING.txt"

_OEIS_NUM_RE = re.compile(r"^(\d+)_")


def oeis_id_from_filename(filename: str) -> str | None:
    """The OEIS A-number for an ``OEIS/Auto`` file (its leading digits).

    Filenames look like ``268597_aacea533.lean`` -> ``A268597``. More reliable
    than parsing the theorem name, some of which carry no A-number.
    """
    match = _OEIS_NUM_RE.match(filename)
    return f"A{int(match.group(1)):06d}" if match else None


def parse_oeis_mapping(text: str) -> list[tuple[str, list[str]]]:
    """Parse ``THEOREM_MAPPING.txt`` into ``(theorem_name, [files])`` entries.

    Each line is ``<conjecture_theorem_name> <file.lean> [<file.lean> ...]``;
    one conjecture occasionally has more than one formalization file.
    """
    entries: list[tuple[str, list[str]]] = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) >= 2:
            entries.append((parts[0], parts[1:]))
    return entries


def oeis_dataset(
    auto_dir: str | Path = OEIS_AUTO_DIR,
    mapping_file: str | Path = OEIS_MAPPING_FILE,
    names: list[str] | None = None,
) -> MemoryDataset:
    """The Formal Conjectures autoformalized OEIS conjectures as Samples.

    One sample per mapping entry (one conjecture). The whole file is the sketch:
    the agent must discharge the embedded *test lemmas* (small-term checks that
    guard against misformalization) as well as the conjecture. The conjecture
    theorem name is the scoring target.

    Args:
        auto_dir: Directory of ``OEIS/Auto`` ``*.lean`` files.
        mapping_file: ``THEOREM_MAPPING.txt`` (theorem name -> file(s)).
        names: If given, keep only these conjecture theorem names (e.g. a smoke
            subset).
    """
    auto = Path(auto_dir)
    entries = parse_oeis_mapping(Path(mapping_file).read_text())
    samples: list[Sample] = []
    for name, files in entries:
        if names is not None and name not in names:
            continue
        source_file = files[0]
        text = (auto / source_file).read_text()
        samples.append(
            Sample(
                input=text,
                id=name,
                metadata={
                    "sketch": text,
                    "target_declarations": [name],
                    "oeis_id": oeis_id_from_filename(source_file),
                    "source_file": source_file,
                    "alt_files": files[1:],
                },
            )
        )
    return MemoryDataset(samples, name="oeis")
