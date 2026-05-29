"""Datasets of Lean proof sketches.

A *sketch* is a Lean file with the proof body replaced by ``sorry`` inside an
EVOLVE region. Each becomes an Inspect :class:`Sample` whose input is the file
text and whose metadata records the target theorem name(s) and the original
sketch text (so the scorer can recover the frozen statement).

This module ships a handful of small bundled sketches for smoke testing and a
loader for a directory of ``.lean`` sketch files (e.g. an export of the Formal
Conjectures Erdos problems, once their proofs are replaced with ``sorry``).
"""

from __future__ import annotations

import re
from pathlib import Path

from inspect_ai.dataset import MemoryDataset, Sample

DATA_DIR = Path(__file__).parent / "data" / "sketches"

_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|example|def)\s+([A-Za-z_][A-Za-z0-9_.'!?]*)",
    re.MULTILINE,
)


def infer_target_declarations(text: str) -> list[str]:
    """Best-effort extraction of named declarations from a sketch.

    Used as a fallback when a sample does not specify ``target_declarations``.
    Anonymous ``example``s yield no name.
    """
    return _DECL_RE.findall(text)


def sketch_sample(
    text: str,
    sample_id: str,
    target_declarations: list[str] | None = None,
) -> Sample:
    """Build a :class:`Sample` from sketch source."""
    declarations = target_declarations or infer_target_declarations(text)
    return Sample(
        input=text,
        id=sample_id,
        metadata={"sketch": text, "target_declarations": declarations},
    )


def dataset_from_dir(directory: str | Path) -> MemoryDataset:
    """Load every ``*.lean`` file in ``directory`` as a sketch sample."""
    path = Path(directory)
    samples = [
        sketch_sample(file.read_text(), file.stem)
        for file in sorted(path.glob("*.lean"))
    ]
    return MemoryDataset(samples, name=path.name)


def bundled_dataset() -> MemoryDataset:
    """The small set of bundled sketches used for smoke testing."""
    return dataset_from_dir(DATA_DIR)
