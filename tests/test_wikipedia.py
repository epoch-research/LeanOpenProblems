"""Tests for the Wikipedia dataset loader (pure Python, no Docker).

The Lean guarantees over the committed ``Isolated/`` specs are enforced in a
container by ``tests/test_wikipedia_isolation.py``; this module checks the
manifest census against the vendored sources, the dataset/sample shape, and
textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re

from apn.dataset import WIKIPEDIA_DIR, load_manifest, wikipedia_dataset
from apn.task import apn_wikipedia
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration
from scripts.wikipedia_isolation import DISPROOF_PREAMBLES, RESEARCH_OPEN_ATTR_RE, SOURCES_DIR


def test_manifest_covers_every_research_open_statement() -> None:
    per_file = {
        f"Sources/{p.name}": len(RESEARCH_OPEN_ATTR_RE.findall(p.read_text()))
        for p in SOURCES_DIR.glob("*.lean")
    }
    assert all(n > 0 for n in per_file.values())
    counts: dict[str, int] = {}
    for row in load_manifest(WIKIPEDIA_DIR):
        counts[row.source] = counts.get(row.source, 0) + 1
    assert counts == per_file


def test_dataset_shape() -> None:
    rows = [r for r in load_manifest(WIKIPEDIA_DIR) if r.excluded is None]
    samples = list(wikipedia_dataset())
    assert [s.id for s in samples] == [r.id for r in rows]
    for sample in samples:
        assert isinstance(sample.input, str)
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source", "decl_name"}


def test_sketches_are_plain_lean_with_one_target() -> None:
    for sample in wikipedia_dataset():
        assert isinstance(sample.input, str)
        code = strip_comments(sample.input)
        assert not re.search(r"^\s*(module|public|@\[expose\])", code, re.MULTILINE), sample.id
        assert not re.search(r"^import FormalConjectures\.", code, re.MULTILINE), sample.id
        assert "answer(" not in code, sample.id
        assert "@[category" not in code, sample.id
        tail = DISPROOF_PREAMBLES.get(str(sample.id), "") + disproof_declaration(str(sample.id))
        assert sample.input.rstrip().endswith(tail), sample.id


def test_task_builds() -> None:
    task = apn_wikipedia(sandbox_backend="docker")
    assert len(task.dataset) == len(
        [r for r in load_manifest(WIKIPEDIA_DIR) if r.excluded is None]
    )
