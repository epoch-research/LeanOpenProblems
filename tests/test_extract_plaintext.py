"""Tests for scripts/extract_plaintext.py's workspace materialization.

The solver records the agent's final ``Submission/`` subtree as a nested tree on
``sample.metadata["submission_contents"]``; ``_write_sample_workspace`` walks
it back to disk under ``<sample_dir>/Submission/``. These cover that round-trip
(no Inspect log / Lean toolchain needed -- the function only reads metadata).
"""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
from typing import cast

from inspect_ai.log import EvalSample

from scripts.extract_plaintext import _write_sample_workspace


def _sample(tree: object) -> EvalSample:
    # _write_sample_workspace only touches sample.metadata.
    return cast(EvalSample, SimpleNamespace(metadata={"submission_contents": tree}))


def test_writes_nested_tree_to_submission_dir(tmp_path: Path) -> None:
    tree = {
        "Spec.lean": "entry contents",
        "Helpers": {"Parity.lean": "helper contents"},
    }
    n = _write_sample_workspace(_sample(tree), tmp_path)
    assert n == 2
    assert (tmp_path / "Submission" / "Spec.lean").read_text() == "entry contents"
    assert (
        tmp_path / "Submission" / "Helpers" / "Parity.lean"
    ).read_text() == "helper contents"


def test_no_workspace_metadata_writes_nothing(tmp_path: Path) -> None:
    sample = cast(EvalSample, SimpleNamespace(metadata={}))
    assert _write_sample_workspace(sample, tmp_path) == 0
    assert not (tmp_path / "Submission").exists()


def test_empty_tree_writes_nothing(tmp_path: Path) -> None:
    assert _write_sample_workspace(_sample({}), tmp_path) == 0
    assert not (tmp_path / "Submission").exists()


def test_none_metadata_writes_nothing(tmp_path: Path) -> None:
    sample = cast(EvalSample, SimpleNamespace(metadata=None))
    assert _write_sample_workspace(sample, tmp_path) == 0
