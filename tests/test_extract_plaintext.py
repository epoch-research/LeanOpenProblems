"""Tests for scripts/extract_plaintext.py's APN-specific extraction helpers.

The solver records the agent's final ``Submission/`` subtree as a nested tree on
``sample.metadata["submission_contents"]``; ``_write_sample_workspace`` walks
it back to disk under ``<sample_dir>/Submission/``. The transcript formatter
also requires the current claim-bearing ``submit_proof`` call shape. None of
these checks needs an Inspect log or Lean toolchain.
"""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
from typing import cast

import pytest
from inspect_ai.log import EvalSample
from inspect_ai.model import ChatMessage, ChatMessageAssistant
from inspect_ai.tool import ToolCall

from scripts.extract_plaintext import (
    _validate_submit_proof_calls,
    _write_sample_workspace,
    format_tool_call,
)


def _sample(tree: object) -> EvalSample:
    # _write_sample_workspace only touches sample.metadata.
    return cast(EvalSample, SimpleNamespace(metadata={"submission_contents": tree}))


def _submit_call(arguments: dict[str, object]) -> ToolCall:
    return ToolCall(
        id="submit-call",
        function="submit_proof",
        arguments=arguments,
    )


@pytest.mark.parametrize("claim", ["proof", "disproof"])
def test_submit_proof_transcript_preserves_claim(claim: str) -> None:
    assert format_tool_call(_submit_call({"claim": claim})) == (
        f'>>> submit_proof(claim="{claim}")'
    )


@pytest.mark.parametrize(
    "arguments",
    [
        {},
        {"claim": "counterexample"},
        {"claim": "proof", "legacy": True},
    ],
)
def test_submit_proof_transcript_rejects_legacy_shape(
    arguments: dict[str, object],
) -> None:
    with pytest.raises(ValueError, match="must have exactly one claim argument"):
        format_tool_call(_submit_call(arguments))


def test_compaction_only_extraction_also_rejects_legacy_submit() -> None:
    messages: list[ChatMessage] = [
        ChatMessageAssistant(content="", tool_calls=[_submit_call({})]),
    ]
    with pytest.raises(ValueError, match="must have exactly one claim argument"):
        _validate_submit_proof_calls(messages)


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
