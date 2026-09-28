"""Tests for the Jacobian-conjecture dataset loader and its prompt (pure
Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` spec are enforced
authoritatively, in a container, by ``tests/test_jacobian_isolation.py``.
"""

from __future__ import annotations

import re

import pytest

from apn.dataset import JACOBIAN_DIR, jacobian_dataset, load_manifest
from apn.prompts import JacobianGoal, jacobian_prompt, user_prompt
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration

ID = "JacobianConjecture.jacobian_conjecture"

_SORRY_RE = re.compile(r"\bsorry\b")
_DECL_RE = re.compile(r"(?m)^(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[⦃]+)")


def test_manifest_census() -> None:
    rows = load_manifest(JACOBIAN_DIR)
    assert [(r.id, r.source) for r in rows] == [(ID, "Sources/JacobianConjecture.lean")]
    assert rows[0].excluded is None
    assert rows[0].statement is None


def test_dataset_sample_shape() -> None:
    ds = jacobian_dataset()
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == ID
    assert sample.metadata is not None
    assert set(sample.metadata) == {"sketch", "source", "decl_name"}
    assert sample.metadata["decl_name"] == ID
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert sketch.startswith("import FormalConjecturesUtil")
    assert "@[category" not in sketch
    assert "answer(" not in strip_comments(sketch)


def test_sketch_declarations() -> None:
    text = (JACOBIAN_DIR / f"Isolated/{ID}.lean").read_text()
    stripped = strip_comments(text)
    assert len(_SORRY_RE.findall(stripped)) == 2
    assert sorted(_DECL_RE.findall(stripped)) == sorted(
        ["jacobian_conjecture", f"{ID}.disproof"]
    )
    assert text.rstrip().endswith(disproof_declaration(ID))


@pytest.mark.parametrize("goal", ["resolve", "counterexample"])
def test_prompt_coordination_section_only_for_deep_agent(goal: JacobianGoal) -> None:
    deep = jacobian_prompt("deep", goal)
    react = jacobian_prompt("react", goal)
    assert "Search and coordination requirements" in deep
    assert "`agent` tool" in deep
    assert "Search and coordination requirements" not in react
    assert "`agent` tool" not in react
    for text in (deep, react):
        assert "Codex" not in text and "multiagent" not in text


def test_resolve_prompt_allows_either_outcome() -> None:
    for agent_type in ("deep", "react"):
        text = jacobian_prompt(agent_type, "resolve")
        assert "Resolve the Jacobian Conjecture completely" in text
        assert "complete affirmative proof" in text
        assert 'claim="disproof"' not in text


def test_counterexample_prompt_requires_disproof() -> None:
    for agent_type in ("deep", "react"):
        text = jacobian_prompt(agent_type, "counterexample")
        assert "Disprove the Jacobian Conjecture by an explicit counterexample" in text
        assert 'submitted with `claim="disproof"`' in text
        assert "A proof of the conjecture theorem does not count" in text
        assert "Resolve the Jacobian Conjecture completely" not in text
        assert "affirmative proof" not in text
        assert "proof and disproof routes" not in text


def test_problem_prompt_leads_user_prompt() -> None:
    problem = jacobian_prompt("deep", "counterexample")
    prompt = user_prompt("Submission/Spec.lean", None, False, "FormalConjecturesUtil", problem)
    assert prompt.startswith(problem)
    assert "Settle the conjecture in the Lean file" in prompt
