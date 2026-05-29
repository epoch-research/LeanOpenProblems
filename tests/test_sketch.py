"""Tests for the proof-sketch text model."""

from __future__ import annotations

import pytest

from apn.sketch import (
    EvolveKind,
    ProofSketch,
    SketchParseError,
    strip_comments,
)

SAMPLE = """\
import Mathlib

theorem foo (n : Nat) : n + 0 = n := by
-- EVOLVE-BLOCK-START
  sorry
-- EVOLVE-BLOCK-END

def myParam : Nat :=
-- EVOLVE-VALUE-START
  1
-- EVOLVE-VALUE-END
"""


def test_parse_regions() -> None:
    sketch = ProofSketch(SAMPLE)
    regions = sketch.regions
    assert [r.kind for r in regions] == [EvolveKind.BLOCK, EvolveKind.VALUE]
    block, value = regions
    assert SAMPLE[block.content_start : block.content_end] == "  sorry\n"
    assert SAMPLE[value.content_start : value.content_end] == "  1\n"


def test_contains_sorry_true() -> None:
    assert ProofSketch(SAMPLE).contains_sorry()


def test_contains_sorry_ignores_comments() -> None:
    code = """\
-- EVOLVE-BLOCK-START
  -- I tried to sorry this goal but found a real proof.
  rfl
-- EVOLVE-BLOCK-END
"""
    assert not ProofSketch(code).contains_sorry()


def test_contains_sorry_ignores_block_comments() -> None:
    code = "/- sorry appears here /- nested -/ still comment -/\nrfl\n"
    assert not ProofSketch(code).contains_sorry()


def test_does_not_match_sorry_ax() -> None:
    code = "-- EVOLVE-BLOCK-START\n  exact sorryAx _\n-- EVOLVE-BLOCK-END\n"
    assert not ProofSketch(code).contains_sorry()


def test_skeleton_blanks_editable_content() -> None:
    sketch = ProofSketch(SAMPLE)
    skeleton = sketch.skeleton()
    assert "sorry" not in skeleton
    assert "theorem foo (n : Nat) : n + 0 = n := by" in skeleton


def test_unbalanced_markers_raise() -> None:
    with pytest.raises(SketchParseError, match="missing its END"):
        _ = ProofSketch("-- EVOLVE-BLOCK-START\nx\n").regions


def test_interleaved_markers_raise() -> None:
    code = "-- EVOLVE-BLOCK-START\n-- EVOLVE-VALUE-START\nx\n-- EVOLVE-VALUE-END\n-- EVOLVE-BLOCK-END\n"
    with pytest.raises(SketchParseError, match="still open"):
        _ = ProofSketch(code).regions


def test_strip_comments_preserves_string_literals() -> None:
    code = 'def s := "not -- a comment"\n'
    assert "not -- a comment" in strip_comments(code)
