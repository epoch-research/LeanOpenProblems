"""Tests for the proof-sketch text model."""

from __future__ import annotations

import pytest

from apn.sketch import (
    EvolveKind,
    ProofSketch,
    SearchReplaceError,
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


def test_search_replace_inside_block() -> None:
    sketch = ProofSketch(SAMPLE)
    updated = sketch.apply_search_replace("  sorry\n", "  simp\n")
    assert "simp" in updated.text
    assert not updated.contains_sorry()
    # The frozen skeleton is unchanged: only editable content differs.
    assert sketch.skeleton() == updated.skeleton()


def test_search_replace_inside_value() -> None:
    sketch = ProofSketch(SAMPLE)
    updated = sketch.apply_search_replace("  1\n", "  42\n")
    assert "42" in updated.text


def test_search_replace_outside_region_rejected() -> None:
    sketch = ProofSketch(SAMPLE)
    with pytest.raises(SearchReplaceError, match="outside the editable regions"):
        sketch.apply_search_replace("n + 0 = n", "n = n")


def test_search_replace_not_found() -> None:
    sketch = ProofSketch(SAMPLE)
    with pytest.raises(SearchReplaceError, match="not found"):
        sketch.apply_search_replace("nonexistent text", "x")


def test_search_replace_ambiguous() -> None:
    code = "-- EVOLVE-BLOCK-START\nfoo\nfoo\n-- EVOLVE-BLOCK-END\n"
    sketch = ProofSketch(code)
    with pytest.raises(SearchReplaceError, match="more than one location"):
        sketch.apply_search_replace("foo\n", "bar\n")


def test_search_replace_empty() -> None:
    with pytest.raises(SearchReplaceError, match="must not be empty"):
        ProofSketch(SAMPLE).apply_search_replace("", "x")


def test_search_replace_spanning_marker_rejected() -> None:
    # A search that straddles the END marker is not fully inside the region.
    sketch = ProofSketch(SAMPLE)
    with pytest.raises(SearchReplaceError, match="outside the editable regions"):
        sketch.apply_search_replace("  sorry\n-- EVOLVE-BLOCK-END", "done")


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
