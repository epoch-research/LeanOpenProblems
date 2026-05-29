"""Tests for sketch dataset construction."""

from __future__ import annotations

from apn.dataset import bundled_dataset, infer_target_declarations, sketch_sample


def test_infer_target_declarations() -> None:
    text = "import Mathlib\ntheorem apn_add_comm (a b : Nat) : a + b = b + a := by\n  sorry\n"
    assert infer_target_declarations(text) == ["apn_add_comm"]


def test_infer_handles_lemma_and_attributes() -> None:
    text = "@[simp]\nlemma foo : True := trivial\n"
    assert infer_target_declarations(text) == ["foo"]


def test_sketch_sample_records_metadata() -> None:
    text = "theorem bar : True := by\n  sorry\n"
    sample = sketch_sample(text, "bar")
    assert sample.input == text
    assert sample.metadata is not None
    assert sample.metadata["target_declarations"] == ["bar"]
    assert sample.metadata["sketch"] == text


def test_bundled_dataset_nonempty_and_has_sorry() -> None:
    dataset = bundled_dataset()
    assert len(dataset) >= 1
    for sample in dataset:
        assert isinstance(sample.input, str)
        assert "sorry" in sample.input
        assert sample.metadata is not None
        assert sample.metadata["target_declarations"]
