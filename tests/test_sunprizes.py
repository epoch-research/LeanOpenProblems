"""Tests for the Sun-prizes dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, only the target + its dependency decls surviving -- are enforced
authoritatively, in a container, by ``tests/test_sunprizes_isolation.py``.
This module checks what can be checked cheaply on every run: the manifest
census (the 8 prized conjectures, none excluded), the dataset/sample shape,
and textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re

import pytest

from apn.dataset import (
    SUNPRIZES_DIR,
    load_manifest,
    sunprizes_dataset,
)
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration

# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:theorem|lemma)\b")
_SORRY_RE = re.compile(r"\bsorry\b")


def test_manifest_census() -> None:
    # The manifest is the membership source of truth: the 8 prized Zhi-Wei Sun
    # conjectures formalized in FC at the pin, one row each, none excluded.
    rows = load_manifest(SUNPRIZES_DIR)
    assert len(rows) == 8
    assert all(r.excluded is None for r in rows)


def test_manifest_row_shape() -> None:
    for row in load_manifest(SUNPRIZES_DIR):
        assert (SUNPRIZES_DIR / row.source).is_file(), row.id
        assert (SUNPRIZES_DIR / row.statement_path).is_file(), row.id
        assert row.source == f"Sources/{row.extra['oeis_id'].removeprefix('A')}.lean", row.id
        assert row.extra["category_at_pin"] == "research open", row.id
        assert isinstance(row.extra["prize_amount"], int), row.id
        assert row.extra["prize_currency"] in ("USD", "RMB"), row.id
        assert row.extra["prize_name"], row.id


def test_manifest_prize_census() -> None:
    # The prizes as stated on Sun's homepage (see NOTICE.md); drift means the
    # transcription changed.
    prizes = {
        r.extra["oeis_id"]: (r.extra["prize_amount"], r.extra["prize_currency"])
        for r in load_manifest(SUNPRIZES_DIR)
    }
    assert prizes == {
        "A303656": (3500, "USD"),
        "A308734": (2500, "USD"),
        "A306477": (2468, "USD"),
        "A281976": (2400, "USD"),
        "A231201": (1000, "USD"),
        "A239957": (2000, "RMB"),
        "A280831": (1680, "RMB"),
        "A232174": (200, "USD"),
    }


def test_spec_files_match_manifest_exactly() -> None:
    rows = load_manifest(SUNPRIZES_DIR)
    expected = sorted(f"{r.id}.lean" for r in rows)
    on_disk = sorted(p.name for p in (SUNPRIZES_DIR / "Isolated").glob("*.lean"))
    assert on_disk == expected


def test_sunprizes_dataset_loads_all_samples() -> None:
    ds = sunprizes_dataset()
    assert len(ds) == 8
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


def test_sunprizes_dataset_sample_shape() -> None:
    ds = sunprizes_dataset(names=["OeisA303656.conjecture"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "OeisA303656.conjecture"
    assert sample.metadata is not None
    assert sample.metadata["source"] == "Sources/303656.lean"
    assert sample.metadata["oeis_id"] == "A303656"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjectures.Util.ProblemImports" in sketch
    assert "theorem conjecture" in sketch


def test_prize_fields_never_reach_sample_metadata() -> None:
    # The prize fields exist for tooling; the sample carries only the sketch,
    # source, oeis_id, and the decl_name the scorer hands to the checker.
    for sample in sunprizes_dataset():
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source", "oeis_id", "decl_name"}


def test_sunprizes_dataset_names_filter_unknown_raises() -> None:
    with pytest.raises(ValueError, match="unknown or excluded"):
        sunprizes_dataset(names=["does_not_exist"])


def test_sketches_have_no_answer_and_no_banner() -> None:
    # All 8 members are plain statements: no `answer(` anywhere in code. The
    # Apache banner is stripped at load.
    for sample in sunprizes_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        assert "answer(" not in strip_comments(sketch), sample.id
        assert "Copyright" not in sketch, sample.id
        assert sketch.startswith("import "), sample.id


def test_sketches_have_no_category_attributes() -> None:
    # FC's `@[category ..., AMS ...]` classification lists are catalogue
    # metadata, not part of the statement -- generation drops every kept
    # declaration's list whole (fc_statements.strip_category_attrs).
    for sample in sunprizes_dataset():
        assert sample.metadata is not None
        sketch = strip_comments(sample.metadata["sketch"])
        assert "@[category" not in sketch, sample.id
        assert "formal_proof" not in sketch, sample.id


def test_sketches_have_no_example_commands() -> None:
    # FC's anonymous `example` sanity checks are cut so the trusted target
    # compile never executes them at score time.
    for sample in sunprizes_dataset():
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


def test_sketches_sorry_count_and_theorem_pair() -> None:
    # Exactly two `sorry`s (the target's proof and its `.disproof`'s) and
    # exactly two theorem/lemma declarations per sketch: the target plus the
    # derived `.disproof` the sketch ends with -- every test lemma was cut,
    # and no target here has theorem-typed dependencies. The deeper Lean
    # guarantee (the disproof type certified as the negation) is enforced in
    # a container by tests/test_sunprizes_isolation.py.
    for row in load_manifest(SUNPRIZES_DIR):
        text = (SUNPRIZES_DIR / row.statement_path).read_text()
        stripped = strip_comments(text)
        assert len(_SORRY_RE.findall(stripped)) == 2, row.id
        assert len(_DECL_RE.findall(text)) == 2, row.id
        assert text.rstrip().endswith(disproof_declaration(row.decl_name)), row.id
