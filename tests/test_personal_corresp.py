"""Tests for the personal-correspondence dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, only the target + its dependency decls + derived disproof
surviving, and the target/disproof statements having their certified meanings
-- are enforced authoritatively, in a container, by
``tests/test_personal_corresp_isolation.py``. This module checks what can be checked
cheaply on every run: the manifest census (every research-category statement
of the vendored files -- see the dataset's ``NOTICE.md``), the
dataset/sample shape, and textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re

import pytest

from apn.dataset import PERSONAL_CORRESP_DIR, load_manifest, personal_corresp_dataset
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration

_SORRY_RE = re.compile(r"\bsorry\b")
# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[⦃]+)")

# The universe: one member per @[category research ...] theorem in the
# vendored files.
EXPECTED = {
    "FinitisticDimension.finitistic_dimension_conjecture": "Sources/FinitisticDimensionConjecture.lean",
    "Nakayama.nakayama_conjecture": "Sources/NakayamaConjecture.lean",
    "NilpotentClosure.nilpotent_mul_closed_implies_add_closed": "Sources/NilpotentClosure.lean",
}


def test_manifest_census() -> None:
    rows = load_manifest(PERSONAL_CORRESP_DIR)
    assert {r.id: r.source for r in rows} == EXPECTED
    assert all(r.excluded is None for r in rows)


def test_manifest_row_shape() -> None:
    for row in load_manifest(PERSONAL_CORRESP_DIR):
        assert (PERSONAL_CORRESP_DIR / row.source).is_file(), row.id
        # Every conjecture is open; there is nothing recorded solved.
        assert row.extra["category"] == "research open", row.id
        assert row.statement is None, row.id
        assert (PERSONAL_CORRESP_DIR / row.statement_path).is_file(), row.id


def test_spec_files_match_manifest_exactly() -> None:
    rows = load_manifest(PERSONAL_CORRESP_DIR)
    expected = sorted((PERSONAL_CORRESP_DIR / r.statement_path).name for r in rows)
    on_disk = sorted(p.name for p in (PERSONAL_CORRESP_DIR / "Isolated").glob("*.lean"))
    assert on_disk == expected


def test_dataset_loads_all_samples() -> None:
    ds = personal_corresp_dataset()
    assert len(ds) == len(EXPECTED) == 3
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


def test_dataset_sample_shape() -> None:
    ds = personal_corresp_dataset(names=["Nakayama.nakayama_conjecture"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "Nakayama.nakayama_conjecture"
    assert sample.metadata is not None
    assert sample.metadata["source"] == "Sources/NakayamaConjecture.lean"
    assert sample.metadata["decl_name"] == "Nakayama.nakayama_conjecture"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjecturesUtil" in sketch
    assert "theorem nakayama_conjecture" in sketch


def test_category_never_reaches_sample_metadata() -> None:
    # The manifest's `category` exists for tooling; resolution status must not
    # flow to the agent-facing sample (same policy as the other datasets).
    for sample in personal_corresp_dataset():
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source", "decl_name"}


def test_dataset_names_filter_unknown_raises() -> None:
    with pytest.raises(ValueError, match="unknown or excluded"):
        personal_corresp_dataset(names=["does_not_exist"])


def test_sketches_have_no_answer_no_banner_no_category() -> None:
    for sample in personal_corresp_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        assert "answer(" not in strip_comments(sketch), sample.id
        assert "Copyright" not in sketch, sample.id
        assert "@[category" not in sketch, sample.id
        assert sketch.startswith("import "), sample.id


def test_sketches_have_no_example_commands() -> None:
    for sample in personal_corresp_dataset():
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly two `sorry`s: the target and its derived `.disproof`.
    for sample in personal_corresp_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        assert n == 2, f"{sample.id}: {n} sorries"


def test_sketches_end_with_disproof_declaration() -> None:
    for row in load_manifest(PERSONAL_CORRESP_DIR):
        text = (PERSONAL_CORRESP_DIR / row.statement_path).read_text()
        assert text.rstrip().endswith(disproof_declaration(row.decl_name)), row.id


def test_only_target_and_disproof_theorems_survive() -> None:
    # The contributed API lemma (`hasFiniteFinitisticDimension_iff`) and any
    # other sibling theorem must be cut; pure-Python guard over the committed
    # files, the authoritative re-extraction check lives in
    # tests/test_personal_corresp_isolation.py.
    for row in load_manifest(PERSONAL_CORRESP_DIR):
        text = (PERSONAL_CORRESP_DIR / row.statement_path).read_text()
        declared = _DECL_RE.findall(strip_comments(text))
        short = row.id.rsplit(".", 1)[1]
        assert sorted(declared) == sorted([short, f"{row.decl_name}.disproof"]), row.id
