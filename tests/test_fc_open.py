"""Tests for the FC directory-scoped research-open dataset loaders
(``wikipedia``, ``arxiv``, ``oeis_open``) -- pure Python, no Docker.

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, the certified ``answer(...) ↔`` rewrite, only the target + its
dependency decls surviving -- are enforced authoritatively, in a container, by
``tests/test_fc_open_isolation.py``. This module checks what can be checked
cheaply on every run: the manifest census, the dataset/sample shape, and
textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re

import pytest
from inspect_ai.dataset import MemoryDataset

from apn.dataset import (
    arxiv_dataset,
    load_manifest,
    oeis_open_dataset,
    wikipedia_dataset,
)
from scripts.fc_open_isolation import DATASETS, FCOpenDataset
from scripts.fc_statements import strip_comments

_SORRY_RE = re.compile(r"\bsorry\b")

LOADERS = {
    "wikipedia": wikipedia_dataset,
    "arxiv": arxiv_dataset,
    "oeis_open": oeis_open_dataset,
}

# (total manifest rows, kept rows) per dataset; drift means the vendored
# sources or the generation pipeline changed.
CENSUS = {
    "wikipedia": (241, 222),
    "arxiv": (32, 30),
    "oeis_open": (222, 203),
}

CASES = sorted(DATASETS)


def _dataset(name: str) -> MemoryDataset:
    return LOADERS[name]()


@pytest.mark.parametrize("name", CASES)
def test_manifest_census(name: str) -> None:
    rows = load_manifest(DATASETS[name].dataset_dir)
    n_total, n_kept = CENSUS[name]
    assert len(rows) == n_total
    assert sum(1 for r in rows if r.excluded is None) == n_kept


@pytest.mark.parametrize("name", CASES)
def test_manifest_row_shape(name: str) -> None:
    cfg = DATASETS[name]
    for row in load_manifest(cfg.dataset_dir):
        assert (cfg.dataset_dir / row.source).is_file(), row.id
        if row.excluded is None:
            assert (cfg.dataset_dir / row.statement_path).is_file(), row.id
            assert row.extra["answer_form"] in (
                None, "lhs_sorry", "lhs_true", "lhs_false",
                "rhs_sorry", "rhs_true", "rhs_false",
            ), row.id
        else:
            assert "answer_form" not in row.extra, row.id


@pytest.mark.parametrize("name", CASES)
def test_spec_files_match_manifest_exactly(name: str) -> None:
    cfg = DATASETS[name]
    rows = load_manifest(cfg.dataset_dir)
    expected = sorted((cfg.dataset_dir / r.statement_path).name for r in rows if r.excluded is None)
    on_disk = sorted(p.name for p in cfg.isolated_dir.glob("*.lean"))
    assert on_disk == expected


@pytest.mark.parametrize("name", CASES)
def test_dataset_loads_all_samples(name: str) -> None:
    ds = _dataset(name)
    assert len(ds) == CENSUS[name][1]
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


@pytest.mark.parametrize("name", CASES)
def test_sample_shape_and_metadata(name: str) -> None:
    # answer_form is tooling-only and must not flow to the agent-facing sample.
    for sample in _dataset(name):
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source"}
        assert sample.input == sample.metadata["sketch"]


@pytest.mark.parametrize("name", CASES)
def test_sketches_have_no_answer_and_no_banner(name: str) -> None:
    # No `answer(` may survive in any sketch's *code* -- all statement forms
    # are rewritten to plain `P`, and the value-typed members are excluded
    # rows. The Apache banner is stripped at load.
    for sample in _dataset(name):
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        assert "answer(" not in strip_comments(sketch), sample.id
        assert "Copyright" not in sketch, sample.id
        assert sketch.startswith("import "), sample.id


@pytest.mark.parametrize("name", CASES)
def test_sketches_have_no_category_attrs(name: str) -> None:
    # FC's `@[category ...]` classification lists (which carry the
    # open/solved resolution status) are stripped from every kept declaration.
    for sample in _dataset(name):
        assert sample.metadata is not None
        assert "@[category" not in sample.metadata["sketch"], sample.id


@pytest.mark.parametrize("name", CASES)
def test_sketches_have_no_example_commands(name: str) -> None:
    # Comment-stripped: module-doc prose may start a line with "example".
    for sample in _dataset(name):
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


@pytest.mark.parametrize("name", CASES)
def test_sketches_sorry_count(name: str) -> None:
    # Exactly one `sorry` per sketch -- the target's proof -- except in the
    # allowlisted files (a kept definition depending on a sorry'd helper),
    # which may carry more.
    cfg: FCOpenDataset = DATASETS[name]
    for sample in _dataset(name):
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        if sample.metadata["source"].removeprefix("Sources/") in cfg.sorry_allowlist_files:
            assert n >= 1, f"{sample.id}: {n} sorries"
        else:
            assert n == 1, f"{sample.id}: {n} sorries"
