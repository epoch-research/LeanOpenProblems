"""Tests for the OEIS dataset loader."""

from __future__ import annotations

import re

import pytest

from apn.dataset import (
    OEIS_DIR,
    available_subsets,
    load_manifest,
    load_subset,
    oeis_dataset,
    strip_license_header,
)

# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:theorem|lemma)\b")

_LICENSE = (
    "/-\n"
    "Copyright 2026 The Formal Conjectures Authors.\n"
    "Licensed under the Apache License, Version 2.0 (the \"License\");\n"
    "-/\n"
)
_BODY = "import FormalConjectures.Util.ProblemImports\n\ntheorem t : True := by sorry\n"


def test_strip_license_header_removes_banner() -> None:
    assert strip_license_header(_LICENSE + "\n" + _BODY) == _BODY


def test_strip_license_header_noop_without_banner() -> None:
    # No leading comment at all -- returned unchanged.
    assert strip_license_header(_BODY) == _BODY


def test_strip_license_header_keeps_doc_comment() -> None:
    # A `/--` doc comment is content, not a license banner -- never stripped,
    # even though it would match `/-`.
    doc = "/-- A268597: smallest x. -/\nnoncomputable def f := 0\n"
    assert strip_license_header(doc) == doc


def test_strip_license_header_keeps_non_copyright_block() -> None:
    other = "/-\nJust a note, no license here.\n-/\nimport X\n"
    assert strip_license_header(other) == other


def test_strip_license_header_leaves_unterminated_comment() -> None:
    broken = "/-\nCopyright but never closed\nimport X\n"
    assert strip_license_header(broken) == broken


def test_strip_license_header_handles_nested_block() -> None:
    nested = "/-\nCopyright /- nested -/ still header\n-/\nimport X\n"
    assert strip_license_header(nested) == "import X\n"


def test_dataset_sketch_has_license_banner_stripped() -> None:
    # The dataset strips the copyright banner at the source, so the sketch the
    # agent writes and the scorer compiles -- and the log UI shows -- starts at
    # the first real line.
    sample = oeis_dataset(names=["oeis_268597_conjecture_0"])[0]
    assert sample.metadata is not None
    sketch = sample.metadata["sketch"]
    assert "Copyright" not in sketch
    assert sketch.startswith("import FormalConjectures.Util.ProblemImports")
    assert "theorem oeis_268597_conjecture_0" in sketch


def test_manifest_census() -> None:
    # 492 conjectures (the paper's OEIS evaluation set), none excluded, every
    # row pointing at a vendored source and carrying its A-number.
    rows = load_manifest(OEIS_DIR)
    assert len(rows) == 492
    assert all(r.excluded is None for r in rows)
    for row in rows:
        assert (OEIS_DIR / row.source).is_file(), row.id
        assert re.fullmatch(r"A\d{6}", row.extra["oeis_id"]), row.id
        assert (OEIS_DIR / row.statement_path).is_file(), row.id


def test_manifest_multi_file_conjectures() -> None:
    # 3 conjectures map to more than one upstream formalization file; the
    # manifest records the unused ones so the solver can warn at run time.
    rows = [r for r in load_manifest(OEIS_DIR) if "other_sources" in r.extra]
    assert len(rows) == 3
    for row in rows:
        for src in row.extra["other_sources"]:
            assert (OEIS_DIR / src).is_file(), row.id


def test_oeis_dataset_loads_full_set() -> None:
    ds = oeis_dataset()
    assert len(ds) == 492
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)  # ids unique


def test_oeis_dataset_sample_shape() -> None:
    ds = oeis_dataset(names=["oeis_268597_conjecture_0"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "oeis_268597_conjecture_0"
    assert sample.metadata is not None
    assert sample.metadata["oeis_id"] == "A268597"
    assert sample.metadata["source"].startswith("Sources/268597_")
    # The isolated spec is the sketch and the input; it imports the FC library.
    sketch = sample.metadata["sketch"]
    assert "import FormalConjectures.Util.ProblemImports" in sketch
    assert sample.input == sketch
    # It contains exactly the one target theorem -- no sibling conjectures or
    # test lemmas (those were removed during isolation).
    assert "theorem oeis_268597_conjecture_0" in sketch
    assert len(_DECL_RE.findall(sketch)) == 1


def test_oeis_dataset_names_filter_unknown_raises() -> None:
    with pytest.raises(ValueError, match="unknown or excluded"):
        oeis_dataset(names=["does_not_exist"])


def test_available_subsets() -> None:
    assert {"lite", "tsoukalas_proved_38", "tsoukalas_unproved_40"} <= set(
        available_subsets(OEIS_DIR)
    )


def test_load_subset_sizes_and_disjoint() -> None:
    proved = load_subset(OEIS_DIR, "tsoukalas_proved_38")
    unproved = load_subset(OEIS_DIR, "tsoukalas_unproved_40")
    assert len(proved) == 38
    assert len(unproved) == 40
    # tsoukalas_unproved_40 is sampled from the complement of tsoukalas_proved_38 -- disjoint.
    assert set(proved).isdisjoint(unproved)
    # load_subset already validates every id against the manifest; the dataset
    # filtered to a subset has exactly its size.
    assert len(oeis_dataset(names=proved)) == 38


def test_lite_subset_reproducible_draw() -> None:
    # lite is a seeded random draw over the sorted manifest ids; the committed
    # file must match the draw exactly (results comparability depends on it).
    import random

    universe = sorted(r.id for r in load_manifest(OEIS_DIR))
    expected = sorted(random.Random(42).sample(universe, 100))
    assert load_subset(OEIS_DIR, "lite") == expected


def test_load_subset_unknown_raises() -> None:
    with pytest.raises(ValueError, match="Unknown subset"):
        load_subset(OEIS_DIR, "does_not_exist")


# Isolated specs that legitimately retain a *proved* helper lemma because a kept
# definition depends on it (e.g. a nonemptiness proof passed to `Finset.min'`),
# so they carry more than one top-level theorem/lemma. Such lemmas are dependency
# closure of the spec's definitions, not sibling conjectures; the conjecture to
# settle is still the single target. Keep this list in sync with
# scripts/generate_oeis_isolated.py output (it is a stable property of the data).
_DEPENDENCY_LEMMA_SPECS = {"oeis_a374265_conjecture_1_boundedness"}


def test_every_conjecture_has_isolated_single_theorem_spec() -> None:
    # Pure-Python structural guard over the committed, Lean-authored Isolated/
    # files (CI has no Lean toolchain). Every manifest row must have an
    # isolated spec that imports the FC library, declares its own target
    # theorem, and -- save for the few dependency-lemma specs above -- has exactly
    # one top-level theorem/lemma (one conjecture per spec, siblings and test
    # lemmas removed). The deeper Lean guarantees (clean elaboration, statement
    # preserved, only the target + its dependency lemmas survive) are enforced
    # authoritatively, in a container, by tests/test_oeis_isolation.py.
    multi_theorem: set[str] = set()
    for row in load_manifest(OEIS_DIR):
        text = (OEIS_DIR / row.statement_path).read_text()
        assert "import FormalConjectures.Util.ProblemImports" in text, row.id
        assert re.search(rf"\b(?:theorem|lemma)\s+{re.escape(row.id)}\b", text), row.id
        if len(_DECL_RE.findall(text)) != 1:
            multi_theorem.add(row.id)
    # Only the documented dependency-lemma specs may carry extra theorems; a new
    # entry here means a regenerate left a sibling/test lemma behind (or added a
    # new dependency-lemma spec to acknowledge).
    assert multi_theorem == _DEPENDENCY_LEMMA_SPECS, (
        f"unexpected multi-theorem isolated specs: {multi_theorem ^ _DEPENDENCY_LEMMA_SPECS}"
    )
