"""Tests for the OEIS dataset loader."""

from __future__ import annotations

import pytest

from apn.dataset import (
    available_subsets,
    load_subset,
    oeis_dataset,
    oeis_id_from_filename,
    parse_oeis_mapping,
    strip_license_header,
)

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


def test_strip_license_header_on_real_dataset_file() -> None:
    metadata = oeis_dataset(names=["oeis_268597_conjecture_0"])[0].metadata
    assert metadata is not None
    sketch = metadata["sketch"]
    stripped = strip_license_header(sketch)
    assert "Copyright" in sketch  # the banner is present in the source
    assert "Copyright" not in stripped
    assert stripped.startswith("import FormalConjectures.Util.ProblemImports")
    assert "theorem oeis_268597_conjecture_0" in stripped


def test_oeis_id_from_filename() -> None:
    assert oeis_id_from_filename("268597_aacea533.lean") == "A268597"
    assert oeis_id_from_filename("7406_a8289e8e.lean") == "A007406"
    assert oeis_id_from_filename("not_a_number.lean") is None


def test_parse_oeis_mapping_single_and_multi_file() -> None:
    text = (
        "oeis_268597_conjecture_0 268597_aacea533.lean\n"
        "A230241_conjecture 230241_a4de9e9f.lean 230241_f18255a1.lean\n"
        "\n"  # blank line ignored
    )
    entries = parse_oeis_mapping(text)
    assert entries == [
        ("oeis_268597_conjecture_0", ["268597_aacea533.lean"]),
        ("A230241_conjecture", ["230241_a4de9e9f.lean", "230241_f18255a1.lean"]),
    ]


def test_oeis_dataset_loads_full_set() -> None:
    ds = oeis_dataset()
    # 492 conjectures (the paper's OEIS evaluation set).
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
    assert sample.metadata["target_declarations"] == ["oeis_268597_conjecture_0"]
    # The whole file is the sketch and the input; it imports the FC library.
    assert "import FormalConjectures.Util.ProblemImports" in sample.metadata["sketch"]
    assert sample.input == sample.metadata["sketch"]


def test_oeis_dataset_names_filter_unknown() -> None:
    assert len(oeis_dataset(names=["does_not_exist"])) == 0


def test_available_subsets_ships_proved38_and_random40() -> None:
    assert {"proved38", "random40"} <= set(available_subsets())


def test_load_subset_sizes_and_disjoint() -> None:
    proved = load_subset("proved38")
    random40 = load_subset("random40")
    assert len(proved) == 38
    assert len(random40) == 40
    # No duplicate names within a subset.
    assert len(set(proved)) == 38
    assert len(set(random40)) == 40
    # random40 is sampled from the complement of proved38 -- disjoint.
    assert set(proved).isdisjoint(random40)


def test_load_subset_strips_comments_and_resolves_to_real_conjectures() -> None:
    names = load_subset("proved38")
    assert all(not n.startswith("#") for n in names)
    # Every name in the subset resolves to a real conjecture in the dataset.
    assert len(oeis_dataset(names=names)) == len(names)


def test_load_subset_unknown_raises() -> None:
    with pytest.raises(ValueError, match="Unknown OEIS subset"):
        load_subset("does_not_exist")
