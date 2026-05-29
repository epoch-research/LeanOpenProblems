"""Tests for the OEIS dataset loader."""

from __future__ import annotations

from apn.dataset import (
    oeis_dataset,
    oeis_id_from_filename,
    parse_oeis_mapping,
)


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
