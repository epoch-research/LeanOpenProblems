"""Tests for the Erdős-autoformalized dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, only the target + its dependency decls + derived disproof
surviving, and the target/disproof statements having their certified meanings
-- are enforced authoritatively, in a container, by
``tests/test_erdos_autoformalized_isolation.py``. This module checks what can
be checked cheaply on every run: the manifest census (every research-category
statement of the 18 vendored files from our own autoformalization run -- see
the dataset's ``NOTICE.md``), the dataset/sample shape, and textual invariants
of the shipped sketches.
"""

from __future__ import annotations

import re

import pytest

from apn.dataset import (
    ERDOS_AUTOFORMALIZED_DIR,
    erdos_autoformalized_dataset,
    load_manifest,
    load_subset,
)
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration

_SORRY_RE = re.compile(r"\bsorry\b")
# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[⦃]+)")

# The universe: one member per @[category research ...] theorem in the 18
# vendored files. 713 and 1206 state two-part problems, hence 20 members.
EXPECTED_IDS = {
    "Erdos86.erdos_86",
    "Erdos104.erdos_104",
    "Erdos181.erdos_181",
    "Erdos322.erdos_322",
    "Erdos431.erdos_431",
    "Erdos478.erdos_478",
    "Erdos548.erdos_548",
    "Erdos571.erdos_571",
    "Erdos583.erdos_583",
    "Erdos713.erdos_713.parts.i",
    "Erdos713.erdos_713.parts.ii",
    "Erdos714.erdos_714",
    "Erdos773.erdos_773",
    "Erdos970.erdos_970",
    "Erdos1020.erdos_1020",
    "Erdos1083.erdos_1083",
    "Erdos1159.erdos_1159",
    "Erdos1206.erdos_1206.parts.i",
    "Erdos1206.erdos_1206.parts.ii",
    "Erdos1207.erdos_1207",
}


def test_manifest_census() -> None:
    rows = load_manifest(ERDOS_AUTOFORMALIZED_DIR)
    assert {r.id for r in rows} == EXPECTED_IDS
    assert all(r.excluded is None for r in rows)
    assert {r.extra["erdos_number"] for r in rows} == {
        86,
        104,
        181,
        322,
        431,
        478,
        548,
        571,
        583,
        713,
        714,
        773,
        970,
        1020,
        1083,
        1159,
        1206,
        1207,
    }


def test_bloom_selection_subset() -> None:
    # Thomas Bloom's verdicts (2026-08-26), apn_erdos_autoformalized's default
    # subset: Problem 1206 is represented by part i alone, 1207 is dropped
    # from the benchmark entirely, and 713 stays split into its two parts.
    ids = load_subset(ERDOS_AUTOFORMALIZED_DIR, "bloom_selection")
    assert len(ids) == 18
    assert set(ids) == EXPECTED_IDS - {
        "Erdos1206.erdos_1206.parts.ii",
        "Erdos1207.erdos_1207",
    }
    assert len(erdos_autoformalized_dataset(names=ids)) == 18


def test_manifest_row_shape() -> None:
    for row in load_manifest(ERDOS_AUTOFORMALIZED_DIR):
        assert (ERDOS_AUTOFORMALIZED_DIR / row.source).is_file(), row.id
        assert row.source == f"Sources/{row.extra['erdos_number']}.lean", row.id
        assert row.id.startswith(f"Erdos{row.extra['erdos_number']}."), row.id
        # Everything was research-open at vendoring; the run targeted problems
        # absent from formal-conjectures precisely because they are open.
        assert row.extra["category"] == "research open", row.id
        assert row.statement is None, row.id
        assert (ERDOS_AUTOFORMALIZED_DIR / row.statement_path).is_file(), row.id


def test_spec_files_match_manifest_exactly() -> None:
    rows = load_manifest(ERDOS_AUTOFORMALIZED_DIR)
    expected = sorted((ERDOS_AUTOFORMALIZED_DIR / r.statement_path).name for r in rows)
    on_disk = sorted(
        p.name for p in (ERDOS_AUTOFORMALIZED_DIR / "Isolated").glob("*.lean")
    )
    assert on_disk == expected


def test_dataset_loads_all_samples() -> None:
    ds = erdos_autoformalized_dataset()
    assert len(ds) == 20
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


def test_dataset_sample_shape() -> None:
    ds = erdos_autoformalized_dataset(names=["Erdos104.erdos_104"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "Erdos104.erdos_104"
    assert sample.metadata is not None
    assert sample.metadata["source"] == "Sources/104.lean"
    assert sample.metadata["decl_name"] == "Erdos104.erdos_104"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjecturesUtil" in sketch
    assert "theorem erdos_104" in sketch


def test_category_never_reaches_sample_metadata() -> None:
    # The manifest's `category` exists for tooling; resolution status must not
    # flow to the agent-facing sample (same policy as the other datasets).
    for sample in erdos_autoformalized_dataset():
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source", "decl_name"}


def test_dataset_names_filter_unknown_raises() -> None:
    with pytest.raises(ValueError, match="unknown or excluded"):
        erdos_autoformalized_dataset(names=["does_not_exist"])


def test_sketches_have_no_answer_no_banner_no_category() -> None:
    # The vendored sources ship no `answer(...)` forms (the run's
    # `answer(sorry) ↔` statements were rewritten upstream of this repo -- see
    # NOTICE.md), and isolation drops the `@[category ...]` catalogue lists.
    for sample in erdos_autoformalized_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        assert "answer(" not in strip_comments(sketch), sample.id
        assert "Copyright" not in sketch, sample.id
        assert "@[category" not in sketch, sample.id
        assert sketch.startswith("import "), sample.id


def test_sketches_have_no_example_commands() -> None:
    # Anonymous `example` sanity checks would be re-run by the scorer inside
    # the trusted target compile on every score call. None exist upstream;
    # keep the guard so a regeneration can never leak one in.
    for sample in erdos_autoformalized_dataset():
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly two `sorry`s: the target and its derived `.disproof`.
    for sample in erdos_autoformalized_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        assert n == 2, f"{sample.id}: {n} sorries"


def test_sketches_end_with_disproof_declaration() -> None:
    for row in load_manifest(ERDOS_AUTOFORMALIZED_DIR):
        text = (ERDOS_AUTOFORMALIZED_DIR / row.statement_path).read_text()
        assert text.rstrip().endswith(disproof_declaration(row.decl_name)), row.id


def _declares(member_id: str, text_name: str) -> bool:
    """Whether a spec's declared source-text name is ``member_id``'s -- the
    text name omits enclosing ``namespace`` components."""
    return member_id == text_name or member_id.endswith("." + text_name)


def test_no_sibling_member_survives_in_any_spec() -> None:
    # The anti-leak cut property, stated directly: no universe member may
    # survive in another member's spec (713's and 1206's part i/ii are each
    # other's siblings). Pure-Python guard over the committed files; the
    # authoritative re-extraction check lives in
    # tests/test_erdos_autoformalized_isolation.py.
    rows = load_manifest(ERDOS_AUTOFORMALIZED_DIR)
    all_ids = [r.id for r in rows]
    for row in rows:
        text = (ERDOS_AUTOFORMALIZED_DIR / row.statement_path).read_text()
        declared = _DECL_RE.findall(text)
        assert any(_declares(row.id, n) for n in declared), row.id
        for name in declared:
            if _declares(row.id, name):
                continue
            offenders = [i for i in all_ids if _declares(i, name) and i != row.id]
            assert (
                not offenders
            ), f"{row.id}: sibling universe member(s) {offenders} survived isolation"
