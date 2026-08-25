"""Tests for the Erdős-universe dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, the certified per-form ``answer(...) ↔`` rewrite, only the target
+ its dependency decls surviving -- are enforced authoritatively, in a
container, by ``tests/test_erdos_isolation.py``. This module checks what can
be checked cheaply on every run: the manifest census (every research-category
statement of the Bloom selection's 48 vendored files), the ``bloom_selection``
subset (the 47 scoreable selected statements, ``apn_erdos``'s default), the
dataset/sample shape, and textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re
from collections import Counter

import pytest

from apn.dataset import (
    ERDOS_DIR,
    SampleRow,
    erdos_dataset,
    load_manifest,
    load_subset,
)
from scripts.erdos_isolation import (
    PROVED_IN_FILE_REASON,
    SORRY_ALLOWLIST_FILES,
    VALUE_TYPED_REASON,
)
from scripts.isolation import matches_name

from scripts.fc_statements import strip_comments

_SORRY_RE = re.compile(r"\bsorry\b")
# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[⦃]+)")

# The Bloom selection (metadata/ERDOS_PROBLEM_STATEMENT_SELECTION.md): the
# selected statement's short name per problem number. 508's selection is the
# excluded value-typed HadwigerNelsonProblem, so the *scoreable* selection --
# the bloom_selection subset -- is the other 47.
SELECTED = {
    1: "erdos_1", 3: "erdos_3", 5: "erdos_5", 7: "erdos_7", 20: "erdos_20",
    23: "erdos_23", 28: "erdos_28", 30: "erdos_30", 39: "erdos_39",
    41: "erdos_41", 52: "erdos_52", 61: "erdos_61", 66: "erdos_66",
    68: "erdos_68", 74: "erdos_74", 89: "erdos_89", 97: "erdos_97",
    101: "erdos_101", 107: "erdos_107", 120: "erdos_120", 126: "erdos_126",
    128: "erdos_128", 138: "erdos_138", 172: "erdos_172", 184: "erdos_184",
    208: "erdos_208.parts.ii", 213: "erdos_213", 241: "erdos_241",
    242: "erdos_242", 324: "erdos_324", 364: "erdos_364", 371: "erdos_371",
    376: "erdos_376", 406: "erdos_406", 508: "HadwigerNelsonProblem",
    564: "erdos_564", 595: "erdos_595", 647: "erdos_647", 672: "erdos_672",
    723: "erdos_723", 812: "erdos_812.parts.i", 821: "erdos_821",
    829: "erdos_829", 952: "erdos_952", 972: "erdos_972", 975: "erdos_975",
    1003: "erdos_1003", 1057: "erdos_1057",
}


def _selected_row(rows: list[SampleRow], number: int) -> SampleRow:
    hits = [
        r for r in rows
        if r.extra["erdos_number"] == number and matches_name(r.id, SELECTED[number])
    ]
    assert len(hits) == 1, (number, [r.id for r in hits])
    return hits[0]


def test_manifest_census() -> None:
    # The universe: every research-category statement of the 48 vendored
    # files -- the selected statements plus their research variants.
    rows = load_manifest(ERDOS_DIR)
    assert len(rows) == 144
    assert {r.extra["erdos_number"] for r in rows} == set(SELECTED)
    excluded = {r.id: r.excluded for r in rows if r.excluded is not None}
    assert excluded == {
        "Erdos508.HadwigerNelsonProblem": VALUE_TYPED_REASON,
        "Erdos975.erdos_975.variants.quadratic": VALUE_TYPED_REASON,
        "Erdos647.erdos_647.variants.twenty_four": PROVED_IN_FILE_REASON,
    }


def test_manifest_row_shape() -> None:
    for row in load_manifest(ERDOS_DIR):
        assert (ERDOS_DIR / row.source).is_file(), row.id
        assert row.extra["category_at_pin"] in ("research open", "research solved"), row.id
        assert row.source == f"Sources/{row.extra['erdos_number']}.lean", row.id
        if row.excluded is None:
            assert (ERDOS_DIR / row.statement_path).is_file(), row.id
            assert row.extra["answer_form"] in (
                None, "lhs_sorry", "lhs_true", "lhs_false",
                "rhs_sorry", "rhs_true", "rhs_false",
            ), row.id
        else:
            assert "answer_form" not in row.extra, row.id


def test_manifest_answer_form_census() -> None:
    # The kept rows' answer(...)-form distribution; drift means the vendored
    # sources or the census changed. (The certified rewrite itself is
    # re-checked per member in tests/test_erdos_isolation.py.)
    forms = Counter(r.extra["answer_form"] for r in load_manifest(ERDOS_DIR) if r.excluded is None)
    assert forms == {
        None: 87,
        "lhs_sorry": 52,
        "lhs_true": 2,
    }


def test_spec_files_match_manifest_exactly() -> None:
    rows = load_manifest(ERDOS_DIR)
    expected = sorted((ERDOS_DIR / r.statement_path).name for r in rows if r.excluded is None)
    on_disk = sorted(p.name for p in (ERDOS_DIR / "Isolated").glob("*.lean"))
    assert on_disk == expected


def test_bloom_selection_subset() -> None:
    # The default subset: the 47 scoreable selected statements -- exactly one
    # per reviewed problem except 508, each `research open` at the pin.
    rows = load_manifest(ERDOS_DIR)
    ids = load_subset(ERDOS_DIR, "bloom_selection")
    assert len(ids) == 47
    assert len(set(ids)) == 47
    by_id = {r.id: r for r in rows}
    numbers = []
    for sample_id in ids:
        row = by_id[sample_id]
        assert row.excluded is None, sample_id
        assert row.extra["category_at_pin"] == "research open", sample_id
        numbers.append(row.extra["erdos_number"])
        assert matches_name(sample_id, SELECTED[row.extra["erdos_number"]]), sample_id
    assert sorted(numbers) == sorted(set(SELECTED) - {508})
    assert len(erdos_dataset(names=ids)) == 47


def test_508_ships_as_excluded_value_typed_row() -> None:
    # The selection's 48th statement: χ(ℝ²) = answer(sorry) is value-typed
    # (sorryAx in the statement type), unscoreable, and 508.lean has no other
    # `research open` statement -- so it ships as an excluded row, documented
    # rather than silently dropped.
    row = _selected_row(load_manifest(ERDOS_DIR), 508)
    assert row.id == "Erdos508.HadwigerNelsonProblem"
    assert row.excluded == VALUE_TYPED_REASON


def test_every_selected_statement_is_research_open_at_pin() -> None:
    rows = load_manifest(ERDOS_DIR)
    for number in SELECTED:
        row = _selected_row(rows, number)
        assert row.extra["category_at_pin"] == "research open", row.id


def test_erdos_dataset_loads_all_samples() -> None:
    ds = erdos_dataset()
    assert len(ds) == 141
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


def test_erdos_dataset_sample_shape() -> None:
    ds = erdos_dataset(names=["Erdos138.erdos_138.variants.difference"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "Erdos138.erdos_138.variants.difference"
    assert sample.metadata is not None
    assert sample.metadata["source"] == "Sources/138.lean"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjecturesUtil" in sketch
    assert "theorem erdos_138.variants.difference" in sketch
    # This member carries a recorded verdict upstream (`answer(True) ↔ P` plus
    # prose crediting the prover) and is shipped un-filled, as plain `P` --
    # the answer key must not leak.
    assert "answer(" not in sketch
    assert "True" not in strip_comments(sketch)


def test_verdict_material_never_reaches_sample_metadata() -> None:
    # category_at_pin and answer_form are the recorded verdict in
    # machine-readable form; they exist for tooling and must not flow to the
    # agent-facing sample.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source"}


def test_erdos_dataset_names_filter_unknown_raises() -> None:
    with pytest.raises(ValueError, match="unknown or excluded"):
        erdos_dataset(names=["does_not_exist"])


def test_sketches_have_no_answer_and_no_banner() -> None:
    # No `answer(` may survive in any sketch's *code* -- all statement forms
    # are rewritten to plain `P`, and the value-typed members are excluded
    # rows. (Kept module docs may mention `answer(sorry)` in prose -- hence
    # the comment-stripped census.) The Apache banner is stripped at load.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        assert "answer(" not in strip_comments(sketch), sample.id
        assert "Copyright" not in sketch, sample.id
        assert sketch.startswith("import "), sample.id


def test_sketches_have_no_fc_annotations() -> None:
    # FC records resolutions as a `research solved` category flip,
    # `formal_proof` URL attributes, and prose crediting the prover. Generation
    # drops every kept declaration's `@[category ...]` classification list
    # whole and removes the verdict prose
    # (scripts/erdos_isolation.py:strip_fc_annotations): the recorded answer
    # must not reach the shipped sketch in any form. None of these markers
    # legitimately occurs in problem prose.
    markers = (
        "@[category", "formal_proof", "research solved",
        "deepmind", "prover agent", "alphaproof",
    )
    for sample in erdos_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"].lower()
        for marker in markers:
            assert marker not in sketch, (sample.id, marker)


def test_sketches_have_no_example_commands() -> None:
    # FC's anonymous `example` sanity checks are cut so the trusted target
    # compile never executes them at score time. Comment-stripped: module-doc
    # prose may start a line with the word "example".
    for sample in erdos_dataset():
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly one `sorry` per sketch -- the target's proof. The allowlist (a
    # kept definition depending on a sorry'd helper theorem) is currently
    # empty; if a future pin re-adds entries, those files may carry two.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        if sample.metadata["source"].removeprefix("Sources/") in SORRY_ALLOWLIST_FILES:
            assert n in (1, 2), f"{sample.id}: {n} sorries"
        else:
            assert n == 1, f"{sample.id}: {n} sorries"


# Universe members that legitimately survive in *sibling* specs because kept
# definitions depend on them (dependency-closure survivors, not cut leaks);
# keep in sync with generation output. None in the Bloom selection.
_DEPENDENCY_KEPT_MEMBERS: set[str] = set()


def _declares(member_id: str, text_name: str) -> bool:
    """Whether a spec's declared source-text name is ``member_id``'s -- the
    text name omits enclosing ``namespace`` components (matches_name
    semantics)."""
    return member_id == text_name or member_id.endswith("." + text_name)


def test_no_sibling_member_survives_in_any_spec() -> None:
    # The anti-leak cut property, stated directly: a spec may keep dependency
    # helpers, but no *universe member* (any manifest row's statement, kept or
    # excluded) may survive in another member's spec beyond the documented
    # dependency-kept few. Pure-Python guard over the committed files; the
    # authoritative re-extraction check lives in tests/test_erdos_isolation.py.
    rows = load_manifest(ERDOS_DIR)
    all_ids = [r.id for r in rows]
    for row in rows:
        if row.excluded is not None:
            continue
        text = (ERDOS_DIR / row.statement_path).read_text()
        declared = _DECL_RE.findall(text)
        assert any(_declares(row.id, n) for n in declared), row.id
        for name in declared:
            if _declares(row.id, name):
                continue
            offenders = [
                i for i in all_ids
                if _declares(i, name) and i != row.id and i not in _DEPENDENCY_KEPT_MEMBERS
            ]
            assert not offenders, (
                f"{row.id}: sibling universe member(s) {offenders} survived isolation"
            )
