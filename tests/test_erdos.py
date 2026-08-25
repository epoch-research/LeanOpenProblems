"""Tests for the Erdős-universe dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, the certified per-form ``answer(...) ↔`` rewrite, only the target
+ its dependency decls surviving -- are enforced authoritatively, in a
container, by ``tests/test_erdos_isolation.py``. This module checks what can
be checked cheaply on every run: the manifest census (the paper's 350
attempted statements, no excluded rows), the ``tsoukalas_attempted`` subset,
the dataset/sample shape, and textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re
from collections import Counter

import pytest

from apn.dataset import (
    ERDOS_DIR,
    erdos_dataset,
    load_manifest,
    load_subset,
)
from scripts.erdos_isolation import SORRY_ALLOWLIST_FILES
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration

_SORRY_RE = re.compile(r"\bsorry\b")
# A top-level theorem/lemma declaration in an isolated spec (column 0;
# `protected` included -- 633.lean's kept dependency lemma is protected).
_DECL_RE = re.compile(r"(?m)^(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[⦃]+)")


def test_manifest_census() -> None:
    # The universe: the paper's canonical attempted set, one row per
    # statement, none excluded.
    rows = load_manifest(ERDOS_DIR)
    assert len(rows) == 350
    assert all(r.excluded is None for r in rows)


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
        None: 85,
        "lhs_sorry": 249,
        "lhs_true": 7,
        "lhs_false": 6,
        "rhs_sorry": 3,
    }


def test_spec_files_match_manifest_exactly() -> None:
    rows = load_manifest(ERDOS_DIR)
    expected = sorted((ERDOS_DIR / r.statement_path).name for r in rows if r.excluded is None)
    on_disk = sorted(p.name for p in (ERDOS_DIR / "Isolated").glob("*.lean"))
    assert on_disk == expected


def test_tsoukalas_attempted_subset() -> None:
    # The paper's canonical 350-statement attempted set: all ids resolve to
    # kept manifest rows, and the dataset filtered to it has exactly 350
    # samples. (The 353->350 derivation lives in the subset's description.)
    ids = load_subset(ERDOS_DIR, "tsoukalas_attempted")
    assert len(ids) == 350
    assert len(set(ids)) == 350
    assert len(erdos_dataset(names=ids)) == 350


def test_erdos_dataset_loads_all_samples() -> None:
    ds = erdos_dataset()
    assert len(ds) == 350
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


def test_erdos_dataset_sample_shape() -> None:
    ds = erdos_dataset(names=["Erdos741.erdos_741.parts.i"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "Erdos741.erdos_741.parts.i"
    assert sample.metadata is not None
    assert sample.metadata["source"] == "Sources/741.lean"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjectures.Util.ProblemImports" in sketch
    assert "theorem erdos_741.parts.i" in sketch
    # This member carries a recorded verdict upstream (`answer(False) ↔ P`)
    # and is shipped un-filled, as plain `P` -- the answer key must not leak.
    assert "answer(" not in sketch
    assert "False" not in strip_comments(sketch)


def test_verdict_material_never_reaches_sample_metadata() -> None:
    # category_at_pin and answer_form are the recorded verdict in
    # machine-readable form; they exist for tooling and must not flow to the
    # agent-facing sample.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source", "decl_name"}


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
    # "deepmind prover", not bare "deepmind": 488.lean carries a legitimate
    # implementation comment linking a google-deepmind PR (no verdict in it).
    markers = (
        "@[category", "formal_proof", "research solved",
        "deepmind prover", "prover agent", "alphaproof",
    )
    for sample in erdos_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"].lower()
        for marker in markers:
            assert marker not in sketch, (sample.id, marker)


def test_sketches_have_no_example_commands() -> None:
    # FC's anonymous `example` sanity checks are cut so the trusted target
    # compile never executes them at score time. Comment-stripped: module-doc
    # prose may start a line with the word "example" (602.lean does).
    for sample in erdos_dataset():
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly two `sorry`s per sketch -- the target's proof and the appended
    # `.disproof` declaration's -- except in the allowlisted files, where a
    # kept definition depends on a sorry'd helper theorem (those samples
    # implicitly require proving it too).
    for sample in erdos_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        if sample.metadata["source"].removeprefix("Sources/") in SORRY_ALLOWLIST_FILES:
            assert n in (2, 3), f"{sample.id}: {n} sorries"
        else:
            assert n == 2, f"{sample.id}: {n} sorries"


# Universe members that legitimately survive in *sibling* specs: kept
# definitions depend on them (697's `def δ := (density_exists m α).choose`;
# 961's `def f := Nat.find (well_defined k hk)`, whose proof uses the
# Sylvester-Schur statement). Dependency-closure survivors, not cut leaks;
# keep in sync with generation output (a stable property of the data).
_DEPENDENCY_KEPT_MEMBERS = {
    "Erdos697.density_exists",
    "Erdos961.erdos_961.variants.well_defined",
    "Erdos961.erdos_961.sylvester_schur",
}


def _declares(member_id: str, text_name: str) -> bool:
    """Whether a spec's declared source-text name is ``member_id``'s -- the
    text name omits enclosing ``namespace`` components (matches_name
    semantics)."""
    return member_id == text_name or member_id.endswith("." + text_name)


def test_sketches_end_with_disproof_declaration() -> None:
    # Every spec's final declaration is the derived `.disproof` line for its
    # target's fully-qualified name (comparator-migration-plan.md §4); the
    # container-side certifier in tests/test_erdos_isolation.py proves its
    # elaborated type is the negation.
    for row in load_manifest(ERDOS_DIR):
        if row.excluded is not None:
            continue
        text = (ERDOS_DIR / row.statement_path).read_text()
        assert text.rstrip().endswith(disproof_declaration(row.decl_name)), row.id


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
