"""Tests for the FC100OpenSet1 dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, the certified ``answer(sorry) ↔`` rewrite, only the target + its
dependency decls surviving -- are enforced authoritatively, in a container, by
``tests/test_fc100_isolation.py``. This module checks what can be checked
cheaply on every run: the manifest census (100 = 86 kept + 14 excluded), the
dataset/sample shape, and textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re

import pytest

from apn.dataset import (
    FC100_DIR,
    fc100open_dataset,
    load_manifest,
    load_subset,
)
from scripts.fc100_isolation import SORRY_ALLOWLIST
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration

# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:theorem|lemma)\b")
_SORRY_RE = re.compile(r"\bsorry\b")


def test_manifest_census() -> None:
    # The manifest is the membership source of truth: exactly the paper's 100
    # frozen members, the 14 value-typed answer(sorry) ones excluded with the
    # reason inline.
    rows = load_manifest(FC100_DIR)
    assert len(rows) == 100
    kept = [r for r in rows if r.excluded is None]
    assert len(kept) == 86
    for row in rows:
        assert (FC100_DIR / row.source).is_file(), row.id
        if row.excluded is None:
            assert (FC100_DIR / row.statement_path).is_file(), row.id
        else:
            assert row.excluded.startswith("value-typed answer(sorry)"), row.id


def test_spec_files_match_manifest_exactly() -> None:
    rows = load_manifest(FC100_DIR)
    expected = sorted(f"{r.id}.lean" for r in rows if r.excluded is None)
    on_disk = sorted(p.name for p in (FC100_DIR / "Isolated").glob("*.lean"))
    assert on_disk == expected


def test_fc100_dataset_loads_full_set() -> None:
    ds = fc100open_dataset()
    assert len(ds) == 86
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


def test_fc100_dataset_sample_shape() -> None:
    ds = fc100open_dataset(names=["Erdos200.erdos_200"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "Erdos200.erdos_200"
    assert sample.metadata is not None
    assert sample.metadata["source"] == "Sources/ErdosProblems/200.lean"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjectures.Util.ProblemImports" in sketch
    assert "theorem erdos_200" in sketch
    # This member was stated `answer(sorry) ↔ P` upstream and is shipped
    # rewritten to plain `P`.
    assert "answer(" not in sketch


def test_fc100_dataset_names_filter_unknown_raises() -> None:
    with pytest.raises(ValueError, match="unknown or excluded"):
        fc100open_dataset(names=["does_not_exist"])


def test_excluded_members_do_not_load() -> None:
    # Excluded rows are census entries, not runnable samples.
    with pytest.raises(ValueError, match="unknown or excluded"):
        fc100open_dataset(names=["Green24.green_24"])


def test_sketches_have_no_answer_and_no_banner() -> None:
    # No `answer(` may survive in any sketch's *code* -- the rewrite removed the
    # propositional uses and the value-typed ones are excluded. (Kept module
    # docs may mention `answer(sorry)` in prose -- ErdosProblems/539.lean does --
    # hence the comment-stripped census.) The Apache banner is stripped at load.
    for sample in fc100open_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        assert "answer(" not in strip_comments(sketch), sample.id
        assert "Copyright" not in sketch, sample.id
        assert sketch.startswith("import "), sample.id


def test_sketches_have_no_category_attributes() -> None:
    # FC's `@[category ..., AMS ...]` classification lists are catalogue
    # metadata, not part of the statement, and their category/formal_proof
    # fields are where FC records resolution status -- generation drops every
    # kept declaration's list whole (fc_statements.strip_category_attrs).
    # Semantic attributes (Selfridge's `@[mk_iff]`) are kept. Comment-stripped,
    # because prose may legitimately *quote* the attribute
    # (OpenQuantumProblems/23's module doc) or mention `research solved` about
    # cut sibling statements (MonochromaticQuantumGraph).
    for sample in fc100open_dataset():
        assert sample.metadata is not None
        sketch = strip_comments(sample.metadata["sketch"])
        assert "@[category" not in sketch, sample.id
        assert "formal_proof" not in sketch, sample.id


def test_sketches_have_no_example_commands() -> None:
    # FC's anonymous `example` sanity checks (GraphConjecture316/327 run
    # `decide +native`) are cut so the trusted target compile never executes
    # them at score time.
    for sample in fc100open_dataset():
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly two `sorry`s per sketch -- the target's proof and the appended
    # `.disproof` declaration's -- except the allowlisted EllipticCurveRank
    # spec, which also keeps FC's own sorry'd Mordell-Weil instance (that
    # sample implicitly requires proving it too).
    for sample in fc100open_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        expected = 3 if sample.id in SORRY_ALLOWLIST else 2
        assert n == expected, f"{sample.id}: {n} sorries"


# Isolated specs that legitimately retain extra *proved* theorem/lemma commands
# because a kept declaration depends on them: EllipticCurveRank's kept
# `IsElliptic` instances prove `isUnit` via `rw [Δ_elkiesKlagsbrun29]` /
# `rw [Δ_elkies28]`, pulling both Δ lemmas into the dependency closure. Keep in
# sync with scripts/generate_fc100_isolated.py output (a stable property of the
# data).
_DEPENDENCY_LEMMA_SPECS = {
    "EllipticCurveRank.RatEllipticCurve.twentyone_le_rank_height_count_asymptotic": 3,
}


def test_every_target_has_isolated_single_theorem_spec() -> None:
    # Pure-Python structural guard over the committed, Lean-authored Isolated/
    # files (CI has no Lean toolchain); the authoritative re-extraction check
    # lives in tests/test_fc100_isolation.py. Each spec carries its target,
    # any dependency lemmas, and the appended `.disproof` declaration.
    for row in load_manifest(FC100_DIR):
        if row.excluded is not None:
            continue
        path = FC100_DIR / row.statement_path
        text = path.read_text()
        assert "import FormalConjectures.Util.ProblemImports" in text, row.id
        short = row.id.rsplit(".", 1)[-1]
        assert re.search(rf"\b(?:theorem|lemma)\s+.*{re.escape(short)}\b", text), row.id
        assert text.rstrip().endswith(disproof_declaration(row.decl_name)), row.id
        expected = _DEPENDENCY_LEMMA_SPECS.get(row.id, 1) + 1
        assert len(_DECL_RE.findall(text)) == expected, row.id


def test_load_subset_unknown_raises() -> None:
    with pytest.raises(ValueError, match="Unknown subset"):
        load_subset(FC100_DIR, "does_not_exist")
