"""Tests for the FC100OpenSet1 dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, the certified ``answer(sorry) ↔`` rewrite, only the target + its
dependency decls surviving -- are enforced authoritatively, in a container, by
``tests/test_fc100_isolation.py``. This module checks what can be checked
cheaply on every run: the membership arithmetic (100 = 86 kept + 14 excluded),
the dataset/sample shape, and textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re

import pytest

from apn.dataset import (
    FC100_ISOLATED_DIR,
    FC100_MAPPING_FILE,
    FC100_SUBSETS_DIR,
    fc100open_dataset,
    load_subset,
    parse_fc100_mapping,
)
from scripts.fc100_isolation import (
    EXCLUDED_FILE,
    SORRY_ALLOWLIST,
    SOURCES_DIR,
    SUBSET_FILE,
    kept_names,
    parse_excluded,
    parse_subset_names,
    strip_comments,
)

# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:theorem|lemma)\b")
_SORRY_RE = re.compile(r"\bsorry\b")


def test_membership_arithmetic() -> None:
    # The vendored subset file is the membership source of truth: exactly 100
    # distinct members, of which exactly the 14 in EXCLUDED.txt are dropped.
    members = parse_subset_names(SUBSET_FILE.read_text())
    assert len(members) == 100
    assert len(set(members)) == 100
    excluded = parse_excluded(EXCLUDED_FILE.read_text())
    assert len(excluded) == 14
    assert set(excluded) <= set(members)
    kept = kept_names()
    assert len(kept) == 86
    assert set(kept) == set(members) - set(excluded)


def test_mapping_matches_membership() -> None:
    # MAPPING.txt (generated) covers exactly the kept members, in subset order,
    # and every mapped source file is vendored.
    entries = parse_fc100_mapping(FC100_MAPPING_FILE.read_text())
    assert [name for name, _ in entries] == kept_names()
    for name, relpath in entries:
        assert (SOURCES_DIR / relpath).is_file(), f"{name}: missing source {relpath}"


def test_every_isolated_file_used_exactly_once() -> None:
    entries = parse_fc100_mapping(FC100_MAPPING_FILE.read_text())
    assert sorted(p.name for p in FC100_ISOLATED_DIR.glob("*.lean")) == sorted(
        f"{name}.lean" for name, _ in entries
    )


def test_fc100_dataset_loads_full_set() -> None:
    ds = fc100open_dataset()
    assert len(ds) == 86
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)
    assert ids == kept_names()


def test_fc100_dataset_sample_shape() -> None:
    ds = fc100open_dataset(names=["Erdos200.erdos_200"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "Erdos200.erdos_200"
    assert sample.metadata is not None
    assert sample.metadata["source_file"] == "ErdosProblems/200.lean"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjectures.Util.ProblemImports" in sketch
    assert "theorem erdos_200" in sketch
    # This member was stated `answer(sorry) ↔ P` upstream and is shipped
    # rewritten to plain `P`.
    assert "answer(" not in sketch


def test_fc100_dataset_names_filter_unknown() -> None:
    assert len(fc100open_dataset(names=["does_not_exist"])) == 0


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


def test_sketches_have_no_example_commands() -> None:
    # FC's anonymous `example` sanity checks (GraphConjecture316/327 run
    # `decide +native`) are cut so the trusted target compile never executes
    # them at score time.
    for sample in fc100open_dataset():
        assert sample.metadata is not None
        assert not re.search(r"(?m)^example\b", sample.metadata["sketch"]), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly one `sorry` per sketch -- the target's proof -- except the
    # allowlisted EllipticCurveRank spec, which also keeps FC's own sorry'd
    # Mordell-Weil instance (that sample implicitly requires proving it too).
    for sample in fc100open_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        expected = 2 if sample.id in SORRY_ALLOWLIST else 1
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
    # lives in tests/test_fc100_isolation.py.
    for name in kept_names():
        path = FC100_ISOLATED_DIR / f"{name}.lean"
        assert path.is_file(), f"missing isolated spec for {name}"
        text = path.read_text()
        assert "import FormalConjectures.Util.ProblemImports" in text, name
        short = name.rsplit(".", 1)[-1]
        assert re.search(rf"\b(?:theorem|lemma)\s+.*{re.escape(short)}\b", text), name
        expected = _DEPENDENCY_LEMMA_SPECS.get(name, 1)
        assert len(_DECL_RE.findall(text)) == expected, name


def test_load_subset_unknown_raises() -> None:
    with pytest.raises(ValueError, match="Unknown subset"):
        load_subset("does_not_exist", FC100_SUBSETS_DIR)
