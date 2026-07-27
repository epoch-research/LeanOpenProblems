"""Tests for the Erdős-attempted-set dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, the certified per-form ``answer(...) ↔`` rewrite, only the target
+ its dependency decls surviving -- are enforced authoritatively, in a
container, by ``tests/test_erdos_isolation.py``. This module checks what can
be checked cheaply on every run: the membership arithmetic (353 attempted =
350 kept + 3 excluded, one upstream rename applied), the dataset/sample shape,
and textual invariants of the shipped sketches.
"""

from __future__ import annotations

import re

import pytest

from apn.dataset import (
    ERDOS_ISOLATED_DIR,
    ERDOS_MAPPING_FILE,
    ERDOS_SUBSETS_DIR,
    erdos_dataset,
    load_subset,
    parse_decl_mapping,
)
from scripts.erdos_isolation import (
    ATTEMPTED_FILE,
    EXCLUDED_FILE,
    RENAMED_FILE,
    SORRY_ALLOWLIST,
    SOURCES_DIR,
    kept_names,
    parse_names,
    parse_renamed,
)
from scripts.fc_statements import strip_comments
from scripts.isolation import matches_name

# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:theorem|lemma)\b")
_SORRY_RE = re.compile(r"\bsorry\b")


def test_membership_arithmetic() -> None:
    # The vendored attempted list is the membership source of truth: exactly
    # 353 distinct names, of which exactly the 3 in EXCLUDED.txt are dropped
    # and the 1 in RENAMED.txt is tracked to its name at the vendored commit.
    attempted = parse_names(ATTEMPTED_FILE.read_text())
    assert len(attempted) == 353
    assert len(set(attempted)) == 353
    excluded = parse_names(EXCLUDED_FILE.read_text())
    assert len(excluded) == 3
    assert set(excluded) <= set(attempted)
    renames = parse_renamed(RENAMED_FILE.read_text())
    assert renames == {"erdos_1082b": "erdos_1082.parts.ii"}
    kept = kept_names()
    assert len(kept) == 350
    assert set(kept) == (set(attempted) - set(excluded) - set(renames)) | set(renames.values())


def test_mapping_matches_membership() -> None:
    # MAPPING.txt (generated) resolves exactly the kept short names, in
    # attempt-list order, to fully qualified declaration names, and every
    # mapped source file is vendored.
    entries = parse_decl_mapping(ERDOS_MAPPING_FILE.read_text())
    kept = kept_names()
    assert len(entries) == len(kept)
    for (full, relpath), short in zip(entries, kept):
        assert matches_name(full, short), f"{full} does not resolve {short}"
        assert (SOURCES_DIR / relpath).is_file(), f"{full}: missing source {relpath}"


def test_every_isolated_file_used_exactly_once() -> None:
    entries = parse_decl_mapping(ERDOS_MAPPING_FILE.read_text())
    assert sorted(p.name for p in ERDOS_ISOLATED_DIR.glob("*.lean")) == sorted(
        f"{name}.lean" for name, _ in entries
    )


def test_erdos_dataset_loads_full_set() -> None:
    ds = erdos_dataset()
    assert len(ds) == 350
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)
    assert ids == [name for name, _ in parse_decl_mapping(ERDOS_MAPPING_FILE.read_text())]


def test_erdos_dataset_sample_shape() -> None:
    ds = erdos_dataset(names=["Erdos741.erdos_741.parts.i"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "Erdos741.erdos_741.parts.i"
    assert sample.metadata is not None
    assert sample.metadata["source_file"] == "741.lean"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjectures.Util.ProblemImports" in sketch
    assert "theorem erdos_741.parts.i" in sketch
    # This member carries a recorded verdict upstream (`answer(False) ↔ P`)
    # and is shipped un-filled, as plain `P` -- the answer key must not leak.
    assert "answer(" not in sketch
    assert "False" not in strip_comments(sketch)


def test_erdos_dataset_names_filter_unknown() -> None:
    assert len(erdos_dataset(names=["does_not_exist"])) == 0


def test_sketches_have_no_answer_and_no_banner() -> None:
    # No `answer(` may survive in any sketch's *code* -- all four statement
    # forms are rewritten to plain `P`, and no member of this set is
    # value-typed. (Kept module docs may mention `answer(sorry)` in prose --
    # hence the comment-stripped census.) The Apache banner is stripped at load.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        assert "answer(" not in strip_comments(sketch), sample.id
        assert "Copyright" not in sketch, sample.id
        assert sketch.startswith("import "), sample.id


def test_sketches_have_no_verdict_annotations() -> None:
    # FC has recorded verdicts on 14 members since the paper's attempts (a
    # `research solved` category flip, `formal_proof` URL attributes, prose
    # crediting the prover agent -- one stating the direction outright).
    # Generation strips them back to the attempt-time form
    # (scripts/erdos_isolation.py:strip_verdict_annotations): the recorded
    # answer must not reach the shipped sketch in any form. None of these
    # markers legitimately occurs in problem prose.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"].lower()
        for marker in ("formal_proof", "research solved", "deepmind", "prover agent"):
            assert marker not in sketch, (sample.id, marker)


def test_sketches_have_no_example_commands() -> None:
    # FC's anonymous `example` sanity checks (1141.lean, 387.lean) are cut so
    # the trusted target compile never executes them at score time.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        assert not re.search(r"(?m)^example\b", sample.metadata["sketch"]), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly one `sorry` per sketch -- the target's proof -- except the
    # allowlisted erdos_1055 spec, whose kept `def p` depends on FC's own
    # sorry'd `exists_p` theorem (that sample implicitly requires proving it
    # too).
    for sample in erdos_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        expected = 2 if sample.id in SORRY_ALLOWLIST else 1
        assert n == expected, f"{sample.id}: {n} sorries"


# Isolated specs that legitimately retain extra theorem/lemma commands because
# a kept declaration depends on them: 1055.lean's kept `def p` uses
# `Nat.find (exists_p r)`, pulling the (sorry'd, allowlisted) `exists_p` into
# the dependency closure. Keep in sync with
# scripts/generate_erdos_isolated.py output (a stable property of the data).
_DEPENDENCY_LEMMA_SPECS = {
    "Erdos1055.erdos_1055": 2,
}


def test_every_target_has_isolated_single_theorem_spec() -> None:
    # Pure-Python structural guard over the committed, Lean-authored Isolated/
    # files (CI has no Lean toolchain); the authoritative re-extraction check
    # lives in tests/test_erdos_isolation.py.
    entries = parse_decl_mapping(ERDOS_MAPPING_FILE.read_text())
    for (name, _), short in zip(entries, kept_names()):
        path = ERDOS_ISOLATED_DIR / f"{name}.lean"
        assert path.is_file(), f"missing isolated spec for {name}"
        text = path.read_text()
        assert "import FormalConjectures.Util.ProblemImports" in text, name
        assert re.search(rf"\b(?:theorem|lemma)\s+{re.escape(short)}\b", text), name
        expected = _DEPENDENCY_LEMMA_SPECS.get(name, 1)
        assert len(_DECL_RE.findall(text)) == expected, name


def test_load_subset_unknown_raises() -> None:
    # No predefined subsets are shipped for this dataset; ad-hoc runs go
    # through --sample-id.
    with pytest.raises(ValueError, match="Unknown subset"):
        load_subset("does_not_exist", ERDOS_SUBSETS_DIR)
