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

import hashlib
import json
import re

import pytest

from apn.dataset import (
    ERDOS_ISOLATED_DIR,
    ERDOS_MAPPING_FILE,
    ERDOS_SOURCES_DIR,
    ERDOS_SOURCES_MANIFEST,
    ERDOS_SUBSETS_DIR,
    erdos_dataset,
    load_subset,
    parse_decl_mapping,
)
from scripts.erdos_isolation import (
    GENERATED_SUBSET,
    SORRY_ALLOWLIST,
    SOURCES_DIR,
    SUBSETS_DIR,
    kept_names,
)
from scripts.fc_statements import strip_comments
from scripts.isolation import matches_name

# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:theorem|lemma)\b")
_SORRY_RE = re.compile(r"\bsorry\b")


def test_sources_corpus_complete_and_unmodified() -> None:
    # Sources/ is the whole FC ErdosProblems directory at the vendored commit,
    # not just the files an evaluation set happens to use; SOURCES.json pins
    # its provenance and a digest per file, so this holds without the
    # (gitignored) local FC clone.
    manifest = json.loads(ERDOS_SOURCES_MANIFEST.read_text())
    digests = manifest["files"]
    assert sorted(p.name for p in ERDOS_SOURCES_DIR.glob("*.lean")) == sorted(digests)
    for name, digest in digests.items():
        actual = hashlib.sha256((ERDOS_SOURCES_DIR / name).read_bytes()).hexdigest()
        assert actual == digest, f"{name} differs from the vendored FC file"


def test_membership_arithmetic() -> None:
    # subsets/tsoukalas.json is the membership source of truth: the paper's 353
    # attempted names, of which exactly its 3 excluded ones are dropped and its
    # 1 rename is tracked to the name at the vendored FC commit.
    subset = json.loads((SUBSETS_DIR / f"{GENERATED_SUBSET}.json").read_text())
    attempted = subset["attempted"]
    assert len(attempted) == 353
    assert len(set(attempted)) == 353
    excluded = {row["target"] for row in subset["excluded"]}
    assert len(excluded) == 3
    assert excluded <= set(attempted)
    renames = {row["attempted"]: row["at_fc_commit"] for row in subset["renamed"]}
    assert renames == {"erdos_1082b": "erdos_1082.parts.ii"}
    kept = kept_names()
    assert len(kept) == 350
    assert set(kept) == (set(attempted) - excluded - set(renames)) | set(renames.values())
    # Every entry carries a reason -- the reconciliation must stay documented.
    assert all(row["reason"].strip() for row in subset["excluded"] + subset["renamed"])


def test_attempted_list_matches_upstream_digest() -> None:
    # The attempted list is a vendored copy of the paper's
    # erdos_problems_attempted.txt (newline-separated, no trailing newline).
    # Pinning its digest means an edit to the list cannot silently redefine the
    # paper's set -- the upstream file is no longer kept alongside it.
    subset = json.loads((SUBSETS_DIR / f"{GENERATED_SUBSET}.json").read_text())
    digest = hashlib.sha256("\n".join(subset["attempted"]).encode()).hexdigest()
    assert digest == subset["_meta"]["upstream"]["sha256"]


def test_subset_samples_match_generated_membership() -> None:
    # The subset's sample ids are the fully qualified resolutions of its kept
    # short names, in the same order -- what load_subset hands the dataset.
    samples = load_subset(GENERATED_SUBSET, ERDOS_SUBSETS_DIR)
    assert len(samples) == 350
    for full, short in zip(samples, kept_names()):
        assert matches_name(full, short), f"{full} does not resolve {short}"
    assert samples == [name for name, _ in parse_decl_mapping(ERDOS_MAPPING_FILE.read_text())]


def test_mapping_matches_membership() -> None:
    # MAPPING.json (generated) resolves exactly the kept short names, in
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


def test_sketches_have_no_fc_annotations() -> None:
    # FC has recorded verdicts on 14 members since the paper's attempts (a
    # `research solved` category flip, `formal_proof` URL attributes, prose
    # crediting the prover agent -- one stating the direction outright).
    # Generation drops every kept declaration's `@[category ...]`
    # classification list whole and removes the verdict prose
    # (scripts/erdos_isolation.py:strip_fc_annotations): the recorded answer
    # must not reach the shipped sketch in any form. None of these markers
    # legitimately occurs in problem prose.
    for sample in erdos_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"].lower()
        for marker in ("@[category", "formal_proof", "research solved", "deepmind", "prover agent"):
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
    with pytest.raises(ValueError, match="Unknown subset"):
        load_subset("does_not_exist", ERDOS_SUBSETS_DIR)
