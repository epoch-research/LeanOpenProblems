"""Tests for the Wikipedia-autoformalized dataset loader (pure Python, no Docker).

The deeper Lean guarantees over the committed ``Isolated/`` specs -- clean
elaboration, the certified ``answer(...) ↔`` rewrite, only the target + its
dependency decls + derived disproof surviving -- are enforced
authoritatively, in a container, by
``tests/test_wikipedia_autoformalized_isolation.py``. This module checks what
can be checked cheaply on every run: the manifest census (every
research-category statement of the vendored final files of our own
autoformalization run -- see the dataset's ``NOTICE.md``), its consistency
with the run table in ``metadata/``, the ``adjudicated_open`` subset
(``apn_wikipedia_autoformalized``'s default), the dataset/sample shape, and
textual invariants of the shipped sketches.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path
from typing import Any

import pytest

from apn.dataset import (
    WIKIPEDIA_AUTOFORMALIZED_DIR,
    SampleRow,
    fc_commit,
    fc_profile,
    load_manifest,
    load_subset,
    wikipedia_autoformalized_dataset,
)
from scripts.erdos_isolation import VALUE_TYPED_REASON
from scripts.fc_statements import strip_comments
from scripts.isolation import disproof_declaration
from scripts.wikipedia_autoformalized_isolation import (
    ACCEPTED_FORMALIZED,
    DEFAULT_SUBSET,
    MIN_CONFIDENCE,
    RUN_INFO_PATH,
    SOURCES_DIR,
    RunSample,
    default_subset_ids,
    is_open_adjudicated,
    is_selected,
    load_run_samples,
    sibling_imports,
    vendored_samples,
)

_SORRY_RE = re.compile(r"\bsorry\b")
# A top-level theorem/lemma declaration in an isolated spec (column 0).
_DECL_RE = re.compile(r"(?m)^(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[⦃]+)")

# The run (metadata/run.json): 335 samples, 248 selected, 243 vendored (5
# selected files import sibling FC modules). Census over the 243 files.
N_RUN_SAMPLES = 335
N_SELECTED = 248
N_VENDORED = 243
N_ROWS = 432
N_EXCLUDED = 15  # every one value-typed answer(sorry)
N_KEPT_SLOTS = 356  # the adjudicator's kept slots across the vendored files
N_KEPT_EXCLUDED = 12
N_KEPT_SOLVED = 38
N_SUBSET = 305  # kept, research open, no recorded verdict, scoreable
N_SUBSET_PROBLEMS = 226


def _rows() -> list[SampleRow]:
    return load_manifest(WIKIPEDIA_AUTOFORMALIZED_DIR)


def _as_dicts(rows: list[SampleRow]) -> list[dict[str, Any]]:
    return [{"id": r.id, "source": r.source, "excluded": r.excluded, **r.extra} for r in rows]


@pytest.fixture(scope="module")
def run_rows() -> list[RunSample]:
    return load_run_samples()


def test_manifest_census() -> None:
    rows = _rows()
    assert len(rows) == N_ROWS
    assert Counter(r.extra["category"] for r in rows) == {
        "research open": 354,
        "research solved": 78,
    }
    excluded = [r for r in rows if r.excluded is not None]
    assert len(excluded) == N_EXCLUDED
    assert {r.excluded for r in excluded} == {VALUE_TYPED_REASON}
    kept = [r for r in rows if r.extra["slot"] is not None]
    assert len(kept) == N_KEPT_SLOTS
    assert sum(r.excluded is not None for r in kept) == N_KEPT_EXCLUDED
    assert sum(r.extra["category"] == "research solved" for r in kept) == N_KEPT_SOLVED


def test_manifest_answer_form_census() -> None:
    # The kept rows' answer(...)-form distribution; drift means the vendored
    # sources or the census changed. (The certified rewrite itself is
    # re-checked per member in the isolation suite.) The three recorded
    # `answer(False)` verdicts are un-filled like every other form -- the
    # shipped spec states plain P.
    forms = Counter(r.extra["answer_form"] for r in _rows() if r.excluded is None)
    assert forms == {None: 287, "lhs_sorry": 127, "lhs_false": 3}


def test_manifest_row_shape(run_rows: list[RunSample]) -> None:
    by_problem = {r.problem_id: r for r in run_rows}
    for row in _rows():
        assert (WIKIPEDIA_AUTOFORMALIZED_DIR / row.source).is_file(), row.id
        run_row = by_problem[row.extra["problem_id"]]
        assert row.source == run_row.source, row.id
        assert row.extra["title"] == run_row.title, row.id
        assert row.extra["category"] in ("research open", "research solved"), row.id
        # The file's run outcome, which is what selected it.
        assert row.extra["formalized"] in ACCEPTED_FORMALIZED, row.id
        assert row.extra["formalized"] == run_row.formalized, row.id
        assert row.extra["adjudicator_confidence"] == run_row.adjudicator_confidence, row.id
        assert MIN_CONFIDENCE <= row.extra["adjudicator_confidence"] <= 1, row.id
        slot = row.extra["slot"]
        if slot is not None:
            assert row.id == f"{run_row.lean_namespace}.{slot}", row.id
        if row.excluded is None:
            assert (WIKIPEDIA_AUTOFORMALIZED_DIR / row.statement_path).is_file(), row.id
            assert row.extra["answer_form"] in (
                None, "lhs_sorry", "lhs_true", "lhs_false",
                "rhs_sorry", "rhs_true", "rhs_false",
            ), row.id
        else:
            assert "answer_form" not in row.extra, row.id
            assert row.statement is None, row.id


def test_run_table_consistency(run_rows: list[RunSample]) -> None:
    """The run table is the selection's ground truth: every row's `selected`
    follows the rule, vendored rows are exactly the selected files without a
    sibling import, `Sources/` holds exactly those files, and the manifest's
    kept-slot rows are exactly the vendored files' kept slots."""
    assert len(run_rows) == N_RUN_SAMPLES
    for r in run_rows:
        assert r.selected == is_selected(r.formalized, r.adjudicator_confidence), r.problem_id
        if r.source is not None:
            assert r.selected and r.not_vendored_reason is None, r.problem_id
            assert (WIKIPEDIA_AUTOFORMALIZED_DIR / r.source).is_file(), r.problem_id
            assert r.kept_slots and len(r.kept_slots) == r.slots_kept, r.problem_id
        elif r.selected:
            assert r.not_vendored_reason, r.problem_id
        else:
            assert r.not_vendored_reason is None, r.problem_id
    assert sum(r.selected for r in run_rows) == N_SELECTED
    vendored = vendored_samples(run_rows)
    assert len(vendored) == N_VENDORED
    assert sorted(p.name for p in SOURCES_DIR.glob("*.lean")) == sorted(
        Path(r.source or "").name for r in vendored
    )
    util_module = fc_profile(fc_commit(WIKIPEDIA_AUTOFORMALIZED_DIR)).util_module
    for r in vendored:
        text = (WIKIPEDIA_AUTOFORMALIZED_DIR / (r.source or "")).read_text()
        assert not sibling_imports(text, util_module), r.problem_id
    expected_slots = {
        kept_id: (r.problem_id, slot)
        for r in vendored
        for kept_id, slot in zip(r.kept_ids, r.kept_slots or [])
    }
    slot_rows = {
        row.id: (row.extra["problem_id"], row.extra["slot"])
        for row in _rows()
        if row.extra["slot"] is not None
    }
    assert slot_rows == expected_slots
    manifest_problems = {row.extra["problem_id"] for row in _rows()}
    assert manifest_problems == {r.problem_id for r in vendored}


def test_run_info(run_rows: list[RunSample]) -> None:
    info = json.loads(RUN_INFO_PATH.read_text())
    assert info["fc_commit"] == fc_commit(WIKIPEDIA_AUTOFORMALIZED_DIR)
    assert info["selection"] == {
        "formalized": list(ACCEPTED_FORMALIZED),
        "min_confidence": MIN_CONFIDENCE,
    }
    counts = info["counts"]
    assert counts["samples"] == len(run_rows) == N_RUN_SAMPLES
    assert counts["selected"] == N_SELECTED
    assert counts["vendored"] == N_VENDORED
    assert counts["not_vendored"] == N_SELECTED - N_VENDORED
    assert counts["kept_slots_vendored"] == N_KEPT_SLOTS
    assert counts["formalized"] == dict(Counter(str(r.formalized) for r in run_rows))


def test_default_subset(run_rows: list[RunSample]) -> None:
    # The kept slots classified research open with no recorded verdict:
    # re-derived from the manifest + run table, and every id scoreable.
    rows = _rows()
    ids = load_subset(WIKIPEDIA_AUTOFORMALIZED_DIR, DEFAULT_SUBSET)
    assert len(ids) == N_SUBSET
    assert ids == default_subset_ids(_as_dicts(rows), run_rows)
    by_id = {r.id: r for r in rows}
    for sample_id in ids:
        row = by_id[sample_id]
        assert row.excluded is None, sample_id
        assert row.extra["slot"] is not None, sample_id
        assert row.extra["category"] == "research open", sample_id
        assert row.extra["answer_form"] in (None, "lhs_sorry", "rhs_sorry"), sample_id
    assert len({by_id[i].extra["problem_id"] for i in ids}) == N_SUBSET_PROBLEMS
    assert len(wikipedia_autoformalized_dataset(names=ids)) == N_SUBSET
    # Nothing that qualifies is left out, and the one research-open kept slot
    # left out for its recorded verdict is the Connes embedding problem.
    left_out = [r.id for r in rows if is_open_adjudicated(_as_dicts([r])[0]) and r.id not in set(ids)]
    assert not left_out
    verdict_rows = [
        r.id
        for r in rows
        if r.excluded is None
        and r.extra["slot"] is not None
        and r.extra["category"] == "research open"
        and r.id not in set(ids)
    ]
    assert verdict_rows == ["ConnesEmbeddingProblem.connes_embedding_problem"]


def test_spec_files_match_manifest_exactly() -> None:
    rows = _rows()
    expected = sorted(
        (WIKIPEDIA_AUTOFORMALIZED_DIR / r.statement_path).name for r in rows if r.excluded is None
    )
    on_disk = sorted(
        p.name for p in (WIKIPEDIA_AUTOFORMALIZED_DIR / "Isolated").glob("*.lean")
    )
    assert on_disk == expected


def test_dataset_loads_all_samples() -> None:
    ds = wikipedia_autoformalized_dataset()
    assert len(ds) == N_ROWS - N_EXCLUDED
    ids = [s.id for s in ds]
    assert len(set(ids)) == len(ids)


def test_dataset_sample_shape() -> None:
    ds = wikipedia_autoformalized_dataset(names=["ClusterPrime.cluster_prime"])
    assert len(ds) == 1
    sample = ds[0]
    assert sample.id == "ClusterPrime.cluster_prime"
    assert sample.metadata is not None
    assert sample.metadata["source"] == "Sources/ClusterPrime.lean"
    assert sample.metadata["decl_name"] == "ClusterPrime.cluster_prime"
    sketch = sample.metadata["sketch"]
    assert sample.input == sketch
    assert "import FormalConjecturesUtil" in sketch
    # The source states `answer(sorry) ↔ {p | IsClusterPrime p}.Infinite`;
    # the spec states the plain proposition.
    assert "theorem cluster_prime : {p : ℕ | IsClusterPrime p}.Infinite" in sketch


def test_run_facts_never_reach_sample_metadata() -> None:
    # The manifest's category (resolution status), slot, score and confidence
    # exist for tooling; none of it flows to the agent-facing sample (same
    # policy as the other datasets).
    for sample in wikipedia_autoformalized_dataset():
        assert sample.metadata is not None
        assert set(sample.metadata) == {"sketch", "source", "decl_name"}


def test_dataset_names_filter_unknown_raises() -> None:
    with pytest.raises(ValueError, match="unknown or excluded"):
        wikipedia_autoformalized_dataset(names=["does_not_exist"])


def test_sketches_have_no_answer_no_banner_no_category() -> None:
    # Every `answer(...) ↔` form is rewritten to plain P, the FC contribution
    # header is stripped at load time, and isolation drops the `@[category
    # ...]` catalogue lists (the resolution-status channel).
    for sample in wikipedia_autoformalized_dataset():
        assert sample.metadata is not None
        sketch = sample.metadata["sketch"]
        code = strip_comments(sketch)
        assert "answer(" not in code, sample.id
        assert "Copyright" not in sketch, sample.id
        assert "@[category" not in code, sample.id
        assert sketch.startswith("import "), sample.id


def test_sketches_have_no_example_commands() -> None:
    # Anonymous `example` sanity checks would be re-run by the scorer inside
    # the trusted target compile on every score call; the sources ship them
    # (some by `decide +native` brute force) and isolation must cut them all.
    for sample in wikipedia_autoformalized_dataset():
        assert sample.metadata is not None
        stripped = strip_comments(sample.metadata["sketch"])
        assert not re.search(r"(?m)^example\b", stripped), sample.id


def test_sketches_sorry_count() -> None:
    # Exactly two `sorry`s: the target and its derived `.disproof`.
    for sample in wikipedia_autoformalized_dataset():
        assert sample.metadata is not None
        n = len(_SORRY_RE.findall(strip_comments(sample.metadata["sketch"])))
        assert n == 2, f"{sample.id}: {n} sorries"


def test_sketches_end_with_disproof_declaration() -> None:
    for row in _rows():
        if row.excluded is not None:
            continue
        text = (WIKIPEDIA_AUTOFORMALIZED_DIR / row.statement_path).read_text()
        assert text.rstrip().endswith(disproof_declaration(row.decl_name)), row.id


def _declares(member_id: str, text_name: str) -> bool:
    """Whether a spec's declared source-text name is ``member_id``'s -- the
    text name omits enclosing ``namespace`` components."""
    return member_id == text_name or member_id.endswith("." + text_name)


def test_no_sibling_member_survives_in_any_spec() -> None:
    # The anti-leak cut property, stated directly: no universe member may
    # survive in another member's spec (a problem's parts/variants and its
    # known-result siblings are each other's siblings). Pure-Python guard over
    # the committed files; the authoritative re-extraction check lives in
    # tests/test_wikipedia_autoformalized_isolation.py.
    rows = _rows()
    by_source: dict[str, list[str]] = {}
    for r in rows:
        by_source.setdefault(r.source, []).append(r.id)
    for row in rows:
        if row.excluded is not None:
            continue
        text = (WIKIPEDIA_AUTOFORMALIZED_DIR / row.statement_path).read_text()
        declared = _DECL_RE.findall(text)
        assert any(_declares(row.id, n) for n in declared), row.id
        siblings = [i for i in by_source[row.source] if i != row.id]
        for name in declared:
            if _declares(row.id, name):
                continue
            offenders = [i for i in siblings if _declares(i, name)]
            assert (
                not offenders
            ), f"{row.id}: sibling universe member(s) {offenders} survived isolation"
