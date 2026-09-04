"""Wikipedia-autoformalized frontend for the per-target isolation pipeline.

The dataset-neutral cut logic lives in ``scripts/isolation.py`` and the
Formal-Conjectures statement conventions (the ``example``-command cut, the
``answer(...) ↔`` rewrite and its re-elaboration certificates) in
``scripts/fc_statements.py``; this module owns the data locations under
``apn/data/wikipedia_autoformalized/`` and the facts about the run the
sources came from. The vendored sources are our own autoformalization
pipeline's accepted final files (see the dataset's ``NOTICE.md``), stated in
FC's conventions -- the ``FormalConjecturesUtil`` import, ``@[category
research ...]`` attributes, ``answer(sorry) ↔ P`` question forms -- so
membership uses the same census as the Erdős universe
(``scripts.erdos_isolation``): every standalone ``theorem``/``lemma``
declaration carrying a research-category attribute is a member, and the
Erdős generator's exclusion rules apply (value-typed ``answer(sorry)``
members and members with a complete in-file proof become ``excluded`` rows).

The run facts ride in ``metadata/run_samples.jsonl`` (one row per sample of
the run, written by ``scripts/vendor_wikipedia_autoformalized.py``): which
samples were selected, which vendored file each became, and the
adjudicator's *kept slots* -- the declarations it accepted as faithful
formalizations of the decomposed sub-questions. Generation joins the census
against that table (every kept slot must resolve to exactly one member) and
derives the default subset from it.

Three callers import this module: the vendor-time tools
``scripts/vendor_wikipedia_autoformalized.py`` (run → ``Sources/`` +
``metadata/``) and ``scripts/generate_wikipedia_autoformalized_isolated.py``
(``Sources/`` + ``metadata/`` → ``samples.jsonl`` + ``Isolated/`` +
``subsets/``), and ``tests/test_wikipedia_autoformalized_isolation.py`` (the
authoritative validation of the committed files).
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from scripts.fc_statements import strip_comments
from scripts.isolation import REPO

WIKIPEDIA_AUTOFORMALIZED_DIR = REPO / "apn" / "data" / "wikipedia_autoformalized"
SOURCES_DIR = WIKIPEDIA_AUTOFORMALIZED_DIR / "Sources"
ISOLATED_DIR = WIKIPEDIA_AUTOFORMALIZED_DIR / "Isolated"
METADATA_DIR = WIKIPEDIA_AUTOFORMALIZED_DIR / "metadata"
RUN_SAMPLES_PATH = METADATA_DIR / "run_samples.jsonl"
RUN_INFO_PATH = METADATA_DIR / "run.json"
SUBSETS_DIR = WIKIPEDIA_AUTOFORMALIZED_DIR / "subsets"

# The selection rule: a run sample's final file is vendored iff the headline
# ``formalized`` score accepted it (CORRECT: every decomposed sub-question
# stated; PARTIAL: unfaithful slots omitted) AND the adjudicator's confidence
# that the file faithfully formalizes every slot it states is at least this.
ACCEPTED_FORMALIZED = ("C", "P")
MIN_CONFIDENCE = 0.8

# The default subset (``apn_wikipedia_autoformalized``'s): the kept slots
# classified research open whose statement records no verdict -- see
# :func:`default_subset_ids`.
DEFAULT_SUBSET = "adjudicated_open"

# The ``answer(...) ↔`` forms carrying a recorded verdict (a filled literal):
# the formalizer's own machine-readable "the answer is known", un-filled in
# the shipped spec like every other form but disqualifying for the default
# subset regardless of the category the statement carries (the run's Connes
# embedding problem is `research open` with an `answer(False)` recording the
# MIP* = RE negative answer).
RECORDED_VERDICT_FORMS = ("lhs_true", "lhs_false", "rhs_true", "rhs_false")

# Files whose isolated specs may carry a `sorry` outside the target theorem
# (a kept def whose dependency closure pulls in a sorry'd helper theorem);
# none today -- generation fails loudly on any new occurrence.
SORRY_ALLOWLIST_FILES: set[str] = set()

# The reason recorded in the run table for a selected sample whose final file
# is NOT vendored: the sandbox images build only the FC proving library (the
# util module's closure), never the conjecture corpus, so a file importing a
# sibling problem module cannot elaborate in the proving environment (the
# extractor would silently drop its declarations, the scorer would fail).
SIBLING_IMPORT_REASON = (
    "imports {modules}: the sandbox images carry only the FC proving library "
    "(the util module's closure), not the conjecture corpus, so the file cannot "
    "elaborate in the proving environment"
)

_IMPORT_RE = re.compile(r"(?m)^import\s+(\S+)")


def sibling_imports(text: str, util_module: str) -> list[str]:
    """The file's ``import``\\ s other than the pin's util module, in order."""
    return [m for m in _IMPORT_RE.findall(strip_comments(text)) if m != util_module]


def is_selected(formalized: str | None, confidence: float | None) -> bool:
    """The selection rule over a run sample's headline score and confidence."""
    return (
        formalized in ACCEPTED_FORMALIZED
        and confidence is not None
        and confidence >= MIN_CONFIDENCE
    )


@dataclass(frozen=True)
class RunSample:
    """One row of ``metadata/run_samples.jsonl``: a sample of the run."""

    problem_id: str
    title: str
    reference_url: str
    uuid: str
    lean_namespace: str
    decision: str | None
    formalized: str | None
    adjudicator_confidence: float | None
    slots_kept: int | None
    slots_total: int | None
    kept_slots: list[str] | None
    probe_claim: str | None
    probe_verified: bool | None
    error: str | None
    selected: bool
    source: str | None
    not_vendored_reason: str | None

    @property
    def kept_ids(self) -> list[str]:
        """The kept slots' fully-qualified declaration names (the manifest ids
        the run's adjudicated statements must resolve to)."""
        return [f"{self.lean_namespace}.{slot}" for slot in (self.kept_slots or [])]

    def to_json(self) -> dict[str, Any]:
        return dict(self.__dict__)


def load_run_samples(path: Path = RUN_SAMPLES_PATH) -> list[RunSample]:
    rows: list[RunSample] = []
    for line in path.read_text().splitlines():
        rec = json.loads(line)
        rows.append(RunSample(**rec))
    ids = [r.problem_id for r in rows]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate problem ids in the run table")
    return rows


def write_run_samples(rows: list[RunSample], path: Path = RUN_SAMPLES_PATH) -> None:
    path.parent.mkdir(exist_ok=True)
    text = "\n".join(
        json.dumps(r.to_json(), ensure_ascii=False)
        for r in sorted(rows, key=lambda r: r.problem_id)
    )
    path.write_text(text + "\n")


def vendored_samples(rows: list[RunSample]) -> list[RunSample]:
    """The run samples whose final file is a vendored source, keyed in
    ``source`` order."""
    return sorted((r for r in rows if r.source is not None), key=lambda r: r.source or "")


def is_open_adjudicated(row: dict[str, Any]) -> bool:
    """Whether a manifest row belongs to the ``adjudicated_open`` subset: a
    scoreable (non-excluded) kept slot classified ``research open`` whose
    statement records no verdict."""
    return (
        row.get("excluded") is None
        and row["slot"] is not None
        and row["category"] == "research open"
        and row.get("answer_form") not in RECORDED_VERDICT_FORMS
    )


def default_subset_ids(manifest_rows: list[dict[str, Any]], run_rows: list[RunSample]) -> list[str]:
    """The ``adjudicated_open`` subset (:func:`is_open_adjudicated`), in
    problem order then the adjudicator's slot order."""
    by_id = {row["id"]: row for row in manifest_rows}
    ids = [
        kept_id
        for run_row in sorted(vendored_samples(run_rows), key=lambda r: r.problem_id)
        for kept_id in run_row.kept_ids
        if is_open_adjudicated(by_id[kept_id])
    ]
    assert len(set(ids)) == len(ids)
    return ids
