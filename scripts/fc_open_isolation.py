"""Frontend for the FC directory-scoped research-open datasets.

The ``wikipedia``, ``arxiv`` and ``oeis_open`` datasets are all cut the same
way from the same FC pin, differing only in which upstream directory they
vendor, so one frontend serves all three. The dataset-neutral cut logic and
Docker plumbing live in ``scripts/isolation.py``, and the Formal-Conjectures
statement conventions (the ``example``-command cut, the ``answer(...) ↔``
rewrite and its re-elaboration certificates, the research-category census) in
``scripts/fc_statements.py``; this module owns the per-dataset data locations
and exclusion/allowlist constants.

Membership is *defined* by the vendored sources: every ``theorem``/``lemma``
declaration carrying a ``@[category research open]`` attribute in a dataset's
``Sources/`` (the files of its FC directory hosting at least one such
statement at the pinned FC commit -- see the dataset's ``NOTICE.md``) is a
universe member. ``research solved`` statements sharing those files are *not*
members -- unlike the Erdős universe, whose per-problem statement selection
makes every research-category sibling a member -- and are cut from the specs
like any other sibling. Value-typed ``answer(sorry)`` members (a ``sorryAx``
in the elaborated statement type, unscoreable by the verifier) and members
carrying a complete in-file proof become ``excluded`` rows.

(``oeis_open`` is unrelated to the ``oeis`` dataset: that one vendors the
Tsoukalas-paper autoformalized OEIS corpus at an older pin with per-conjecture
membership; this one is simply the research-open statements of
``FormalConjectures/OEIS`` at this pin.)

Two callers import this module: ``scripts/generate_fc_open_isolated.py`` (the
vendor-time tool that produces each dataset's ``samples.jsonl`` +
``Isolated/``) and ``tests/test_fc_open_isolation.py`` (the authoritative
validation of the committed files).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from scripts.isolation import REPO


@dataclass(frozen=True)
class FCOpenDataset:
    """One FC directory-scoped research-open dataset."""

    name: str
    """The dataset's directory name under ``apn/data/``."""

    fc_directory: str
    """The upstream directory vendored into ``Sources/`` (provenance only --
    membership is defined by the vendored files themselves)."""

    sorry_allowlist_files: frozenset[str] = frozenset()
    """Files (relpaths under ``Sources/``) whose isolated specs may carry a
    ``sorry`` outside the target theorem: a kept non-theorem declaration
    proved with ``sorry`` in FC itself, or one whose dependency closure pulls
    in a sorry'd helper theorem. Such samples implicitly also require proving
    the helper; generation reports them instead of failing."""

    @property
    def dataset_dir(self) -> Path:
        return REPO / "apn" / "data" / self.name

    @property
    def sources_dir(self) -> Path:
        return self.dataset_dir / "Sources"

    @property
    def isolated_dir(self) -> Path:
        return self.dataset_dir / "Isolated"


DATASETS = {
    d.name: d
    for d in (
        FCOpenDataset(
            name="wikipedia",
            fc_directory="FormalConjectures/Wikipedia",
            # MovingSofa's kept `def`s depend on the sorry'd existsUnique
            # helper theorem, which therefore survives the cut.
            sorry_allowlist_files=frozenset({"MovingSofa.lean"}),
        ),
        FCOpenDataset(name="arxiv", fc_directory="FormalConjectures/Arxiv"),
        FCOpenDataset(name="oeis_open", fc_directory="FormalConjectures/OEIS"),
    )
}

# The reason recorded on value-typed answer(sorry) rows (mirrors the Erdős
# dataset's).
VALUE_TYPED_REASON = (
    "value-typed answer(sorry): the placeholder elaborates to a position-labeled "
    "sorryAx in the statement's type, so the statement cannot be closed (or even "
    'stated) without the paper\'s google.answer "with_auxiliary" machinery, and '
    "SafeVerify cannot score it"
)

# The reason recorded on rows whose declaration carries a complete formal
# proof in the source file itself (no `sorry` anywhere in the command): the
# statement is not an open task, and no spec can ship without either leaking
# the proof text verbatim or inventing un-filling surgery for arbitrary proof
# terms.
PROVED_IN_FILE_REASON = (
    "complete formal proof in the source file at the pin: the statement is not "
    "an open task, and shipping it would leak the proof text"
)

# The reason recorded on rows this pipeline cannot (or deliberately does not)
# ship a sound isolated spec for -- these datasets cast a wide net, so a
# problematic member is dropped with its reason recorded rather than holding
# up the rest. The specific obstruction is appended per row.
DROPPED_REASON_PREFIX = "dropped at vendor time: "
