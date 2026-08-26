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

from dataclasses import dataclass, field
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

    drop_members: dict[str, str] = field(default_factory=dict)
    """Members (manifest ids) dropped by hand at vendor time, with the reason
    (fails the compile gate, verdict leakage found in review, ...). They ship
    as excluded rows; see DROPPED_REASON_PREFIX."""

    @property
    def dataset_dir(self) -> Path:
        return REPO / "apn" / "data" / self.name

    @property
    def sources_dir(self) -> Path:
        return self.dataset_dir / "Sources"

    @property
    def isolated_dir(self) -> Path:
        return self.dataset_dir / "Isolated"


# The drop reasons below come from the vendor-time review sweep (one agent
# pass over every isolated spec) plus the vendor-time full compile sweep;
# these wide-net sets drop problematic members rather than fixing them.
DATASETS = {
    d.name: d
    for d in (
        FCOpenDataset(
            name="wikipedia",
            fc_directory="FormalConjectures/Wikipedia",
            # MovingSofa's kept `def`s depend on the sorry'd existsUnique
            # helper theorem, which therefore survives the cut.
            sorry_allowlist_files=frozenset({"MovingSofa.lean"}),
            drop_members={
                "MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa": (
                    "module docs cite the solution paper (Baek 2024, Optimality of "
                    "Gerver's Sofa) -- verdict leakage"
                ),
                "JacobianConjecture.jacobian_conjecture_two_variables": (
                    "the file embeds named counterexample definitions disproving the "
                    "general conjecture -- verdict leakage"
                ),
                "DiophantineTuple.hasUniqueExtension_of_forall": (
                    "doc comment references a sibling lemma cut during isolation"
                ),
                "EllipticCurveRank.RatEllipticCurve.finite_twentyone_lt_finrank": (
                    "doc comment refers to 'the previous conjecture', cut during isolation"
                ),
                "EllipticCurveRank.RatEllipticCurve.rank_height_count_asymptotic": (
                    "docstring references sibling theorems cut during isolation"
                ),
                "Kaplansky.idempotent_conjecture": (
                    "an orphaned 'Counterexamples' section (for the cut unit-conjecture "
                    "siblings) misleadingly follows the target"
                ),
                "Kaplansky.zero_divisor_conjecture": (
                    "an orphaned 'Counterexamples' section (for the cut unit-conjecture "
                    "siblings) misleadingly follows the target"
                ),
            },
        ),
        FCOpenDataset(
            name="arxiv",
            fc_directory="FormalConjectures/Arxiv",
            drop_members={
                "Arxiv.«2607.05349».microscopic_weighting_iff_finite_concentration": (
                    "doc comment references the concentration_unique lemma cut during "
                    "isolation"
                ),
                "Margulis.conjecture_1_1": (
                    "a dangling comment announces a companion formalization cut during "
                    "isolation"
                ),
            },
        ),
        FCOpenDataset(
            name="oeis_open",
            fc_directory="FormalConjectures/OEIS",
            drop_members={
                "OeisA100434.conjecture1": (
                    "trivially false as stated (fails by direct computation at n = 0)"
                ),
                "OeisA103425.conjecture": (
                    "trivially true as formalized (the constant sequence 4 with "
                    "(a,b,c) = (1,0,0) satisfies it)"
                ),
                "OeisA211417.general_divisibility": (
                    "trivially true as stated (no 0 < D hypothesis, so D = 0 "
                    "discharges it)"
                ),
                "OeisA211417.supercongruence": (
                    "module references cite an AI proof-search solution paper -- "
                    "verdict signal"
                ),
                "OeisA2326.conjecture2": (
                    "doc comment refers to 'the previous conjecture', cut during isolation"
                ),
                "OeisA114362.conjecture1": (
                    "a leftover definition's doc refers to a sibling conjecture cut "
                    "during isolation"
                ),
                "OeisA34693.a_unbounded": (
                    "doc comment is a counter-conjecture to a sibling cut during isolation"
                ),
            },
        ),
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
