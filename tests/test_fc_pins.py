"""The per-dataset FC pins (``apn/data/<dataset>/fc_commit``) are loadable,
resolve to registered FC profiles, and produce valid docker image tags. Fast,
no docker."""

import re
from pathlib import Path

import pytest

from apn.dataset import ERDOS_DIR, FC100_DIR, OEIS_DIR, fc_commit, fc_profile
from apn.task import get_identifier_for_image

DATASET_DIRS = {"erdos": ERDOS_DIR, "fc100open": FC100_DIR, "oeis": OEIS_DIR}


@pytest.mark.parametrize("dataset_dir", DATASET_DIRS.values(), ids=DATASET_DIRS.keys())
def test_pin_loads(dataset_dir: Path) -> None:
    commit = fc_commit(dataset_dir)
    assert re.fullmatch(r"[0-9a-f]{40}", commit)


@pytest.mark.parametrize("dataset_dir", DATASET_DIRS.values(), ids=DATASET_DIRS.keys())
def test_pin_makes_valid_image_tag(dataset_dir: Path) -> None:
    # agent_corpus is the longest image kind.
    tag = get_identifier_for_image("agent_corpus", fc_commit(dataset_dir))
    assert re.fullmatch(r"[A-Za-z0-9_.-]+", tag)
    assert len(tag) <= 128


@pytest.mark.parametrize("dataset_dir", DATASET_DIRS.values(), ids=DATASET_DIRS.keys())
def test_pin_resolves_to_profile(dataset_dir: Path) -> None:
    # Every dataset pin must be in the FC profile registry; a pin move without
    # a registry update must fail here, not at task-construction time.
    profile = fc_profile(fc_commit(dataset_dir))
    assert profile.util_module in (
        "FormalConjectures.Util.ProblemImports",
        "FormalConjecturesUtil",
    )


def test_unknown_pin_fails_loudly() -> None:
    with pytest.raises(KeyError, match="No FC profile registered"):
        fc_profile("0" * 40)
