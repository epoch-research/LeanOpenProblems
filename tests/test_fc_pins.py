"""The per-dataset FC pins (``apn/data/<dataset>/fc_commit``) are loadable
and produce valid docker image tags. Fast, no docker."""

import re
from pathlib import Path

import pytest

from apn.dataset import ERDOS_DIR, FC100_DIR, OEIS_DIR, fc_commit
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
