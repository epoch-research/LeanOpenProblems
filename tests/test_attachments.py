"""Tests for task attachments (``apn/data/attachments/<name>/`` shipped to the
agent's sandbox via ``Sample.files``; see that directory's README) and the
wikipedia ``abc`` subset -- pure Python, no Docker."""

from __future__ import annotations

from pathlib import Path

import pytest

from apn.dataset import (
    ATTACHMENTS_ROOT,
    WIKIPEDIA_DIR,
    attachment_dir,
    available_attachments,
    load_subset,
    wikipedia_dataset,
    with_attachments,
)
from apn.layout import ATTACHMENTS_DIR, PROJECT
from apn.prompts import user_prompt
from apn.task import apn_wikipedia

N_CONJECTURE = "n_conjecture_strong"
UTIL_MODULE = "FormalConjecturesUtil"


def test_n_conjecture_attachment_is_the_archive_minus_info_json() -> None:
    directory = attachment_dir(N_CONJECTURE)
    files = sorted(p.relative_to(directory).as_posix() for p in directory.rglob("*") if p.is_file())
    assert "README.md" in files
    assert "first-formulation/submission/Spec.lean" in files
    assert "quality-formulation/submission/Spec.lean" in files
    assert not [f for f in files if f.endswith("info.json")]
    # Provenance lives in the attachments README, not inside the shipped copy.
    assert (ATTACHMENTS_ROOT / "README.md").is_file()


def test_available_attachments() -> None:
    assert N_CONJECTURE in available_attachments()


def test_unknown_attachment_fails_at_construction() -> None:
    with pytest.raises(ValueError, match="Unknown attachment"):
        attachment_dir("no_such_attachment")
    with pytest.raises(ValueError, match="Unknown attachment"):
        attachment_dir("../wikipedia")


def test_attachments_dir_is_outside_the_lake_project() -> None:
    assert not ATTACHMENTS_DIR.startswith(PROJECT + "/")


def test_with_attachments_none_ships_nothing() -> None:
    for sample in with_attachments(wikipedia_dataset(names=["ABC.abc"]), None):
        assert not sample.files


def test_with_attachments_maps_sandbox_dir_to_local_copy() -> None:
    ds = with_attachments(wikipedia_dataset(names=["ABC.abc"]), N_CONJECTURE)
    (sample,) = list(ds)
    assert sample.files == {ATTACHMENTS_DIR: str(attachment_dir(N_CONJECTURE))}


def test_abc_subset_is_the_conjecture_itself() -> None:
    assert load_subset(WIKIPEDIA_DIR, "abc") == ["ABC.abc"]


def test_apn_wikipedia_abc_with_attachment() -> None:
    task = apn_wikipedia(subset="abc", attachments=N_CONJECTURE)
    (sample,) = list(task.dataset)
    assert sample.id == "ABC.abc"
    assert sample.metadata is not None
    assert sample.metadata["decl_name"] == "ABC.abc"
    assert sample.files == {ATTACHMENTS_DIR: str(attachment_dir(N_CONJECTURE))}


def test_apn_wikipedia_default_has_no_attachment() -> None:
    for sample in apn_wikipedia(subset="abc").dataset:
        assert not sample.files


def test_user_prompt_attachments_note_gated() -> None:
    path = f"{PROJECT}/Submission/Spec.lean"
    plain = user_prompt(path, token_limit=None, literature=False, util_module=UTIL_MODULE)
    assert ATTACHMENTS_DIR not in plain
    noted = user_prompt(
        path, token_limit=None, literature=False, util_module=UTIL_MODULE, attachments=True
    )
    assert ATTACHMENTS_DIR in noted
    assert "README.md" in noted


def test_inspect_expands_the_attachment_directory() -> None:
    # Inspect resolves a directory-valued ``files`` entry into one entry per
    # file, joined under the sandbox key (inspect_ai._eval.task.sandbox); pin
    # that the copy lands at ATTACHMENTS_DIR/<relative path>, info.json-free.
    from inspect_ai._eval.task.sandbox import resolve_sample_files

    directory = attachment_dir(N_CONJECTURE)
    resolved = resolve_sample_files({ATTACHMENTS_DIR: str(directory)})
    expected = {
        f"{ATTACHMENTS_DIR}/{p.relative_to(directory).as_posix()}": p
        for p in directory.rglob("*")
        if p.is_file()
    }
    # Inspect reports the local sources as file:// URIs; compare by path.
    assert {k: Path(v.removeprefix("file://")) for k, v in resolved.items()} == expected
    assert len(resolved) == 18
    assert f"{ATTACHMENTS_DIR}/README.md" in resolved
    assert f"{ATTACHMENTS_DIR}/quality-formulation/submission/Spec.lean" in resolved
