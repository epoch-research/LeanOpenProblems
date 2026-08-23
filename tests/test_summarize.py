"""Fast checks for the metadata summarization tasks. No model or Docker calls."""

from pathlib import Path

from apn.dataset import OEIS_DIR, fc_commit
from apn.task import get_identifier_for_image
from scripts.summarize.task import (
    get_agent_compose_file,
    summarize_conjectures,
    summarize_sequences,
)


def test_lite_catalog_tasks_load_current_dataset(tmp_path: Path) -> None:
    sequences = summarize_sequences()
    conjectures = summarize_conjectures(metadata_dir=str(tmp_path))

    assert len(sequences.dataset) == 99  # two Lite conjectures share one sequence
    assert len(conjectures.dataset) == 100


def test_proof_summarizer_compose_uses_oeis_pin() -> None:
    commit = fc_commit(OEIS_DIR)
    compose = get_agent_compose_file().read_text()

    assert get_identifier_for_image("agent", commit) in compose
    assert f"FC_COMMIT: {commit}" in compose
    assert "network_mode: none" in compose
