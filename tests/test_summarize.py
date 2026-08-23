"""Fast checks for the metadata summarization tasks. No model or Docker calls."""

import json
from pathlib import Path

from apn.dataset import OEIS_DIR, fc_commit, oeis_dataset
from apn.task import get_identifier_for_image
from scripts.summarize.collect import (
    Generated,
    _group_proof_outputs,
    _proof_metadata,
)
from scripts.summarize.task import (
    PROOF_OUTPUTS,
    get_agent_compose_file,
    summarize_conjectures,
    summarize_proofs,
    summarize_sequences,
    subset_conjectures,
)


def test_lite_catalog_tasks_load_current_dataset(tmp_path: Path) -> None:
    sequences = summarize_sequences()
    conjectures = summarize_conjectures(metadata_dir=str(tmp_path))

    assert len(sequences.dataset) == 99  # two Lite conjectures share one sequence
    assert len(conjectures.dataset) == 100


def test_all_conjectures_load_full_dataset_in_order() -> None:
    conjectures = subset_conjectures("all")

    assert len(conjectures) == 492
    assert [conjecture.id for conjecture in conjectures] == [
        str(sample.id) for sample in oeis_dataset()
    ]


def test_proof_summarizer_compose_uses_oeis_pin() -> None:
    commit = fc_commit(OEIS_DIR)
    compose = get_agent_compose_file().read_text()

    assert get_identifier_for_image("agent", commit) in compose
    assert f"FC_COMMIT: {commit}" in compose
    assert "network_mode: none" in compose


def test_proof_task_creates_independent_summary_and_full_proof(
    tmp_path: Path,
) -> None:
    conjecture = subset_conjectures("lite")[0]
    sample_dir = tmp_path / "run" / "test_plaintext" / conjecture.id
    submission_dir = sample_dir / "Submission"
    submission_dir.mkdir(parents=True)
    (sample_dir / "scores.json").write_text(
        json.dumps({"proof_scorer": {"value": "C"}})
    )
    (sample_dir / "info.json").write_text(
        json.dumps({"oeis_id": conjecture.oeis_id})
    )
    (submission_dir / "Spec.lean").write_text(
        "theorem accepted_proof : True := by trivial\n"
    )
    metadata_dir = tmp_path / "metadata"
    metadata_dir.mkdir()
    (metadata_dir / "sequences.json").write_text("{}")
    (metadata_dir / "conjectures.json").write_text("{}")

    task = summarize_proofs(
        run_dir=str(tmp_path / "run"), metadata_dir=str(metadata_dir)
    )
    samples = list(task.dataset)

    assert len(samples) == 2
    sample_metadata = [sample.metadata for sample in samples]
    assert all(metadata is not None for metadata in sample_metadata)
    metadata_rows = [metadata or {} for metadata in sample_metadata]
    assert [metadata["proof_output"] for metadata in metadata_rows] == [
        "summary",
        "full_proof",
    ]
    assert len({sample.id for sample in samples}) == 2
    for sample, metadata, output in zip(
        samples, metadata_rows, PROOF_OUTPUTS, strict=True
    ):
        assert metadata["proof_id"] == conjecture.id
        assert output.submit_tool in str(sample.input)
        assert "relying on another generated version" not in str(sample.input)
    summary_prompt = " ".join(str(samples[0].input).split())
    full_proof_prompt = " ".join(str(samples[1].input).split())
    assert (
        "one or two concise sentences explaining the key mathematical ideas "
        "of this specific proof"
        in summary_prompt
    )
    assert "complete, self-contained natural-language proof" in full_proof_prompt
    assert "There is no maximum length" in full_proof_prompt
    assert "3,000-word exposition is entirely acceptable" in full_proof_prompt
    assert "not a synopsis or an expanded summary" in full_proof_prompt


def test_proof_collection_groups_summary_and_full_proof() -> None:
    generated = {
        "proof-id__summary": Generated(
            row={"proof_summary": "Short."},
            metadata={"proof_id": "proof-id", "proof_output": "summary"},
            generation={"model": "summary-model", "source_eval": "summary.eval"},
        ),
        "proof-id__full_proof": Generated(
            row={"full_proof": "A complete proof with all intermediate steps."},
            metadata={"proof_id": "proof-id", "proof_output": "full_proof"},
            generation={"model": "proof-model", "source_eval": "proof.eval"},
        ),
    }

    grouped = _group_proof_outputs(generated)
    metadata = _proof_metadata("proved", grouped["proof-id"])

    assert metadata == {
        "settlement": "proved",
        "summary": {
            "text": "Short.",
            "generation": {
                "model": "summary-model",
                "source_eval": "summary.eval",
            },
        },
        "full_proof": {
            "text": "A complete proof with all intermediate steps.",
            "generation": {
                "model": "proof-model",
                "source_eval": "proof.eval",
            },
        },
    }
