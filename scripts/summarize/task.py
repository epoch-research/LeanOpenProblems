"""Inspect tasks that write LLM summaries of the conjectures settled in an eval run.

For each conjecture a run settled (hawk-download layout under logs/), two stages
produce the pieces of a per-conjecture table row for the paper:

1. ``summarize_sequences`` -- one agent per unique OEIS sequence, writes a short
   description of the sequence from its OEIS record (no sandbox).
2. ``summarize_proofs`` -- one agent per settled conjecture, writes a one-sentence
   conjecture description and a short proof summary. Runs in the agent docker
   sandbox with the accepted proof at Submission/Spec.lean and the Mathlib
   source tree browsable. Takes the stage-1 descriptions as input so it does
   not repeat them.

Usage:
    RUN=logs/oeis-lite-200usd-fable-i7s7n9q7v4emgjp7
    inspect eval scripts/summarize/task.py@summarize_sequences \\
        -T run_dir=$RUN --model ... --log-dir logs/summarize
    python scripts/summarize/collect.py --sequences logs/summarize/<seq>.eval -o out
    inspect eval scripts/summarize/task.py@summarize_proofs \\
        -T run_dir=$RUN -T sequences=out/sequences.jsonl \\
        --model ... --log-dir logs/summarize --max-sandboxes 8
    python scripts/summarize/collect.py \\
        --sequences logs/summarize/<seq>.eval --proofs logs/summarize/<proof>.eval -o out
"""

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from inspect_ai import Task, task
from inspect_ai.agent import AgentSubmit, as_solver, react
from inspect_ai.dataset import MemoryDataset, Sample
from inspect_ai.model import CompactionSummary
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolResult, text_editor, tool
from inspect_ai.util import sandbox, store

import apn
from apn.layout import ENTRY_PATH
from apn.task import COMPOSE_FILES_DIR, IMAGE_REPOSITORY, get_identifier_for_image
from apn.tools import bash

REPO_ROOT = Path(__file__).resolve().parents[2]
OEIS_DATA = Path(apn.__file__).parent / "data" / "oeis"
RECORDS_PATH = OEIS_DATA / "raw" / "oeis_records.jsonl"
PROVENANCE_PATH = OEIS_DATA / "conjecture_provenance.jsonl"

MATHLIB_SOURCE = "/workspace/leanproject/.lake/packages/mathlib/"


def get_agent_compose_file() -> Path:
    """Agent-image-only variant of apn.task.get_compose_file. No build section:
    unlike the apn tasks this must run with a locally available image (no ECR
    access, and a rebuild would need network)."""
    content = f"""
services:
  default:
    image: {IMAGE_REPOSITORY}:{get_identifier_for_image("agent")}
    init: true
    entrypoint: tail -f /dev/null
    mem_limit: 10g
    network_mode: none
"""
    path = COMPOSE_FILES_DIR / "summarize" / "compose.yaml"
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text() != content:
        path.write_text(content)
    return path


def _resolve(path: str) -> Path:
    """Inspect loads task files with cwd set to the task file's directory, so
    relative task args are resolved against the repo root instead."""
    p = Path(path)
    return p if p.is_absolute() else REPO_ROOT / p


def _read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def load_records() -> dict[str, dict]:
    return {row["oeis_id"]: row["record"] for row in _read_jsonl(RECORDS_PATH)}


def load_provenance() -> dict[str, dict]:
    return {row["theorem_name"]: row for row in _read_jsonl(PROVENANCE_PATH)}


@dataclass
class Solve:
    id: str
    oeis_id: str
    proof: str
    verdict: Literal["proved", "disproved"]


def plaintext_dir(run_dir: Path) -> Path:
    matches = sorted(run_dir.glob("*_plaintext"))
    if len(matches) != 1:
        raise ValueError(
            f"expected exactly one *_plaintext dir under {run_dir}, found {len(matches)}"
        )
    return matches[0]


def solved_samples(run_dir: Path) -> list[Solve]:
    solves = []
    for sample_dir in sorted(plaintext_dir(run_dir).iterdir()):
        if not sample_dir.is_dir():
            continue
        score = json.loads((sample_dir / "scores.json").read_text())["proof_scorer"]
        if score["value"] != "C":
            continue
        proof = (sample_dir / "Submission" / "Spec.lean").read_text()
        info = json.loads((sample_dir / "info.json").read_text())
        solves.append(
            Solve(
                id=sample_dir.name,
                oeis_id=info["oeis_id"],
                proof=proof,
                verdict="disproved" if ".disproof" in proof else "proved",
            )
        )
    if not solves:
        raise ValueError(f"no solved samples under {run_dir}")
    return solves


def sequence_prompt(oeis_id: str, record: dict) -> str:
    return f"""\
You are writing a short description of the OEIS sequence {oeis_id} for a table in a mathematics paper.
The full OEIS record is below.

Call submit_sequence with a description of the sequence of at most about 10 words, suitable for
a table cell. Plain text, LaTeX math allowed.

<oeis_record>
{json.dumps(record, indent=2)}
</oeis_record>
"""


def proof_prompt(
    solve: Solve, record: dict, provenance: dict | None, sequence_description: str
) -> str:
    noun = "proof" if solve.verdict == "proved" else "disproof"
    return f"""\
An AI agent settled a conjecture about the OEIS sequence {solve.oeis_id}: it {solve.verdict} the
conjecture stated in {ENTRY_PATH}, and that file contains its accepted {noun}. You are
writing two table cells about this result for a mathematics paper. They will appear in a row
right after this already-written sequence-description cell:

    {solve.oeis_id}: {sequence_description}

Do not repeat information that cell already covers.

1. conjecture: one sentence stating the conjecture.
2. proof_summary: one or two sentences summarizing the {noun}, naming the key ideas.

A Lean 4 toolchain with the full Mathlib source tree ({MATHLIB_SOURCE}) is
available, along with `rg` and `python`. Investigate as much as you find useful.

When ready, call submit_summary. Plain text, LaTeX math allowed.

Context below: the full OEIS record for {solve.oeis_id}, and provenance notes on where the
conjecture was stated.

<oeis_record>
{json.dumps(record, indent=2)}
</oeis_record>

<provenance>
{json.dumps(provenance, indent=2)}
</provenance>
"""


@tool
def submit_sequence() -> Tool:
    async def execute(description: str) -> ToolResult:
        """Submit the sequence description.

        Args:
          description: Description of the sequence, at most about 10 words.
        """
        store().set("summary", {"description": description})
        return "Submitted."

    return execute


@tool
def submit_summary() -> Tool:
    async def execute(conjecture: str, proof_summary: str) -> ToolResult:
        """Submit the two table cells.

        Args:
          conjecture: One sentence stating the conjecture.
          proof_summary: One or two sentences summarizing the proof or disproof.
        """
        store().set("summary", {"conjecture": conjecture, "proof_summary": proof_summary})
        return "Submitted."

    return execute


@solver
def summarizer(kind: Literal["sequence", "proof"]) -> Solver:
    async def solve(state: TaskState, generate: Generate) -> TaskState:
        if kind == "proof":
            await sandbox().write_file(ENTRY_PATH, state.metadata["proof"])
            tools = [text_editor(), bash(timeout=300)]
            submit = AgentSubmit(
                tool=submit_summary(), name="submit_summary", keep_in_messages=True
            )
        else:
            tools = []
            submit = AgentSubmit(
                tool=submit_sequence(), name="submit_sequence", keep_in_messages=True
            )
        agent = react(
            tools=tools,
            submit=submit,
            compaction=CompactionSummary(threshold=300_000),
        )
        state = await as_solver(agent)(state, generate)

        summary = state.store.get("summary")
        if summary is not None:
            state.output.completion = json.dumps(summary)
        state.completed = True
        return state

    return solve


@task
def summarize_sequences(run_dir: str, token_limit: int = 500_000) -> Task:
    records = load_records()
    oeis_ids = sorted(
        {s.oeis_id for s in solved_samples(_resolve(run_dir))}, key=lambda i: int(i[1:])
    )
    missing = [i for i in oeis_ids if i not in records]
    if missing:
        raise ValueError(f"no OEIS record for {missing} in {RECORDS_PATH}")
    samples = [
        Sample(input=sequence_prompt(i, records[i]), id=i) for i in oeis_ids
    ]
    return Task(
        dataset=MemoryDataset(samples),
        solver=summarizer("sequence"),
        token_limit=token_limit,
    )


@task
def summarize_proofs(run_dir: str, sequences: str, token_limit: int = 500_000) -> Task:
    records = load_records()
    provenance = load_provenance()
    descriptions = {
        row["oeis_id"]: row["description"] for row in _read_jsonl(_resolve(sequences))
    }
    samples = []
    for solve in solved_samples(_resolve(run_dir)):
        if solve.oeis_id not in descriptions:
            raise ValueError(
                f"{sequences} has no description for {solve.oeis_id} "
                f"(needed by {solve.id}); run summarize_sequences first"
            )
        samples.append(
            Sample(
                input=proof_prompt(
                    solve,
                    records[solve.oeis_id],
                    provenance.get(solve.id),
                    descriptions[solve.oeis_id],
                ),
                id=solve.id,
                metadata={
                    "proof": solve.proof,
                    "oeis_id": solve.oeis_id,
                    "verdict": solve.verdict,
                },
            )
        )
    return Task(
        dataset=MemoryDataset(samples),
        solver=summarizer("proof"),
        sandbox=("docker", str(get_agent_compose_file())),
        token_limit=token_limit,
    )
