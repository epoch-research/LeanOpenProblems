"""Inspect tasks for generating normalized OEIS metadata.

The sequence and conjecture tasks are run once for the Lite dataset. A concise
summary and a full natural-language proof or disproof are generated independently
for each accepted result in an evaluation run. Deterministic collection into
``metadata/*.json`` and per-sample ``metadata.json`` files is handled by
``collect.py``.

Examples::

    inspect eval scripts/summarize/task.py@summarize_sequences \
        -T subset=lite --model openai/gpt-5.6-sol --log-dir logs/summarize
    inspect eval scripts/summarize/task.py@summarize_conjectures \
        -T subset=lite -T metadata_dir=metadata \
        --model openai/gpt-5.6-sol --log-dir logs/summarize
    inspect eval scripts/summarize/task.py@summarize_proofs \
        -T run_dir=logs/<run> -T subset=lite -T metadata_dir=metadata \
        --model openai/gpt-5.6-sol --log-dir logs/summarize
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Literal, NamedTuple

from inspect_ai import Task, task
from inspect_ai.agent import AgentSubmit, as_solver, react
from inspect_ai.dataset import MemoryDataset, Sample
from inspect_ai.model import CompactionSummary
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolResult, text_editor, tool
from inspect_ai.util import sandbox, store

import apn
from apn.dataset import OEIS_DIR, fc_commit, load_subset, oeis_dataset
from apn.layout import ENTRY_PATH
from apn.task import COMPOSE_FILES_DIR, IMAGE_REPOSITORY, get_identifier_for_image
from apn.tools import bash

REPO_ROOT = Path(__file__).resolve().parents[2]
OEIS_DATA = Path(apn.__file__).parent / "data" / "oeis"
OEIS_METADATA = OEIS_DATA / "metadata"
RECORDS_PATH = OEIS_METADATA / "snapshots" / "oeis_records.jsonl"
PROVENANCE_PATH = OEIS_METADATA / "derived" / "provenance.jsonl"
MATHLIB_SOURCE = "/workspace/leanproject/.lake/packages/mathlib/"


def get_agent_compose_file() -> Path:
    """Return a network-isolated compose file for a locally built agent image."""
    image_context = Path(apn.__file__).parent / "lean"
    oeis_fc_commit = fc_commit(OEIS_DIR)
    content = f"""
services:
  default:
    image: {IMAGE_REPOSITORY}:{get_identifier_for_image("agent", oeis_fc_commit)}
    build:
      context: {image_context}
      target: agent
      args:
        FC_COMMIT: {oeis_fc_commit}
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


def _resolve(path: str | Path) -> Path:
    """Resolve task arguments relative to the repository root."""
    value = Path(path)
    return value if value.is_absolute() else REPO_ROOT / value


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def _read_json_object(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"warning: cannot read {path}: {exc}", file=sys.stderr)
        return None
    if not isinstance(value, dict):
        print(f"warning: expected a JSON object in {path}", file=sys.stderr)
        return None
    return value


def load_records() -> dict[str, dict[str, Any]]:
    return {row["oeis_id"]: row["record"] for row in _read_jsonl(RECORDS_PATH)}


def load_provenance() -> dict[str, dict[str, Any]]:
    return {row["theorem_name"]: row for row in _read_jsonl(PROVENANCE_PATH)}


class Conjecture(NamedTuple):
    id: str
    oeis_id: str | None
    sketch: str


class Solve(NamedTuple):
    id: str
    oeis_id: str
    proof: str
    settlement: Literal["proved", "disproved"]
    directory: Path


class ProofOutput(NamedTuple):
    name: str
    field: str
    submit_tool: str
    instruction: str


# The full-proof suggestion is deliberately not a limit: informal proofs in the
# paper's appendix reach roughly 2,000 words.
PROOF_OUTPUTS = (
    ProofOutput(
        name="summary",
        field="proof_summary",
        submit_tool="submit_proof_summary",
        instruction=(
            "one or two concise sentences explaining the key mathematical "
            "ideas of this specific {noun}. Do not restate the sequence or "
            "conjecture"
        ),
    ),
    ProofOutput(
        name="full_proof",
        field="full_proof",
        submit_tool="submit_full_proof",
        instruction=(
            "a complete, self-contained natural-language {noun} with every "
            "essential construction, intermediate result, reduction, and case "
            "split explained. There is no maximum length: use as much space as "
            "the argument needs. For example, a 3,000-word exposition is entirely "
            "acceptable if that is what a clear proof requires. This must be "
            "the full mathematical argument, not a synopsis or an expanded "
            "summary; introduce the necessary notation and explain how every "
            "substantive step follows"
        ),
    ),
)


def subset_conjectures(subset: str) -> list[Conjecture]:
    """Return the subset's conjectures in its authoritative order."""
    names = load_subset(OEIS_DIR, subset)
    samples = {str(sample.id): sample for sample in oeis_dataset(names=names)}
    conjectures: list[Conjecture] = []
    for name in names:
        sample = samples.get(name)
        if sample is None:
            print(f"warning: {name} is absent from the OEIS dataset", file=sys.stderr)
            continue
        metadata = sample.metadata or {}
        oeis_id = metadata.get("oeis_id")
        sketch = metadata.get("sketch")
        conjectures.append(
            Conjecture(
                id=name,
                oeis_id=str(oeis_id) if oeis_id else None,
                sketch=str(sketch) if sketch else str(sample.input),
            )
        )
    return conjectures


def plaintext_dir(run_dir: Path) -> Path:
    matches = sorted(path for path in run_dir.glob("*_plaintext") if path.is_dir())
    if len(matches) != 1:
        raise ValueError(
            f"expected exactly one *_plaintext dir under {run_dir}, found {len(matches)}"
        )
    return matches[0]


def solved_samples(run_dir: Path) -> list[Solve]:
    """Read accepted proofs, skipping incomplete or malformed sample data."""
    solves: list[Solve] = []
    for sample_dir in sorted(plaintext_dir(run_dir).iterdir()):
        if not sample_dir.is_dir():
            continue

        scores = _read_json_object(sample_dir / "scores.json")
        score = (scores or {}).get("proof_scorer")
        if not isinstance(score, dict):
            print(f"warning: no proof_scorer score for {sample_dir.name}", file=sys.stderr)
            continue
        if score.get("value") != "C":
            continue

        info = _read_json_object(sample_dir / "info.json")
        oeis_id = (info or {}).get("oeis_id")
        if not oeis_id:
            print(f"warning: no oeis_id for accepted sample {sample_dir.name}", file=sys.stderr)
            continue

        proof_path = sample_dir / "Submission" / "Spec.lean"
        try:
            proof = proof_path.read_text()
        except OSError as exc:
            print(f"warning: cannot read accepted proof {proof_path}: {exc}", file=sys.stderr)
            continue

        solves.append(
            Solve(
                id=sample_dir.name,
                oeis_id=str(oeis_id),
                proof=proof,
                settlement="disproved" if ".disproof" in proof else "proved",
                directory=sample_dir,
            )
        )
    return solves


def _load_metadata(path: Path) -> dict[str, dict[str, Any]]:
    value = _read_json_object(path)
    if value is None:
        return {}
    return {key: item for key, item in value.items() if isinstance(item, dict)}


def sequence_prompt(oeis_id: str, record: dict[str, Any]) -> str:
    return f"""\
Write a short description of the OEIS sequence {oeis_id} for a public data catalog.
The full OEIS record is below.

Call submit_sequence with a description of at most about 10 words. Describe the
sequence itself, not a conjecture about it. Plain text with LaTeX math is allowed.

<oeis_record>
{json.dumps(record, indent=2)}
</oeis_record>
"""


def conjecture_prompt(
    conjecture: Conjecture,
    record: dict[str, Any],
    provenance: dict[str, Any] | None,
    sequence_description: str | None,
) -> str:
    return f"""\
Write one concise sentence stating the conjecture {conjecture.id} about OEIS
sequence {conjecture.oeis_id}. This is canonical conjecture metadata, independent
of whether any particular model solved it.

The conjecture sentence will be displayed immediately after this separate
sequence-description field:

<sequence_description>
{sequence_description or "(unavailable)"}
</sequence_description>

Do not repeat or paraphrase that sequence description, its defining formula, or
its OEIS identifier. State only the conjectured property, using a(n) directly
when the sequence description already defines it. For example, prefer "For every
prime ..." over "For the sequence a(n)=..., every prime ...".

Call submit_conjecture with the sentence. Plain text with LaTeX math is allowed.

<lean_statement>
{conjecture.sketch}
</lean_statement>

<oeis_record>
{json.dumps(record, indent=2)}
</oeis_record>

<provenance>
{json.dumps(provenance, indent=2)}
</provenance>
"""


def proof_prompt(
    solve: Solve,
    record: dict[str, Any],
    provenance: dict[str, Any] | None,
    sequence_description: str | None,
    conjecture_description: str | None,
    output: ProofOutput,
) -> str:
    noun = "proof" if solve.settlement == "proved" else "disproof"
    output_label = output.name.replace("_", " ")
    instruction = output.instruction.format(noun=noun)
    return f"""\
An AI agent {solve.settlement} the conjecture {solve.id} about OEIS sequence
{solve.oeis_id}. The accepted {noun} is in {ENTRY_PATH}.

Call {output.submit_tool} with {instruction}.

Focus exclusively on the mathematical argument: omit Lean tactics, internal
library-lemma names, proof-assistant architecture, implementation details, and
claims that a computation is "kernel-checked", "verified", or "certified"
merely because it was formalized. State the mathematical content of any invoked
result and describe each finite or modular computation by its mathematical role.

Examples of the intended style:
- "a kernel-checked finite avoidance computation" becomes
  "a finite avoidance computation";
- "a verified bit-sieve" becomes "a bit-sieve";

Plain text with LaTeX math is allowed.

<canonical_sequence_description>
{sequence_description or "(unavailable)"}
</canonical_sequence_description>

<canonical_conjecture_description>
{conjecture_description or "(unavailable)"}
</canonical_conjecture_description>

A Lean 4 toolchain with the full Mathlib source tree ({MATHLIB_SOURCE}) is
available, along with `rg` and `python`. Investigate the accepted {noun} as much
as useful before writing the requested {output_label}.

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
        """Submit a short description of the OEIS sequence.

        Args:
          description: Description of the sequence, at most about 10 words.
        """
        store().set("submission", {"description": description})
        return "Submitted."

    return execute


@tool
def submit_conjecture() -> Tool:
    async def execute(conjecture: str) -> ToolResult:
        """Submit a concise statement of the conjecture.

        Args:
          conjecture: One sentence stating the conjecture.
        """
        store().set("submission", {"conjecture": conjecture})
        return "Submitted."

    return execute


@tool
def submit_proof_summary() -> Tool:
    async def execute(proof_summary: str) -> ToolResult:
        """Submit the requested summary of the accepted proof or disproof.

        Args:
          proof_summary: Summary respecting the length requested in the prompt.
        """
        store().set("submission", {"proof_summary": proof_summary})
        return "Submitted."

    return execute


@tool
def submit_full_proof() -> Tool:
    async def execute(full_proof: str) -> ToolResult:
        """Submit the full exposition of the accepted proof or disproof.

        Args:
          full_proof: Complete natural-language proof with no maximum length.
        """
        store().set("submission", {"full_proof": full_proof})
        return "Submitted."

    return execute


@solver
def summarizer(kind: Literal["sequence", "conjecture", "proof"]) -> Solver:
    async def solve(state: TaskState, generate: Generate) -> TaskState:
        if kind == "proof":
            await sandbox().write_file(ENTRY_PATH, state.metadata["proof"])
            tools = [text_editor(), bash(timeout=300)]
            proof_output = state.metadata["proof_output"]
            if proof_output == "full_proof":
                submit = AgentSubmit(
                    tool=submit_full_proof(),
                    name="submit_full_proof",
                    keep_in_messages=True,
                )
            elif proof_output == "summary":
                submit = AgentSubmit(
                    tool=submit_proof_summary(),
                    name="submit_proof_summary",
                    keep_in_messages=True,
                )
            else:
                raise ValueError(f"unknown proof output: {proof_output!r}")
        elif kind == "conjecture":
            tools = []
            submit = AgentSubmit(
                tool=submit_conjecture(),
                name="submit_conjecture",
                keep_in_messages=True,
            )
        else:
            tools = []
            submit = AgentSubmit(
                tool=submit_sequence(),
                name="submit_sequence",
                keep_in_messages=True,
            )

        agent = react(
            tools=tools,
            submit=submit,
            compaction=CompactionSummary(threshold=300_000),
        )
        state = await as_solver(agent)(state, generate)

        submission = state.store.get("submission")
        if submission is not None:
            state.output.completion = json.dumps(submission)
        state.completed = True
        return state

    return solve


@task
def summarize_sequences(subset: str = "lite", token_limit: int = 500_000) -> Task:
    records = load_records()
    oeis_ids = sorted(
        {item.oeis_id for item in subset_conjectures(subset) if item.oeis_id},
        key=lambda value: int(value[1:]),
    )
    samples = []
    for oeis_id in oeis_ids:
        record = records.get(oeis_id)
        if record is None:
            print(f"warning: no OEIS record for {oeis_id}", file=sys.stderr)
            continue
        samples.append(
            Sample(
                input=sequence_prompt(oeis_id, record),
                id=oeis_id,
                metadata={"oeis_id": oeis_id},
            )
        )
    return Task(
        dataset=MemoryDataset(samples),
        solver=summarizer("sequence"),
        token_limit=token_limit,
    )


@task
def summarize_conjectures(
    subset: str = "lite",
    metadata_dir: str = "metadata",
    token_limit: int = 500_000,
) -> Task:
    records = load_records()
    provenance = load_provenance()
    sequences = _load_metadata(_resolve(metadata_dir) / "sequences.json")
    samples = []
    for conjecture in subset_conjectures(subset):
        record = records.get(conjecture.oeis_id or "", {})
        sequence = sequences.get(conjecture.oeis_id or "") or {}
        samples.append(
            Sample(
                input=conjecture_prompt(
                    conjecture,
                    record,
                    provenance.get(conjecture.id),
                    sequence.get("description"),
                ),
                id=conjecture.id,
                metadata={"oeis_id": conjecture.oeis_id},
            )
        )
    return Task(
        dataset=MemoryDataset(samples),
        solver=summarizer("conjecture"),
        token_limit=token_limit,
    )


@task
def summarize_proofs(
    run_dir: str,
    subset: str = "lite",
    metadata_dir: str = "metadata",
    token_limit: int = 500_000,
) -> Task:
    records = load_records()
    provenance = load_provenance()
    metadata_root = _resolve(metadata_dir)
    sequences = _load_metadata(metadata_root / "sequences.json")
    conjectures = _load_metadata(metadata_root / "conjectures.json")

    allowed = {conjecture.id for conjecture in subset_conjectures(subset)}
    samples = []
    for solve in solved_samples(_resolve(run_dir)):
        if solve.id not in allowed:
            continue
        sequence = sequences.get(solve.oeis_id) or {}
        conjecture = conjectures.get(solve.id) or {}
        for output in PROOF_OUTPUTS:
            samples.append(
                Sample(
                    input=proof_prompt(
                        solve,
                        records.get(solve.oeis_id, {}),
                        provenance.get(solve.id),
                        sequence.get("description"),
                        conjecture.get("conjecture"),
                        output,
                    ),
                    id=f"{solve.id}__{output.name}",
                    metadata={
                        "proof": solve.proof,
                        "proof_id": solve.id,
                        "oeis_id": solve.oeis_id,
                        "settlement": solve.settlement,
                        "proof_output": output.name,
                    },
                )
            )
    return Task(
        dataset=MemoryDataset(samples),
        solver=summarizer("proof"),
        sandbox=("docker", str(get_agent_compose_file())),
        token_limit=token_limit,
    )
