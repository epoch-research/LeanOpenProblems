"""The Lean-proving solver: a thin wrapper around Inspect's ``deepagent``.

The agent is given the proof file in the sandbox plus two tools -- the built-in
``text_editor`` to edit it and ``lean_check`` to compile it -- and left to prove
the theorem. There is no bespoke episode/subagent orchestration: ``deepagent``
runs its own loop and submits when done. Run several independent attempts per
problem by passing ``--epochs N`` at eval time; each epoch is a fresh sample run
with its own sandbox.
"""

from __future__ import annotations

from inspect_ai.agent import AgentSubmit, deepagent, run
from inspect_ai.model import ModelOutput, get_model
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolResult, text_editor, tool
from inspect_ai.util import sandbox

from apn.prompts import LEAN_INSTRUCTIONS, render_task
from apn.tools import lean_check
from apn.verifier.base import LeanVerifier

# Path of the proof file inside the sample's sandbox.
PROOF_PATH = "/tmp/apn_proof.lean"


@tool
def submit() -> Tool:
    """A no-argument submit tool.

    The proof is the edited file, not a text answer, so submitting takes no
    arguments -- the model just signals it is done.
    """

    async def execute() -> ToolResult:
        """Submit the proof for verification.

        Call this once the file compiles with no remaining `sorry`. Takes no
        arguments: your edited file is the submission.
        """
        return "Submitted."

    return execute


@solver
def lean_prover(verifier: LeanVerifier, model: str | None = None) -> Solver:
    """Prove the sample's theorem with a ``deepagent``.

    Reads the initial Lean file from ``metadata['sketch']`` (else the sample
    input), writes it into the sandbox, runs the agent, and stores the final
    file contents under ``final_proof`` for the scorer.
    """

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        sketch = state.metadata.get("sketch") or state.input_text
        await sandbox().write_file(PROOF_PATH, sketch)

        agent = deepagent(
            tools=[text_editor(), lean_check(verifier, PROOF_PATH)],
            instructions=LEAN_INSTRUCTIONS,
            memory=False,
            submit=AgentSubmit(tool=submit(), name="submit"),
            model=get_model(model) if model is not None else None,
        )
        try:
            await run(agent, render_task(PROOF_PATH))
        finally:
            # Always capture whatever the agent left in the file -- even if a
            # token/time limit interrupted it mid-loop (in which case this runs
            # during exception unwinding). The scorer then judges the actual
            # file the agent produced rather than seeing nothing. A complete
            # proof that the agent finished but never `submit`ted still counts.
            try:
                final_proof = await sandbox().read_file(PROOF_PATH)
            except Exception:  # noqa: BLE001 - fall back to the original sketch
                final_proof = sketch
            state.store.set("final_proof", final_proof)
            state.output = ModelOutput.from_content(
                model=str(state.model), content=final_proof
            )

        state.completed = True
        return state

    return solve
