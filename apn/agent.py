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
from inspect_ai.model import get_model
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import Tool, ToolError, ToolResult, bash, text_editor, tool
from inspect_ai.util import sandbox

from apn.checker import SafeVerifyChecker
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


@tool
def gated_submit(checker: SafeVerifyChecker, target: str, proof_path: str) -> Tool:
    """A submit tool that runs SafeVerify and only accepts a valid proof.

    On a passing submission the tool returns normally and the agent loop ends.
    On a (clean) verification failure it raises ``ToolError``; the react loop
    does not treat an errored tool call as a submission, so the agent is forced
    to keep working until it produces a valid proof or hits a limit.

    The verifier's output is deliberately withheld -- the agent is told only that
    verification failed -- so it cannot probe SafeVerify for gaps to exploit. An
    *infrastructure* failure of SafeVerify (the checker raising) propagates rather
    than becoming a ``ToolError``, so it crashes the sample instead of being
    silently treated as a rejection.

    Args:
        checker: The SafeVerify checker (pointed at the trusted scorer sandbox).
        target: The original spec the submission must implement (verbatim).
        proof_path: Path of the agent's proof file in its workspace sandbox.
    """

    async def execute() -> ToolResult:
        """Submit the proof for verification. Takes no arguments: your edited
        file is the submission. It is accepted only if verification passes; if
        it fails you must keep working (the verifier's output is not shown)."""
        submission = await sandbox().read_file(proof_path)
        outcome = await checker.check(target, submission)
        if outcome.ok:
            return "Submission accepted: verification passed."
        raise ToolError(
            "Verification failed: your submission was not accepted. Keep working "
            "to find a correct, complete proof. (The verifier's output is not "
            "disclosed.)"
        )

    return execute


@solver
def lean_prover(
    verifier: LeanVerifier,
    model: str | None = None,
    gate: SafeVerifyChecker | None = None,
) -> Solver:
    """Prove the sample's theorem with a ``deepagent``.

    Reads the initial Lean file from ``metadata['sketch']`` (else the sample
    input), writes it into the sandbox, runs the agent, and stores the final
    file contents under ``final_proof`` for the scorer.

    Args:
        verifier: In-loop compiler for the ``lean_check`` tool.
        model: Optional model override for the agent.
        gate: If provided, enables *gated submit*: a submission is verified with
            this SafeVerify checker and only accepted if it passes; a failed
            submission forces the agent to keep working (until a limit). If
            ``None``, ``submit`` simply ends the loop and validation happens
            afterwards in the scorer.
    """

    async def solve(state: TaskState, generate: Generate) -> TaskState:
        sketch = state.metadata.get("sketch") or state.input_text
        await sandbox().write_file(PROOF_PATH, sketch)

        submit_tool = (
            gated_submit(gate, sketch, PROOF_PATH) if gate is not None else submit()
        )
        agent = deepagent(
            tools=[
                text_editor(),
                lean_check(verifier, PROOF_PATH),
                # Shell access to the workspace image, so the agent can run
                # `python3` to explore numerically (compute sequence terms,
                # check small cases) before committing to a Lean proof.
                bash(timeout=120),
            ],
            instructions=LEAN_INSTRUCTIONS,
            memory=False,
            submit=AgentSubmit(tool=submit_tool, name="submit"),
            model=get_model(model) if model is not None else None,
        )
        try:
            state.output = (await run(agent, render_task(PROOF_PATH))).output
        finally:
            # Capture whatever the agent left in the file -- even if a token/time
            # limit interrupted it mid-loop (this block then runs during exception
            # unwinding, before the limit propagates on), so a complete proof the
            # agent finished but never `submit`ted still counts. read_file isn't
            # gated by the token limit, and the file was written at the start, so
            # this normally succeeds; a genuine read failure is a real sandbox
            # problem and should error the sample rather than be masked by
            # silently substituting the unproven sketch. The proof itself is read
            # from the store by the scorer (not from state.output).
            final_proof = await sandbox().read_file(PROOF_PATH)
            state.store.set("final_proof", final_proof)

        state.completed = True
        return state

    return solve
