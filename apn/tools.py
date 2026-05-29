"""Tools available to prover subagents.

Editing is done with Inspect's built-in ``text_editor`` tool (a robust,
model-friendly file editor that operates on the sandbox filesystem). The proof
sketch lives as a file in the sandbox; the model views and edits it with
``text_editor`` and calls ``lean_check`` to compile the file and get Lean
compiler feedback. (The paper's bespoke ``search_replace`` tool is replaced by
``text_editor`` here.)

EVOLVE-region and statement integrity are enforced after the episode by
SafeVerify rather than inside the editor.
"""

from __future__ import annotations

from inspect_ai.tool import Tool, tool
from inspect_ai.util import sandbox

from apn.verifier.base import CompileResult, LeanVerifier


def format_check_feedback(result: CompileResult) -> str:
    """Render compiler output for the ``lean_check`` tool, with a status note."""
    feedback = result.feedback()
    if result.system_error is not None:
        return feedback
    if result.ok and not result.has_sorry:
        feedback += (
            "\n\nThe file compiles with no errors and no remaining `sorry`. "
            "The proof is complete."
        )
    elif result.ok and result.has_sorry:
        feedback += "\n\nThe file compiles, but it still contains `sorry`."
    return feedback


@tool
def lean_check(
    verifier: LeanVerifier, path: str, sandbox_name: str | None = None
) -> Tool:
    """Build a tool that compiles the proof file and returns Lean feedback."""

    async def execute() -> str:
        """Compile the current Lean proof file and return the compiler feedback.

        Call this after editing the file with the text editor to see compilation
        errors and whether any `sorry` remains. The execution environment already
        imports Mathlib, so `import` lines are ignored.

        Returns:
            The Lean compiler messages, plus a note on whether the proof is
            complete.
        """
        code = await sandbox(sandbox_name).read_file(path)
        result = await verifier.compile(code)
        return format_check_feedback(result)

    return execute
