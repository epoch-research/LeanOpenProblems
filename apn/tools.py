"""Tools for the proving agent.

Editing is done with Inspect's built-in ``text_editor`` tool; the only custom
tool is ``lean_check``, which compiles the proof file in the sandbox and returns
the Lean compiler feedback. Statement integrity and the axiom guard are enforced
by SafeVerify at scoring time, not inside the tools.
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
