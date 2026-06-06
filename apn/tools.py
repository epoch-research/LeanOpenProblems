"""Tools for the proving agent.

Editing is done with Inspect's built-in ``text_editor`` tool. ``bash`` gives the
agent a shell in the workspace where PyPantograph is installed and the Mathlib +
FormalConjectures oleans are baked into the image, so it can drive
``pantograph.Server`` from Python directly. On the *agent-corpus* image the
shell also has an offline arXiv-math corpus baked in at ``/corpus`` (built by
``apn/lean/build_corpus.py``), which the agent searches with plain ``rg``/``cat``
-- no bespoke tool. Statement integrity and the axiom guard are enforced by
SafeVerify at scoring time, not inside the tools.
"""

from __future__ import annotations

from inspect_ai.tool import Tool, tool
from inspect_ai.util import sandbox


@tool(name="bash")
def bash(
    timeout: int | None = None,
    user: str | None = None,
    sandbox_name: str | None = None,
) -> Tool:
    """Bash tool that surfaces the exit status to the agent on failure.

    Equivalent to ``inspect_ai.tool.bash`` on success (stdout, with stderr
    prepended if any). On a non-zero exit -- which the built-in tool would
    silently swallow -- the agent gets stdout, stderr, and the raw returncode
    each in pseudo-XML tags so the model sees the streams separately and knows
    the command failed. Interpreting specific codes (137 = SIGKILL/OOM,
    127 = command not found, ...) is left to the model.
    """

    async def execute(command: str) -> str:
        """
        Use this function to execute bash commands.

        Args:
          command: The bash command to execute.

        Returns:
          The output of the command.
        """
        result = await sandbox(sandbox_name).exec(
            cmd=["bash", "--login", "-c", command], timeout=timeout, user=user
        )
        if result.returncode == 0:
            # Mimic inspect_ai.tool.bash, which just concatenates
            # stderr and stdout.
            output = ""
            if result.stderr:
                output = f"{result.stderr}\n"
            return f"{output}{result.stdout}"
        return (
            f"<stdout>{result.stdout}</stdout>\n"
            f"<stderr>{result.stderr}</stderr>\n"
            f"<returncode>{result.returncode}</returncode>"
        )

    return execute

