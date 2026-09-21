
from __future__ import annotations

from inspect_ai.tool import Tool, tool
from inspect_ai.util import sandbox


@tool(name="bash")
def bash(
    timeout: int | None = None,
    user: str | None = None,
    sandbox_name: str | None = None,
) -> Tool:

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
