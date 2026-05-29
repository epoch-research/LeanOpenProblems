"""Tools available to prover subagents.

The basic agent's only tool is ``search_replace``: the model proposes edits to
the current proof sketch as find/replace pairs (a compact diff format that
scales to large Lean files), and each edit is applied and recompiled so the
model gets compiler feedback on the next turn.
"""

from __future__ import annotations

from dataclasses import dataclass

from inspect_ai.tool import Tool, ToolError, tool

from apn.sketch import ProofSketch, SearchReplaceError
from apn.verifier.base import CompileResult, LeanVerifier


@dataclass
class EpisodeState:
    """Mutable state threaded through a single proving episode.

    The ``search_replace`` tool reads and updates this; the agent reads the
    final ``sketch`` once the episode's LLM session ends.
    """

    sketch: ProofSketch
    verifier: LeanVerifier
    max_edits: int = 90
    edits: int = 0
    last_compile: CompileResult | None = None


@tool
def search_replace(state: EpisodeState) -> Tool:
    """Build a ``search_replace`` tool bound to an episode's mutable state."""

    async def execute(search: str, replace: str) -> str:
        """Edit the current Lean proof, then compile and return the feedback.

        Finds the single occurrence of `search` in the current proof and
        replaces it with `replace`. The match must occur exactly once and lie
        entirely within an `-- EVOLVE-BLOCK-START`/`-- EVOLVE-BLOCK-END` or
        `-- EVOLVE-VALUE-START`/`-- EVOLVE-VALUE-END` region; edits elsewhere are
        rejected so the target theorem statement cannot change. After applying
        the edit the Lean compiler runs and its messages are returned. The edit
        is kept even if it does not compile, so you can fix errors with further
        edits.

        Args:
            search: The exact existing text to find. Include enough surrounding
                context that it appears exactly once in the file.
            replace: The text to substitute in its place.

        Returns:
            Lean compiler feedback after applying the edit.
        """
        if state.edits >= state.max_edits:
            raise ToolError(
                f"Edit budget exhausted ({state.max_edits} edits this episode). "
                "Make sure the file compiles and wrap up."
            )
        try:
            new_sketch = state.sketch.apply_search_replace(search, replace)
        except SearchReplaceError as exc:
            raise ToolError(str(exc))
        compiled = await state.verifier.compile(new_sketch.text)
        state.sketch = new_sketch
        state.edits += 1
        state.last_compile = compiled
        return compiled.feedback()

    return execute
