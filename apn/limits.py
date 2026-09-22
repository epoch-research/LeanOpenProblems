from __future__ import annotations

from inspect_ai.agent import AgentContinue, AgentState
from inspect_boltons.limits import NoToolCallLimit, RepeatedTextLimit

UNPRODUCTIVE_LOOP_LIMITS = (
    NoToolCallLimit(turns=100, unproductive_tools=["resources"]),
    RepeatedTextLimit(turns=30),
)


def continue_unless_looping(message: str) -> AgentContinue:
    async def on_continue(state: AgentState) -> bool | str:
        for limit in UNPRODUCTIVE_LOOP_LIMITS:
            limit.check(state)
        if state.output.message.tool_calls:
            return True
        return message

    return on_continue
