from __future__ import annotations

import pytest
from inspect_ai.agent import AgentState
from inspect_ai.model import ChatMessage, ChatMessageAssistant, ChatMessageTool, ChatMessageUser
from inspect_ai.tool import ToolCall
from inspect_ai.util import LimitExceededError

from apn.limits import continue_unless_looping

CONTINUE = "Continue working on the problem."


def _text(content: str) -> ChatMessageAssistant:
    return ChatMessageAssistant(content=content)


def _tool_call() -> list[ChatMessage]:
    return [
        ChatMessageAssistant(
            content="", tool_calls=[ToolCall(id="c", function="bash", arguments={})]
        ),
        ChatMessageTool(content="ok", tool_call_id="c", function="bash"),
    ]


def _state(*messages: ChatMessage) -> AgentState:
    return AgentState(messages=[ChatMessageUser(content="go"), *messages])


def _no_tool_turns(n: int) -> list[ChatMessage]:
    return [_text(f"Thinking about step {i}.") for i in range(n)]


async def test_plays_back_message_only_when_no_tool_call() -> None:
    on_continue = continue_unless_looping(CONTINUE)
    assert await on_continue(_state(_text("Hmm."))) == CONTINUE
    assert await on_continue(_state(*_tool_call())) is True


async def test_stops_after_100_turns_without_tool_call() -> None:
    on_continue = continue_unless_looping(CONTINUE)
    assert await on_continue(_state(*_tool_call(), *_no_tool_turns(99))) == CONTINUE
    with pytest.raises(LimitExceededError) as excinfo:
        await on_continue(_state(*_tool_call(), *_no_tool_turns(100)))
    assert excinfo.value.type == "custom"
    assert excinfo.value.limit == 100


async def test_stops_after_30_turns_of_identical_text() -> None:
    on_continue = continue_unless_looping(CONTINUE)
    repeated = [_text("Still working.") for _ in range(30)]
    assert await on_continue(_state(*repeated[:-1])) == CONTINUE
    with pytest.raises(LimitExceededError) as excinfo:
        await on_continue(_state(*repeated))
    assert excinfo.value.type == "custom"
    assert excinfo.value.limit == 30


async def test_tool_call_resets_both_counts() -> None:
    on_continue = continue_unless_looping(CONTINUE)
    repeated = [_text("Still working.") for _ in range(29)]
    state = _state(*repeated, *_tool_call(), _text("Still working."))
    assert await on_continue(state) == CONTINUE
