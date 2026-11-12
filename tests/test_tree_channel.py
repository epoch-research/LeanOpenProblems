from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Any, Awaitable, Callable

import pytest
from inspect_ai import Task, eval_async
from inspect_ai.agent import Agent, AgentState, agent
from inspect_ai.dataset import Sample
from inspect_ai.event import InfoEvent
from inspect_ai.tool import Tool, ToolDef, ToolError
from inspect_swarm import MemberInfo, leaderless, member, swarm, swarm_tools

from apn.solver import swarm_member_names, swarm_tree
from apn.tree_channel import tree

PARENTS: dict[str, str | None] = {
    "root": None,
    "mgr": "root",
    "leaf-a": "mgr",
    "leaf-b": "mgr",
}


def test_swarm_tree_of_32_with_5_managers() -> None:
    parents = swarm_tree(32, 5)
    assert len(parents) == 32
    assert [name for name, parent in parents.items() if parent is None] == ["root"]
    assert [name for name, parent in parents.items() if parent == "root"] == [
        f"mgr-{m}" for m in range(1, 6)
    ]
    leaves = Counter(p for p in parents.values() if p is not None and p != "root")
    assert sorted(leaves.values()) == [5, 5, 5, 5, 6]
    assert sum(leaves.values()) == 26
    assert swarm_member_names(32, 5) == list(parents)


def test_swarm_tree_needs_a_leaf_per_manager() -> None:
    with pytest.raises(ValueError, match="one leaf per manager"):
        swarm_tree(10, 5)


@pytest.mark.parametrize(
    "parents,error",
    [
        ({"a": None, "b": None}, "exactly one root"),
        ({"a": None, "b": "c"}, "not in the tree"),
        ({"a": None, "b": "c", "c": "b"}, "cycle"),
    ],
)
def test_tree_rejects_a_non_tree(parents: dict[str, str | None], error: str) -> None:
    with pytest.raises(ValueError, match=error):
        tree(parents)


def test_tree_rejects_a_roster_that_differs_from_the_tree() -> None:
    with pytest.raises(ValueError, match="same members"):
        tree(PARENTS).check([MemberInfo(name, None) for name in ("root", "mgr")])


def test_each_member_is_shown_the_whole_tree_and_its_place_in_it() -> None:
    channel = tree(PARENTS)
    root = channel.instructions(MemberInfo("root", None))
    mgr = channel.instructions(MemberInfo("mgr", None))
    leaf = channel.instructions(MemberInfo("leaf-a", None))
    assert root is not None and mgr is not None and leaf is not None
    for text in (root, mgr, leaf):
        assert (
            "The swarm's 4 members are organised as a tree of height 2, with root at "
            "the top (1 at depth 0, 1 at depth 1, 2 at depth 2)."
        ) in text
    assert "\n\nroot\n  mgr\n    leaf-a  <- you\n    leaf-b\n\n" in leaf
    assert "\n\nroot  <- you\n  mgr\n    leaf-a\n    leaf-b\n\n" in root
    assert "You are the root: you have no manager. Your direct reports are mgr." in root
    assert (
        "You are mgr, at depth 1. Your manager is root. "
        "Your direct reports are leaf-a, leaf-b."
    ) in mgr
    assert (
        "You are leaf-a, at depth 2. Your manager is mgr. You have no direct reports."
    ) in leaf


Script = Callable[[dict[str, Tool]], Awaitable[None]]
RESULTS: dict[str, list[str]] = {}


async def _read_until(tools: dict[str, Tool], name: str) -> str:
    for _ in range(50):
        await tools["swarm_wait"]()
        text = str(await tools["read_messages"]())
        if text != "No unread messages.":
            RESULTS[name].append(text)
            return text
    raise AssertionError(f"{name} never received a message")


async def _leaf_a(tools: dict[str, Tool]) -> None:
    RESULTS["leaf-a"].append(str(await tools["send_message"](["mgr"], "up from a")))
    for to in (["root"], ["leaf-b"], ["mgr", "root"]):
        with pytest.raises(ToolError, match="only your manager and direct reports"):
            await tools["send_message"](to, "skip")
    await _read_until(tools, "leaf-a")


async def _mgr(tools: dict[str, Tool]) -> None:
    await _read_until(tools, "mgr")
    await tools["send_message"](["root"], "summary for root")
    await tools["send_message"](["leaf-a", "leaf-b"], "down to leaves")


async def _root(tools: dict[str, Tool]) -> None:
    await _read_until(tools, "root")


async def _leaf_b(tools: dict[str, Tool]) -> None:
    await _read_until(tools, "leaf-b")


SCRIPTS: dict[str, Script] = {
    "root": _root,
    "mgr": _mgr,
    "leaf-a": _leaf_a,
    "leaf-b": _leaf_b,
}


@agent
def scripted(script: str) -> Agent:
    async def execute(state: AgentState) -> AgentState:
        tools = {ToolDef(t).name: t for t in await swarm_tools().tools()}
        await SCRIPTS[script](tools)
        return state

    return execute


async def test_messages_flow_only_along_tree_edges(tmp_path: Path) -> None:
    RESULTS.clear()
    RESULTS.update({name: [] for name in PARENTS})
    [log] = await eval_async(
        Task(
            dataset=[Sample(input="task")],
            solver=swarm(
                [member(scripted, name=name, args={"script": name}) for name in PARENTS],
                controller=leaderless(stop_on_submission=False),
                channels=[tree(PARENTS)],
            ),
        ),
        model="mockllm/model",
        log_dir=str(tmp_path),
    )
    assert log.status == "success", log.error

    assert RESULTS["leaf-a"][0] == "Sent m-1 to mgr."
    assert RESULTS["mgr"] == ['<message id="m-1" from="leaf-a">\nup from a\n</message>']
    assert RESULTS["root"] == [
        '<message id="m-5" from="mgr">\nsummary for root\n</message>'
    ]
    for leaf in ("leaf-a", "leaf-b"):
        assert RESULTS[leaf][-1] == (
            '<message id="m-6" from="mgr">\ndown to leaves\n</message>'
        )

    assert log.samples is not None
    sent: list[dict[str, Any]] = [
        e.data
        for e in log.samples[0].events
        if isinstance(e, InfoEvent)
        and e.source == "inspect_swarm"
        and isinstance(e.data, dict)
        and e.data["type"] == "comm"
        and e.data["kind"] == "sent"
    ]
    refused = [s for s in sent if s["rejected"] is not None]
    assert [(s["member"], s["record"]["recipients"]) for s in refused] == [
        ("leaf-a", ["root"]),
        ("leaf-a", ["leaf-b"]),
        ("leaf-a", ["mgr", "root"]),
    ]
    assert {s["rejected"]["control"] for s in refused} == {"admit"}
