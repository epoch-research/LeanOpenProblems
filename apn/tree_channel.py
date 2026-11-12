from __future__ import annotations

import re
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass

from inspect_ai.tool import Tool, ToolDef, ToolError
from inspect_ai.util._span import current_agent_span_id, current_span_id
from inspect_swarm import (
    Channel,
    ChannelRun,
    ChannelState,
    MemberInfo,
    Record,
    WaitNews,
    WaitSpec,
    swarm_channel,
)
from inspect_swarm._bus._record import Draft
from inspect_swarm._bus._storm import StormControls
from inspect_swarm._evidence import comm_read
from inspect_swarm._fence import fence
from pydantic import JsonValue

CHANNEL = "tree"

_MEMBER_NAME = re.compile(r"[a-z][a-z0-9_-]{0,47}")

_SEND_DESCRIPTION = (
    "Send a message to your manager or to one or more of your direct reports. "
    "No other member can be messaged."
)

_READ_DESCRIPTION = (
    "Read the messages sent to you that you have not read yet. Each is shown once."
)


class _Tree(Channel):
    name = CHANNEL
    prefix = "m"
    reach = "loop"

    def __init__(
        self,
        parents: Mapping[str, str | None],
        max_message_bytes: int,
        rate: tuple[int, float] | None,
        max_wait: int,
    ) -> None:
        self.parents = dict(parents)
        self.children: dict[str, list[str]] = {name: [] for name in self.parents}
        for name, parent in self.parents.items():
            if parent is not None:
                self.children[parent].append(name)
        self.storm = StormControls(max_bytes=max_message_bytes, rate=rate)
        self.max_wait = max_wait

    def neighbours(self, name: str) -> list[str]:
        parent = self.parents[name]
        return ([] if parent is None else [parent]) + self.children[name]

    def check(self, roster: Sequence[MemberInfo]) -> None:
        names = [info.name for info in roster]
        for name in names:
            if not _MEMBER_NAME.fullmatch(name):
                raise ValueError(
                    f"tree(): member {name!r} has a name the channel cannot use: names must start with a lowercase letter, followed by at most 47 lowercase letters, digits, _ or -."
                )
        missing = [name for name in names if name not in self.parents]
        extra = [name for name in self.parents if name not in names]
        if missing or extra:
            raise ValueError(
                f"tree(): the tree and the roster must have the same members; not in the tree: {missing}, not in the roster: {extra}."
            )

    def open(self, run: ChannelRun) -> ChannelState | None:
        return _TreeState(self, run)

    def depth(self, name: str) -> int:
        parent = self.parents[name]
        return 0 if parent is None else self.depth(parent) + 1

    def instructions(self, member: MemberInfo) -> str | None:
        name = member.name
        [root] = [n for n, p in self.parents.items() if p is None]
        depths = Counter(self.depth(n) for n in self.parents)
        levels = ", ".join(
            f"{depths[d]} at depth {d}" for d in sorted(depths)
        )
        outline: list[str] = []

        def draw(node: str) -> None:
            mark = "  <- you" if node == name else ""
            outline.append(f"{'  ' * self.depth(node)}{node}{mark}")
            for child in self.children[node]:
                draw(child)

        draw(root)
        parent = self.parents[name]
        children = self.children[name]
        position = [
            f"You are {name}, at depth {self.depth(name)}.",
            "You are the root: you have no manager."
            if parent is None
            else f"Your manager is {parent}.",
            f"Your direct reports are {', '.join(children)}."
            if children
            else "You have no direct reports.",
        ]
        return "\n\n".join(
            [
                f"The swarm's {len(self.parents)} members are organised as a tree of height {max(depths)}, with {root} at the top ({levels}). "
                "Each member below the root has one manager, the member directly above it, and the members directly below a member are its direct reports. "
                "The whole tree, each member indented under its manager:",
                "\n".join(["```", *outline, "```"]),
                " ".join(position),
                "Messages travel only along the tree's edges: you can message only your manager and your direct reports, with `send_message`, and messages to anyone else are refused. "
                "Anything meant for a member further away has to be passed on by each member in between, so a leaf's message reaches the root only if its manager forwards it, and the root reaches a leaf only through that leaf's manager. "
                "Read messages sent to you with `read_messages`, which shows each message once. "
                "To wait for a message rather than polling, call `swarm_wait`.",
            ]
        )


@dataclass(frozen=True)
class _Message:
    id: str
    sender: str
    text: str


class _TreeState:
    def __init__(self, tree: _Tree, run: ChannelRun) -> None:
        self._tree = tree
        self._bus = run.bus
        self._unread: dict[str, list[_Message]] = {info.name: [] for info in run.roster}
        self._tools: list[Tool] | None = None

    def tools(self) -> list[Tool]:
        if self._tools is None:
            self._tools = [self._send_tool(), self._read_tool()]
        return self._tools

    def validate(self, record: Record) -> None:
        if record.kind != "message" or not record.recipients:
            raise ToolError("a message needs at least one recipient")

    def admit(self, record: Record) -> None:
        allowed = self._tree.neighbours(record.sender)
        refused = [name for name in record.recipients if name not in allowed]
        if refused:
            raise ToolError(
                f"you can message only your manager and direct reports ({', '.join(allowed)}); "
                f"{', '.join(refused)} {'is' if len(refused) == 1 else 'are'} not among them."
            )

    def apply(self, record: Record) -> tuple[list[str], Mapping[str, JsonValue] | None]:
        message = _Message(record.id, record.sender, record.payload)
        for name in record.recipients:
            self._unread[name].append(message)
        return list(record.recipients), None

    def wait_check(self, spec: WaitSpec) -> None:
        return None

    def wakes(self, spec: WaitSpec, record: Record) -> bool:
        return spec.member in record.recipients

    def news(self, spec: WaitSpec) -> WaitNews | None:
        unread = self._unread[spec.member]
        if not unread:
            return None
        senders = sorted({m.sender for m in unread})
        count = f"{len(unread)} unread message{'s' if len(unread) > 1 else ''}"
        return WaitNews(
            lines=[
                f"{count} from {', '.join(senders)}. Read them with read_messages()."
            ],
            files=[{"message": m.id, "sender": m.sender} for m in unread],
        )

    def _send_tool(self) -> Tool:
        async def execute(to: list[str], message: str) -> str:
            """Send a message.

            Args:
                to: The recipients: your manager or your direct reports, by name.
                message: The message.
            """
            delivery = await self._bus.deliver(
                Draft(
                    CHANNEL,
                    "message",
                    to=tuple(to),
                    payload=message,
                    wake=True,
                )
            )
            record = delivery.record
            return f"Sent {record.id} to {', '.join(record.recipients)}."

        return ToolDef(
            execute, name="send_message", description=_SEND_DESCRIPTION
        ).as_tool()

    def _read_tool(self) -> Tool:
        async def execute() -> str:
            """Read your unread messages."""
            context = self._bus.member()
            if context is None:
                raise RuntimeError(
                    "The read_messages tool was called outside a member of its swarm."
                )
            unread = self._unread[context.name]
            self._unread[context.name] = []
            if not unread:
                return "No unread messages."
            comm_read(
                context.span_id,
                context.name,
                CHANNEL,
                self._bus.read_id(),
                current_agent_span_id(),
                False,
                current_span_id(),
                [{"message": m.id, "sender": m.sender} for m in unread],
                False,
            )
            return "\n\n".join(
                fence("message", [("id", m.id), ("from", m.sender)], m.text)
                for m in unread
            )

        return ToolDef(
            execute, name="read_messages", description=_READ_DESCRIPTION
        ).as_tool()


@swarm_channel
def tree(
    parents: dict[str, str | None],
    max_message_bytes: int = 100_000,
    rate: tuple[int, float] | list[int | float] | None = (60, 60.0),
    max_wait: int = 600,
) -> Channel:
    roots = [name for name, parent in parents.items() if parent is None]
    if len(roots) != 1:
        raise ValueError(f"tree(): the tree must have exactly one root, got {roots}.")
    for name, parent in parents.items():
        if parent is not None and parent not in parents:
            raise ValueError(f"tree(): {name}'s parent {parent!r} is not in the tree.")
    for name in parents:
        seen = {name}
        node = parents[name]
        while node is not None:
            if node in seen:
                raise ValueError(f"tree(): {name} is on a cycle.")
            seen.add(node)
            node = parents[node]
    if rate is not None:
        count, window = rate
        rate = (int(count), float(window))
    return _Tree(parents, max_message_bytes, rate, max_wait)
