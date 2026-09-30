from __future__ import annotations

from contextlib import AbstractAsyncContextManager, nullcontext
from contextvars import ContextVar
from dataclasses import dataclass, field

# Where the submit tool records the agent's declared claim (see apn.solver).
CLAIM_STORE_KEY = "submission_claim"


@dataclass(frozen=True)
class Workspace:
    name: str | None = None
    sandbox: str | None = None
    claim_key: str = CLAIM_STORE_KEY
    check_lock: AbstractAsyncContextManager[object] = field(default_factory=nullcontext)


_current: ContextVar[Workspace] = ContextVar("apn_workspace", default=Workspace())


def current_workspace() -> Workspace:
    return _current.get()


def set_workspace(workspace: Workspace) -> None:
    _current.set(workspace)
