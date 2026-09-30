from __future__ import annotations

from contextlib import AbstractAsyncContextManager, nullcontext
from contextvars import ContextVar
from dataclasses import dataclass, field

from apn.layout import ENTRY_REL, PROJECT, SUBMISSION_LIB

# Where the submit tool records the agent's declared claim (see apn.solver).
CLAIM_STORE_KEY = "submission_claim"


@dataclass(frozen=True)
class Workspace:
    name: str | None = None
    project: str = PROJECT
    claim_key: str = CLAIM_STORE_KEY
    check_lock: AbstractAsyncContextManager[object] = field(default_factory=nullcontext)

    @property
    def submission_dir(self) -> str:
        return f"{self.project}/{SUBMISSION_LIB}"

    @property
    def entry_path(self) -> str:
        return f"{self.project}/{ENTRY_REL}"


_current: ContextVar[Workspace] = ContextVar("apn_workspace", default=Workspace())


def current_workspace() -> Workspace:
    return _current.get()


def set_workspace(workspace: Workspace) -> None:
    _current.set(workspace)
