from __future__ import annotations

import posixpath
import shlex
from contextlib import AbstractAsyncContextManager, nullcontext

import anyio
from inspect_ai.agent import AgentAttempts, AgentSubmit, run
from inspect_ai.model import ChatMessageUser, CompactionSummary
from inspect_ai.scorer import Score, Scorer, Target, accuracy, scorer, stderr
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import memory, text_editor
from inspect_ai.util import LimitExceededError, sandbox
from inspect_boltons.tools import resources

from apn.checker import ProofChecker
from apn.layout import ENTRY_PATH, PROJECT
from apn.limits import continue_unless_looping
from apn.prompts import user_prompt
from apn.scorer import score_workspace
from apn.solver import (
    _warn_if_ignored_formalizations,
    build_agent,
    gated_incorrect_message,
    submit,
)
from apn.tools import bash
from apn.workspace import CLAIM_STORE_KEY, Workspace, current_workspace, set_workspace

SWARM_ROOT = "/workspace/swarm"


def swarm_prompt(name: str, swarm_size: int, workspace: Workspace) -> str:
    return f"""\
You are {name}, one of {swarm_size} peer agents working on this same problem in parallel. There is no leader.

Your Lake project is `{workspace.project}`; every path above refers to your copy. Each peer has its own copy at `{SWARM_ROOT}/<name>/leanproject`. You may read and copy from peers' projects, but never write to them.

Coordinate with your peers through the `memory` tool: its `/memories` directory is shared by all of them. 
"""


async def _create_projects(members: list[Workspace]) -> None:
    script = "set -e\n" + "".join(
        f"mkdir -p {shlex.quote(posixpath.dirname(m.project))}\n"
        f"cp -a {PROJECT} {shlex.quote(m.project)}\n"
        for m in members
    )
    result = await sandbox().exec(["sh", "-c", script])
    if result.returncode != 0:
        raise RuntimeError(
            f"swarm project copy failed (exit {result.returncode}):\n{result.stderr[-2000:]}"
        )


def swarm_members(
    swarm_size: int,
    check_lock: AbstractAsyncContextManager[object] = nullcontext(),
) -> dict[str, Workspace]:
    return {
        f"agent-{i}": Workspace(
            name=f"agent-{i}",
            project=f"{SWARM_ROOT}/agent-{i}/leanproject",
            claim_key=f"{CLAIM_STORE_KEY}:agent-{i}",
            check_lock=check_lock,
        )
        for i in range(swarm_size)
    }


async def _score_member(
    state: TaskState, checker: ProofChecker, workspace: Workspace
) -> Score:
    return await score_workspace(
        state, checker, workspace, tree_key=f"submission_contents_{workspace.name}"
    )


@scorer(metrics={"*": [accuracy(), stderr()]})
def swarm_scorer(checker: ProofChecker, swarm_size: int) -> Scorer:
    async def score(state: TaskState, target: Target) -> Score:
        submitting = current_workspace()
        if submitting.name is not None:
            return await _score_member(state, checker, submitting)
        scores = {
            name: await _score_member(state, checker, workspace)
            for name, workspace in swarm_members(swarm_size).items()
        }
        return Score(
            value={name: s.as_str() for name, s in scores.items()},
            metadata={name: s.metadata for name, s in scores.items()},
        )

    return score


@solver
def lean_swarm(
    swarm_size: int,
    literature: bool,
    util_module: str,
) -> Solver:
    async def solve(state: TaskState, generate: Generate) -> TaskState:
        _warn_if_ignored_formalizations(state)
        await sandbox().write_file(ENTRY_PATH, state.metadata["sketch"])

        members = swarm_members(swarm_size, check_lock=anyio.Lock())
        await _create_projects(list(members.values()))

        async with anyio.create_task_group() as tg:

            async def run_member(name: str, workspace: Workspace) -> None:
                set_workspace(workspace)
                agent = build_agent(
                    "react",
                    tools=[
                        text_editor(),
                        bash(timeout=300, cwd=workspace.project),
                        resources(),
                        memory(),
                    ],
                    attempts=AgentAttempts(
                        attempts=99_999_999,
                        incorrect_message=gated_incorrect_message,
                    ),
                    submit=AgentSubmit(
                        tool=submit(), name="submit_proof", keep_in_messages=True
                    ),
                    on_continue=continue_unless_looping("Continue working on the problem."),
                    compaction=CompactionSummary(threshold=300_000),
                )
                prompt = "\n\n".join(
                    [
                        user_prompt(
                            workspace.entry_path,
                            state.token_limit,
                            literature,
                            util_module,
                            workspace=workspace,
                        ),
                        swarm_prompt(name, swarm_size, workspace),
                    ]
                )
                try:
                    await run(agent, [ChatMessageUser(content=prompt)], name=name)
                except LimitExceededError as ex:
                    if ex.type != "custom":
                        raise

            for name, workspace in members.items():
                tg.start_soon(run_member, name, workspace)

        state.completed = True
        return state

    return solve
