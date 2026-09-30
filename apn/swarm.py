from __future__ import annotations

from contextlib import AbstractAsyncContextManager, contextmanager, nullcontext
from copy import deepcopy
from pathlib import Path
from typing import Iterator

import anyio
import yaml
from inspect_ai import Task, task
from inspect_ai.agent import AgentAttempts, AgentSubmit, run
from inspect_ai.model import ChatMessageUser, CompactionSummary
from inspect_ai.scorer import Score, Scorer, Target, accuracy, scorer, stderr
from inspect_ai.solver import Generate, Solver, TaskState, solver
from inspect_ai.tool import memory, text_editor
from inspect_ai.util import LimitExceededError, sandbox, sandbox_default
from inspect_ai.util._sandbox.context import sandbox_environments_context_var
from inspect_boltons.tools import resources

from apn.checker import ProofChecker, SandboxComparator
from apn.dataset import fc_commit, fc_profile, load_subset
from apn.layout import ENTRY_PATH
from apn.limits import continue_unless_looping
from apn.prompts import user_prompt
from apn.scorer import score_workspace
from apn.solver import (
    _warn_if_ignored_formalizations,
    build_agent,
    gated_incorrect_message,
    submit,
)
from apn.task import BENCHMARKS, Benchmark, SandboxBackend, get_sandbox_config
from apn.tools import bash
from apn.workspace import CLAIM_STORE_KEY, Workspace, current_workspace, set_workspace


def _sandbox_name(index: int) -> str:
    return "default" if index == 0 else f"agent-{index}"


@contextmanager
def _only_sandboxes(names: list[str]) -> Iterator[None]:
    environments = sandbox_environments_context_var.get()
    token = sandbox_environments_context_var.set({n: environments[n] for n in names})
    try:
        yield
    finally:
        sandbox_environments_context_var.reset(token)


def swarm_members(
    swarm_size: int,
    check_lock: AbstractAsyncContextManager[object] = nullcontext(),
) -> dict[str, Workspace]:
    return {
        f"agent-{i}": Workspace(
            name=f"agent-{i}",
            sandbox=_sandbox_name(i),
            claim_key=f"{CLAIM_STORE_KEY}:agent-{i}",
            check_lock=check_lock,
        )
        for i in range(swarm_size)
    }


def swarm_sandbox_config(
    fc_commit: str, literature: bool, backend: SandboxBackend, swarm_size: int
) -> tuple[str, str]:
    backend_type, path = get_sandbox_config(fc_commit, literature, backend)
    config = yaml.safe_load(Path(path).read_text())
    services = config["services"]
    agent = services.pop("default")
    config["services"] = {
        **{_sandbox_name(i): deepcopy(agent) for i in range(swarm_size)},
        **services,
    }
    out = Path(path).with_name(
        f"swarm-{swarm_size}.compose.yaml"
        if backend == "docker"
        else f"swarm-{swarm_size}-values.yaml"
    )
    content = yaml.safe_dump(config, sort_keys=False)
    if not out.exists() or out.read_text() != content:
        out.write_text(content)
    return (backend_type, str(out))


def swarm_prompt(name: str, swarm_size: int) -> str:
    return f"""\
You are {name}, one of {swarm_size} peer agents working on this same problem in parallel.  
Each peer works in its own separate environment; you cannot see theirs and they cannot see yours.

Coordinate with your peers through the `memory` tool. The tool is shared by all peers and is the only channel between you.
"""


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
        members = swarm_members(swarm_size, check_lock=anyio.Lock())
        for workspace in members.values():
            await sandbox(workspace.sandbox).write_file(
                ENTRY_PATH, state.metadata["sketch"]
            )

        prompt = user_prompt(ENTRY_PATH, state.token_limit, literature, util_module)

        async def run_member(name: str, workspace: Workspace, sandbox_name: str) -> None:
            set_workspace(workspace)
            agent = build_agent(
                "react",
                tools=[text_editor(), bash(timeout=300), resources(), memory()],
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
            content = f"{prompt}\n\n{swarm_prompt(name, swarm_size)}"
            with sandbox_default(sandbox_name), _only_sandboxes([sandbox_name, "comparator"]):
                try:
                    await run(agent, [ChatMessageUser(content=content)], name=name)
                except LimitExceededError as ex:
                    if ex.type != "custom":
                        raise

        async with anyio.create_task_group() as tg:
            for i, (name, workspace) in enumerate(members.items()):
                tg.start_soon(run_member, name, workspace, _sandbox_name(i))

        state.completed = True
        return state

    return solve


@task
def apn_swarm(
    benchmark: Benchmark,
    subset: str | None = None,
    swarm_size: int = 3,
    literature: bool = False,
    sandbox_backend: SandboxBackend = "docker",
) -> Task:
    dataset_dir, dataset_fn = BENCHMARKS[benchmark]
    name_list = load_subset(dataset_dir, subset) if subset is not None else None
    pin = fc_commit(dataset_dir)
    return Task(
        dataset=dataset_fn(names=name_list),
        solver=lean_swarm(
            swarm_size=swarm_size,
            literature=literature,
            util_module=fc_profile(pin).util_module,
        ),
        scorer=swarm_scorer(SandboxComparator(), swarm_size=swarm_size),
        sandbox=swarm_sandbox_config(pin, literature, sandbox_backend, swarm_size),
    )
