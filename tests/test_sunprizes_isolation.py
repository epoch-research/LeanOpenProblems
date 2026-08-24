"""Authoritative validation of the committed ``apn/data/sunprizes/Isolated/`` specs.

``scripts/generate_sunprizes_isolated.py`` only *writes* the isolated files;
the checks that prove they are sound live here, running the Lean toolchain in
a container via the shared plumbing in ``tests/lean_sandbox.py`` (see its
docstring for the sandbox lifecycle).

The gates (all over the committed files, recomputing independently what
*should* be true):

* **Structural** -- re-extract each isolated file and confirm the target theorem
  is present exactly once and the surviving theorem/lemma commands are exactly
  the ones the cut predicts (target + its definitional-dependency lemmas,
  nothing else).
* **Statement certificate** -- the target's *elaborated* statement must equal
  the vendored source's (up to hygiene normalization); all 8 members are plain
  statements, so no ``answer(...)`` rewrite forms are involved.
* **Compile** -- every isolated file compiles cleanly with the scorer's exact
  ``lake env lean -o`` command, in parallel in the container.

Docker is part of the test environment, so these always run -- they are not
gated or skipped. The first run builds the image (Lean + Mathlib) from the
Dockerfile; subsequent runs reuse the docker layer cache.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import pytest
import pytest_asyncio

from apn.dataset import SUNPRIZES_DIR, fc_commit, load_manifest
from scripts.sunprizes_isolation import (
    ISOLATED_DIR,
    SOURCES_DIR,
)
from scripts.fc_statements import is_example_command, normalize_hygiene
from scripts.isolation import (
    matches_name,
    planned_survivors,
    theorem_command_decls,
)
from tests.lean_sandbox import compile_all, extract, generate_env


# --------------------------------------------------------------------------- #
# Fixtures: extract + compile once, in one sandbox, share the results.         #
# --------------------------------------------------------------------------- #
@dataclass
class IsoData:
    """Everything the gates need, gathered from a single sandbox bring-up."""

    src_ranges: dict[str, dict[str, Any]]  # extractor records for Sources/, by relpath
    iso_ranges: dict[str, dict[str, Any]]  # extractor records for Isolated/, by stem (= name)
    compile_failures: list[str]  # stems of Isolated/ files that failed to compile


@pytest.fixture(scope="session")
def mapping() -> list[tuple[str, str]]:
    # The manifest rows (the 8 prized conjectures, none excluded) as
    # (id, source relpath) pairs.
    rows = load_manifest(SUNPRIZES_DIR)
    assert len(rows) == 8
    assert all(r.excluded is None for r in rows)
    return [(r.id, r.source.removeprefix("Sources/")) for r in rows]


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data(mapping: list[tuple[str, str]]) -> IsoData:
    """Bring the sandbox up once and run every Lean step inside it: extract the
    vendored sources and the Isolated files, then compile every Isolated file.

    The vendored tree is flat (relpath == basename, unique), and Isolated
    basenames (fully qualified decl names) are unique too. Same async/loop-scope
    arrangement as ``tests/test_fc100_isolation.py::iso_data``, for the same
    reasons.
    """
    async with generate_env("pytest_sunprizes_isolation", fc_commit(SUNPRIZES_DIR)) as env:
        rels = sorted({rel for _, rel in mapping})
        src = await extract(env, [SOURCES_DIR / rel for rel in rels], arcnames=rels)
        iso_files = sorted(ISOLATED_DIR.glob("*.lean"))
        iso = await extract(env, iso_files)
        failures = await compile_all(env, iso_files)
    return IsoData(
        src_ranges={fr["file"]: fr for fr in src},
        iso_ranges={fr["file"][: -len(".lean")]: fr for fr in iso},
        compile_failures=failures,
    )


# --------------------------------------------------------------------------- #
# Gates. Async + module-scoped loop so they share the one sandbox bring-up      #
# above; the bodies are pure assertions over the precomputed ``iso_data``.      #
# --------------------------------------------------------------------------- #
@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_are_structurally_correct(
    mapping: list[tuple[str, str]], iso_data: IsoData
) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas
    (the cut's prediction), with the target's statement equal to the source's
    up to hygiene normalization -- no member here has an ``answer(...)`` form,
    so nothing is rewritten."""
    failures: list[str] = []
    for name, rel in mapping:
        src_type, planned = planned_survivors(iso_data.src_ranges[rel], name)
        src_type = normalize_hygiene(src_type)
        fr = iso_data.iso_ranges.get(name)
        if fr is None:
            failures.append(f"{name}: no isolated file extracted")
            continue
        thms = theorem_command_decls(fr)
        target_hits = [d for d in thms if matches_name(d["name"], name)]
        if len(target_hits) != 1:
            failures.append(
                f"{name}: target appears {len(target_hits)}x among {[d['name'] for d in thms]}"
            )
            continue
        remaining = sorted(d["name"] for d in thms)
        if remaining != planned:
            failures.append(f"{name}: surviving theorems {remaining} != planned {planned}")
            continue
        if normalize_hygiene(target_hits[0]["type"]) != src_type:
            failures.append(f"{name}: target statement changed during isolation")
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_no_example_commands_survive(
    mapping: list[tuple[str, str]], iso_data: IsoData
) -> None:
    """FC's anonymous ``example`` sanity checks are cut: keeping one would make
    the scorer re-run its proof inside the trusted target compile on every
    score call."""
    offenders = []
    for name, _ in mapping:
        src = (ISOLATED_DIR / f"{name}.lean").read_bytes()
        fr = iso_data.iso_ranges[name]
        if any(is_example_command(src, c) for c in fr["commands"]):
            offenders.append(name)
    assert not offenders, f"example commands survived isolation in: {offenders}"


@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_compile(iso_data: IsoData) -> None:
    """The authoritative gate: every isolated file compiles with the scorer's
    exact ``lake env lean -o`` command."""
    assert not iso_data.compile_failures, (
        f"{len(iso_data.compile_failures)} isolated file(s) failed to compile: "
        f"{iso_data.compile_failures}"
    )
