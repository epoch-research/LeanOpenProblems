"""Authoritative validation of the committed ``apn/data/oeis/Isolated/`` specs.

``scripts/generate_oeis_isolated.py`` only *writes* the isolated files; the checks
that prove they are sound live here. There is no local Lean toolchain, so these
run the extractor and the ``lake env lean -o`` compile (the same elaboration the
scorer performs at eval time) inside a container -- "CI has no Lean" is not a
reason to weaken the gate; we bring Lean up in Docker.

The container bring-up and the stage/extract/compile plumbing are shared with
``tests/test_fc100_isolation.py`` and live in ``tests/lean_sandbox.py`` (see
its docstring for the how and why of the sandbox lifecycle).

The gates (all over the committed files, recomputing independently what *should*
be true):

* **Structural** -- re-extract each isolated file and confirm the target theorem
  is present exactly once, the surviving theorem/lemma commands are exactly the
  ones the cut predicts (target + its definitional-dependency lemmas, nothing
  else), and the target's elaborated statement is byte-for-byte the source's.
* **Compile** -- every isolated file compiles cleanly with the scorer's exact
  command, in parallel in the container.
* **Oracle** -- for the paper's solved problems, our isolated target's elaborated
  type matches the published challenge file's ``target_theorem_0``.

Docker is part of the test environment, so these always run -- they are not
gated or skipped. The first run builds the image (Lean + Mathlib) from the
Dockerfile; subsequent runs reuse the docker layer cache.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast

import pytest
import pytest_asyncio

from scripts.isolation import (
    matches_name,
    planned_survivors,
    theorem_command_decls,
    theorem_decls,
)
from scripts.oeis_isolation import AUTO_DIR, ISOLATED_DIR, MAPPING_FILE, parse_mapping
from tests.lean_sandbox import compile_all, extract, generate_env

# The paper's published challenge files (the oracle cross-checks our isolated
# target's elaborated type against each one's ``target_theorem_0``). Vendored and
# committed under tests/data (NOT read from the gitignored ``reference_sources/``
# clone, which is absent in CI) -- see tests/data/gold_proofs/README.md.
REF_DIR = Path(__file__).resolve().parent / "data" / "gold_proofs"


# --------------------------------------------------------------------------- #
# Fixtures: extract + compile once, in one sandbox, share the results.         #
# --------------------------------------------------------------------------- #
@dataclass
class IsoData:
    """Everything the gates need, gathered from a single sandbox bring-up."""

    auto_ranges: dict[str, dict[str, Any]]  # extractor records for distinct Auto/ sources, by filename
    iso_ranges: dict[str, dict[str, Any]]  # extractor records for every Isolated/ file, by stem (= name)
    ref_ranges: list[dict[str, Any]]  # extractor records for the published challenge files
    compile_failures: list[str]  # stems of Isolated/ files that failed to compile


@pytest.fixture(scope="session")
def mapping() -> list[tuple[str, list[str]]]:
    entries = parse_mapping(MAPPING_FILE.read_text())
    assert len(entries) == 492
    return entries


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data(mapping: list[tuple[str, list[str]]]) -> IsoData:
    """Bring the sandbox up once and run every Lean step inside it: extract the
    Auto sources, the Isolated files, and the reference challenge files, then
    compile every Isolated file.

    An async, module-scoped fixture (with the gate tests on the same module-scoped
    event loop) -- the only safe way to drive Inspect's sandbox lifecycle from
    pytest. Driving it from a plain fixture via ``asyncio.run`` would spin up a
    second event loop that Inspect's loop-bound globals deadlock against; sharing
    pytest-asyncio's own loop avoids that. The gates below just assert against the
    returned data, so they need no further sandbox access."""
    async with generate_env("pytest_oeis_isolation") as env:
        source_files = sorted({files[0] for _, files in mapping})
        auto = await extract(env, [AUTO_DIR / f for f in source_files])
        iso_files = sorted(ISOLATED_DIR.glob("*.lean"))
        iso = await extract(env, iso_files)
        ref_files = sorted(REF_DIR.glob("*.lean"))
        ref = await extract(env, ref_files) if ref_files else []
        failures = await compile_all(env, iso_files)
    return IsoData(
        auto_ranges={fr["file"]: fr for fr in auto},
        iso_ranges={fr["file"][: -len(".lean")]: fr for fr in iso},
        ref_ranges=ref,
        compile_failures=failures,
    )


# --------------------------------------------------------------------------- #
# Gates. Async + module-scoped loop so they share the one sandbox bring-up      #
# above; the bodies are pure assertions over the precomputed ``iso_data``.      #
# --------------------------------------------------------------------------- #
@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_are_structurally_correct(
    mapping: list[tuple[str, list[str]]], iso_data: IsoData
) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas (the
    cut's prediction), with the target's statement preserved verbatim."""
    failures: list[str] = []
    for name, files in mapping:
        src_type, planned = planned_survivors(iso_data.auto_ranges[files[0]], name)
        fr = iso_data.iso_ranges.get(name)
        if fr is None:
            failures.append(f"{name}: no isolated file extracted")
            continue
        thms = theorem_command_decls(fr)
        target_hits = [d for d in thms if matches_name(d["name"], name)]
        if len(target_hits) != 1:
            failures.append(f"{name}: target appears {len(target_hits)}x among {[d['name'] for d in thms]}")
            continue
        remaining = sorted(d["name"] for d in thms)
        if remaining != planned:
            failures.append(f"{name}: surviving theorems {remaining} != planned {planned}")
            continue
        if target_hits[0]["type"] != src_type:
            failures.append(f"{name}: target statement changed during isolation")
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_compile(iso_data: IsoData) -> None:
    """The authoritative gate: every isolated file compiles with the scorer's
    exact ``lake env lean -o`` command."""
    assert not iso_data.compile_failures, (
        f"{len(iso_data.compile_failures)} isolated file(s) failed to compile: "
        f"{iso_data.compile_failures}"
    )


@pytest.mark.asyncio(loop_scope="module")
async def test_oracle_matches_published_challenge_files(iso_data: IsoData) -> None:
    """For each solved problem the paper published, our isolated target's
    elaborated type matches its ``target_theorem_0`` (the paper renames the
    conjecture). Confirms isolation reproduces the published challenge statement."""
    if not iso_data.ref_ranges:
        pytest.skip("no reference challenge files vendored")

    def target_type(name: str, fr: dict[str, Any]) -> str:
        (target,) = [d for d in theorem_command_decls(fr) if matches_name(d["name"], name)]
        return cast(str, target["type"])

    iso_types = {name: target_type(name, fr) for name, fr in iso_data.iso_ranges.items()}
    match = mismatch = 0
    mismatches: list[str] = []
    for fr in iso_data.ref_ranges:
        name = fr["file"].rsplit("/", 1)[-1][: -len(".lean")]
        if name not in iso_types:
            continue
        tgt = [d for d in theorem_decls(fr) if matches_name(d["name"], "target_theorem_0")]
        if len(tgt) != 1:
            continue
        if tgt[0]["type"] == iso_types[name]:
            match += 1
        else:
            mismatch += 1
            mismatches.append(name)
    assert mismatch == 0, f"oracle mismatch for: {mismatches}"
    assert match == len(iso_data.ref_ranges), (
        f"only {match}/{len(iso_data.ref_ranges)} reference files matched"
    )
