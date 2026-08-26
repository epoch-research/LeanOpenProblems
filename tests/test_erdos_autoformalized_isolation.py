"""Authoritative validation of the committed
``apn/data/erdos_autoformalized/Isolated/`` specs.

``scripts/generate_erdos_autoformalized_isolated.py`` only *writes* the
isolated files; the checks that prove they are sound live here, running the
Lean toolchain in a container via the shared plumbing in
``tests/lean_sandbox.py`` (see its docstring for the sandbox lifecycle).

The gates (all over the committed files, recomputing independently what
*should* be true):

* **Structural** -- re-extract each isolated file and confirm the target theorem
  is present exactly once and the surviving theorem/lemma commands are exactly
  the ones the cut predicts (target + its definitional-dependency lemmas,
  nothing else), with the target's *elaborated* statement equal to the vendored
  source's (up to the ``normalize_hygiene`` display-artifact erasure --
  α-equivalence). There is no ``answer(...) ↔`` rewrite in this dataset, so the
  certificate is plain equality; the test re-detects the source form
  independently and asserts it is ``None`` for every member.
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

from apn.dataset import (
    ERDOS_AUTOFORMALIZED_DIR,
    SampleRow,
    fc_commit,
    fc_profile,
    load_manifest,
)
from scripts.erdos_autoformalized_isolation import ISOLATED_DIR, SOURCES_DIR
from scripts.fc_statements import (
    answer_certified,
    detect_answer_form,
    is_example_command,
    normalize_hygiene,
    strip_comments,
)
from scripts.isolation import (
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
def rows() -> list[SampleRow]:
    # Every manifest row has an isolated spec: this dataset ships no excluded
    # members (generation fails loudly instead -- see the generator).
    manifest = load_manifest(ERDOS_AUTOFORMALIZED_DIR)
    assert all(r.excluded is None for r in manifest)
    return manifest


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data(rows: list[SampleRow]) -> IsoData:
    """Bring the sandbox up once and run every Lean step inside it: extract the
    vendored sources and the Isolated files, then compile every Isolated file.

    The vendored tree is flat (relpath == basename, unique), so sources stage
    under their basenames; Isolated basenames are unique too. Same async/
    loop-scope arrangement as ``tests/test_erdos_isolation.py::iso_data``, for
    the same reasons.
    """
    pin = fc_commit(ERDOS_AUTOFORMALIZED_DIR)
    util_module = fc_profile(pin).util_module
    async with generate_env("pytest_erdos_autoformalized_isolation", pin) as env:
        rels = sorted({r.source.removeprefix("Sources/") for r in rows})
        src = await extract(env, [SOURCES_DIR / rel for rel in rels], util_module, arcnames=rels)
        iso_files = sorted(ISOLATED_DIR.glob("*.lean"))
        iso = await extract(env, iso_files, util_module)
        failures = await compile_all(env, iso_files)
    return IsoData(
        src_ranges={fr["file"]: fr for fr in src},
        iso_ranges={fr["file"][: -len(".lean")]: fr for fr in iso},
        compile_failures=failures,
    )


def _source_form(name: str, rel: str, filerec: dict[str, Any]) -> str | None:
    """The ``answer(...) ↔`` form of the target's *source* command, re-detected
    from the vendored span text (comment-stripped) -- independent of
    generation, which asserted there is none."""
    src = (SOURCES_DIR / rel).read_bytes()
    spans = [
        src[c["declStart"] : c["declEnd"]]
        for c in filerec["commands"]
        if any(d["kind"] == "theorem" and d["name"] == name for d in c["decls"])
    ]
    assert len(spans) == 1, f"{name}: {len(spans)} source commands declare the target"
    form: str | None = detect_answer_form(strip_comments(spans[0].decode("utf-8")))
    return form


# --------------------------------------------------------------------------- #
# Gates. Async + module-scoped loop so they share the one sandbox bring-up      #
# above; the bodies are pure assertions over the precomputed ``iso_data``.      #
# --------------------------------------------------------------------------- #
@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_are_structurally_correct(
    rows: list[SampleRow], iso_data: IsoData
) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas
    (the cut's prediction), with the target's elaborated statement equal to
    the source's up to hygiene normalization -- no member may carry an
    ``answer(...)`` form in this dataset."""
    failures: list[str] = []
    for row in rows:
        name, rel = row.id, row.source.removeprefix("Sources/")
        stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
        src_type, planned = planned_survivors(iso_data.src_ranges[rel], name)
        src_type = normalize_hygiene(src_type)
        fr = iso_data.iso_ranges.get(stem)
        if fr is None:
            failures.append(f"{name}: no isolated file extracted")
            continue
        thms = theorem_command_decls(fr)
        target_hits = [d for d in thms if d["name"] == name]
        if len(target_hits) != 1:
            failures.append(
                f"{name}: target appears {len(target_hits)}x among {[d['name'] for d in thms]}"
            )
            continue
        remaining = sorted(d["name"] for d in thms)
        if remaining != planned:
            failures.append(f"{name}: surviving theorems {remaining} != planned {planned}")
            continue
        form = _source_form(name, rel, iso_data.src_ranges[rel])
        if form is not None:
            failures.append(f"{name}: source statement carries an answer(...) form ({form})")
            continue
        iso_type = normalize_hygiene(target_hits[0]["type"])
        if not answer_certified(None, src_type, iso_type):
            failures.append(f"{name}: target statement changed during isolation")
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_no_example_commands_survive(rows: list[SampleRow], iso_data: IsoData) -> None:
    """Anonymous ``example`` sanity checks are cut: keeping one would make the
    scorer re-run its proof inside the trusted target compile on every score
    call. The vendored sources ship none; the isolated files must not either."""
    offenders = []
    for row in rows:
        src = (ERDOS_AUTOFORMALIZED_DIR / row.statement_path).read_bytes()
        stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
        fr = iso_data.iso_ranges[stem]
        if any(is_example_command(src, c) for c in fr["commands"]):
            offenders.append(row.id)
    assert not offenders, f"example commands survived isolation in: {offenders}"


@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_compile(iso_data: IsoData) -> None:
    """The authoritative gate: every isolated file compiles with the scorer's
    exact ``lake env lean -o`` command."""
    assert not iso_data.compile_failures, (
        f"{len(iso_data.compile_failures)} isolated file(s) failed to compile: "
        f"{iso_data.compile_failures}"
    )
