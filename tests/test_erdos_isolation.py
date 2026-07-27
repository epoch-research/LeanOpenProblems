"""Authoritative validation of the committed ``apn/data/erdos/Isolated/`` specs.

``scripts/generate_erdos_isolated.py`` only *writes* the isolated files; the
checks that prove they are sound live here, running the Lean toolchain in a
container via the shared plumbing in ``tests/lean_sandbox.py`` (see its
docstring for the sandbox lifecycle).

The gates (all over the committed files, recomputing independently what
*should* be true):

* **Structural** -- re-extract each isolated file and confirm the target theorem
  is present exactly once and the surviving theorem/lemma commands are exactly
  the ones the cut predicts (target + its definitional-dependency lemmas,
  nothing else).
* **Rewrite certificates** -- the target's *elaborated* statement must relate
  to the vendored source's exactly, per the source statement's ``answer(...)``
  form, which this test re-detects from the source span independently of
  generation: equal for the 85 plain members, and the pinned per-form
  ``Iff``-wrapper inserted at the conclusion boundary for the four rewritten
  forms (see ``scripts.fc_statements.answer_certified``; binders before the
  colon hoist over the iff). The per-form census (85/249/7/6/3) is asserted.
  Both sides are compared after erasing elaboration-context display artifacts
  (``normalize_hygiene`` -- α-equivalence). This certifies the text surgery
  preserved elaborated meaning -- in particular that un-filling the 13
  recorded ``answer(True/False)`` verdicts changed nothing but the answer-key
  wrapper -- by Lean's own elaborator rather than by trusting the regex.
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

from scripts.erdos_isolation import (
    FORM_CENSUS,
    ISOLATED_DIR,
    MAPPING_FILE,
    SOURCES_DIR,
    kept_names,
    parse_mapping,
)
from scripts.fc_statements import (
    answer_certified,
    detect_answer_form,
    is_example_command,
    normalize_hygiene,
    strip_comments,
)
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
    entries: list[tuple[str, str]] = parse_mapping(MAPPING_FILE.read_text())
    # The mapping must resolve exactly the kept members (353 attempted minus
    # the 3 excluded, rename applied), in attempt-list order; the mapped names
    # are the fully qualified forms of the short kept names.
    kept = kept_names()
    assert len(entries) == len(kept)
    assert all(matches_name(full, short) for (full, _), short in zip(entries, kept))
    return entries


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data(mapping: list[tuple[str, str]]) -> IsoData:
    """Bring the sandbox up once and run every Lean step inside it: extract the
    vendored sources and the Isolated files, then compile every Isolated file.

    The vendored tree is flat (relpath == basename, unique), so sources stage
    under their basenames; Isolated basenames (fully qualified decl names) are
    unique too. Same async/loop-scope arrangement as
    ``tests/test_fc100_isolation.py::iso_data``, for the same reasons.
    """
    async with generate_env("pytest_erdos_isolation") as env:
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


def _source_form(name: str, rel: str, filerec: dict[str, Any]) -> str | None:
    """The ``answer(...) ↔`` form of the target's *source* command, re-detected
    from the vendored span text (comment-stripped) -- independent of what
    generation did, so the census below is a genuine cross-check."""
    src = (SOURCES_DIR / rel).read_bytes()
    spans = [
        src[c["declStart"] : c["declEnd"]]
        for c in filerec["commands"]
        if any(d["kind"] == "theorem" and matches_name(d["name"], name) for d in c["decls"])
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
    mapping: list[tuple[str, str]], iso_data: IsoData
) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas
    (the cut's prediction), with the target's statement certified against the
    source per its re-detected ``answer(...)`` form: equal up to hygiene
    normalization for plain members, the pinned wrapper of the isolated type
    for the four rewritten forms."""
    failures: list[str] = []
    census: dict[str | None, int] = {form: 0 for form in FORM_CENSUS}
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
        form = _source_form(name, rel, iso_data.src_ranges[rel])
        census[form] += 1
        iso_type = normalize_hygiene(target_hits[0]["type"])
        if not answer_certified(form, src_type, iso_type):
            failures.append(f"{name}: target statement changed during isolation ({form=})")
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)
    # The set's census: 85 plain propositions and 265 rewritten members across
    # the four answer(...) ↔ forms, no more, no fewer.
    assert census == FORM_CENSUS, f"form census drifted: {census} != {FORM_CENSUS}"


@pytest.mark.asyncio(loop_scope="module")
async def test_no_example_commands_survive(
    mapping: list[tuple[str, str]], iso_data: IsoData
) -> None:
    """FC's anonymous ``example`` sanity checks (1141.lean, 387.lean) are cut:
    keeping one would make the scorer re-run its proof inside the trusted
    target compile on every score call."""
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
