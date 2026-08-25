"""Authoritative validation of the committed ``apn/data/erdos/Isolated/`` specs.

``scripts/generate_erdos_isolated.py`` only *writes* the isolated files; the
checks that prove they are sound live here, running the Lean toolchain in a
container via the shared plumbing in ``tests/lean_sandbox.py`` (see its
docstring for the sandbox lifecycle).

The gates (all over the committed files, recomputing independently what
*should* be true):

* **Structural** -- re-extract each isolated file and confirm the target theorem
  is present exactly once and the surviving theorem/lemma commands are exactly
  the ones the cut predicts (target + its definitional-dependency lemmas + the
  appended ``.disproof`` declaration, nothing else).
* **Disproof certification** -- every spec declares exactly its target plus
  ``<target>.disproof``, whose elaborated type an independent metaprogram
  (``certify_disproof``, recomputing via ``mkNot``) certifies as exactly the
  target statement's negation (comparator-migration-plan.md §4).
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

from apn.dataset import ERDOS_DIR, SampleRow, fc_commit, load_manifest
from scripts.erdos_isolation import (
    ISOLATED_DIR,
    SOURCES_DIR,
)
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
from tests.lean_sandbox import certify, compile_all, extract, generate_env


# --------------------------------------------------------------------------- #
# Fixtures: extract + compile once, in one sandbox, share the results.         #
# --------------------------------------------------------------------------- #
@dataclass
class IsoData:
    """Everything the gates need, gathered from a single sandbox bring-up."""

    src_ranges: dict[str, dict[str, Any]]  # extractor records for Sources/, by relpath
    iso_ranges: dict[str, dict[str, Any]]  # extractor records for Isolated/, by stem (= name)
    cert_verdicts: dict[str, dict[str, Any]]  # certify_disproof verdicts, by stem
    compile_failures: list[str]  # stems of Isolated/ files that failed to compile


@pytest.fixture(scope="session")
def kept_rows() -> list[SampleRow]:
    # The committed manifest's kept rows are the members with isolated specs;
    # excluded rows (value-typed / proved-in-file) have none.
    return [r for r in load_manifest(ERDOS_DIR) if r.excluded is None]


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data(kept_rows: list[SampleRow]) -> IsoData:
    """Bring the sandbox up once and run every Lean step inside it: extract the
    vendored sources and the Isolated files, then compile every Isolated file.

    The vendored tree is flat (relpath == basename, unique), so sources stage
    under their basenames; Isolated basenames are unique too (a case-collision
    disambiguator keeps them distinct even casefolded). Same async/loop-scope
    arrangement as ``tests/test_fc100_isolation.py::iso_data``, for the same
    reasons.
    """
    async with generate_env("pytest_erdos_isolation", fc_commit(ERDOS_DIR)) as env:
        rels = sorted({r.source.removeprefix("Sources/") for r in kept_rows})
        src = await extract(env, [SOURCES_DIR / rel for rel in rels], arcnames=rels)
        iso_files = sorted(ISOLATED_DIR.glob("*.lean"))
        iso = await extract(env, iso_files)
        cert = await certify(env, iso_files)
        failures = await compile_all(env, iso_files)
    return IsoData(
        src_ranges={fr["file"]: fr for fr in src},
        iso_ranges={fr["file"][: -len(".lean")]: fr for fr in iso},
        cert_verdicts={v["file"][: -len(".lean")]: v for v in cert},
        compile_failures=failures,
    )


def _source_form(name: str, rel: str, filerec: dict[str, Any]) -> str | None:
    """The ``answer(...) ↔`` form of the target's *source* command, re-detected
    from the vendored span text (comment-stripped) -- independent of what
    generation recorded in the manifest, so the per-row cross-check below is
    genuine."""
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
    kept_rows: list[SampleRow], iso_data: IsoData
) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas
    (the cut's prediction), with the target's statement certified against the
    source per its re-detected ``answer(...)`` form -- which must also match
    the manifest's recorded ``answer_form``: equal up to hygiene normalization
    for plain members, the pinned wrapper of the isolated type for the
    rewritten forms."""
    failures: list[str] = []
    for row in kept_rows:
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
        # The committed spec is the cut's prediction plus the appended
        # `.disproof` declaration (comparator-migration-plan.md §4).
        expected = sorted(planned + [f"{row.decl_name}.disproof"])
        if remaining != expected:
            failures.append(f"{name}: surviving theorems {remaining} != expected {expected}")
            continue
        form = _source_form(name, rel, iso_data.src_ranges[rel])
        if form != row.extra["answer_form"]:
            failures.append(
                f"{name}: manifest answer_form {row.extra['answer_form']} != source's {form}"
            )
            continue
        iso_type = normalize_hygiene(target_hits[0]["type"])
        if not answer_certified(form, src_type, iso_type):
            failures.append(f"{name}: target statement changed during isolation ({form=})")
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_no_example_commands_survive(
    kept_rows: list[SampleRow], iso_data: IsoData
) -> None:
    """FC's anonymous ``example`` sanity checks (1141.lean, 387.lean) are cut:
    keeping one would make the scorer re-run its proof inside the trusted
    target compile on every score call."""
    offenders = []
    for row in kept_rows:
        src = (ERDOS_DIR / row.statement_path).read_bytes()
        stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
        fr = iso_data.iso_ranges[stem]
        if any(is_example_command(src, c) for c in fr["commands"]):
            offenders.append(row.id)
    assert not offenders, f"example commands survived isolation in: {offenders}"


@pytest.mark.asyncio(loop_scope="module")
async def test_disproof_declarations_certified(
    kept_rows: list[SampleRow], iso_data: IsoData
) -> None:
    """Every spec declares exactly its target plus ``<target>.disproof``, and
    the certifier's independent ``mkNot`` recomputation confirms the disproof's
    elaborated type is the target statement's negation (plan §4)."""
    failures: list[str] = []
    for row in kept_rows:
        stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
        v = iso_data.cert_verdicts.get(stem)
        if v is None:
            failures.append(f"{row.id}: no certifier verdict")
        elif not v["ok"]:
            failures.append(f"{row.id}: {v['error']}")
        elif v["target"] != row.decl_name or v["disproof"] != f"{row.decl_name}.disproof":
            failures.append(
                f"{row.id}: certified pair ({v['target']}, {v['disproof']}) does not "
                f"match the manifest decl name {row.decl_name}"
            )
    assert not failures, "disproof certification failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_compile(iso_data: IsoData) -> None:
    """The authoritative gate: every isolated file compiles cleanly with
    ``lake env lean -o`` in the project environment."""
    assert not iso_data.compile_failures, (
        f"{len(iso_data.compile_failures)} isolated file(s) failed to compile: "
        f"{iso_data.compile_failures}"
    )
