"""Authoritative validation of the committed ``apn/data/wikipedia/Isolated/`` specs.

The same gates as ``tests/test_erdos_isolation.py`` (see its docstring),
with the source side taken from the de-modulized, sibling-import-patched text
every spec is cut from (``scripts.wikipedia_isolation.extraction_source``):

* **Structural** -- each isolated file's surviving theorems are exactly the
  cut's prediction plus the appended ``.disproof``, and the target's
  elaborated statement relates to the source's per its re-detected
  ``answer(...)`` form.
* **Disproof certification** -- ``<target>.disproof`` elaborates to exactly
  the target's negation.
* **Compile** -- every isolated file compiles with the scorer's
  ``lake env lean -o`` command.
"""

from __future__ import annotations

import re
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest
import pytest_asyncio

from apn.dataset import WIKIPEDIA_DIR, SampleRow, fc_commit, fc_profile, load_manifest
from scripts.fc_statements import (
    answer_certified,
    detect_answer_form,
    is_example_command,
    normalize_hygiene,
    strip_comments,
)
from scripts.isolation import planned_survivors, theorem_command_decls
from scripts.wikipedia_isolation import ISOLATED_DIR, extraction_source
from tests.lean_sandbox import certify, compile_all, extract, generate_env


_PRIVATE_PREFIX_RE = re.compile(r"^_private\.(?:[^.]+\.)*?0\.")


@dataclass
class IsoData:
    src_texts: dict[str, str]  # extraction sources, by relpath
    src_ranges: dict[str, dict[str, Any]]
    iso_ranges: dict[str, dict[str, Any]]
    cert_verdicts: dict[str, dict[str, Any]]
    compile_failures: list[str]


@pytest.fixture(scope="session")
def kept_rows() -> list[SampleRow]:
    return [r for r in load_manifest(WIKIPEDIA_DIR) if r.excluded is None]


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data(kept_rows: list[SampleRow]) -> IsoData:
    pin = fc_commit(WIKIPEDIA_DIR)
    util_module = fc_profile(pin).util_module
    rels = sorted({r.source.removeprefix("Sources/") for r in kept_rows})
    src_texts = {rel: extraction_source(rel) for rel in rels}
    with tempfile.TemporaryDirectory() as tmp:
        staged = []
        for rel in rels:
            path = Path(tmp) / rel
            path.write_text(src_texts[rel])
            staged.append(path)
        async with generate_env("pytest_wikipedia_isolation", pin) as env:
            src = await extract(env, staged, util_module, arcnames=rels)
            iso_files = sorted(ISOLATED_DIR.glob("*.lean"))
            iso = await extract(env, iso_files, util_module)
            cert = await certify(env, iso_files, util_module)
            failures = await compile_all(env, iso_files)
    return IsoData(
        src_texts=src_texts,
        src_ranges={fr["file"]: fr for fr in src},
        iso_ranges={fr["file"][: -len(".lean")]: fr for fr in iso},
        cert_verdicts={v["file"][: -len(".lean")]: v for v in cert},
        compile_failures=failures,
    )


def _source_form(name: str, src_text: str, filerec: dict[str, Any]) -> str | None:
    src = src_text.encode()
    spans = [
        src[c["declStart"] : c["declEnd"]]
        for c in filerec["commands"]
        if any(d["kind"] == "theorem" and d["name"] == name for d in c["decls"])
    ]
    assert len(spans) == 1, f"{name}: {len(spans)} source commands declare the target"
    form: str | None = detect_answer_form(strip_comments(spans[0].decode("utf-8")))
    return form


@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_are_structurally_correct(
    kept_rows: list[SampleRow], iso_data: IsoData
) -> None:
    failures: list[str] = []
    for row in kept_rows:
        name, rel = row.id, row.source.removeprefix("Sources/")
        stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
        src_type, planned = planned_survivors(iso_data.src_ranges[rel], name)
        # Specs ship with `private` stripped, so kept private theorems carry
        # their plain names.
        planned = [_PRIVATE_PREFIX_RE.sub("", d) for d in planned]
        src_type = normalize_hygiene(src_type)
        fr = iso_data.iso_ranges.get(stem)
        if fr is None:
            failures.append(f"{row.id}: no isolated file extracted")
            continue
        thms = theorem_command_decls(fr)
        target_hits = [d for d in thms if d["name"] == name]
        if len(target_hits) != 1:
            failures.append(
                f"{row.id}: target appears {len(target_hits)}x among {[d['name'] for d in thms]}"
            )
            continue
        remaining = sorted(d["name"] for d in thms)
        expected = sorted(planned + [f"{row.decl_name}.disproof"])
        if remaining != expected:
            failures.append(f"{row.id}: surviving theorems {remaining} != expected {expected}")
            continue
        iso_type = normalize_hygiene(target_hits[0]["type"])
        form = _source_form(name, iso_data.src_texts[rel], iso_data.src_ranges[rel])
        if form != row.extra["answer_form"]:
            failures.append(
                f"{row.id}: manifest answer_form {row.extra['answer_form']} != source's {form}"
            )
            continue
        if not answer_certified(form, src_type, iso_type):
            failures.append(f"{row.id}: target statement changed during isolation ({form=})")
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_no_example_commands_survive(
    kept_rows: list[SampleRow], iso_data: IsoData
) -> None:
    offenders = []
    for row in kept_rows:
        src = (WIKIPEDIA_DIR / row.statement_path).read_bytes()
        stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
        fr = iso_data.iso_ranges[stem]
        if any(is_example_command(src, c) for c in fr["commands"]):
            offenders.append(row.id)
    assert not offenders, f"example commands survived isolation in: {offenders}"


@pytest.mark.asyncio(loop_scope="module")
async def test_disproof_declarations_certified(
    kept_rows: list[SampleRow], iso_data: IsoData
) -> None:
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
    assert not iso_data.compile_failures, (
        f"{len(iso_data.compile_failures)} isolated file(s) failed to compile: "
        f"{iso_data.compile_failures}"
    )
