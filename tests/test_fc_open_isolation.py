"""Authoritative validation of the committed ``Isolated/`` specs of the FC
directory-scoped research-open datasets (``wikipedia``, ``arxiv``,
``oeis_open``).

Same gates as ``tests/test_erdos_isolation.py`` (see its docstring), over all
three datasets through one sandbox bring-up -- they share one FC pin by
construction (asserted below):

* **Structural** -- re-extract each isolated file and confirm the target
  theorem is present exactly once and the surviving theorem/lemma commands are
  exactly the ones the cut predicts.
* **Rewrite certificates** -- the target's *elaborated* statement must relate
  to the vendored source's exactly, per the source statement's re-detected
  ``answer(...)`` form (which must match the manifest's ``answer_form``).
* **Compile** -- every isolated file compiles cleanly with the scorer's exact
  ``lake env lean -o`` command.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import pytest
import pytest_asyncio

from apn.dataset import SampleRow, fc_commit, fc_profile, load_manifest
from scripts.fc_open_isolation import DATASETS, FCOpenDataset
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


@dataclass
class IsoData:
    """Everything the gates need for one dataset."""

    src_ranges: dict[str, dict[str, Any]]  # extractor records for Sources/, by relpath
    iso_ranges: dict[str, dict[str, Any]]  # extractor records for Isolated/, by stem
    compile_failures: list[str]  # stems of Isolated/ files that failed to compile


def kept_rows(cfg: FCOpenDataset) -> list[SampleRow]:
    # The committed manifest's kept rows are the members with isolated specs;
    # excluded rows (value-typed / proved-in-file / dropped) have none.
    return [r for r in load_manifest(cfg.dataset_dir) if r.excluded is None]


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data() -> dict[str, IsoData]:
    """Bring the sandbox up once (the datasets share one FC pin) and run every
    Lean step inside it, per dataset: extract the vendored sources and the
    Isolated files, then compile every Isolated file."""
    pins = {fc_commit(cfg.dataset_dir) for cfg in DATASETS.values()}
    assert len(pins) == 1, f"fc_open datasets have diverging pins: {pins}"
    pin = pins.pop()
    util_module = fc_profile(pin).util_module
    data: dict[str, IsoData] = {}
    async with generate_env("pytest_fc_open_isolation", pin) as env:
        for name, cfg in sorted(DATASETS.items()):
            rels = sorted({r.source.removeprefix("Sources/") for r in kept_rows(cfg)})
            src = await extract(
                env, [cfg.sources_dir / rel for rel in rels], util_module, arcnames=rels
            )
            iso_files = sorted(cfg.isolated_dir.glob("*.lean"))
            iso = await extract(env, iso_files, util_module)
            failures = await compile_all(env, iso_files)
            data[name] = IsoData(
                src_ranges={fr["file"]: fr for fr in src},
                iso_ranges={fr["file"][: -len(".lean")]: fr for fr in iso},
                compile_failures=failures,
            )
    return data


def _source_form(name: str, cfg: FCOpenDataset, rel: str, filerec: dict[str, Any]) -> str | None:
    """The ``answer(...) ↔`` form of the target's *source* command, re-detected
    from the vendored span text (comment-stripped) -- independent of what
    generation recorded in the manifest, so the per-row cross-check below is
    genuine."""
    src = (cfg.sources_dir / rel).read_bytes()
    spans = [
        src[c["declStart"] : c["declEnd"]]
        for c in filerec["commands"]
        if any(d["kind"] == "theorem" and d["name"] == name for d in c["decls"])
    ]
    assert len(spans) == 1, f"{name}: {len(spans)} source commands declare the target"
    form: str | None = detect_answer_form(strip_comments(spans[0].decode("utf-8")))
    return form


@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_are_structurally_correct(iso_data: dict[str, IsoData]) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas
    (the cut's prediction), with the target's statement certified against the
    source per its re-detected ``answer(...)`` form -- which must also match
    the manifest's recorded ``answer_form``."""
    failures: list[str] = []
    for ds_name, cfg in sorted(DATASETS.items()):
        data = iso_data[ds_name]
        for row in kept_rows(cfg):
            name, rel = row.id, row.source.removeprefix("Sources/")
            stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
            src_type, planned = planned_survivors(data.src_ranges[rel], name)
            src_type = normalize_hygiene(src_type)
            fr = data.iso_ranges.get(stem)
            if fr is None:
                failures.append(f"{ds_name}/{name}: no isolated file extracted")
                continue
            thms = theorem_command_decls(fr)
            target_hits = [d for d in thms if d["name"] == name]
            if len(target_hits) != 1:
                failures.append(
                    f"{ds_name}/{name}: target appears {len(target_hits)}x among "
                    f"{[d['name'] for d in thms]}"
                )
                continue
            remaining = sorted(d["name"] for d in thms)
            if remaining != planned:
                failures.append(
                    f"{ds_name}/{name}: surviving theorems {remaining} != planned {planned}"
                )
                continue
            form = _source_form(name, cfg, rel, data.src_ranges[rel])
            if form != row.extra["answer_form"]:
                failures.append(
                    f"{ds_name}/{name}: manifest answer_form {row.extra['answer_form']} "
                    f"!= source's {form}"
                )
                continue
            iso_type = normalize_hygiene(target_hits[0]["type"])
            if not answer_certified(form, src_type, iso_type):
                failures.append(
                    f"{ds_name}/{name}: target statement changed during isolation ({form=})"
                )
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_no_example_commands_survive(iso_data: dict[str, IsoData]) -> None:
    """FC's anonymous ``example`` sanity checks are cut: keeping one would
    make the scorer re-run its proof inside the trusted target compile on
    every score call."""
    offenders = []
    for ds_name, cfg in sorted(DATASETS.items()):
        data = iso_data[ds_name]
        for row in kept_rows(cfg):
            src = (cfg.dataset_dir / row.statement_path).read_bytes()
            stem = row.statement_path.removeprefix("Isolated/").removesuffix(".lean")
            fr = data.iso_ranges[stem]
            if any(is_example_command(src, c) for c in fr["commands"]):
                offenders.append(f"{ds_name}/{row.id}")
    assert not offenders, f"example commands survived isolation in: {offenders}"


@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_compile(iso_data: dict[str, IsoData]) -> None:
    """The authoritative gate: every isolated file compiles with the scorer's
    exact ``lake env lean -o`` command."""
    failures = {ds: d.compile_failures for ds, d in iso_data.items() if d.compile_failures}
    assert not failures, f"isolated file(s) failed to compile: {failures}"
