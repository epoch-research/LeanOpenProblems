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
  ones the cut predicts (target + its definitional-dependency lemmas + the
  appended ``.disproof`` declaration, nothing else), and the target's elaborated
  statement is byte-for-byte the source's.
* **Disproof certification** -- every spec declares exactly its target plus
  ``<target>.disproof``, whose elaborated type an independent metaprogram
  (``certify_disproof``, recomputing via ``mkNot``) certifies as exactly the
  target statement's negation (comparator-migration-plan.md §4).
* **Compile** -- every isolated file compiles cleanly with ``lake env lean -o``,
  in parallel in the container.
* **Oracle** -- for the paper's solved problems, our isolated target's elaborated
  type matches the published challenge file's ``target_theorem_0``.

Docker is part of the test environment, so these always run -- they are not
gated or skipped. The first run builds the image (Lean + Mathlib) from the
Dockerfile; subsequent runs reuse the docker layer cache.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast

import pytest
import pytest_asyncio

from apn.dataset import OEIS_DIR, SampleRow, fc_commit, fc_profile, load_manifest
from scripts.isolation import (
    matches_name,
    planned_survivors,
    theorem_command_decls,
    theorem_decls,
)
from scripts.oeis_isolation import ISOLATED_DIR, SOURCES_DIR
from tests.lean_sandbox import certify, compile_all, extract, generate_env

# The paper's published challenge files (the oracle cross-checks our isolated
# target's elaborated type against each one's ``target_theorem_0``). Vendored and
# committed under tests/data (NOT read from the gitignored ``reference_sources/``
# clone, which is absent in CI) -- see tests/data/gold_proofs/README.md.
REF_DIR = Path(__file__).resolve().parent / "data" / "gold_proofs"

# The OEIS generator strips `private` from these samples' specs while their
# vendored sources keep it (scripts.isolation.strip_private; comparator#58 /
# plan §3.3 amendment). Privacy changes only how a referenced helper's name is
# mangled (`_private.0.products` in the source vs `products` in the spec), so
# for exactly these samples the raw-`Expr` statement comparisons below hold
# modulo `unmangle_private_names`; every other sample must match byte-for-byte.
# Pinned by test_stripped_private_ids_pinned against the committed files.
STRIPPED_PRIVATE_IDS = frozenset({
    "A253187.universal_sum_conjecture",
    "A277223_conjecture",
    "A381358_limit_exists",
    "general_supercongruence_conjecture",
    "oeis_145062_conjecture_0",
    "oeis_253187_conjecture_1",
    "oeis_354766_conjecture_1_multiplicative",
    "oeis_60957_conjecture_0",
    "oeis_A078590_conjecture",
    "oeis_A258667_conjecture_0",
    "oeis_A262781_conjecture",
    "oeis_a103885_conjecture_0",
    "oeis_a279612_conjecture_i",
    "poincare_series_conjecture",
})

# A mangled `private` name inside a raw-`Expr` string: `_private.<module
# components>.<idx>.<name>` -- under the extractor's anonymous main module just
# `_private.<idx>.<name>` (e.g. `_private.0.products`).
_PRIVATE_MANGLE_RE = re.compile(r"_private\.(?:[A-Za-z_«][\w'«»!?]*\.)*\d+\.")


def unmangle_private_names(expr_str: str) -> str:
    """Erase ``_private.<module>.<idx>.`` mangles from a raw-``Expr`` string,
    leaving the user-facing name (``_private.0.products`` -> ``products``).
    Privacy changes only the referenced constant's *name*, so for the stripped
    samples "statement preserved" means equality modulo this mangle."""
    return _PRIVATE_MANGLE_RE.sub("", expr_str)


def test_unmangle_private_names() -> None:
    # Anonymous-main-module shape (the extractor's) and module-named shape;
    # no-op on strings without a mangle.
    assert unmangle_private_names("(_private.0.products n)") == "(products n)"
    assert (
        unmangle_private_names("Not (_private.Challenge.0.Erdos101.linesWithPointsFor k S)")
        == "Not (Erdos101.linesWithPointsFor k S)"
    )
    plain = "forall (n : Nat), Nat.Prime n"
    assert unmangle_private_names(plain) == plain


# --------------------------------------------------------------------------- #
# Fixtures: extract + compile once, in one sandbox, share the results.         #
# --------------------------------------------------------------------------- #
@dataclass
class IsoData:
    """Everything the gates need, gathered from a single sandbox bring-up."""

    src_ranges: dict[str, dict[str, Any]]  # extractor records for distinct Sources/ files, by filename
    iso_ranges: dict[str, dict[str, Any]]  # extractor records for every Isolated/ file, by stem (= name)
    ref_ranges: list[dict[str, Any]]  # extractor records for the published challenge files
    cert_verdicts: dict[str, dict[str, Any]]  # certify_disproof verdicts, by stem
    compile_failures: list[str]  # stems of Isolated/ files that failed to compile


@pytest.fixture(scope="session")
def manifest() -> list[SampleRow]:
    rows = load_manifest(OEIS_DIR)
    assert len(rows) == 492
    return rows


def test_stripped_private_ids_pinned(manifest: list[SampleRow]) -> None:
    """Pure-python guard (no container): the hardcoded exception set above is
    exactly the samples whose vendored source declares `private` while the
    committed spec does not -- i.e. the ones the generator's strip changed. A
    regenerate or dataset bump that adds/removes a stripped sample must update
    STRIPPED_PRIVATE_IDS consciously rather than silently widening the modulo-
    mangle comparison."""
    from scripts.comparator_drift import drift_reasons

    derived = {
        row.id
        for row in manifest
        if "private-decl" in drift_reasons((OEIS_DIR / row.source).read_text())
        and "private-decl" not in drift_reasons((OEIS_DIR / row.statement_path).read_text())
    }
    assert derived == STRIPPED_PRIVATE_IDS, (
        f"stripped-private sample set changed;\n"
        f"  newly stripped: {sorted(derived - STRIPPED_PRIVATE_IDS)}\n"
        f"  no longer stripped: {sorted(STRIPPED_PRIVATE_IDS - derived)}"
    )


@pytest_asyncio.fixture(loop_scope="module", scope="module")
async def iso_data(manifest: list[SampleRow]) -> IsoData:
    """Bring the sandbox up once and run every Lean step inside it: extract the
    vendored sources, the Isolated files, and the reference challenge files,
    then compile every Isolated file.

    An async, module-scoped fixture (with the gate tests on the same module-scoped
    event loop) -- the only safe way to drive Inspect's sandbox lifecycle from
    pytest. Driving it from a plain fixture via ``asyncio.run`` would spin up a
    second event loop that Inspect's loop-bound globals deadlock against; sharing
    pytest-asyncio's own loop avoids that. The gates below just assert against the
    returned data, so they need no further sandbox access."""
    pin = fc_commit(OEIS_DIR)
    util_module = fc_profile(pin).util_module
    async with generate_env("pytest_oeis_isolation", pin) as env:
        source_files = sorted({r.source.rsplit("/", 1)[-1] for r in manifest})
        src = await extract(env, [SOURCES_DIR / f for f in source_files], util_module)
        iso_files = sorted(ISOLATED_DIR.glob("*.lean"))
        iso = await extract(env, iso_files, util_module)
        ref_files = sorted(REF_DIR.glob("*.lean"))
        ref = await extract(env, ref_files, util_module) if ref_files else []
        cert = await certify(env, iso_files, util_module)
        failures = await compile_all(env, iso_files)
    return IsoData(
        src_ranges={fr["file"]: fr for fr in src},
        iso_ranges={fr["file"][: -len(".lean")]: fr for fr in iso},
        ref_ranges=ref,
        cert_verdicts={v["file"][: -len(".lean")]: v for v in cert},
        compile_failures=failures,
    )


# --------------------------------------------------------------------------- #
# Gates. Async + module-scoped loop so they share the one sandbox bring-up      #
# above; the bodies are pure assertions over the precomputed ``iso_data``.      #
# --------------------------------------------------------------------------- #
@pytest.mark.asyncio(loop_scope="module")
async def test_isolated_files_are_structurally_correct(
    manifest: list[SampleRow], iso_data: IsoData
) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas (the
    cut's prediction), with the target's statement preserved verbatim."""
    failures: list[str] = []
    for row in manifest:
        name = row.id
        src_type, planned = planned_survivors(
            iso_data.src_ranges[row.source.rsplit("/", 1)[-1]], name
        )
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
        # The committed spec is the cut's prediction plus the appended
        # `.disproof` declaration (comparator-migration-plan.md §4).
        expected = sorted(planned + [f"{row.decl_name}.disproof"])
        if remaining != expected:
            failures.append(f"{name}: surviving theorems {remaining} != expected {expected}")
            continue
        iso_type, want = target_hits[0]["type"], src_type
        if name in STRIPPED_PRIVATE_IDS:
            iso_type = unmangle_private_names(iso_type)
            want = unmangle_private_names(want)
        if iso_type != want:
            failures.append(f"{name}: target statement changed during isolation")
    assert not failures, "structural validation failed:\n  " + "\n  ".join(failures)


@pytest.mark.asyncio(loop_scope="module")
async def test_disproof_declarations_certified(
    manifest: list[SampleRow], iso_data: IsoData
) -> None:
    """Every spec declares exactly its target plus ``<target>.disproof``, and
    the certifier's independent ``mkNot`` recomputation confirms the disproof's
    elaborated type is the target statement's negation (plan §4)."""
    failures: list[str] = []
    for row in manifest:
        v = iso_data.cert_verdicts.get(row.id)
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
        ref_type, iso_type = cast(str, tgt[0]["type"]), iso_types[name]
        if name in STRIPPED_PRIVATE_IDS:
            # The published file keeps `private` helpers our spec has stripped.
            ref_type = unmangle_private_names(ref_type)
            iso_type = unmangle_private_names(iso_type)
        if ref_type == iso_type:
            match += 1
        else:
            mismatch += 1
            mismatches.append(name)
    assert mismatch == 0, f"oracle mismatch for: {mismatches}"
    assert match == len(iso_data.ref_ranges), (
        f"only {match}/{len(iso_data.ref_ranges)} reference files matched"
    )
