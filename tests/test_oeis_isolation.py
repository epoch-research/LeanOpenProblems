"""Authoritative validation of the committed ``apn/data/oeis/Isolated/`` specs.

``scripts/generate_isolated.py`` only *writes* the isolated files; the checks
that prove they are sound live here. There is no local Lean toolchain, so these
run the extractor and the ``lake env lean -o`` compile in a container (the same
elaboration the scorer performs at eval time) -- "CI has no Lean" is not a reason
to weaken the gate; we bring Lean up in Docker.

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

These require Docker + a Lean container holding the extractor; when neither a
running container nor the ``generate`` image is available they ``skip`` (the
pure-Python structural invariant in ``test_oeis.py`` always runs). Point them at
a container with ``APN_LEAN_CONTAINER`` / build the image as
``docker build --target generate -t apn-generate apn/lean``.
"""

from __future__ import annotations

import os
import shutil
import subprocess

import pytest

from scripts.oeis_isolation import (
    AUTO_DIR,
    BAKED_EXE,
    CONTAINER_PROJECT,
    CONTAINER_REPO,
    DEFAULT_CONTAINER,
    DEV_EXE,
    ISOLATED_DIR,
    MAPPING_FILE,
    REF_DIR,
    REPO,
    compile_all,
    matches_name,
    parse_mapping,
    planned_survivors,
    run_extractor,
    theorem_command_decls,
    theorem_decls,
)

GENERATE_IMAGE = os.environ.get("APN_GENERATE_IMAGE", "apn-generate")


def _docker_available() -> bool:
    return shutil.which("docker") is not None


def _container_running(name: str) -> bool:
    proc = subprocess.run(
        ["docker", "inspect", "-f", "{{.State.Running}}", name],
        capture_output=True,
        text=True,
    )
    return proc.returncode == 0 and proc.stdout.strip() == "true"


def _exe_present(container: str, exe: str) -> bool:
    return subprocess.run(["docker", "exec", container, "test", "-x", exe]).returncode == 0


def _image_exists(image: str) -> bool:
    return subprocess.run(["docker", "image", "inspect", image], capture_output=True).returncode == 0


# The extractor source, mounted into the container at /repo.
_SRC_DIR = f"{CONTAINER_REPO}/apn/lean/extract_ranges"


def _ensure_extractor(container: str) -> str:
    """Path to a *current* extractor in ``container``.

    When the repo is mounted (the normal case) the extractor is (re)built from
    the in-tree source, so it always matches the ``ExtractRanges.lean`` under
    test -- a binary baked into an older image can lag and silently drop fields
    (e.g. the ``deps`` the structural check relies on). Falls back to a baked
    binary only when no source is mounted, and skips if neither is available.
    """
    if subprocess.run(
        ["docker", "exec", container, "test", "-f", f"{_SRC_DIR}/ExtractRanges.lean"]
    ).returncode == 0:
        build = subprocess.run(
            ["docker", "exec", "-w", _SRC_DIR, container, "lake", "build", "extract_ranges"],
            capture_output=True, text=True,
        )
        if build.returncode != 0:
            pytest.skip(f"extractor failed to build in '{container}':\n{build.stderr[-2000:]}")
        return DEV_EXE
    if _exe_present(container, BAKED_EXE):
        return BAKED_EXE
    pytest.skip(f"no extractor source or baked binary in container '{container}'")


@pytest.fixture(scope="session")
def lean_container() -> tuple[str, str]:
    """A running Lean container plus the extractor path inside it, or ``skip``.

    Reuses a container named ``APN_LEAN_CONTAINER`` (default ``apn-isolate-dev``)
    if it is already up; otherwise spins an ephemeral one from the ``generate``
    image with the repo mounted, and tears it down at session end. Skips when
    neither is available so a Docker-less machine still collects/runs the rest of
    the suite.
    """
    if not _docker_available():
        pytest.skip("docker not available")
    name = os.environ.get("APN_LEAN_CONTAINER", DEFAULT_CONTAINER)
    started = False
    if not _container_running(name):
        if not _image_exists(GENERATE_IMAGE):
            pytest.skip(
                f"no running container '{name}' and image '{GENERATE_IMAGE}' absent; "
                f"build it with `docker build --target generate -t {GENERATE_IMAGE} apn/lean` "
                "or start a dev container (see scripts/generate_isolated.py)."
            )
        subprocess.run(
            ["docker", "run", "-d", "--rm", "--name", name,
             "-v", f"{REPO}:{CONTAINER_REPO}", "-w", CONTAINER_PROJECT,
             GENERATE_IMAGE, "sleep", "infinity"],
            check=True, capture_output=True,
        )
        started = True
    try:
        yield name, _ensure_extractor(name)
    finally:
        if started:
            subprocess.run(["docker", "rm", "-f", name], capture_output=True)


@pytest.fixture(scope="session")
def mapping() -> list[tuple[str, list[str]]]:
    entries = parse_mapping(MAPPING_FILE.read_text())
    assert len(entries) == 492
    return entries


@pytest.fixture(scope="session")
def auto_ranges(lean_container, mapping) -> dict[str, dict]:
    """Extractor records for the distinct ``Auto/`` source files, by filename."""
    container, exe = lean_container
    source_files = sorted({files[0] for _, files in mapping})
    recs = run_extractor([AUTO_DIR / f for f in source_files], container, exe)
    return {fr["file"].rsplit("/", 1)[-1]: fr for fr in recs}


@pytest.fixture(scope="session")
def iso_ranges(lean_container) -> dict[str, dict]:
    """Extractor records for every committed ``Isolated/`` file, by stem (= name)."""
    container, exe = lean_container
    recs = run_extractor(sorted(ISOLATED_DIR.glob("*.lean")), container, exe)
    return {fr["file"].rsplit("/", 1)[-1][: -len(".lean")]: fr for fr in recs}


def test_isolated_files_are_structurally_correct(mapping, auto_ranges, iso_ranges) -> None:
    """Each isolated file carries exactly the target + its dependency lemmas (the
    cut's prediction), with the target's statement preserved verbatim."""
    failures: list[str] = []
    for name, files in mapping:
        src_type, planned = planned_survivors(auto_ranges[files[0]], name)
        fr = iso_ranges.get(name)
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


def test_isolated_files_compile(lean_container, iso_ranges) -> None:
    """The authoritative gate: every isolated file compiles with the scorer's
    exact ``lake env lean -o`` command."""
    container, _ = lean_container
    failed = compile_all(sorted(ISOLATED_DIR.glob("*.lean")), container)
    assert not failed, f"{len(failed)} isolated file(s) failed to compile: {failed}"


def test_oracle_matches_published_challenge_files(lean_container, iso_ranges) -> None:
    """For each solved problem the paper published, our isolated target's
    elaborated type matches its ``target_theorem_0`` (the paper renames the
    conjecture). Confirms isolation reproduces the published challenge statement."""
    container, exe = lean_container
    ref_files = sorted(REF_DIR.glob("*.lean"))
    if not ref_files:
        pytest.skip("no reference challenge files vendored")
    ref_ranges = run_extractor(ref_files, container, exe)

    def target_type(name: str, fr: dict) -> str:
        (target,) = [d for d in theorem_command_decls(fr) if matches_name(d["name"], name)]
        return target["type"]

    iso_types = {name: target_type(name, fr) for name, fr in iso_ranges.items()}
    match = mismatch = unmatched = 0
    mismatches: list[str] = []
    for fr in ref_ranges:
        name = fr["file"].rsplit("/", 1)[-1][: -len(".lean")]
        if name not in iso_types:
            unmatched += 1
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
    assert match == len(ref_files), f"only {match}/{len(ref_files)} reference files matched"
