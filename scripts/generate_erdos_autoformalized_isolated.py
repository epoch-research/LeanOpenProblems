# type: ignore
"""Generate the Erdős-autoformalized universe:
``apn/data/erdos_autoformalized/samples.jsonl`` (the manifest) plus the
per-target isolated specs in ``apn/data/erdos_autoformalized/Isolated/``.

Membership is *defined* by the vendored sources, so this script computes it:
every ``theorem``/``lemma`` declaration carrying a ``@[category research ...]``
attribute in ``Sources/`` (the 18 files of our own autoformalization run; see
``apn/data/erdos_autoformalized/NOTICE.md``) is a universe member. Each
member's spec keeps its file's definitions + the single target theorem and
cuts every other standalone ``theorem``/``lemma``, then drops the target's
``@[category ...]`` classification list (catalogue metadata, not part of the
statement).

Unlike ``scripts/generate_erdos_isolated.py`` there is no un-recording surgery
and no exclusion machinery: the sources were vendored already in shipping form
(no ``answer(...)`` statements, every proof a bare ``sorry``, no recorded
verdicts). Generation *asserts* those invariants -- a member that trips one
(value-typed statement, filled proof, an ``answer(`` occurrence) fails the
run for a curation decision instead of becoming an excluded row.

This is a *vendor-time* dev tool, not imported at runtime; ``apn/dataset.py``
reads the committed manifest + ``Isolated/`` directly. The committed files are
validated by ``tests/test_erdos_autoformalized_isolation.py`` --
re-extraction structural checks and the authoritative ``lake env lean -o``
compile gate -- which run the Lean toolchain in a container. After
regenerating, run those tests to confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean
container with the repo mounted; the baked extractor of the Dockerfile's
``generate`` stage is the default ``--exe``:

    docker build --target generate -t apn-generate \\
        --build-arg FC_COMMIT="$(cat apn/data/erdos_autoformalized/fc_commit)" apn/lean
    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-generate sleep infinity

Then generate:

    python scripts/generate_erdos_autoformalized_isolated.py
"""

from __future__ import annotations

import argparse
import re
import sys
from concurrent.futures import ThreadPoolExecutor

from apn.dataset import fc_commit, fc_profile, write_manifest
from scripts.erdos_autoformalized_isolation import (
    ERDOS_AUTOFORMALIZED_DIR,
    ISOLATED_DIR,
    SOURCES_DIR,
)
from scripts.erdos_isolation import (
    RESEARCH_ATTR_RE,
    research_categories,
    universe_members,
)
from scripts.fc_statements import (
    fc_kept_flags,
    strip_category_attrs,
    strip_comments,
)
from scripts.isolation import (
    DEFAULT_CONTAINER,
    BAKED_EXE,
    dependency_closure,
    host_to_container,
    isolate,
    kept_flags,
    matches_name,
    run_extractor,
    tidy,
)

_SORRY_RE = re.compile(rb"\bsorry\b")


def proof_is_bare_sorry(src: bytes, filerec: dict, decl_name: str) -> bool:
    """Whether the member's command carries the expected unfilled proof: a
    ``sorry`` token in its comment-stripped span (there is no ``answer(sorry)``
    placeholder in this dataset to mask out first)."""
    for cmd in filerec["commands"]:
        if any(d["name"] == decl_name for d in cmd["decls"]):
            code = strip_comments(src[cmd["declStart"] : cmd["declEnd"]].decode("utf-8"))
            return bool(re.search(r"\bsorry\b", code))
    raise SystemExit(f"{decl_name}: command not found in its file record")


def extract_sources(container: str, exe: str, util_module: str, jobs: int) -> dict[str, dict]:
    """Extractor records for every vendored source file, keyed by *relative*
    path under ``Sources/`` (flat here, so relpath == basename). Extraction
    elaborates each file, so the sweep runs ``jobs`` extractor processes over
    chunks of the list."""
    rels = sorted(str(p.relative_to(SOURCES_DIR)) for p in SOURCES_DIR.rglob("*.lean"))
    print(f"Extracting decl ranges from {len(rels)} source files ({jobs} jobs)...", flush=True)
    chunks = [rels[i::jobs] for i in range(jobs)]
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = pool.map(
            lambda chunk: run_extractor(
                [SOURCES_DIR / r for r in chunk], container, exe, util_module
            ),
            [c for c in chunks if c],
        )
    prefix = host_to_container(SOURCES_DIR) + "/"
    by_rel: dict[str, dict] = {}
    for ranges in results:
        for fr in ranges:
            assert fr["file"].startswith(prefix), fr["file"]
            if fr["errors"]:
                raise SystemExit(f"{fr['file']}: source failed to elaborate:\n{fr['errors']}")
            by_rel[fr["file"][len(prefix) :]] = fr
    assert sorted(by_rel) == rels
    return by_rel


def check_sorries(name: str, src: bytes, filerec: dict, flags: list[bool]) -> list[str]:
    """The isolated spec's sorry'd non-target *declarations* (checked on the
    kept commands' source spans; no-decl commands are skipped, since a module
    doc may say "sorry" in prose). A stray ``sorry`` in a kept sibling would
    make the sample unscorable-as-intended; there is no allowlist here --
    violations are collected and fail the run at the end, so one run surfaces
    them all."""
    violations: list[str] = []
    for c, keep in zip(filerec["commands"], flags):
        if not keep or not c["decls"]:
            continue
        if not _SORRY_RE.search(src[c["declStart"] : c["declEnd"]]):
            continue
        decls = [d["name"] for d in c["decls"]]
        if any(matches_name(d, name) for d in decls):
            continue  # the target's own `sorry` proof
        violations.append(f"{name}: unexpected sorry outside the target, in {decls}")
    return violations


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=BAKED_EXE, help="extractor path in container (default: baked)")
    ap.add_argument("--jobs", type=int, default=6, help="parallel extractor processes")
    args = ap.parse_args()

    by_rel = extract_sources(
        args.container,
        args.exe,
        fc_profile(fc_commit(ERDOS_AUTOFORMALIZED_DIR)).util_module,
        args.jobs,
    )

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    rows: list[dict] = []
    n_category_stripped = 0
    problems: list[str] = []
    filenames_casefolded: set[str] = set()
    for rel in sorted(by_rel, key=lambda r: int(r.removesuffix(".lean"))):
        filerec = by_rel[rel]
        src = (SOURCES_DIR / rel).read_bytes()
        members = universe_members(src, filerec)
        # No research attribute may escape the census: the file total must be
        # accounted for by per-command hits (members + anonymous examples).
        per_command = sum(
            len(research_categories(src[c["declStart"] : c["declEnd"]]))
            for c in filerec["commands"]
        )
        file_total = len(RESEARCH_ATTR_RE.findall(src.decode("utf-8")))
        if per_command != file_total:
            raise SystemExit(
                f"{rel}: {file_total} research attributes in file, only "
                f"{per_command} attached to commands"
            )
        if not members:
            raise SystemExit(f"{rel}: no universe members")
        for decl, category in members:
            # The shipping-form invariants (see module docstring): a hit means
            # the vendored sources changed shape and needs a curation decision.
            if "sorryAx" in decl["type"]:
                raise SystemExit(f"{decl['name']}: value-typed statement (sorryAx in type)")
            if not proof_is_bare_sorry(src, filerec, decl["name"]):
                raise SystemExit(f"{decl['name']}: proof is not a bare sorry")

            closure = dependency_closure(filerec, decl["name"])
            flags = fc_kept_flags(src, filerec, kept_flags(filerec, closure))
            problems.extend(check_sorries(decl["name"], src, filerec, flags))
            text = tidy(isolate(src, filerec, flags)).decode("utf-8")
            if "answer(" in strip_comments(text):
                problems.append(f"{decl['name']}: answer( in isolated spec")
                continue
            text, n = strip_category_attrs(text)
            if n != 1:
                problems.append(f"{decl['name']}: {n} @[category ...] lists stripped, not 1")
                continue
            n_category_stripped += n
            filename = f"{decl['name']}.lean"
            if filename.casefold() in filenames_casefolded:
                # The repo is developed on a case-insensitive filesystem; a
                # collision needs the erdos generator's `statement` machinery.
                raise SystemExit(f"{decl['name']}: casefolded spec filename collision")
            filenames_casefolded.add(filename.casefold())
            (ISOLATED_DIR / filename).write_text(text)
            rows.append(
                {
                    "id": decl["name"],
                    "source": f"Sources/{rel}",
                    "erdos_number": int(rel.removesuffix(".lean")),
                    "category": category,
                }
            )

    if problems:
        raise SystemExit(f"{len(problems)} problem(s):\n" + "\n".join(problems))

    write_manifest(ERDOS_AUTOFORMALIZED_DIR, rows)
    print(
        f"Wrote {len(rows)} manifest rows and {len(rows)} isolated files to "
        f"{ISOLATED_DIR}.\nCategory lists stripped: {n_category_stripped}\n"
        "Validate with: pytest tests/test_erdos_autoformalized_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
