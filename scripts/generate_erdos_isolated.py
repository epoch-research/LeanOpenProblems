# type: ignore
"""Generate the per-target isolated Erdős-attempted-set specs in
``apn/data/erdos/Isolated/`` (plus ``MAPPING.json``).

Membership comes from ``subsets/tsoukalas.json`` (the Tsoukalas paper's
canonical 353-statement Erdős attempted set, arXiv 2605.22763, minus its 3
names with no statement at the vendored FC commit, with its 1 upstream rename
applied) -> 350 kept targets. ``Sources/`` itself is the whole FC
ErdosProblems directory and says nothing about membership; generating specs
for a further set means pointing ``GENERATED_SUBSET`` at another subsets/ file.
Each short attempted name is resolved to the
unique vendored ``Sources/`` declaration via suffix matching; the resulting
spec keeps that file's definitions + the single target theorem and cuts every
other standalone ``theorem``/``lemma`` and FC's anonymous ``example`` sanity
checks. All four ``answer(...) ↔`` statement forms are rewritten to plain
``P`` -- including the 13 recorded-verdict ``answer(True/False)`` members,
whose answer key must not leak -- and the per-form census is asserted (see
``scripts/erdos_isolation.py``; the rewrite's re-elaboration certificate lives
in ``scripts/fc_statements.py`` / ``tests/test_erdos_isolation.py``).

This is a *vendor-time* dev tool, not imported at runtime; ``apn/dataset.py``
reads the committed ``Isolated/`` + ``MAPPING.json`` directly. The committed
files are validated by ``tests/test_erdos_isolation.py`` -- re-extraction
structural checks incl. the per-form rewrite certificates, and the
authoritative ``lake env lean -o`` compile gate -- which run the Lean
toolchain in a container. After regenerating, run those tests to confirm the
output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean
container with the repo mounted; the baked extractor of the Dockerfile's
``generate`` stage is the default ``--exe``:

    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        "$IMAGE_REPOSITORY:LeanOpenProblems_generate_<version>" sleep infinity

Then generate:

    python scripts/generate_erdos_isolated.py
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from scripts.erdos_isolation import (
    FC_COMMIT,
    FORM_CENSUS,
    GENERATED_SUBSET,
    ISOLATED_DIR,
    MAPPING_FILE,
    SORRY_ALLOWLIST,
    SOURCES_DIR,
    ANNOTATION_TOTALS,
    kept_names,
    strip_fc_annotations,
)
from scripts.fc_statements import (
    fc_kept_flags,
    rewrite_answer_iff,
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
    resolve_target,
    run_extractor,
    theorem_decls,
    tidy,
)

_SORRY_RE = re.compile(rb"\bsorry\b")


def extract_sources(container: str, exe: str) -> dict[str, dict]:
    """Extractor records for every vendored source file, keyed by *relative*
    path under ``Sources/`` (flat here, so relpath == basename)."""
    rels = sorted(
        str(p.relative_to(SOURCES_DIR)) for p in SOURCES_DIR.rglob("*.lean")
    )
    print(f"Extracting decl ranges from {len(rels)} source files...", flush=True)
    ranges = run_extractor([SOURCES_DIR / rel for rel in rels], container, exe)
    prefix = host_to_container(SOURCES_DIR) + "/"
    by_rel: dict[str, dict] = {}
    for fr in ranges:
        assert fr["file"].startswith(prefix), fr["file"]
        if fr["errors"]:
            raise SystemExit(f"{fr['file']}: source failed to elaborate:\n{fr['errors']}")
        by_rel[fr["file"][len(prefix) :]] = fr
    return by_rel


def build_mapping(names: list[str], by_rel: dict[str, dict]) -> list[tuple[str, str]]:
    """Resolve each kept *short* name to the unique vendored declaration:
    ``(fully_qualified_decl_name, source_relpath)`` entries, in attempt-list
    order. Exactly one theorem across all files may match (suffix semantics --
    the declarations live inside ``namespace ErdosN`` blocks)."""
    mapping: list[tuple[str, str]] = []
    for name in names:
        hits = [
            (d["name"], rel)
            for rel, fr in sorted(by_rel.items())
            for d in theorem_decls(fr)
            if matches_name(d["name"], name)
        ]
        if len(hits) != 1:
            raise SystemExit(f"{name}: {len(hits)} matching declarations: {hits}")
        mapping.append(hits[0])
    full_names = [full for full, _ in mapping]
    if len(set(full_names)) != len(full_names):
        raise SystemExit("distinct attempted names resolved to the same declaration")
    return mapping


def check_sorries(name: str, src: bytes, filerec: dict, flags: list[bool]) -> None:
    """Assert the isolated spec's only sorry'd *declaration* is the target
    (checked on the kept commands' source spans; no-decl commands are skipped,
    since a module doc may say "sorry" in prose). A stray ``sorry`` in a kept
    sibling would make the sample unscorable-as-intended; an allowlisted one
    (1055's `exists_p` dependency) is reported, not fatal."""
    for c, keep in zip(filerec["commands"], flags):
        if not keep or not c["decls"]:
            continue
        if not _SORRY_RE.search(src[c["declStart"] : c["declEnd"]]):
            continue
        decls = [d["name"] for d in c["decls"]]
        if any(matches_name(d, name) for d in decls):
            continue  # the target's own `sorry` proof (and, pre-rewrite, answer(...))
        if name in SORRY_ALLOWLIST:
            print(f"  note: {name}: allowlisted extra sorry in {decls}")
            continue
        raise SystemExit(f"{name}: unexpected sorry outside the target, in {decls}")


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=BAKED_EXE, help="extractor path in container (default: baked)")
    args = ap.parse_args()

    names = kept_names()
    by_rel = extract_sources(args.container, args.exe)
    mapping = build_mapping(names, by_rel)

    # Sources/ is the whole FC ErdosProblems directory, so most files host no
    # target of the generated subset; that is expected, not an error.
    unused = sorted(set(by_rel) - {rel for _, rel in mapping})
    print(f"{len(mapping)} targets across {len(by_rel) - len(unused)} source files "
          f"({len(unused)} files host no {GENERATED_SUBSET} target)")

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    census: dict[str | None, int] = {form: 0 for form in FORM_CENSUS}
    annotations = {kind: 0 for kind in ANNOTATION_TOTALS}
    for name, rel in mapping:
        filerec = by_rel[rel]
        src = (SOURCES_DIR / rel).read_bytes()
        target = resolve_target(name, filerec)  # the unique target theorem
        closure = dependency_closure(filerec, target["name"])
        flags = fc_kept_flags(src, filerec, kept_flags(filerec, closure))
        check_sorries(name, src, filerec, flags)
        text = tidy(isolate(src, filerec, flags)).decode("utf-8")
        # Census `answer(` in *code* only -- kept docs may mention it in prose.
        n_answers = strip_comments(text).count("answer(")
        if n_answers > 1:
            raise SystemExit(f"{name}: {n_answers} answer( occurrences in isolated spec")
        form = None
        if n_answers == 1:
            text, form, n = rewrite_answer_iff(text)
            if form is None or n != 1 or "answer(" in strip_comments(text):
                raise SystemExit(f"{name}: answer(...) ↔ rewrite did not apply cleanly")
        census[form] += 1
        text, counts = strip_fc_annotations(text)
        for kind, n in counts.items():
            annotations[kind] += n
        (ISOLATED_DIR / f"{name}.lean").write_text(text)

    if census != FORM_CENSUS:
        raise SystemExit(f"form census drifted: {census} != {FORM_CENSUS}")
    if annotations != ANNOTATION_TOTALS:
        raise SystemExit(f"annotation strip drifted: {annotations} != {ANNOTATION_TOTALS}")

    MAPPING_FILE.write_text(
        json.dumps(
            {
                "_meta": {
                    "description": (
                        "Runnable targets of the Erdős dataset: fully qualified "
                        "declaration name -> its file under Sources/. One isolated "
                        "spec per row, under Isolated/<target>.lean. This is the "
                        "universe of what can be run; which targets form a given "
                        "evaluation set is defined under subsets/."
                    ),
                    "generator": "scripts/generate_erdos_isolated.py",
                    "generated_subset": GENERATED_SUBSET,
                    "fc_commit": FC_COMMIT,
                },
                "targets": [
                    {"target": name, "source_file": rel} for name, rel in mapping
                ],
            },
            indent=1,
            ensure_ascii=False,
        )
        + "\n"
    )
    n_rewritten = sum(n for form, n in census.items() if form is not None)
    print(
        f"Wrote {len(mapping)} isolated files ({n_rewritten} rewritten: "
        f"{ {k: v for k, v in census.items() if k} }) to "
        f"{ISOLATED_DIR} and {MAPPING_FILE.name}.\n"
        "Validate with: pytest tests/test_erdos_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
