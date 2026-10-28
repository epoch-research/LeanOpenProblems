# type: ignore
"""Generate the Wikipedia dataset: ``apn/data/wikipedia/samples.jsonl`` (the
manifest) plus the per-target isolated specs in ``apn/data/wikipedia/Isolated/``.

Membership is computed from the vendored sources: every ``theorem``/``lemma``
carrying ``@[category research open ...]`` in ``Sources/`` (see
``scripts/wikipedia_isolation.py``). Each spec is cut from the file's
de-modulized text (:func:`scripts.wikipedia_isolation.extraction_source`),
keeping the file's definitions + the single target theorem, with the
``answer(sorry) ↔`` form rewritten to plain ``P``, FC's ``@[category ...]``
lists dropped, ``private`` modifiers removed, and the derived
``<target>.disproof`` declaration appended.

This is a *vendor-time* dev tool; validate its output with
``pytest tests/test_wikipedia_isolation.py``.

Setup (one-time):

    docker build --target generate -t apn-generate \\
        --build-arg FC_COMMIT="$(cat apn/data/wikipedia/fc_commit)" apn/lean
    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-generate sleep infinity

Then generate:

    python scripts/generate_wikipedia_isolated.py
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from apn.dataset import fc_commit, fc_profile, write_manifest
from scripts.fc_statements import (
    fc_kept_flags,
    rewrite_answer_iff,
    strip_category_attrs,
    strip_comments,
)
from scripts.isolation import (
    BAKED_EXE,
    DEFAULT_CONTAINER,
    REPO,
    append_disproof,
    dependency_closure,
    host_to_container,
    isolate,
    kept_flags,
    matches_name,
    run_extractor,
    strip_private,
    tidy,
)
from scripts.wikipedia_isolation import (
    ANY_RESEARCH_ATTR_RE,
    ISOLATED_DIR,
    PROVED_IN_FILE_REASON,
    RESEARCH_OPEN_ATTR_RE,
    SORRY_ALLOWLIST_FILES,
    SOURCES_DIR,
    VALUE_TYPED_REASON,
    WIKIPEDIA_DIR,
    extraction_source,
    universe_members,
)

_SORRY_RE = re.compile(rb"\bsorry\b")
_ANSWER_SORRY_RE = re.compile(r"answer\(\s*sorry\s*\)")


def proof_is_filled(src: bytes, filerec: dict, decl_name: str) -> bool:
    for cmd in filerec["commands"]:
        if any(d["name"] == decl_name for d in cmd["decls"]):
            code = strip_comments(src[cmd["declStart"] : cmd["declEnd"]].decode("utf-8"))
            return not re.search(r"\bsorry\b", _ANSWER_SORRY_RE.sub("answer(_)", code))
    raise SystemExit(f"{decl_name}: command not found in its file record")


def extract_sources(
    staged: Path, container: str, exe: str, util_module: str, jobs: int
) -> dict[str, dict]:
    """Extractor records for every staged (de-modulized) source, by basename."""
    rels = sorted(p.name for p in staged.glob("*.lean"))
    print(f"Extracting decl ranges from {len(rels)} source files ({jobs} jobs)...", flush=True)
    chunks = [rels[i::jobs] for i in range(jobs)]
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = pool.map(
            lambda chunk: run_extractor([staged / r for r in chunk], container, exe, util_module),
            [c for c in chunks if c],
        )
    prefix = host_to_container(staged) + "/"
    by_rel: dict[str, dict] = {}
    errors: list[str] = []
    for ranges in results:
        for fr in ranges:
            assert fr["file"].startswith(prefix), fr["file"]
            if fr["errors"]:
                errors.append(f"{fr['file']}: source failed to elaborate:\n{fr['errors']}")
            by_rel[fr["file"][len(prefix) :]] = fr
    if errors:
        raise SystemExit("\n".join(errors))
    assert sorted(by_rel) == rels
    return by_rel


def check_sorries(name: str, rel: str, src: bytes, filerec: dict, flags: list[bool]) -> list[str]:
    violations: list[str] = []
    for c, keep in zip(filerec["commands"], flags):
        if not keep or not c["decls"]:
            continue
        if not _SORRY_RE.search(src[c["declStart"] : c["declEnd"]]):
            continue
        decls = [d["name"] for d in c["decls"]]
        if any(matches_name(d, name) for d in decls):
            continue
        if rel in SORRY_ALLOWLIST_FILES:
            print(f"  note: {name}: allowlisted extra sorry in {decls}")
            continue
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

    staged = Path(tempfile.mkdtemp(prefix=".wikipedia_extract_", dir=REPO))
    try:
        for p in SOURCES_DIR.glob("*.lean"):
            (staged / p.name).write_text(extraction_source(p.name))
        by_rel = extract_sources(
            staged,
            args.container,
            args.exe,
            fc_profile(fc_commit(WIKIPEDIA_DIR)).util_module,
            args.jobs,
        )
        srcs = {rel: (staged / rel).read_bytes() for rel in by_rel}
    finally:
        shutil.rmtree(staged)

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    rows: list[dict] = []
    forms: dict[str | None, int] = {}
    n_excluded = 0
    problems: list[str] = []
    casefold_seen: dict[str, int] = {}
    for rel in sorted(by_rel):
        filerec = by_rel[rel]
        src = srcs[rel]
        members = universe_members(src, filerec)
        text_all = src.decode("utf-8")
        per_command = sum(
            len(ANY_RESEARCH_ATTR_RE.findall(src[c["declStart"] : c["declEnd"]].decode("utf-8")))
            for c in filerec["commands"]
        )
        if per_command != len(ANY_RESEARCH_ATTR_RE.findall(text_all)):
            raise SystemExit(f"{rel}: research attributes not all attached to commands")
        if len(members) != len(RESEARCH_OPEN_ATTR_RE.findall(text_all)):
            raise SystemExit(f"{rel}: research-open attribute on a non-declaration command")
        for decl in members:
            row: dict = {"id": decl["name"], "source": f"Sources/{rel}"}
            if "sorryAx" in decl["type"]:
                row["excluded"] = VALUE_TYPED_REASON
                n_excluded += 1
                rows.append(row)
                continue
            if proof_is_filled(src, filerec, decl["name"]):
                row["excluded"] = PROVED_IN_FILE_REASON
                n_excluded += 1
                rows.append(row)
                continue

            closure = dependency_closure(filerec, decl["name"])
            flags = fc_kept_flags(src, filerec, kept_flags(filerec, closure))
            problems.extend(check_sorries(decl["name"], rel, src, filerec, flags))
            text = tidy(isolate(src, filerec, flags)).decode("utf-8")
            text = strip_private(text)
            n_answers = strip_comments(text).count("answer(")
            if n_answers > 1:
                problems.append(f"{decl['name']}: {n_answers} answer( in isolated spec")
                continue
            form = None
            if n_answers == 1:
                text, form, n = rewrite_answer_iff(text)
                if form is None or n != 1 or "answer(" in strip_comments(text):
                    problems.append(f"{decl['name']}: answer(...) ↔ rewrite did not apply cleanly")
                    continue
            forms[form] = forms.get(form, 0) + 1
            row["answer_form"] = form
            text, _ = strip_category_attrs(text)
            text, _ = append_disproof(text, decl["name"], decl["name"])
            n_seen = casefold_seen[decl["name"].casefold()] = (
                casefold_seen.get(decl["name"].casefold(), 0) + 1
            )
            filename = f"{decl['name']}.lean" if n_seen == 1 else f"{decl['name']}_{n_seen}.lean"
            if n_seen > 1:
                row["statement"] = f"Isolated/{filename}"
            (ISOLATED_DIR / filename).write_text(text)
            rows.append(row)

    if problems:
        raise SystemExit(f"{len(problems)} problem(s):\n" + "\n".join(problems))

    write_manifest(WIKIPEDIA_DIR, rows)
    print(
        f"Wrote {len(rows)} manifest rows ({n_excluded} excluded) and "
        f"{len(rows) - n_excluded} isolated files to {ISOLATED_DIR}.\n"
        f"Forms: {forms}\n"
        "Validate with: pytest tests/test_wikipedia_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
