# type: ignore
"""Generate the Erdős universe: ``apn/data/erdos/samples.jsonl`` (the manifest)
plus the per-target isolated specs in ``apn/data/erdos/Isolated/``.

Membership is *defined* by the vendored sources, so this script computes it:
every ``theorem``/``lemma`` declaration carrying a ``@[category research ...]``
attribute in ``Sources/`` (the Bloom statement selection's 48
``FormalConjectures/ErdosProblems`` files at the pinned FC commit; see
``apn/data/erdos/NOTICE.md``) is a universe member, resolution status
notwithstanding. Value-typed ``answer(sorry)`` members -- a ``sorryAx`` in the
elaborated statement type, unscoreable by SafeVerify -- and members carrying a
complete in-file proof become ``excluded`` manifest rows with no isolated
spec. Each kept member's spec keeps its file's
definitions + the single target theorem and cuts every other standalone
``theorem``/``lemma`` and FC's anonymous ``example`` sanity checks. All four
``answer(...) ↔`` statement forms are rewritten to plain ``P`` -- including
recorded-verdict ``answer(True/False)`` members, whose answer key must not
leak -- and FC's recorded-verdict annotations are stripped (see
``scripts/erdos_isolation.py``; the rewrite's re-elaboration certificate lives
in ``scripts/fc_statements.py`` / ``tests/test_erdos_isolation.py``). The
per-row ``answer_form``/``category_at_pin`` land in the manifest for tooling
and tests; ``apn/dataset.py`` deliberately keeps them out of sample metadata.

This is a *vendor-time* dev tool, not imported at runtime; ``apn/dataset.py``
reads the committed manifest + ``Isolated/`` directly. The committed files are
validated by ``tests/test_erdos_isolation.py`` -- re-extraction structural
checks incl. the per-form rewrite certificates, and the authoritative
``lake env lean -o`` compile gate -- which run the Lean toolchain in a
container. After regenerating, run those tests to confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean
container with the repo mounted; the baked extractor of the Dockerfile's
``generate`` stage is the default ``--exe``:

    docker build --target generate -t apn-generate \\
        --build-arg FC_COMMIT="$(cat apn/data/erdos/fc_commit)" apn/lean
    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-generate sleep infinity

Then generate:

    python scripts/generate_erdos_isolated.py
"""

from __future__ import annotations

import argparse
import re
import sys
from concurrent.futures import ThreadPoolExecutor

from apn.dataset import fc_commit, fc_profile, write_manifest
from scripts.erdos_isolation import (
    ERDOS_DIR,
    ISOLATED_DIR,
    PROVED_IN_FILE_REASON,
    RESEARCH_ATTR_RE,
    SORRY_ALLOWLIST_FILES,
    SOURCES_DIR,
    VALUE_TYPED_REASON,
    VERDICT_PROSE,
    research_categories,
    strip_fc_annotations,
    universe_members,
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
    run_extractor,
    tidy,
)

_SORRY_RE = re.compile(rb"\bsorry\b")
_ANSWER_SORRY_RE = re.compile(r"answer\(\s*sorry\s*\)")


def proof_is_filled(src: bytes, filerec: dict, decl_name: str) -> bool:
    """Whether the member's command carries a complete formal proof: no
    ``sorry`` token anywhere in its comment-stripped span, the statement's
    ``answer(sorry)`` placeholder masked out first."""
    for cmd in filerec["commands"]:
        if any(d["name"] == decl_name for d in cmd["decls"]):
            code = strip_comments(src[cmd["declStart"] : cmd["declEnd"]].decode("utf-8"))
            return not re.search(r"\bsorry\b", _ANSWER_SORRY_RE.sub("answer(_)", code))
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


def check_sorries(name: str, rel: str, src: bytes, filerec: dict, flags: list[bool]) -> list[str]:
    """The isolated spec's sorry'd non-target *declarations* (checked on the
    kept commands' source spans; no-decl commands are skipped, since a module
    doc may say "sorry" in prose). A stray ``sorry`` in a kept sibling would
    make the sample unscorable-as-intended; allowlisted files (sorry'd
    textbook-lemma dependencies of kept defs) are reported, not fatal --
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
            continue  # the target's own `sorry` proof (and, pre-rewrite, answer(...))
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

    by_rel = extract_sources(
        args.container, args.exe, fc_profile(fc_commit(ERDOS_DIR)).util_module, args.jobs
    )

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    rows: list[dict] = []
    forms: dict[str | None, int] = {}
    annotations = {"category": 0, "prose": 0}
    prose_hits = {snippet: 0 for snippet in VERDICT_PROSE}
    n_excluded = 0
    problems: list[str] = []
    # Spec filenames must stay distinct on case-insensitive filesystems (the
    # repo is developed on one): ids differing only in case (the Tsoukalas-era
    # 889 had V1/v1 variants; none currently do) get a deterministic ordinal
    # suffix, recorded in the row's `statement` field.
    casefold_seen: dict[str, int] = {}
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
        for decl, category in members:
            row: dict = {"id": decl["name"], "source": f"Sources/{rel}"}
            if "sorryAx" in decl["type"]:
                row["excluded"] = VALUE_TYPED_REASON
                n_excluded += 1
            elif proof_is_filled(src, filerec, decl["name"]):
                row["excluded"] = PROVED_IN_FILE_REASON
                n_excluded += 1
            row["erdos_number"] = int(rel.removesuffix(".lean"))
            row["category_at_pin"] = category
            if "excluded" in row:
                rows.append(row)
                continue

            closure = dependency_closure(filerec, decl["name"])
            flags = fc_kept_flags(src, filerec, kept_flags(filerec, closure))
            problems.extend(check_sorries(decl["name"], rel, src, filerec, flags))
            text = tidy(isolate(src, filerec, flags)).decode("utf-8")
            # Census `answer(` in *code* only -- kept docs may mention it in prose.
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
            for snippet in VERDICT_PROSE:
                if snippet in text:
                    prose_hits[snippet] += 1
            text, counts = strip_fc_annotations(text)
            for kind, n in counts.items():
                annotations[kind] += n
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
    stale = [s for s, n in prose_hits.items() if n == 0]
    if stale:
        raise SystemExit(
            f"{len(stale)} VERDICT_PROSE snippet(s) matched nothing (stale against "
            f"the vendored sources):\n" + "\n".join(repr(s[:80]) for s in stale)
        )

    write_manifest(ERDOS_DIR, rows)
    print(
        f"Wrote {len(rows)} manifest rows ({n_excluded} excluded) and "
        f"{len(rows) - n_excluded} isolated files to {ISOLATED_DIR}.\n"
        f"Forms: {forms}\nAnnotations stripped: {annotations}\n"
        "Validate with: pytest tests/test_erdos_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
