# type: ignore
"""Generate the FC directory-scoped research-open datasets: each dataset's
``apn/data/<name>/samples.jsonl`` (the manifest) plus the per-target isolated
specs in ``apn/data/<name>/Isolated/``.

Membership is *defined* by the vendored sources, so this script computes it:
every ``theorem``/``lemma`` declaration carrying a ``@[category research
open]`` attribute in ``Sources/`` (the dataset's FC-directory files hosting at
least one such statement at the pinned FC commit; see the dataset's
``NOTICE.md``) is a universe member. ``research solved`` statements sharing
those files are not members and are cut from the specs like any other sibling.
Value-typed ``answer(sorry)`` members -- a ``sorryAx`` in the elaborated
statement type, unscoreable by SafeVerify -- and members carrying a complete
in-file proof become ``excluded`` manifest rows with no isolated spec; so do
members whose spec this pipeline cannot ship soundly (a stray ``sorry``
outside the allowlist, an ``answer(...)`` form the rewrite does not cover) --
these datasets cast a wide net, and a problematic member is *dropped with its
reason recorded* rather than holding up the rest. Each kept member's spec
keeps its file's definitions + the single target theorem and cuts every other
standalone ``theorem``/``lemma`` and FC's anonymous ``example`` sanity checks.
All ``answer(...) ↔`` statement forms are rewritten to plain ``P`` (see
``scripts/fc_statements.py`` for the rewrite and its re-elaboration
certificate; ``tests/test_fc_open_isolation.py`` runs the certificate), and
every kept declaration's ``@[category ...]`` classification list is dropped.
The per-row ``answer_form`` lands in the manifest for tooling and tests;
``apn/dataset.py`` deliberately keeps it out of sample metadata.

This is a *vendor-time* dev tool, not imported at runtime; ``apn/dataset.py``
reads the committed manifest + ``Isolated/`` directly. The committed files are
validated by ``tests/test_fc_open_isolation.py`` -- re-extraction structural
checks incl. the per-form rewrite certificates, and the authoritative
``lake env lean -o`` compile gate -- which run the Lean toolchain in a
container. After regenerating, run those tests to confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean
container with the repo mounted; the baked extractor of the Dockerfile's
``generate`` stage is the default ``--exe``:

    docker build --target generate -t apn-generate \\
        --build-arg FC_COMMIT="$(cat apn/data/wikipedia/fc_commit)" apn/lean
    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-generate sleep infinity

Then generate (all three datasets, or name the ones to regenerate):

    python scripts/generate_fc_open_isolated.py [wikipedia arxiv oeis_open]
"""

from __future__ import annotations

import argparse
import re
import sys
from concurrent.futures import ThreadPoolExecutor

from apn.dataset import fc_commit, fc_profile, write_manifest
from scripts.fc_open_isolation import (
    DATASETS,
    DROPPED_REASON_PREFIX,
    PROVED_IN_FILE_REASON,
    VALUE_TYPED_REASON,
    FCOpenDataset,
)
from scripts.fc_statements import (
    RESEARCH_ATTR_RE,
    fc_kept_flags,
    research_categories,
    rewrite_answer_iff,
    strip_category_attrs,
    strip_comments,
    universe_members,
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


def extract_sources(
    cfg: FCOpenDataset, container: str, exe: str, util_module: str, jobs: int
) -> dict[str, dict]:
    """Extractor records for every vendored source file, keyed by *relative*
    path under ``Sources/`` (arxiv nests per-paper directories, so relpath,
    not basename). Extraction elaborates each file, so the sweep runs
    ``jobs`` extractor processes over chunks of the list. Files that fail to
    elaborate are reported all at once -- unvendor them and rerun."""
    rels = sorted(str(p.relative_to(cfg.sources_dir)) for p in cfg.sources_dir.rglob("*.lean"))
    print(f"[{cfg.name}] Extracting decl ranges from {len(rels)} source files ({jobs} jobs)...", flush=True)
    chunks = [rels[i::jobs] for i in range(jobs)]
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = pool.map(
            lambda chunk: run_extractor(
                [cfg.sources_dir / r for r in chunk], container, exe, util_module
            ),
            [c for c in chunks if c],
        )
    prefix = host_to_container(cfg.sources_dir) + "/"
    by_rel: dict[str, dict] = {}
    broken: list[str] = []
    for ranges in results:
        for fr in ranges:
            assert fr["file"].startswith(prefix), fr["file"]
            rel = fr["file"][len(prefix) :]
            if fr["errors"]:
                broken.append(f"{rel}:\n{fr['errors']}")
                continue
            by_rel[rel] = fr
    if broken:
        raise SystemExit(
            f"[{cfg.name}] {len(broken)} source file(s) failed to elaborate -- "
            "unvendor them and rerun:\n" + "\n".join(broken)
        )
    assert sorted(by_rel) == rels
    return by_rel


def stray_sorries(
    cfg: FCOpenDataset, name: str, rel: str, src: bytes, filerec: dict, flags: list[bool]
) -> list[str]:
    """The isolated spec's sorry'd non-target *declarations* (checked on the
    kept commands' source spans; no-decl commands are skipped, since a module
    doc may say "sorry" in prose). A stray ``sorry`` in a kept sibling would
    make the sample unscorable-as-intended; allowlisted files are reported,
    not fatal. Non-allowlisted hits drop the member (recorded on its row)."""
    hits: list[str] = []
    for c, keep in zip(filerec["commands"], flags):
        if not keep or not c["decls"]:
            continue
        if not _SORRY_RE.search(src[c["declStart"] : c["declEnd"]]):
            continue
        decls = [d["name"] for d in c["decls"]]
        if any(matches_name(d, name) for d in decls):
            continue  # the target's own `sorry` proof (and, pre-rewrite, answer(...))
        if rel in cfg.sorry_allowlist_files:
            print(f"  note: {name}: allowlisted extra sorry in {decls}")
            continue
        hits.append(f"unexpected sorry outside the target, in {decls}")
    return hits


def generate(cfg: FCOpenDataset, container: str, exe: str, jobs: int) -> None:
    by_rel = extract_sources(
        cfg, container, exe, fc_profile(fc_commit(cfg.dataset_dir)).util_module, jobs
    )

    cfg.isolated_dir.mkdir(exist_ok=True)
    for old in cfg.isolated_dir.glob("*.lean"):
        old.unlink()

    rows: list[dict] = []
    forms: dict[str | None, int] = {}
    n_category = 0
    n_excluded = 0
    n_solved_nonmembers = 0
    dropped: list[str] = []
    # Spec filenames must stay distinct on case-insensitive filesystems (the
    # repo is developed on one): ids differing only in case get a deterministic
    # ordinal suffix, recorded in the row's `statement` field.
    casefold_seen: dict[str, int] = {}
    for rel in sorted(by_rel):
        filerec = by_rel[rel]
        src = (cfg.sources_dir / rel).read_bytes()
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
        open_members = [(d, c) for d, c in members if c == "research open"]
        n_solved_nonmembers += len(members) - len(open_members)
        if not open_members:
            # Vendored files hosting no member carry dead weight (and dead
            # license obligations); Sources/ must be exactly the hosting set.
            raise SystemExit(f"{rel}: vendored but hosts no research-open statement")
        for decl, _category in open_members:

            def drop(row: dict, reason: str) -> None:
                row["excluded"] = DROPPED_REASON_PREFIX + reason
                dropped.append(f"{row['id']}: {reason}")
                rows.append(row)

            row: dict = {"id": decl["name"], "source": f"Sources/{rel}"}
            if "sorryAx" in decl["type"]:
                row["excluded"] = VALUE_TYPED_REASON
                n_excluded += 1
            elif proof_is_filled(src, filerec, decl["name"]):
                row["excluded"] = PROVED_IN_FILE_REASON
                n_excluded += 1
            if "excluded" in row:
                rows.append(row)
                continue

            closure = dependency_closure(filerec, decl["name"])
            flags = fc_kept_flags(src, filerec, kept_flags(filerec, closure))
            strays = stray_sorries(cfg, decl["name"], rel, src, filerec, flags)
            if strays:
                drop(row, "; ".join(strays))
                continue
            text = tidy(isolate(src, filerec, flags)).decode("utf-8")
            # Census `answer(` in *code* only -- kept docs may mention it in prose.
            n_answers = strip_comments(text).count("answer(")
            if n_answers > 1:
                drop(row, f"{n_answers} answer( occurrences in the isolated spec")
                continue
            form = None
            if n_answers == 1:
                text, form, n = rewrite_answer_iff(text)
                if form is None or n != 1 or "answer(" in strip_comments(text):
                    drop(row, "answer(...) ↔ rewrite did not apply cleanly")
                    continue
            forms[form] = forms.get(form, 0) + 1
            row["answer_form"] = form
            text, n = strip_category_attrs(text)
            n_category += n
            n_seen = casefold_seen[decl["name"].casefold()] = (
                casefold_seen.get(decl["name"].casefold(), 0) + 1
            )
            filename = f"{decl['name']}.lean" if n_seen == 1 else f"{decl['name']}_{n_seen}.lean"
            if n_seen > 1:
                row["statement"] = f"Isolated/{filename}"
            (cfg.isolated_dir / filename).write_text(text)
            rows.append(row)

    write_manifest(cfg.dataset_dir, rows)
    if dropped:
        print(f"[{cfg.name}] {len(dropped)} member(s) dropped (recorded on their rows):")
        for line in dropped:
            print(f"  {line}")
    print(
        f"[{cfg.name}] Wrote {len(rows)} manifest rows ({n_excluded} excluded, "
        f"{len(dropped)} dropped) and {len(rows) - n_excluded - len(dropped)} isolated "
        f"files to {cfg.isolated_dir}.\n"
        f"[{cfg.name}] Forms: {forms}; category lists stripped: {n_category}; "
        f"research-solved non-members cut: {n_solved_nonmembers}"
    )


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "datasets", nargs="*", choices=sorted(DATASETS),
        help="datasets to regenerate (default: all)",
    )
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=BAKED_EXE, help="extractor path in container (default: baked)")
    ap.add_argument("--jobs", type=int, default=6, help="parallel extractor processes")
    args = ap.parse_args()

    for name in args.datasets or sorted(DATASETS):
        generate(DATASETS[name], args.container, args.exe, args.jobs)
    print("Validate with: pytest tests/test_fc_open_isolation.py")


if __name__ == "__main__":
    sys.exit(main())
