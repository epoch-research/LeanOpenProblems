# type: ignore
"""Generate the Wikipedia-autoformalized universe:
``apn/data/wikipedia_autoformalized/samples.jsonl`` (the manifest), the
per-target isolated specs in ``.../Isolated/``, and the default subset
``.../subsets/adjudicated_open.json``.

Membership is *defined* by the vendored sources, so this script computes it:
every ``theorem``/``lemma`` declaration carrying a ``@[category research
...]`` attribute in ``Sources/`` (the accepted final files of our own
autoformalization run; see ``apn/data/wikipedia_autoformalized/NOTICE.md``)
is a universe member -- the run's adjudicated statements *and* the
formalizers' additional research variants and research-solved known results
that share their files. As in the Erdős generator, value-typed
``answer(sorry)`` members (a ``sorryAx`` in the elaborated statement type,
unscoreable by the verifier) and members carrying a complete in-file proof
become ``excluded`` rows with no isolated spec.

Each kept member's spec keeps its file's definitions + the single target
theorem and cuts every other standalone ``theorem``/``lemma`` and anonymous
``example``; ``private`` modifiers are dropped; the ``answer(sorry) ↔ P``
question form is rewritten to plain ``P`` (certified by re-elaboration in the
test suite); FC's ``@[category ...]`` classification lists are dropped (each
must be a plain ``category, AMS`` list -- a list carrying any other attribute
fails the run instead of losing it silently); and the mechanically derived
``<target>.disproof`` is appended.

The run table ``metadata/run_samples.jsonl`` (written by
``scripts/vendor_wikipedia_autoformalized.py``) supplies each file's problem
id, title, headline score, adjudicator confidence and *kept slots*. Every
kept slot must resolve to exactly one member of its file (its row records
the ``slot``); the default subset is the kept slots classified research open
with no recorded verdict
(``scripts.wikipedia_autoformalized_isolation.default_subset_ids``).

This is a *vendor-time* dev tool, not imported at runtime; ``apn/dataset.py``
reads the committed manifest + ``Isolated/`` directly. The committed files
are validated by ``tests/test_wikipedia_autoformalized_isolation.py`` --
re-extraction structural checks incl. the per-form rewrite certificates, the
disproof certification and the authoritative ``lake env lean -o`` compile
gate -- which run the Lean toolchain in a container. After regenerating, run
those tests to confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean
container with the repo mounted; the baked extractor of the Dockerfile's
``generate`` stage is the default ``--exe``:

    docker build --target generate -t apn-generate \\
        --build-arg FC_COMMIT="$(cat apn/data/wikipedia_autoformalized/fc_commit)" apn/lean
    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-generate sleep infinity

Then generate:

    python scripts/generate_wikipedia_autoformalized_isolated.py
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from apn.dataset import fc_commit, fc_profile, write_manifest, write_subset
from scripts.erdos_isolation import (
    PROVED_IN_FILE_REASON,
    RESEARCH_ATTR_RE,
    VALUE_TYPED_REASON,
    research_categories,
    universe_members,
)
from scripts.fc_statements import (
    CATEGORY_ATTR_RE,
    fc_kept_flags,
    rewrite_answer_iff,
    strip_category_attrs,
    strip_comments,
)
from scripts.isolation import (
    BAKED_EXE,
    DEFAULT_CONTAINER,
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
from scripts.wikipedia_autoformalized_isolation import (
    DEFAULT_SUBSET,
    ISOLATED_DIR,
    SORRY_ALLOWLIST_FILES,
    SOURCES_DIR,
    SUBSETS_DIR,
    WIKIPEDIA_AUTOFORMALIZED_DIR,
    default_subset_ids,
    load_run_samples,
    vendored_samples,
)

_SORRY_RE = re.compile(rb"\bsorry\b")
_ANSWER_SORRY_RE = re.compile(r"answer\(\s*sorry\s*\)")
# A plain FC classification list: the category and AMS codes, nothing else.
# `strip_category_attrs` removes whole lists, so a list also carrying a
# semantic attribute (`simp`, `mk_iff`, ...) must be handled by hand, not
# stripped along -- the generator fails on one.
_PLAIN_CATEGORY_RE = re.compile(
    r"@\[category (?:research open|research solved|test|API|textbook), AMS(?: \d+)+\]"
)

SUBSET_DESCRIPTION = (
    "The run's adjudicated open statements: every kept slot -- a declaration the "
    "autoformalization run's adjudicator accepted as a faithful formalization of "
    "one of its problem's decomposed sub-questions (metadata/run_samples.jsonl; "
    "the manifest row records the slot) -- that is classified research open, "
    "records no answer(True/False) verdict, and is scoreable (not an excluded "
    "value-typed row). Leaves out the formalizers' additional research variants "
    "(not adjudicated sub-questions), the research-solved kept slots (known "
    "results) and the kept slots whose statement the formalizer itself marked "
    "answered. {n} statements over {m} problems, in problem-id order then the "
    "adjudicator's slot order."
)


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
    make the sample unscorable-as-intended; violations are collected and fail
    the run at the end, so one run surfaces them all."""
    violations: list[str] = []
    for c, keep in zip(filerec["commands"], flags):
        if not keep or not c["decls"]:
            continue
        if not _SORRY_RE.search(src[c["declStart"] : c["declEnd"]]):
            continue
        decls = [d["name"] for d in c["decls"]]
        if any(matches_name(d, name) for d in decls):
            continue  # the target's own `sorry` proof (and, pre-rewrite, answer(sorry))
        if rel in SORRY_ALLOWLIST_FILES:
            print(f"  note: {name}: allowlisted extra sorry in {decls}")
            continue
        violations.append(f"{name}: unexpected sorry outside the target, in {decls}")
    return violations


def strip_plain_category_attrs(text: str) -> tuple[str, int, list[str]]:
    """Drop the spec's ``@[category ...]`` lists, refusing any that is not a
    plain classification list. Returns (text, #stripped, offending lists)."""
    offending = [
        m.group(0).rstrip("\n")
        for m in CATEGORY_ATTR_RE.finditer(text)
        if not _PLAIN_CATEGORY_RE.fullmatch(m.group(0).rstrip("\n"))
    ]
    if offending:
        return text, 0, offending
    text, n = strip_category_attrs(text)
    return text, n, []


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=BAKED_EXE, help="extractor path in container (default: baked)")
    ap.add_argument("--jobs", type=int, default=6, help="parallel extractor processes")
    args = ap.parse_args()

    run_rows = load_run_samples()
    by_source = {Path(r.source).name: r for r in vendored_samples(run_rows)}
    on_disk = sorted(p.name for p in SOURCES_DIR.glob("*.lean"))
    if on_disk != sorted(by_source):
        raise SystemExit(
            f"Sources/ disagrees with the run table: stray {sorted(set(on_disk) - set(by_source))}, "
            f"missing {sorted(set(by_source) - set(on_disk))}"
        )

    by_rel = extract_sources(
        args.container,
        args.exe,
        fc_profile(fc_commit(WIKIPEDIA_AUTOFORMALIZED_DIR)).util_module,
        args.jobs,
    )

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    rows: list[dict] = []
    forms: Counter = Counter()
    categories: Counter = Counter()
    excluded: Counter = Counter()
    n_category_stripped = 0
    problems: list[str] = []
    # Spec filenames must stay distinct on case-insensitive filesystems (the
    # repo is developed on one): ids differing only in case get a
    # deterministic ordinal suffix, recorded in the row's `statement` field.
    casefold_seen: dict[str, int] = {}
    for rel in sorted(by_rel):
        run_row = by_source[rel]
        filerec = by_rel[rel]
        src = (SOURCES_DIR / rel).read_bytes()
        members = universe_members(src, filerec)
        # No research attribute may escape the census: the file total must be
        # accounted for by per-command hits.
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
        kept_ids = dict(zip(run_row.kept_ids, run_row.kept_slots or []))
        member_names = {decl["name"] for decl, _ in members}
        unresolved = sorted(set(kept_ids) - member_names)
        if unresolved:
            problems.append(f"{rel}: kept slots not among the file's research members: {unresolved}")
        for decl, category in members:
            name = decl["name"]
            row: dict = {"id": name, "source": f"Sources/{rel}"}
            if "sorryAx" in decl["type"]:
                row["excluded"] = VALUE_TYPED_REASON
            elif proof_is_filled(src, filerec, name):
                row["excluded"] = PROVED_IN_FILE_REASON
            row.update(
                {
                    "problem_id": run_row.problem_id,
                    "title": run_row.title,
                    "category": category,
                    "slot": kept_ids.get(name),
                    "formalized": run_row.formalized,
                    "adjudicator_confidence": run_row.adjudicator_confidence,
                }
            )
            categories[category] += 1
            if "excluded" in row:
                excluded[row["excluded"][:40]] += 1
                rows.append(row)
                continue

            closure = dependency_closure(filerec, name)
            flags = fc_kept_flags(src, filerec, kept_flags(filerec, closure))
            problems.extend(check_sorries(name, rel, src, filerec, flags))
            text = tidy(isolate(src, filerec, flags)).decode("utf-8")
            # Drop `private` modifiers: their module-mangled names falsely
            # reject faithful submissions under Comparator (plan §3.3).
            text = strip_private(text)
            # Census `answer(` in *code* only -- kept docs may mention it in prose.
            n_answers = strip_comments(text).count("answer(")
            if n_answers > 1:
                problems.append(f"{name}: {n_answers} answer( in isolated spec")
                continue
            form = None
            if n_answers == 1:
                text, form, n = rewrite_answer_iff(text)
                if form is None or n != 1 or "answer(" in strip_comments(text):
                    problems.append(f"{name}: answer(...) ↔ rewrite did not apply cleanly")
                    continue
            forms[form] += 1
            row["answer_form"] = form
            text, n_stripped, offending = strip_plain_category_attrs(text)
            if offending:
                problems.append(f"{name}: non-plain @[category ...] list(s) in spec: {offending}")
                continue
            if n_stripped < 1:
                problems.append(f"{name}: no @[category ...] list stripped")
                continue
            n_category_stripped += n_stripped
            # Comparator scores either the target or this mechanically derived
            # negation, selected by the agent's declared claim.
            text, _ = append_disproof(text, name, name)
            n_seen = casefold_seen[name.casefold()] = casefold_seen.get(name.casefold(), 0) + 1
            filename = f"{name}.lean" if n_seen == 1 else f"{name}_{n_seen}.lean"
            if n_seen > 1:
                row["statement"] = f"Isolated/{filename}"
            (ISOLATED_DIR / filename).write_text(text)
            rows.append(row)

    if problems:
        raise SystemExit(f"{len(problems)} problem(s):\n" + "\n".join(problems))

    write_manifest(WIKIPEDIA_AUTOFORMALIZED_DIR, rows)
    subset_ids = default_subset_ids(rows, run_rows)
    n_problems = len({r["problem_id"] for r in rows if r["id"] in set(subset_ids)})
    write_subset(
        SUBSETS_DIR / f"{DEFAULT_SUBSET}.json",
        SUBSET_DESCRIPTION.format(n=len(subset_ids), m=n_problems),
        subset_ids,
    )
    n_excluded = sum(excluded.values())
    kept_rows = [r for r in rows if r["slot"] is not None]
    print(
        f"Wrote {len(rows)} manifest rows ({n_excluded} excluded) and "
        f"{len(rows) - n_excluded} isolated files to {ISOLATED_DIR}.\n"
        f"Categories: {dict(categories)}\nExcluded: {dict(excluded)}\nForms: {dict(forms)}\n"
        f"Kept slots: {len(kept_rows)} rows, {sum('excluded' in r for r in kept_rows)} excluded, "
        f"{sum(r['category'] == 'research solved' for r in kept_rows)} research solved\n"
        f"Category lists stripped: {n_category_stripped}\n"
        f"Subset {DEFAULT_SUBSET}: {len(subset_ids)} ids over {n_problems} problems\n"
        "Validate with: pytest tests/test_wikipedia_autoformalized_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
