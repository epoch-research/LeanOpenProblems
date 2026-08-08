# type: ignore
"""Generate the per-target isolated FC100OpenSet1 specs in
``apn/data/fc100open/Isolated/``.

Membership is the committed ``samples.jsonl`` manifest (the paper's frozen
100-problem open subset; its 14 value-typed ``answer(sorry)`` members are
``excluded`` rows) -> 86 kept targets. For each kept target this reads its
recorded ``Sources/`` file, keeps that file's definitions + the single target
theorem, and cuts every other standalone ``theorem``/``lemma`` *and* FC's
anonymous ``example`` sanity checks; the 46 propositional
``answer(sorry) ↔ P`` statements are rewritten to plain ``P`` (see
``scripts/fc_statements.py`` for why, and for the re-elaboration certificate
of that rewrite). Each excluded row's recorded reason is re-verified against
the elaborated statement (a ``sorryAx`` in its type).

This is a *vendor-time* dev tool, not imported at runtime; ``apn/dataset.py``
reads the committed manifest + ``Isolated/`` directly. The committed files are
validated by ``tests/test_fc100_isolation.py`` -- re-extraction structural
checks incl. the rewrite certificate, and the authoritative
``lake env lean -o`` compile gate -- which run the Lean toolchain in a
container. After regenerating, run those tests to confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean
container with the repo mounted; the baked extractor of the Dockerfile's
``generate`` stage is the default ``--exe``:

    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        "$IMAGE_REPOSITORY:LeanOpenProblems_generate_<version>" sleep infinity

Then generate:

    python scripts/generate_fc100_isolated.py
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from apn.dataset import load_manifest
from scripts.fc100_isolation import (
    FC100_DIR,
    ISOLATED_DIR,
    SORRY_ALLOWLIST,
    SOURCES_DIR,
)
from scripts.fc_statements import (
    LHS_SORRY,
    fc_kept_flags,
    rewrite_answer_iff,
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
    resolve_target,
    run_extractor,
    tidy,
)

_SORRY_RE = re.compile(rb"\bsorry\b")


def extract_sources(container: str, exe: str) -> dict[str, dict]:
    """Extractor records for every vendored source file, keyed by *relative*
    path under ``Sources/``. Keying by relpath, not basename, matters: the FC
    tree has basename collisions (two ``23.lean``, two ``61.lean``)."""
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


def check_excluded(row, by_rel: dict[str, dict]) -> None:
    """Re-verify an excluded row's recorded reason: its statement's elaborated
    type must carry a ``sorryAx`` (the value-typed ``answer(sorry)``
    placeholder), the very thing that makes it unscoreable."""
    rel = row.source.removeprefix("Sources/")
    target = resolve_target(row.id, by_rel[rel])
    if "sorryAx" not in target["type"]:
        raise SystemExit(f"{row.id}: excluded but its statement type has no sorryAx")


def check_sorries(name: str, src: bytes, filerec: dict, flags: list[bool]) -> None:
    """Assert the isolated spec's only sorry'd *declaration* is the target
    (checked on the kept commands' source spans; no-decl commands are skipped,
    since a module doc may say "sorry" in prose). A stray ``sorry`` in a kept
    sibling would make the sample unscorable-as-intended; only the allowlisted
    EllipticCurveRank Mordell-Weil instance may carry one (reported, not
    fatal)."""
    for c, keep in zip(filerec["commands"], flags):
        if not keep or not c["decls"]:
            continue
        if not _SORRY_RE.search(src[c["declStart"] : c["declEnd"]]):
            continue
        decls = [d["name"] for d in c["decls"]]
        if any(matches_name(d, name) for d in decls):
            continue  # the target's own `sorry` proof (and, pre-rewrite, answer(sorry))
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

    rows = load_manifest(FC100_DIR)
    by_rel = extract_sources(args.container, args.exe)

    unused = sorted(set(by_rel) - {r.source.removeprefix("Sources/") for r in rows})
    if unused:
        # Vendored files no row points at carry dead weight (and dead license
        # obligations); keep Sources/ exactly the hosting set.
        raise SystemExit(
            f"{len(unused)} vendored source file(s) host no manifest member -- "
            f"remove them from Sources/:\n  " + "\n  ".join(unused)
        )
    for row in rows:
        if row.excluded is not None:
            check_excluded(row, by_rel)

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    rewritten: list[str] = []
    n_category = 0
    for row in (r for r in rows if r.excluded is None):
        name, rel = row.id, row.source.removeprefix("Sources/")
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
        if n_answers == 1:
            text, form, n = rewrite_answer_iff(text)
            # This subset's census is LHS-`answer(sorry)` only; any other form
            # showing up means the vendored sources changed.
            if form != LHS_SORRY or n != 1 or "answer(" in strip_comments(text):
                raise SystemExit(f"{name}: answer(sorry) ↔ rewrite did not apply cleanly")
            rewritten.append(name)
        text, n = strip_category_attrs(text)
        n_category += n
        (ISOLATED_DIR / f"{name}.lean").write_text(text)

    # The subset's census: 46 propositional answer(sorry) ↔ members among the
    # 86 kept. Any drift means membership or vendored sources changed.
    if len(rewritten) != 46:
        raise SystemExit(f"expected 46 rewritten members, got {len(rewritten)}")
    # 91 classification lists: one per kept declaration carrying one -- the 86
    # targets plus EllipticCurveRank's 5 kept dependency decls. (A 92nd
    # occurrence of `@[category` is backtick-quoted prose in
    # OpenQuantumProblems/23's module doc; the line-anchored pattern skips it.)
    if n_category != 91:
        raise SystemExit(f"expected 91 category lists stripped, got {n_category}")

    print(
        f"Wrote {sum(1 for r in rows if r.excluded is None)} isolated files "
        f"({len(rewritten)} rewritten) to {ISOLATED_DIR}.\n"
        "Validate with: pytest tests/test_fc100_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
