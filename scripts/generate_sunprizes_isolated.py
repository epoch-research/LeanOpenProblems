# type: ignore
"""Generate the per-target isolated Sun-prizes specs in
``apn/data/sunprizes/Isolated/``.

Membership is the committed ``samples.jsonl`` manifest (the 8 prized Zhi-Wei
Sun conjectures formalized in FC at the pin; see the dataset's ``NOTICE.md``).
For each target this reads its recorded ``Sources/`` file, keeps that file's
definitions + the single target theorem, and cuts every other standalone
``theorem``/``lemma`` (FC's ``@[category test]`` sanity lemmas) and any
anonymous ``example`` commands; the targets' ``@[category ...]``
classification lists are dropped. All 8 statements are plain ``research
open`` conjectures -- generation asserts no ``answer(`` occurs anywhere.

This is a *vendor-time* dev tool, not imported at runtime; ``apn/dataset.py``
reads the committed manifest + ``Isolated/`` directly. The committed files are
validated by ``tests/test_sunprizes_isolation.py`` -- re-extraction structural
checks and the authoritative ``lake env lean -o`` compile gate -- which run
the Lean toolchain in a container. After regenerating, run those tests to
confirm the output is sound.

Setup (one-time, since there is no local Lean toolchain). Start a Lean
container with the repo mounted; the baked extractor of the Dockerfile's
``generate`` stage is the default ``--exe``:

    docker build --target generate -t apn-generate \\
        --build-arg FC_COMMIT="$(cat apn/data/sunprizes/fc_commit)" apn/lean
    docker run -d --name apn-isolate-dev -v "$PWD":/repo -w /repo \\
        apn-generate sleep infinity

Then generate:

    python scripts/generate_sunprizes_isolated.py
"""

from __future__ import annotations

import argparse
import re
import sys

from apn.dataset import load_manifest
from scripts.sunprizes_isolation import (
    ISOLATED_DIR,
    SOURCES_DIR,
    SUNPRIZES_DIR,
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
    resolve_target,
    run_extractor,
    tidy,
)

_SORRY_RE = re.compile(rb"\bsorry\b")


def extract_sources(container: str, exe: str) -> dict[str, dict]:
    """Extractor records for every vendored source file, keyed by *relative*
    path under ``Sources/`` (flat here, so relpath == basename)."""
    rels = sorted(str(p.relative_to(SOURCES_DIR)) for p in SOURCES_DIR.rglob("*.lean"))
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


def check_sorries(name: str, src: bytes, filerec: dict, flags: list[bool]) -> None:
    """Assert the isolated spec's only sorry'd *declaration* is the target
    (checked on the kept commands' source spans; no-decl commands are skipped,
    since a module doc may say "sorry" in prose). A stray ``sorry`` in a kept
    sibling would make the sample unscorable-as-intended."""
    for c, keep in zip(filerec["commands"], flags):
        if not keep or not c["decls"]:
            continue
        if not _SORRY_RE.search(src[c["declStart"] : c["declEnd"]]):
            continue
        decls = [d["name"] for d in c["decls"]]
        if any(matches_name(d, name) for d in decls):
            continue  # the target's own `sorry` proof
        raise SystemExit(f"{name}: unexpected sorry outside the target, in {decls}")


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--container", default=DEFAULT_CONTAINER, help="Lean container name")
    ap.add_argument("--exe", default=BAKED_EXE, help="extractor path in container (default: baked)")
    args = ap.parse_args()

    rows = load_manifest(SUNPRIZES_DIR)
    by_rel = extract_sources(args.container, args.exe)

    unused = sorted(set(by_rel) - {r.source.removeprefix("Sources/") for r in rows})
    if unused:
        # Vendored files no row points at carry dead weight (and dead license
        # obligations); keep Sources/ exactly the hosting set.
        raise SystemExit(
            f"{len(unused)} vendored source file(s) host no manifest member -- "
            f"remove them from Sources/:\n  " + "\n  ".join(unused)
        )

    ISOLATED_DIR.mkdir(exist_ok=True)
    for old in ISOLATED_DIR.glob("*.lean"):
        old.unlink()

    n_category = 0
    written: set[str] = set()
    for row in rows:
        name, rel = row.id, row.source.removeprefix("Sources/")
        # No filename collisions, casefolded: the repo must check out intact
        # on case-insensitive filesystems.
        if name.casefold() in written:
            raise SystemExit(f"isolated-filename collision: {name}")
        written.add(name.casefold())
        filerec = by_rel[rel]
        src = (SOURCES_DIR / rel).read_bytes()
        target = resolve_target(name, filerec)  # the unique target theorem
        closure = dependency_closure(filerec, target["name"])
        flags = fc_kept_flags(src, filerec, kept_flags(filerec, closure))
        check_sorries(name, src, filerec, flags)
        text = tidy(isolate(src, filerec, flags)).decode("utf-8")
        # All 8 members are plain statements: no answer( anywhere, code or prose.
        if "answer(" in strip_comments(text):
            raise SystemExit(f"{name}: unexpected answer( in isolated spec")
        text, n = strip_category_attrs(text)
        n_category += n
        (ISOLATED_DIR / f"{name}.lean").write_text(text)

    # The census: one classification list per target theorem (the cut removed
    # every attributed test lemma). Any drift means the vendored sources changed.
    if n_category != len(rows):
        raise SystemExit(f"expected {len(rows)} category lists stripped, got {n_category}")

    print(
        f"Wrote {len(rows)} isolated files to {ISOLATED_DIR}.\n"
        "Validate with: pytest tests/test_sunprizes_isolation.py"
    )


if __name__ == "__main__":
    sys.exit(main())
