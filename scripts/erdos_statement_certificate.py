# type: ignore
"""Certify the vendored Erdős pin against the Bloom-review commit.

The Bloom statement selection (``apn/data/erdos/metadata/
ERDOS_PROBLEM_STATEMENT_SELECTION.md``) was reviewed against FC commit
``56534c04`` (Lean v4.33.1), but the dataset vendors ``488aade2`` (the last FC
commit on this harness's Lean v4.27.0 toolchain, 21 commits earlier). This
script is the auditable link between the two: for each selected declaration it
extracts the declaration command's source span (attribute list + statement +
``sorry`` body) from ``FormalConjectures/ErdosProblems/<n>.lean`` at *both*
commits and asserts byte-equality, then summarizes which files carry residual
(non-selected-statement) diffs. The result is recorded in
``apn/data/erdos/NOTICE.md``; re-run this whenever either commit moves.

This is a *vendor-time* one-off, not imported at runtime and not run in CI:
it needs a local formal-conjectures clone (pass ``--fc-repo``) containing both
commits (``git fetch origin <commit>`` them if missing).

    python scripts/erdos_statement_certificate.py --fc-repo ~/src/formal-conjectures
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

from apn.dataset import fc_commit

REPO = Path(__file__).resolve().parent.parent
ERDOS_DIR = REPO / "apn" / "data" / "erdos"
SELECTION_DOC = ERDOS_DIR / "metadata" / "ERDOS_PROBLEM_STATEMENT_SELECTION.md"
REVIEW_COMMIT = "56534c04092446f2fd549d2865f2496924812da8"

# A markdown table row of the selection doc: | <problem> | `<decl>` | <reason> |
_ROW_RE = re.compile(r"^\|\s*(\d+)\s*\|\s*`([^`]+)`\s*\|")

# A line that starts a new top-level command, terminating the previous
# declaration's span. FC style keeps continuation lines indented, so matching
# at column 0 is reliable for these files.
_NEXT_CMD_RE = re.compile(
    r"^(?:/--|/-!|/-|--|@\[|theorem\b|lemma\b|def\b|abbrev\b|instance\b|"
    r"noncomputable\b|open\b|namespace\b|end\b|example\b|structure\b|"
    r"section\b|variable\b|axiom\b|set_option\b)"
)


def selection() -> list[tuple[int, str]]:
    """The (problem number, selected declaration short name) pairs from the
    vendored selection doc's table."""
    pairs = [
        (int(m.group(1)), m.group(2))
        for line in SELECTION_DOC.read_text().splitlines()
        if (m := _ROW_RE.match(line))
    ]
    if len(pairs) != 48:
        raise SystemExit(f"selection doc table has {len(pairs)} rows, expected 48")
    return pairs


def fc_file(fc_repo: Path, commit: str, number: int) -> str:
    return subprocess.run(
        ["git", "-C", str(fc_repo), "show", f"{commit}:FormalConjectures/ErdosProblems/{number}.lean"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout


def decl_span(text: str, name: str) -> str:
    """The declaration command's source span for short ``name``: its attribute
    list (contiguous ``@[...]``/modifier lines directly above the keyword)
    through the end of the command (the line before the next top-level
    command), trailing whitespace stripped."""
    lines = text.splitlines(keepends=True)
    decl_re = re.compile(rf"^(?:theorem|lemma)\s+{re.escape(name)}(?![\w.])")
    starts = [i for i, line in enumerate(lines) if decl_re.match(line)]
    if len(starts) != 1:
        raise SystemExit(f"{name}: {len(starts)} declaration lines found, expected 1")
    lo = starts[0]
    # Attribute lines (and `open ... in`-style modifiers) directly above the
    # keyword belong to the command.
    while lo > 0 and (
        lines[lo - 1].startswith("@[") or lines[lo - 1].rstrip().endswith(" in")
    ):
        lo -= 1
    hi = starts[0] + 1
    while hi < len(lines) and not _NEXT_CMD_RE.match(lines[hi]):
        hi += 1
    return "".join(lines[lo:hi]).rstrip()


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--fc-repo",
        required=True,
        type=Path,
        help="local formal-conjectures clone containing both commits",
    )
    args = ap.parse_args()
    vendored_commit = fc_commit(ERDOS_DIR)

    mismatches: list[str] = []
    residual: list[int] = []
    for number, name in selection():
        at_pin = fc_file(args.fc_repo, vendored_commit, number)
        at_review = fc_file(args.fc_repo, REVIEW_COMMIT, number)
        if at_pin != at_review:
            residual.append(number)
        if decl_span(at_pin, name) != decl_span(at_review, name):
            mismatches.append(f"{number} ({name})")
        # The vendored copy must be the pin's file, byte for byte.
        vendored = (ERDOS_DIR / "Sources" / f"{number}.lean").read_text()
        if vendored != at_pin:
            mismatches.append(f"{number}: vendored Sources/{number}.lean != FC at the pin")

    print(
        f"Certified {48 - len(mismatches)}/48 selected declarations byte-identical "
        f"between {vendored_commit[:8]} (vendored pin) and {REVIEW_COMMIT[:8]} "
        f"(review commit).\n"
        f"Files with residual (non-selected-statement) diffs: {residual or 'none'}"
    )
    if mismatches:
        raise SystemExit("MISMATCHES:\n  " + "\n  ".join(mismatches))


if __name__ == "__main__":
    sys.exit(main())
