"""Datasets of Lean proof sketches.

A *sketch* is a Lean file containing the sequence definitions plus a single
target conjecture theorem whose proof body is ``sorry``. Each becomes an Inspect
:class:`Sample` whose input is the file text and whose metadata records the
target theorem name and the original sketch text (so the scorer can check the
statement was preserved).

This loads the autoformalized OEIS conjectures from Formal Conjectures (the
paper's 492-conjecture evaluation). The benchmark unit is the *conjecture*, but
each upstream ``Auto/*.lean`` file bundles the definitions, sanity "test" lemmas,
and one or more conjecture theorems together. We therefore read the per-conjecture
*isolated* specs under ``Isolated/`` -- each keeps the file's definitions and the
single target theorem, with all other theorems/lemmas removed -- so a sample is
scored on its own conjecture alone. The isolated files are derived from ``Auto/``
+ ``THEOREM_MAPPING.txt`` by ``scripts/generate_isolated.py``; see
``apn/data/oeis/NOTICE.md``.
"""

from __future__ import annotations

import re
from pathlib import Path

from inspect_ai.dataset import MemoryDataset, Sample

OEIS_DIR = Path(__file__).parent / "data" / "oeis"
OEIS_AUTO_DIR = OEIS_DIR / "Auto"
OEIS_ISOLATED_DIR = OEIS_DIR / "Isolated"
OEIS_MAPPING_FILE = OEIS_DIR / "THEOREM_MAPPING.txt"
OEIS_SUBSETS_DIR = OEIS_DIR / "subsets"

_OEIS_NUM_RE = re.compile(r"^(\d+)_")


def available_subsets() -> list[str]:
    """Names of the predefined OEIS subsets (one ``<name>.txt`` per subset)."""
    if not OEIS_SUBSETS_DIR.is_dir():
        return []
    return sorted(p.stem for p in OEIS_SUBSETS_DIR.glob("*.txt"))


def load_subset(name: str) -> list[str]:
    """Resolve a named OEIS subset to its list of conjecture theorem names.

    Subsets are plain-text files under ``apn/data/oeis/subsets/`` (one theorem
    name per line; blank lines and ``#`` comments ignored), so a curated smoke
    set lives in the package rather than being pasted inline into eval-set
    configs. See :func:`available_subsets`.
    """
    path = OEIS_SUBSETS_DIR / f"{name}.txt"
    if not path.is_file():
        raise ValueError(
            f"Unknown OEIS subset {name!r}; available: {available_subsets()}"
        )
    names: list[str] = []
    for line in path.read_text().splitlines():
        entry = line.split("#", 1)[0].strip()
        if entry:
            names.append(entry)
    return names


def strip_license_header(text: str) -> str:
    """Drop a leading Lean copyright/license block comment to save the agent tokens.

    Every Formal Conjectures file opens with the same ``/- ... -/`` Apache banner
    (484/484 OEIS files) before the imports -- pure boilerplate the agent never
    needs but pays for on every read. We remove it before writing the file to the
    sandbox (see :mod:`apn.agent`); the scorer's target keeps the original text.

    Only a *leading* ``/-`` block comment that mentions "Copyright" is removed:
    a ``/--``/``/-!`` doc comment, a non-copyright comment, or a file with no
    leading comment is returned unchanged. Nested ``/- -/`` is honoured so the
    matching close is found correctly.
    """
    stripped = text.lstrip()
    if not stripped.startswith("/-") or stripped.startswith("/--"):
        return text
    depth = 0
    i = 0
    end = -1
    n = len(stripped)
    while i < n - 1:
        pair = stripped[i : i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif pair == "-/":
            depth -= 1
            i += 2
            if depth == 0:
                end = i
                break
        else:
            i += 1
    if end == -1:  # unterminated comment -- leave the file untouched
        return text
    if "copyright" not in stripped[:end].lower():
        return text
    return stripped[end:].lstrip()


def oeis_id_from_filename(filename: str) -> str | None:
    """The OEIS A-number for an ``OEIS/Auto`` file (its leading digits).

    Filenames look like ``268597_aacea533.lean`` -> ``A268597``. More reliable
    than parsing the theorem name, some of which carry no A-number.
    """
    match = _OEIS_NUM_RE.match(filename)
    return f"A{int(match.group(1)):06d}" if match else None


def parse_oeis_mapping(text: str) -> list[tuple[str, list[str]]]:
    """Parse ``THEOREM_MAPPING.txt`` into ``(theorem_name, [files])`` entries.

    Each line is ``<conjecture_theorem_name> <file.lean> [<file.lean> ...]``;
    one conjecture occasionally has more than one formalization file.
    """
    entries: list[tuple[str, list[str]]] = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) >= 2:
            entries.append((parts[0], parts[1:]))
    return entries


def oeis_dataset(
    isolated_dir: str | Path = OEIS_ISOLATED_DIR,
    mapping_file: str | Path = OEIS_MAPPING_FILE,
    names: list[str] | None = None,
) -> MemoryDataset:
    """The Formal Conjectures autoformalized OEIS conjectures as Samples.

    One sample per mapping entry (one conjecture). The sketch is the conjecture's
    *isolated* spec under ``Isolated/<name>.lean`` -- the sequence definitions plus
    the single target theorem (all sibling conjectures and test lemmas removed) --
    so the agent settles, and the scorer checks, that one conjecture alone. The
    conjecture theorem name is the scoring target.

    Args:
        isolated_dir: Directory of per-conjecture ``Isolated/<name>.lean`` specs
            (generated by ``scripts/generate_isolated.py``).
        mapping_file: ``THEOREM_MAPPING.txt`` (theorem name -> source file(s)),
            used to enumerate conjectures and derive the OEIS id / source file.
        names: If given, keep only these conjecture theorem names (e.g. a smoke
            subset).
    """
    isolated = Path(isolated_dir)
    entries = parse_oeis_mapping(Path(mapping_file).read_text())
    samples: list[Sample] = []
    for name, files in entries:
        if names is not None and name not in names:
            continue
        source_file = files[0]
        text = (isolated / f"{name}.lean").read_text()
        samples.append(
            Sample(
                input=text,
                id=name,
                metadata={
                    "sketch": text,
                    "target_declarations": [name],
                    "oeis_id": oeis_id_from_filename(source_file),
                    "source_file": source_file,
                    "alt_files": files[1:],
                },
            )
        )
    return MemoryDataset(samples, name="oeis")
