"""Datasets of Lean proof sketches.

A *sketch* is a Lean file containing the sequence definitions plus a single
target conjecture theorem whose proof body is ``sorry``. Each becomes an Inspect
:class:`Sample` whose input is the file text and whose metadata records the
target theorem name and the original sketch text (so the scorer can check the
statement was preserved).

Two datasets load this way. The autoformalized OEIS conjectures (the paper's
492-conjecture evaluation) bundle definitions, sanity "test" lemmas, and one or
more conjecture theorems per upstream ``Auto/*.lean`` file. FC100OpenSet1 (the
paper's frozen 100-problem open subset; 86 kept here, see
``apn/data/fc100open/EXCLUDED.txt``) bundles the same way in FC's hand-written
problem files. Both therefore read per-target *isolated* specs under their
``Isolated/`` directory -- each keeps the file's definitions and the single
target theorem, with all other theorems/lemmas removed -- so a sample is scored
on its own target alone. The isolated files are derived by
``scripts/generate_oeis_isolated.py`` / ``scripts/generate_fc100_isolated.py``;
see the ``NOTICE.md`` in each data directory.
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

FC100_DIR = Path(__file__).parent / "data" / "fc100open"
FC100_ISOLATED_DIR = FC100_DIR / "Isolated"
FC100_MAPPING_FILE = FC100_DIR / "MAPPING.txt"
FC100_SUBSETS_DIR = FC100_DIR / "subsets"

_OEIS_NUM_RE = re.compile(r"^(\d+)_")


def available_subsets(subsets_dir: str | Path = OEIS_SUBSETS_DIR) -> list[str]:
    """Names of a dataset's predefined subsets (one ``<name>.txt`` per subset)."""
    subsets_dir = Path(subsets_dir)
    if not subsets_dir.is_dir():
        return []
    return sorted(p.stem for p in subsets_dir.glob("*.txt"))


def load_subset(name: str, subsets_dir: str | Path = OEIS_SUBSETS_DIR) -> list[str]:
    """Resolve a named subset to its list of target theorem names.

    Subsets are plain-text files under a dataset's ``subsets/`` directory (one
    theorem name per line; blank lines and ``#`` comments ignored), so a curated
    subset lives in the package rather than being pasted inline into eval-set
    configs. See :func:`available_subsets`. Defaults to the OEIS subsets; pass
    :data:`FC100_SUBSETS_DIR` for FC100OpenSet1.
    """
    subsets_dir = Path(subsets_dir)
    path = subsets_dir / f"{name}.txt"
    if not path.is_file():
        raise ValueError(
            f"Unknown subset {name!r}; available: {available_subsets(subsets_dir)}"
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
            (generated by ``scripts/generate_oeis_isolated.py``).
        mapping_file: ``THEOREM_MAPPING.txt`` (theorem name -> source file(s)),
            used to enumerate conjectures and derive the OEIS id.
        names: If given, keep only these conjecture theorem names (e.g. a
            curated subset).
    """
    isolated = Path(isolated_dir)
    entries = parse_oeis_mapping(Path(mapping_file).read_text())
    samples: list[Sample] = []
    for name, files in entries:
        if names is not None and name not in names:
            continue
        # Strip the Apache copyright banner here, at the single source: it is
        # identical boilerplate across every conjecture, pure token waste in the
        # agent's context, and clutter in the log UI. Both consumers downstream
        # are unaffected -- the agent writes this text as its entry file, and the
        # scorer compiles it as the verification target (a leading comment never
        # reaches the olean).
        text = strip_license_header((isolated / f"{name}.lean").read_text())
        metadata = {
            "sketch": text,
            # OEIS id derived from the upstream Auto filename's leading digits
            # (files[0]); the conjecture name doesn't reliably carry an A-number.
            # The sample's own identity is ``id``.
            "oeis_id": oeis_id_from_filename(files[0]),
        }
        # A few conjectures (3/492, only 1 a substantive difference) map to more
        # than one upstream file; we use files[0] and record the rest so the
        # solver can warn at run time -- warning at build time would fire even for
        # samples Inspect later drops via --sample-id/--limit.
        if len(files) > 1:
            metadata["unused_formalization_files"] = files[1:]
        samples.append(Sample(input=text, id=name, metadata=metadata))
    return MemoryDataset(samples, name="oeis")


def parse_fc100_mapping(text: str) -> list[tuple[str, str]]:
    """Parse FC100's ``MAPPING.txt`` into ``(full_decl_name, source_relpath)``
    entries. Each line is ``<full_decl_name> <relpath under Sources/>``; unlike
    the OEIS mapping, every target has exactly one source file."""
    entries: list[tuple[str, str]] = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) == 2:
            entries.append((parts[0], parts[1]))
    return entries


def fc100open_dataset(names: list[str] | None = None) -> MemoryDataset:
    """The FC100OpenSet1 open problems (86 of the paper's frozen 100) as Samples.

    One sample per ``MAPPING.txt`` entry; the sample id is the target's fully
    qualified declaration name (e.g. ``Erdos200.erdos_200``). The sketch is the
    target's *isolated* spec under ``Isolated/<name>.lean`` -- the source file's
    definitions plus the single target theorem, siblings/test lemmas/``example``
    commands removed, and propositional ``answer(sorry) ↔ P`` statements
    rewritten to plain ``P`` (certified by ``tests/test_fc100_isolation.py``).
    The 14 value-typed ``answer(sorry)`` members of the paper's 100 are excluded
    (``EXCLUDED.txt``): their statement types contain ``sorryAx``, which
    SafeVerify cannot score.

    Args:
        names: If given, keep only these target names (e.g. a curated subset).
    """
    entries = parse_fc100_mapping(FC100_MAPPING_FILE.read_text())
    samples: list[Sample] = []
    for name, relpath in entries:
        if names is not None and name not in names:
            continue
        # Same single-source banner strip as oeis_dataset (see comment there).
        text = strip_license_header((FC100_ISOLATED_DIR / f"{name}.lean").read_text())
        metadata = {
            "sketch": text,
            # The FC repo file (relative to FormalConjectures/) the target was
            # isolated from; the sample's own identity is ``id``.
            "source_file": relpath,
        }
        samples.append(Sample(input=text, id=name, metadata=metadata))
    return MemoryDataset(samples, name="fc100open")
