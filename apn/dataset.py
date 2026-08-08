from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from inspect_ai.dataset import MemoryDataset, Sample

OEIS_DIR = Path(__file__).parent / "data" / "oeis"
FC100_DIR = Path(__file__).parent / "data" / "fc100open"
ERDOS_DIR = Path(__file__).parent / "data" / "erdos"


@dataclass(frozen=True)
class SampleRow:
    """One universe member of a dataset's ``samples.jsonl`` manifest.

    A row records facts about the dataset itself (never benchmark lineage --
    that lives in ``subsets/``): the sample id, the vendored source file
    hosting the declaration, an optional exclusion reason for members the
    harness cannot score, and any dataset-specific fields (``oeis_id``,
    ``category_at_pin``, ...) in ``extra``. The isolated spec of a
    non-excluded row is ``Isolated/<id>.lean`` by convention.
    """

    id: str
    source: str
    excluded: str | None = None
    extra: dict[str, Any] = field(default_factory=dict)


def load_manifest(dataset_dir: str | Path) -> list[SampleRow]:
    """Parse a dataset's ``samples.jsonl`` (one JSON object per line)."""
    dataset_dir = Path(dataset_dir)
    rows: list[SampleRow] = []
    for line in (dataset_dir / "samples.jsonl").read_text().splitlines():
        rec = json.loads(line)
        rows.append(
            SampleRow(
                id=rec.pop("id"),
                source=rec.pop("source"),
                excluded=rec.pop("excluded", None),
                extra=rec,
            )
        )
    ids = [r.id for r in rows]
    if len(set(ids)) != len(ids):
        dupes = sorted({i for i in ids if ids.count(i) > 1})
        raise ValueError(f"{dataset_dir.name}: duplicate manifest ids: {dupes}")
    return rows


def write_manifest(dataset_dir: str | Path, rows: Iterable[dict[str, Any]]) -> Path:
    """Write ``samples.jsonl`` (vendor-time; generators construct the rows).

    Rows are sorted by ``id`` and serialized one compact object per line, keys
    in the given order with ``id``/``source`` leading -- kept next to
    :func:`load_manifest` so the format is defined in one place.
    """
    out = []
    for rec in sorted(rows, key=lambda r: r["id"]):
        ordered = {"id": rec["id"], "source": rec["source"]}
        ordered.update(rec)
        out.append(json.dumps(ordered, ensure_ascii=False))
    path = Path(dataset_dir) / "samples.jsonl"
    path.write_text("\n".join(out) + "\n")
    return path


def available_subsets(dataset_dir: str | Path) -> list[str]:
    """Names of a dataset's predefined subsets (one ``subsets/<name>.json`` each)."""
    subsets_dir = Path(dataset_dir) / "subsets"
    if not subsets_dir.is_dir():
        return []
    return sorted(p.stem for p in subsets_dir.glob("*.json"))


def load_subset(dataset_dir: str | Path, name: str) -> list[str]:
    """Resolve a named subset to its list of sample ids.

    A subset is exactly that -- every id must exist in the dataset's manifest;
    derivation stories (upstream lists, seeds, renames) are prose in the file's
    ``description``, not membership data.
    """
    dataset_dir = Path(dataset_dir)
    path = dataset_dir / "subsets" / f"{name}.json"
    if not path.is_file():
        raise ValueError(
            f"Unknown subset {name!r}; available: {available_subsets(dataset_dir)}"
        )
    ids: list[str] = json.loads(path.read_text())["ids"]
    if len(set(ids)) != len(ids):
        raise ValueError(f"subset {name!r} has duplicate ids")
    known = {r.id for r in load_manifest(dataset_dir)}
    missing = sorted(set(ids) - known)
    if missing:
        raise ValueError(f"subset {name!r} ids missing from the manifest: {missing}")
    return ids


def write_subset(path: str | Path, description: str, ids: list[str]) -> Path:
    """Write a ``subsets/<name>.json`` file (vendor-time; see :func:`load_subset`)."""
    path = Path(path)
    path.parent.mkdir(exist_ok=True)
    path.write_text(
        json.dumps({"description": description, "ids": ids}, indent=2, ensure_ascii=False)
        + "\n"
    )
    return path


def strip_license_header(text: str) -> str:
    """Drop a leading Lean copyright/license block comment (wastes tokens and human attention)."""
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


def build_dataset(
    dataset_dir: str | Path,
    name: str,
    metadata_keys: tuple[str, ...] = (),
    names: list[str] | None = None,
) -> MemoryDataset:
    """A dataset's non-excluded manifest rows as Samples.

    Each sample's input is its isolated spec (``Isolated/<id>.lean``, license
    header stripped). ``Sample.metadata`` gets ``sketch``, ``source``, and the
    whitelisted ``metadata_keys`` only -- other manifest fields (notably
    ``category_at_pin``/``answer_form``, the recorded verdict in
    machine-readable form) exist for tooling and must not reach the agent.

    Args:
        dataset_dir: The dataset's directory under ``apn/data/``.
        name: Dataset name for the ``MemoryDataset``.
        metadata_keys: Manifest ``extra`` fields to copy into sample metadata.
        names: If given, keep only these sample ids (e.g. a subset's).
    """
    dataset_dir = Path(dataset_dir)
    rows = [r for r in load_manifest(dataset_dir) if r.excluded is None]
    if names is not None:
        missing = sorted(set(names) - {r.id for r in rows})
        if missing:
            raise ValueError(f"{name}: unknown or excluded sample ids: {missing}")
        wanted = set(names)
        rows = [r for r in rows if r.id in wanted]
    samples: list[Sample] = []
    for row in rows:
        text = strip_license_header(
            (dataset_dir / "Isolated" / f"{row.id}.lean").read_text()
        )
        metadata: dict[str, Any] = {"sketch": text, "source": row.source}
        for key in metadata_keys:
            if key in row.extra:
                metadata[key] = row.extra[key]
        samples.append(Sample(input=text, id=row.id, metadata=metadata))
    return MemoryDataset(samples, name=name)


def oeis_dataset(names: list[str] | None = None) -> MemoryDataset:
    """The Formal Conjectures autoformalized OEIS conjectures as Samples.

    One sample per manifest row (one conjecture; 492). The sketch is the
    conjecture's *isolated* spec: the sequence definitions plus the single
    target theorem (all sibling conjectures and test lemmas removed).
    ``oeis_id`` and (for the 3 multi-formalization conjectures)
    ``other_sources`` ride along in metadata.
    """
    return build_dataset(OEIS_DIR, "oeis", ("oeis_id", "other_sources"), names)


def fc100open_dataset(names: list[str] | None = None) -> MemoryDataset:
    """The FC100OpenSet1 open problems (86 of the paper's frozen 100) as Samples.

    One sample per non-excluded manifest row; the sample id is the target's
    fully qualified declaration name (e.g. ``Erdos200.erdos_200``). The sketch
    is the target's *isolated* spec -- the source file's definitions plus the
    single target theorem, siblings/test lemmas/``example`` commands removed,
    propositional ``answer(sorry) ↔ P`` statements rewritten to plain ``P``
    (certified by ``tests/test_fc100_isolation.py``), and FC's
    ``@[category ...]`` classification lists dropped. The 14 value-typed
    ``answer(sorry)`` members of the paper's 100 are excluded manifest rows.
    """
    return build_dataset(FC100_DIR, "fc100open", (), names)


def erdos_dataset(names: list[str] | None = None) -> MemoryDataset:
    """Every research-category FC ErdosProblems statement at the pinned commit,
    as Samples.

    One sample per non-excluded manifest row; the sample id is the target's
    fully qualified declaration name (e.g. ``Erdos200.erdos_200``). The sketch
    is the target's *isolated* spec -- the source file's definitions plus the
    single target theorem, siblings/test lemmas/``example`` commands removed,
    and all four ``answer(...) ↔`` statement forms rewritten to plain ``P``
    (recorded ``True``/``False`` verdicts un-filled and FC's recorded-verdict
    annotations stripped -- the answer key must not leak; certified by
    ``tests/test_erdos_isolation.py``). Value-typed ``answer(sorry)``
    statements are excluded manifest rows (unscoreable by SafeVerify). The
    Tsoukalas paper's canonical attempted set (arXiv 2605.22763) is the
    ``tsoukalas_attempted`` subset.
    """
    return build_dataset(ERDOS_DIR, "erdos", (), names)
