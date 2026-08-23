"""Materialize normalized metadata from summarize eval logs.

Examples::

    python scripts/summarize/collect.py sequences \
        --subset lite --eval logs/summarize/<sequences>.eval
    python scripts/summarize/collect.py conjectures \
        --subset lite --eval logs/summarize/<conjectures>.eval
    python scripts/summarize/collect.py proofs \
        --run-dir logs/<run> --eval logs/summarize/<proofs>.eval

Later ``--eval`` arguments replace earlier submissions for the same id, making
small patch-up runs deterministic.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from inspect_ai.log import EvalSample, read_eval_log

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from scripts.summarize.task import (  # noqa: E402
    load_provenance,
    load_records,
    plaintext_dir,
    solved_samples,
    subset_conjectures,
)


@dataclass(frozen=True)
class Generated:
    row: dict[str, Any]
    metadata: dict[str, Any]
    generation: dict[str, str]


def _submitted_row(sample: EvalSample, tool_name: str) -> dict[str, Any] | None:
    if sample.output and sample.output.completion:
        try:
            row = json.loads(sample.output.completion)
            if isinstance(row, dict):
                return row
        except json.JSONDecodeError:
            pass
    for message in reversed(sample.messages or []):
        for call in getattr(message, "tool_calls", None) or []:
            if call.function == tool_name:
                return dict(call.arguments)
    return None


def extract(log_paths: list[Path], tool_name: str) -> dict[str, Generated]:
    """Extract submissions, with later log arguments winning by sample id."""
    generated: dict[str, Generated] = {}
    seen: set[str] = set()
    for path in log_paths:
        log = read_eval_log(str(path))
        model = str(log.eval.model)
        for sample in log.samples or []:
            sample_id = str(sample.id)
            seen.add(sample_id)
            row = _submitted_row(sample, tool_name)
            if row is None:
                continue
            generated[sample_id] = Generated(
                row=row,
                metadata=sample.metadata or {},
                generation={"model": model, "source_eval": path.name},
            )
    missing = sorted(seen - generated.keys())
    if missing:
        print(f"warning: no {tool_name} submission for: {missing}", file=sys.stderr)
    return generated


def _output_path(path: Path) -> Path:
    return path if path.is_absolute() else REPO_ROOT / path


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)
    print(f"wrote {len(value)} entries to {path}")


def collect_sequences(args: argparse.Namespace) -> int:
    generated = extract(args.eval, "submit_sequence")
    records = load_records()
    oeis_ids = sorted(
        {item.oeis_id for item in subset_conjectures(args.subset) if item.oeis_id},
        key=lambda value: int(value[1:]),
    )
    output = {}
    for oeis_id in oeis_ids:
        item = generated.get(oeis_id)
        output[oeis_id] = {
            "name": records.get(oeis_id, {}).get("name"),
            "description": item.row.get("description") if item else None,
            "generation": item.generation if item else None,
        }
    write_json(_output_path(args.metadata_dir) / "sequences.json", output)
    return 0


def collect_conjectures(args: argparse.Namespace) -> int:
    generated = extract(args.eval, "submit_conjecture")
    provenance = load_provenance()
    output = {}
    for conjecture in subset_conjectures(args.subset):
        item = generated.get(conjecture.id)
        source = provenance.get(conjecture.id, {})
        output[conjecture.id] = {
            "oeis_id": conjecture.oeis_id,
            "conjecture": item.row.get("conjecture") if item else None,
            "proposer": source.get("proposer"),
            "proposed_date": source.get("proposed_date"),
            "generation": item.generation if item else None,
        }
    write_json(_output_path(args.metadata_dir) / "conjectures.json", output)
    return 0


def collect_proofs(args: argparse.Namespace) -> int:
    generated = extract(args.eval, "submit_proof_summary")
    run_dir = _output_path(args.run_dir)
    allowed = {conjecture.id for conjecture in subset_conjectures(args.subset)}
    solves = {
        solve.id: solve
        for solve in solved_samples(run_dir)
        if solve.id in allowed
    }

    unexpected = sorted(generated.keys() - solves.keys())
    if unexpected:
        print(
            f"warning: proof summaries do not match accepted samples in {run_dir}: "
            f"{unexpected}",
            file=sys.stderr,
        )

    written = 0
    for sample_id, solve in sorted(solves.items()):
        item = generated.get(sample_id)
        value = {
            "settlement": solve.settlement,
            "proof_summary": item.row.get("proof_summary") if item else None,
            "generation": item.generation if item else None,
        }
        write_json(solve.directory / "metadata.json", value)
        written += 1
    print(f"wrote proof metadata for {written} accepted samples under {plaintext_dir(run_dir)}")
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    for name, help_text in (
        ("sequences", "write metadata/sequences.json"),
        ("conjectures", "write metadata/conjectures.json"),
    ):
        command = subparsers.add_parser(name, help=help_text)
        command.add_argument("--subset", default="lite")
        command.add_argument("--eval", nargs="+", required=True, type=Path)
        command.add_argument("--metadata-dir", type=Path, default=Path("metadata"))

    proofs = subparsers.add_parser(
        "proofs", help="write metadata.json beside each accepted proof"
    )
    proofs.add_argument("--run-dir", required=True, type=Path)
    proofs.add_argument("--subset", default="lite")
    proofs.add_argument("--eval", nargs="+", required=True, type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.command == "sequences":
        return collect_sequences(args)
    if args.command == "conjectures":
        return collect_conjectures(args)
    return collect_proofs(args)


if __name__ == "__main__":
    raise SystemExit(main())
