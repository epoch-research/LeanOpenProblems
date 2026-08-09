"""Collect LLM-written summaries from summarize eval logs into JSONL.

With only --sequences, writes sequences.jsonl (the input summarize_proofs
needs). With --proofs too, also writes conjectures.jsonl -- one row per settled
conjecture, joined to its sequence description and to the original run's proof
cost (token usage priced at API rates) and working time.

When the same sample id appears in multiple logs, later logs win, so patch-up
reruns via --sample-id can simply be appended.

Usage:
    python scripts/summarize/collect.py --sequences <seq.eval>... [--proofs <proof.eval>...] -o out
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from inspect_ai.log import read_eval_log, read_eval_log_sample_summaries

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from eval_cost import DEFAULT_PRICES, PriceTable, usage_cost
from task import load_provenance, load_records, plaintext_dir


class SummarizePrices(PriceTable):
    """PriceTable that also resolves proxy-prefixed names like epoch/claude-fable-5
    to the table's anthropic.<model> entries."""

    def _lookup(self, name: str):
        found = super()._lookup(name)
        if found is None:
            found = super()._lookup("anthropic." + name.split("/", 1)[-1])
        return found


def _submitted_row(sample, tool_name: str) -> dict | None:
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


def extract(log_paths: list[Path], tool_name: str):
    """Submitted rows and metadata per sample id, plus the logs' task_args run_dirs."""
    rows: dict[str, dict] = {}
    metadata: dict[str, dict] = {}
    seen: set[str] = set()
    run_dirs: set[str] = set()
    for path in log_paths:
        log = read_eval_log(str(path))
        run_dir = (log.eval.task_args or {}).get("run_dir")
        if run_dir:
            run_dirs.add(run_dir)
        for sample in log.samples or []:
            sample_id = str(sample.id)
            seen.add(sample_id)
            row = _submitted_row(sample, tool_name)
            if row is not None:
                rows[sample_id] = row
                metadata[sample_id] = sample.metadata or {}
    missing = sorted(seen - rows.keys())
    if missing:
        print(f"warning: no {tool_name} submission for: {missing}", file=sys.stderr)
    return rows, metadata, run_dirs


def proof_costs(run_dir: Path, prices: PriceTable) -> dict[str, float]:
    costs = {}
    for sample_dir in sorted(plaintext_dir(run_dir).iterdir()):
        if not sample_dir.is_dir():
            continue
        info = json.loads((sample_dir / "info.json").read_text())
        costs[str(info["id"])] = sum(
            usage_cost(usage, prices.price(model))
            for model, usage in (info.get("model_usage") or {}).items()
        )
    return costs


def working_times(run_dir: Path) -> dict[str, float]:
    times = {}
    for path in sorted(run_dir.glob("*.eval")):
        for summary in read_eval_log_sample_summaries(str(path)):
            times[str(summary.id)] = summary.working_time
    return times


def a_number(oeis_id: str | None) -> int:
    return int(oeis_id[1:]) if oeis_id else 0


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))
    print(f"wrote {len(rows)} rows to {path}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--sequences", nargs="+", required=True, type=Path,
                        help="summarize_sequences .eval log(s)")
    parser.add_argument("--proofs", nargs="*", type=Path, default=[],
                        help="summarize_proofs .eval log(s)")
    parser.add_argument("-o", "--output-dir", type=Path, default=Path("."))
    parser.add_argument("--run-dir", type=Path, default=None,
                        help="original run dir (default: from the proof logs' task_args)")
    parser.add_argument("--prices", type=Path, default=DEFAULT_PRICES,
                        help="LiteLLM-format price table JSON")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)

    records = load_records()

    seq_rows, _, _ = extract(args.sequences, "submit_sequence")
    descriptions = {oeis_id: row["description"] for oeis_id, row in seq_rows.items()}
    write_jsonl(
        args.output_dir / "sequences.jsonl",
        [
            {
                "oeis_id": oeis_id,
                "description": descriptions[oeis_id],
                "oeis_name": records.get(oeis_id, {}).get("name"),
            }
            for oeis_id in sorted(descriptions, key=a_number)
        ],
    )

    if not args.proofs:
        return 0

    proof_rows, proof_meta, run_dirs = extract(args.proofs, "submit_summary")
    if args.run_dir:
        run_dir = args.run_dir
    elif len(run_dirs) == 1:
        run_dir = Path(run_dirs.pop())
    else:
        parser.error(f"cannot infer a unique run_dir from proof logs ({run_dirs}); pass --run-dir")

    prices = SummarizePrices(args.prices)
    costs = proof_costs(run_dir, prices)
    times = working_times(run_dir)
    provenance = load_provenance()

    conjectures = []
    for sample_id in sorted(
        proof_rows, key=lambda i: (a_number(proof_meta[i].get("oeis_id")), i)
    ):
        row, meta = proof_rows[sample_id], proof_meta[sample_id]
        oeis_id = meta.get("oeis_id")
        prov = provenance.get(sample_id, {})
        if oeis_id not in descriptions:
            print(f"warning: no sequence description for {oeis_id} ({sample_id})",
                  file=sys.stderr)
        conjectures.append(
            {
                "id": sample_id,
                "oeis_id": oeis_id,
                "verdict": meta.get("verdict"),
                "sequence_description": descriptions.get(oeis_id),
                "oeis_name": records.get(oeis_id, {}).get("name"),
                "conjecture": row.get("conjecture"),
                "proof_summary": row.get("proof_summary"),
                "proposer": prov.get("proposer"),
                "proposed_date": prov.get("proposed_date"),
                "cost_usd": costs.get(sample_id),
                "working_time": times.get(sample_id),
            }
        )
    write_jsonl(args.output_dir / "conjectures.jsonl", conjectures)

    if prices.unknown_models:
        print(f"warning: no price found for (counted as $0): {sorted(prices.unknown_models)}",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
