"""Merge several conjectures.jsonl files (see collect.py) into one union.

Usage:
    python scripts/summarize/union.py out/conjectures.jsonl out/opus-full/conjectures.jsonl \
        -o out/union.jsonl

A conjecture settled in more than one run is kept once, carrying the row from
the run that settled it most cheaply; `cost_usd` is therefore the cheapest
demonstrated cost of settling it. `settled_by` records how many inputs settled
it, and `source` the file the kept row came from.
"""

import argparse
import json
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("-o", "--output", type=Path, required=True)
    args = parser.parse_args()

    best: dict[str, dict] = {}
    for path in args.inputs:
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            kept = best.get(row["id"])
            if kept is None or row["cost_usd"] < kept["cost_usd"]:
                row = {**row, "source": str(path), "settled_by": 1}
                if kept:
                    row["settled_by"] = kept["settled_by"] + 1
                best[row["id"]] = row
            else:
                kept["settled_by"] += 1

    rows = sorted(best.values(), key=lambda r: -r["cost_usd"])
    with args.output.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")
    shared = sum(1 for r in rows if r["settled_by"] > 1)
    print(f"wrote {len(rows)} rows to {args.output} ({shared} settled by more than one run)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
