#!/usr/bin/env python3
"""Compute the API cost of Inspect eval runs from extracted plaintext.

Reads the per-sample ``info.json`` files written by ``scripts/extract_plaintext.py``
(each carries that sample's ``model_usage``) and multiplies token usage by the
per-token prices in a LiteLLM-format price table
(``scripts/data/model_prices_and_context_window.json``). Reading the small JSON
files is far faster than re-parsing the ``.eval`` archives, so run
``extract_plaintext.py`` first.

Cost per (sample, model) is:

    input_tokens        * input_cost_per_token
  + output_tokens       * output_cost_per_token
  + cache_read_tokens   * cache_read_input_token_cost
  + cache_write_tokens  * cache_creation_input_token_cost

Inspect reports cache read/write tokens separately from ``input_tokens``, so the
four terms do not double-count.

Fable 5 (any ``*fable*`` model) is excluded from the totals by request — see
IGNORED_MODEL_SUBSTRINGS.

Usage:
    scripts/eval_cost.py                  # cost every info.json under logs/, by eval-set
    scripts/eval_cost.py logs/oeis-u40-*  # specific eval-set dirs
    scripts/eval_cost.py --by-model       # add a per-model breakdown
    scripts/eval_cost.py --by-sample      # one row per sample
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PRICES = REPO_ROOT / "scripts" / "data" / "model_prices_and_context_window.json"

# Models that legitimately have no cost (mocked / unset) — don't flag as unknown.
ZERO_COST_MODELS = {"mockllm/model", "none/none", "none", ""}

# Models excluded from cost analysis entirely (not counted, not flagged).
IGNORED_MODEL_SUBSTRINGS = ("fable",)


@dataclass
class Price:
    input: float = 0.0
    output: float = 0.0
    cache_read: float = 0.0
    cache_write: float = 0.0


class PriceTable:
    """Resolve Inspect model names (e.g. ``anthropic/claude-opus-4-8``) to prices."""

    def __init__(self, prices_path: Path):
        with prices_path.open() as f:
            self._raw = json.load(f)
        self.unknown_models: set[str] = set()
        self._cache: dict[str, Price | None] = {}

    def _lookup(self, name: str) -> Price | None:
        # Try the full name, then the part after the provider prefix
        # ("anthropic/claude-opus-4-8" -> "claude-opus-4-8"), then lowercase.
        # Also strip a "-data-retention" suffix, which is a billing/routing
        # variant priced identically to the base model.
        bare = name.split("/", 1)[-1]
        candidates = [name, bare, bare.removesuffix("-data-retention")]
        candidates += [c.lower() for c in candidates]
        for key in candidates:
            entry = self._raw.get(key)
            if entry is not None:
                return Price(
                    input=entry.get("input_cost_per_token") or 0.0,
                    output=entry.get("output_cost_per_token") or 0.0,
                    cache_read=entry.get("cache_read_input_token_cost") or 0.0,
                    cache_write=entry.get("cache_creation_input_token_cost") or 0.0,
                )
        return None

    def price(self, name: str) -> Price:
        if name not in self._cache:
            self._cache[name] = self._lookup(name)
        price = self._cache[name]
        if price is None:
            if name not in ZERO_COST_MODELS:
                self.unknown_models.add(name)
            return Price()
        return price


def is_ignored(model: str) -> bool:
    lname = model.lower()
    return any(sub in lname for sub in IGNORED_MODEL_SUBSTRINGS)


def usage_cost(usage: dict, price: Price) -> float:
    return (
        (usage.get("input_tokens") or 0) * price.input
        + (usage.get("output_tokens") or 0) * price.output
        + (usage.get("input_tokens_cache_read") or 0) * price.cache_read
        + (usage.get("input_tokens_cache_write") or 0) * price.cache_write
    )


@dataclass
class SampleResult:
    sample_id: str
    total: float = 0.0
    by_model: dict[str, float] = field(default_factory=dict)


def cost_info_file(path: Path, prices: PriceTable) -> SampleResult:
    with path.open() as f:
        info = json.load(f)
    result = SampleResult(sample_id=str(info.get("id", path.parent.name)))
    for model, usage in (info.get("model_usage") or {}).items():
        if is_ignored(model):
            continue
        cost = usage_cost(usage, prices.price(model))
        result.by_model[model] = result.by_model.get(model, 0.0) + cost
        result.total += cost
    return result


def eval_set_of(info_path: Path) -> str:
    """The eval-set id for an info.json.

    Layout is ``<set>/<eval_stem>_plaintext/<sample>/info.json``, so the
    eval-set is three directories up from the file.
    """
    parents = info_path.parents
    return parents[2].name if len(parents) >= 3 else info_path.parent.name


def collect_info_files(paths: list[str]) -> list[Path]:
    files: list[Path] = []
    for p in paths:
        path = Path(p)
        if path.is_dir():
            files.extend(sorted(path.rglob("info.json")))
        elif path.name == "info.json":
            files.append(path)
        else:
            print(f"warning: skipping non-info path {path}", file=sys.stderr)
    seen: set[Path] = set()
    return [f for f in files if not (f in seen or seen.add(f))]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paths", nargs="*", default=["logs"], help="Dirs containing extracted info.json (default: logs)")
    parser.add_argument("--prices", type=Path, default=DEFAULT_PRICES, help="LiteLLM-format price table JSON")
    parser.add_argument("--by-model", action="store_true", help="Show a per-model cost breakdown")
    parser.add_argument("--by-sample", action="store_true", help="Show per-sample costs")
    args = parser.parse_args()

    prices = PriceTable(args.prices)
    info_files = collect_info_files(args.paths or ["logs"])
    if not info_files:
        print("No info.json files found. Run scripts/extract_plaintext.py first.", file=sys.stderr)
        return 1

    # Group samples by eval-set.
    by_set: dict[str, list[SampleResult]] = {}
    for path in info_files:
        try:
            r = cost_info_file(path, prices)
        except Exception as e:  # noqa: BLE001 — keep going across a mixed tree
            print(f"  ERROR reading {path}: {e}", file=sys.stderr)
            continue
        by_set.setdefault(eval_set_of(path), []).append(r)

    grand_total = 0.0
    grand_samples = 0
    grand_by_model: dict[str, float] = {}

    for eval_set in sorted(by_set):
        samples = by_set[eval_set]
        set_total = sum(s.total for s in samples)
        set_by_model: dict[str, float] = {}
        for s in samples:
            for m, c in s.by_model.items():
                set_by_model[m] = set_by_model.get(m, 0.0) + c
                grand_by_model[m] = grand_by_model.get(m, 0.0) + c
        grand_total += set_total
        grand_samples += len(samples)

        print(f"{eval_set}  ({len(samples)} samples)  ${set_total:,.2f}")
        if args.by_model:
            for m, c in sorted(set_by_model.items(), key=lambda kv: -kv[1]):
                print(f"    {m:<40} ${c:,.4f}")
        if args.by_sample:
            for s in sorted(samples, key=lambda s: -s.total):
                print(f"    sample {s.sample_id:<24} ${s.total:,.4f}")

    print("=" * 60)
    print(f"TOTAL  eval-sets={len(by_set)}  samples={grand_samples}  cost=${grand_total:,.2f}  (Fable 5 excluded)")
    if args.by_model:
        for m, c in sorted(grand_by_model.items(), key=lambda kv: -kv[1]):
            print(f"  {m:<40} ${c:,.2f}")
    if prices.unknown_models:
        print(f"\nWARNING: no price found for (counted as $0): {sorted(prices.unknown_models)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
