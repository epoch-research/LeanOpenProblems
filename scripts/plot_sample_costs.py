#!/usr/bin/env python3
"""Per-run, per-model bar plots of problem cost, colored by solve rate.

One plot per **(.eval file, model)**: each bar is one OEIS problem's cost *for
that model* (computed from the extracted plaintext ``info.json``, **excluding
Fable 5** like ``eval_cost.py``), with cost **averaged over epochs**. Bars are
colored on a red→green gradient by the problem's **solve rate** (fraction of
epochs that scored CORRECT, ``proof_scorer == "C"``); problems with no score are
gray.

Each plot states its dataset subset — ``proved38`` (proofs already known) vs
``unproved40`` (open problems) vs ``lite`` — which dominates token usage and
therefore cost, so comparisons are only meaningful within the same subset.

Runs that are unreliable are dropped: if more than ``MAX_UNSCORED_FRAC`` of a
run's samples have no score (a bug, or the eval stopped early), the whole run is
excluded.

Reads the plaintext written by ``scripts/extract_plaintext.py`` (run it first)
plus each run's ``.eval`` header (header-only, cheap) for config.

Usage:
    scripts/plot_sample_costs.py                 # every run under logs/
    scripts/plot_sample_costs.py logs/oeis-u40-* # specific eval-set dirs
    scripts/plot_sample_costs.py -o logs/cost_plots
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from eval_cost import DEFAULT_PRICES, PriceTable, is_ignored, usage_cost  # noqa: E402

from inspect_ai.log import read_eval_log  # noqa: E402

CORRECT_VALUE = "C"  # Inspect's CORRECT score value
MAX_UNSCORED_FRAC = 0.10  # drop a run if more than this fraction of samples are unscored

SUBSETS_DIR = Path(__file__).resolve().parent.parent / "apn" / "data" / "oeis" / "subsets"


def _norm_id(name: str) -> str:
    """Normalize a conjecture name for cross-source matching."""
    s = name.strip().lower().removeprefix("oeis_")
    if "_ep" in s and s.rsplit("_ep", 1)[-1].isdigit():
        s = s.rsplit("_ep", 1)[0]
    return s


def _load_subset(name: str) -> set[str]:
    path = SUBSETS_DIR / f"{name}.txt"
    if not path.exists():
        return set()
    return {_norm_id(ln) for ln in path.read_text().splitlines() if ln.strip() and not ln.startswith("#")}


_SUBSET_SETS = {name: _load_subset(name) for name in ("proved38", "unproved40", "lite")}


def classify_subset(sample_ids: list[str], task_subset: str | None) -> str:
    """Determine the dataset subset, preferring the header's task_args value."""
    if task_subset and task_subset != "?":
        return task_subset
    ids = {_norm_id(s) for s in sample_ids}
    if not ids:
        return "?"
    best, best_frac = "?", 0.0
    for name, ref in _SUBSET_SETS.items():
        if ref and (frac := len(ids & ref) / len(ids)) > best_frac:
            best, best_frac = name, frac
    if best_frac >= 0.8:
        return best if best_frac == 1.0 else f"{best}~{best_frac:.0%}"
    return "mixed/?"


def human_tokens(n: int | None) -> str:
    if not n:
        return "—"
    for unit, scale in (("B", 1e9), ("M", 1e6), ("K", 1e3)):
        if n >= scale:
            return f"{n / scale:g}{unit}"
    return str(n)


def usd(x: float) -> str:
    return f"\\${x:,.0f}"  # escape $ so matplotlib doesn't read it as mathtext


def short_label(sample_id: str) -> str:
    # "oeis_340737_conjecture_0_ep002" -> "340737/c0/ep002"
    s = sample_id.replace("oeis_", "").replace("_conjecture_", "/c").replace("_ep", "/ep")
    return s


def sample_correct(scores: dict) -> bool | None:
    if not scores:
        return None
    score = scores.get("proof_scorer") or next(iter(scores.values()))
    value = score.get("value")
    return None if value is None else value == CORRECT_VALUE


UNSCORED_COLOR = "#bbbbbb"


@dataclass
class Problem:
    problem_id: str
    cost: float  # mean over epochs, for one model
    solve_rate: float | None  # fraction of scored epochs that were correct


def run_config(eval_path: Path) -> dict:
    e = read_eval_log(str(eval_path), header_only=True).eval
    args = e.task_args or {}
    return {
        "eval_set": eval_path.parent.name,
        "stem": eval_path.stem,
        "model": e.model,
        "subset": args.get("subset", "?"),
        "token_limit": getattr(e.config, "token_limit", None),
        "epochs": (e.config.epochs or 1),
    }


def process_run(eval_path: Path, prices: PriceTable) -> tuple[dict, dict[str, list[Problem]]] | None:
    """(config, {model: [Problem,...]}) for one run, or None if dropped/empty.

    Each Problem is one OEIS problem with cost averaged over its epochs and a
    solve_rate = (#epochs solved / #epochs scored).
    """
    plaintext_dir = eval_path.parent / (eval_path.stem + "_plaintext")
    if not plaintext_dir.is_dir():
        return None

    # one entry per epoch, grouped by epoch-independent problem id (info["id"])
    by_problem: dict[str, list[tuple[dict, bool | None]]] = defaultdict(list)
    n_samples = n_unscored = 0
    for sample_dir in sorted(p for p in plaintext_dir.iterdir() if p.is_dir()):
        info_path = sample_dir / "info.json"
        if not info_path.exists():
            continue
        info = json.loads(info_path.read_text())
        scores_path = sample_dir / "scores.json"
        scores = json.loads(scores_path.read_text()) if scores_path.exists() else {}
        correct = sample_correct(scores)
        by_problem[str(info.get("id", sample_dir.name))].append((info.get("model_usage") or {}, correct))
        n_samples += 1
        n_unscored += correct is None

    if n_samples == 0:
        return None

    frac = n_unscored / n_samples
    if frac > MAX_UNSCORED_FRAC:
        print(
            f"  DROP {eval_path.parent.name}/{eval_path.stem[:24]} — {n_unscored}/{n_samples} "
            f"({frac:.0%}) unscored",
            file=sys.stderr,
        )
        return None

    cfg = run_config(eval_path)
    cfg["subset"] = classify_subset(list(by_problem), cfg["subset"])

    models = {m for epochs in by_problem.values() for usage, _ in epochs for m in usage if not is_ignored(m)}
    by_model: dict[str, list[Problem]] = {m: [] for m in models}
    for pid, epochs in by_problem.items():
        scored = [ok for _, ok in epochs if ok is not None]
        solve_rate = (sum(scored) / len(scored)) if scored else None
        for model in models:
            avg_cost = sum(usage_cost(u[model], prices.price(model)) for u, _ in epochs if model in u) / len(epochs)
            by_model[model].append(Problem(pid, avg_cost, solve_rate))
    return cfg, by_model


def plot_run_model(cfg: dict, model: str, problems: list[Problem], out_dir: Path) -> Path | None:
    total = sum(p.cost for p in problems)
    if total == 0:
        return None
    problems = sorted(problems, key=lambda p: p.cost, reverse=True)
    costs = [p.cost for p in problems]

    cmap = matplotlib.colormaps["RdYlGn"]
    colors = [cmap(p.solve_rate) if p.solve_rate is not None else UNSCORED_COLOR for p in problems]
    solved = [p for p in problems if p.solve_rate is not None]
    mean_solve = (sum(p.solve_rate for p in solved) / len(solved)) if solved else float("nan")

    fig, ax = plt.subplots(figsize=(max(8, len(problems) * 0.20), 5.4))
    ax.bar(range(len(problems)), costs, color=colors)
    if len(problems) <= 60:
        ax.set_xticks(range(len(problems)))
        ax.set_xticklabels([short_label(p.problem_id) for p in problems], rotation=90, fontsize=6)
    else:
        ax.set_xticks([])
        ax.set_xlabel(f"{len(problems)} problems (sorted by cost)")
    ax.set_ylabel("Cost (USD/problem, mean over epochs)")
    ax.margins(x=0.005)

    sl = cfg["subset"].lower()
    kind = "UNPROVED" if "unproved" in sl else ("PROVED" if "proved" in sl else cfg["subset"].upper())
    subtitle = (
        f"DATASET: {kind} ({cfg['subset']})   ·   token_limit={human_tokens(cfg['token_limit'])}   ·   epochs={cfg['epochs']}\n"
        f"run: {cfg['eval_set']} / {cfg['stem']}\n"
        f"problems={len(problems)}  ·  mean solve rate={mean_solve:.0%}  ·  total={usd(total)}  ·  mean/problem={usd(total / len(problems))}"
    )
    ax.set_title(f"model = {model}\n{subtitle}", fontsize=9)

    sm = plt.cm.ScalarMappable(cmap=cmap, norm=matplotlib.colors.Normalize(0, 1))
    cbar = fig.colorbar(sm, ax=ax, pad=0.01)
    cbar.set_label("solve rate (fraction of epochs solved)", fontsize=8)
    if any(p.solve_rate is None for p in problems):
        ax.bar(0, 0, color=UNSCORED_COLOR, label="unscored")
        ax.legend(fontsize=8, loc="upper right")

    fig.tight_layout()
    set_dir = out_dir / cfg["eval_set"]
    set_dir.mkdir(parents=True, exist_ok=True)
    out_path = set_dir / f"{cfg['stem']}__{model.replace('/', '_')}.png"
    fig.savefig(out_path, dpi=130)
    plt.close(fig)
    print(f"  {cfg['eval_set']}/{out_path.name}  (problems={len(problems)}, mean_solve={mean_solve:.0%}, total={usd(total)})")
    return out_path


def collect_eval_files(paths: list[str]) -> list[Path]:
    files: list[Path] = []
    for p in paths:
        path = Path(p)
        if path.is_dir():
            files.extend(sorted(path.rglob("*.eval")))
        elif path.suffix == ".eval":
            files.append(path)
    seen: set[Path] = set()
    return [f for f in files if not (f in seen or seen.add(f))]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paths", nargs="*", default=["logs"], help="Eval files or dirs (default: logs)")
    parser.add_argument("--prices", type=Path, default=DEFAULT_PRICES)
    parser.add_argument("-o", "--out-dir", type=Path, default=Path("logs/cost_plots"))
    args = parser.parse_args()

    prices = PriceTable(args.prices)
    files = collect_eval_files(args.paths or ["logs"])
    if not files:
        print("No .eval files found.", file=sys.stderr)
        return 1

    made = 0
    for eval_path in files:
        try:
            result = process_run(eval_path, prices)
        except Exception as e:  # noqa: BLE001
            print(f"  ERROR {eval_path}: {e}", file=sys.stderr)
            continue
        if result is None:
            continue
        cfg, by_model = result
        for model, problems in sorted(by_model.items()):
            if plot_run_model(cfg, model, problems, args.out_dir):
                made += 1
    print(f"\nWrote {made} plot(s) to {args.out_dir}/")
    if prices.unknown_models:
        print(f"WARNING: no price for (counted $0): {sorted(prices.unknown_models)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
