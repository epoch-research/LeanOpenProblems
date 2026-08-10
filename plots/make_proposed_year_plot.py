"""Solve rate binned by the year the conjecture was proposed (from
apn/data/oeis/conjecture_provenance.jsonl), for the benchmark's full and lite
runs. Per-year counts are too small (3-45) for per-year rates, so years are
binned into calendar eras of roughly equal n."""

import json
import glob
import re
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams

from bench_names import (BENCH_FULL, BENCH_LITE, MODEL_LABELS, PROVIDER_RE,
                         PROVIDERS, SERIES)

LOGS = Path("logs")
OUT = Path("plots")

INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
BASELINE = "#c3c2b7"
SURFACE = "#ffffff"

rcParams.update({
    "font.family": ["Helvetica Neue", "Arial", "DejaVu Sans"],
    "figure.facecolor": SURFACE,
    "axes.facecolor": SURFACE,
    "savefig.facecolor": SURFACE,
    "text.color": INK,
    "axes.edgecolor": BASELINE,
    "xtick.color": INK2,
    "ytick.color": MUTED,
})

# --- proposal year ----------------------------------------------------------
year = {}
for line in open("apn/data/oeis/conjecture_provenance.jsonl"):
    d = json.loads(line)
    if d.get("proposed_date"):
        year[d["theorem_name"]] = int(d["proposed_date"][:4])

# --- outcomes ---------------------------------------------------------------
# per eval set: sample -> provider -> fraction of that model's runs that solved
# (full: one run per model, so 0/1; lite: pooled over base/deep/lit, so 0..1)
def collect(glob_pat):
    hits = defaultdict(lambda: defaultdict(list))
    for run in glob.glob(str(LOGS / glob_pat / "*_plaintext")):
        prov = re.search(rf"-({PROVIDER_RE})-[a-z0-9]+$", Path(run).parent.name).group(1)
        for sd in Path(run).iterdir():
            if not sd.is_dir():
                continue
            sc = json.loads((sd / "scores.json").read_text()).get("proof_scorer") or {}
            tid = json.loads((sd / "info.json").read_text())["id"]
            hits[tid][prov].append(sc.get("value") == "C")
    return {s: {p: sum(v) / len(v) for p, v in per.items()} for s, per in hits.items()}

full_frac = collect("oeis-full-*")
lite_frac = collect("oeis-lite-*")

BINS = [("≤2006", 0, 2006), ("2007–11", 2007, 2011), ("2012–16", 2012, 2016),
        ("2017–21", 2017, 2021), ("2022–25", 2022, 2025)]

ROWS = [
    (BENCH_FULL, full_frac, BINS, 0.62),
    (BENCH_LITE, lite_frac, BINS, 1.04),
]

fig, axes = plt.subplots(2, 1, figsize=(9.2, 8.4))
bar_w = 0.26
for (row_title, frac, bins, ymax), ax in zip(ROWS, axes):
    dated = [s for s in frac if s in year]
    groups = [[s for s in dated if lo <= year[s] <= hi] for _, lo, hi in bins]
    provs = [p for p in PROVIDERS if any(p in per for per in frac.values())]
    w = min(bar_w, 0.84 / len(provs) - 0.02)
    for j, prov in enumerate(provs):
        xs, ys, errs = [], [], []
        for i, members in enumerate(groups):
            vals = [frac[s].get(prov, 0.0) for s in members]
            n = len(vals)
            mean = sum(vals) / n
            var = sum((v - mean) ** 2 for v in vals) / n
            xs.append(i + (j - (len(provs) - 1) / 2) * (w + 0.02))
            ys.append(mean)
            errs.append((var / n) ** 0.5)
        ax.bar(xs, ys, width=w, color=SERIES[prov], label=MODEL_LABELS[prov])
        ax.errorbar(xs, ys, yerr=errs, fmt="none", ecolor=INK2,
                    elinewidth=1, capsize=2)
    ax.set_xticks(range(len(bins)))
    ax.set_xticklabels([f"{lbl}\nn={len(g)}"
                        for (lbl, _, _), g in zip(bins, groups)], fontsize=9.5)
    ax.set_ylim(0, ymax)
    ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")
    ax.yaxis.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(BASELINE)
    ax.tick_params(length=0)
    n_binned = sum(len(g) for g in groups)
    note = f"{len(dated)}/{len(frac)} conjectures with a date"
    if n_binned < len(dated):
        note += f", {len(dated) - n_binned} pre-{BINS[0][1]} excluded"
    print(f"{row_title}: {note}")
    ax.set_title(row_title, fontsize=10.5, loc="left", color=INK, pad=10)

axes[1].set_xlabel("year the conjecture was proposed", fontsize=9, color=INK2)
# the lite panel has every provider, the full panel may not; legend from the union
handles = {}
for ax in axes:
    h, l = ax.get_legend_handles_labels()
    handles.update(zip(l, h))
axes[0].legend(handles.values(), handles.keys(), frameon=False, fontsize=9,
               loc="upper left")
fig.suptitle("Solve rate by year the conjecture was proposed",
             fontsize="x-large")
fig.tight_layout(rect=(0, 0, 1, 0.96), h_pad=3)
fig.savefig(OUT / "proposed_year_solve_rate.png", dpi=200)
print("wrote", OUT / "proposed_year_solve_rate.png")
