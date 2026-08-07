"""Solve rate binned by citation metadata in apn/data/oeis (native OEIS page
citations and OpenAlex citing works), for the benchmark's full and lite runs."""

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

# --- citation metadata ------------------------------------------------------
native = {}
for line in open("apn/data/oeis/oeis_native_citations.jsonl"):
    d = json.loads(line)
    native[d["oeis_id"]] = len(d["citations"])
openalex = {}
for line in open("apn/data/oeis/openalex_citations.jsonl"):
    d = json.loads(line)
    openalex[d["oeis_id"]] = len(d["citations"])

# --- outcomes ---------------------------------------------------------------
# per eval set: sample -> provider -> fraction of that model's runs that solved
# (full: one run per model, so 0/1; lite: pooled over base/deep/lit, so 0..1)
def collect(glob_pat):
    hits = defaultdict(lambda: defaultdict(list))
    oeis_of = {}
    for run in glob.glob(str(LOGS / glob_pat / "*_plaintext")):
        prov = re.search(rf"-({PROVIDER_RE})-[a-z0-9]+$", Path(run).parent.name).group(1)
        for sd in Path(run).iterdir():
            if not sd.is_dir():
                continue
            sc = json.loads((sd / "scores.json").read_text())["proof_scorer"]
            info = json.loads((sd / "info.json").read_text())
            hits[sd.name][prov].append(sc["value"] == "C")
            oeis_of[sd.name] = info.get("oeis_id")
    frac = {s: {p: sum(v) / len(v) for p, v in per.items()} for s, per in hits.items()}
    return frac, oeis_of

full_frac, full_oeis = collect("oeis-full-*")
lite_frac, lite_oeis = collect("oeis-lite-*")

NATIVE_FULL = [("0", 0, 0), ("1–2", 1, 2), ("3–9", 3, 9), ("10+", 10, 10**9)]
NATIVE_LITE = [("0", 0, 0), ("1–2", 1, 2), ("3+", 3, 10**9)]
OPENALEX = [("0", 0, 0), ("1+", 1, 10**9)]

ROWS = [
    (BENCH_FULL, full_frac, full_oeis, NATIVE_FULL),
    (BENCH_LITE, lite_frac, lite_oeis, NATIVE_LITE),
]

fig, axes = plt.subplots(2, 2, figsize=(11.5, 8.6),
                         gridspec_kw={"width_ratios": [4, 2.2]})
bar_w = 0.26
for (row_title, frac, oeis_of, native_bins), (axl, axr) in zip(ROWS, axes):
    for ax, counts, bins, title in [
        (axl, native, native_bins, "OEIS page citations"),
        (axr, openalex, OPENALEX, "OpenAlex citing works"),
    ]:
        groups = [[s for s in frac if lo <= counts.get(oeis_of[s], 0) <= hi]
                  for _, lo, hi in bins]
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
            ax.bar(xs, ys, width=w, color=SERIES[prov],
                   label=MODEL_LABELS[prov])
            ax.errorbar(xs, ys, yerr=errs, fmt="none", ecolor=INK2,
                        elinewidth=1, capsize=2)
        ax.set_xticks(range(len(bins)))
        ax.set_xticklabels([f"{lbl}\nn={len(g)}"
                            for (lbl, _, _), g in zip(bins, groups)], fontsize=9.5)
        ax.set_ylim(0, 0.62)
        ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")
        ax.yaxis.grid(True, color=GRID, linewidth=0.8)
        ax.set_axisbelow(True)
        for side in ("top", "right", "left"):
            ax.spines[side].set_visible(False)
        ax.spines["bottom"].set_color(BASELINE)
        ax.tick_params(length=0)
        ax.set_title(title, fontsize=10, loc="left", color=INK2, pad=8)
    axl.text(0, 1.22, row_title, transform=axl.transAxes, fontsize=10.5,
             color=INK, fontweight="bold")
    axr.set_xlabel("")
    axl.set_xlabel("")

axes[1][0].set_xlabel("citations of the sample's OEIS sequence", fontsize=9, color=INK2)
axes[1][1].set_xlabel("citations of the sample's OEIS sequence", fontsize=9, color=INK2)
# the lite row has every provider, the full row may not; legend from the union
handles = {}
for ax in (axes[0][0], axes[1][0]):
    h, l = ax.get_legend_handles_labels()
    handles.update(zip(l, h))
axes[0][0].legend(handles.values(), handles.keys(), frameon=False, fontsize=9,
                  loc="upper left")
fig.suptitle("Solve rate by citation count of the underlying sequence",
             fontsize="x-large")
fig.tight_layout(rect=(0, 0, 1, 0.95), h_pad=4)
fig.savefig(OUT / "citations_solve_rate.png", dpi=200)
print("wrote", OUT / "citations_solve_rate.png")
