"""Bar plots of top-level scores.json accuracy across OEIS eval runs."""

import json
import re
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams

from bench_names import (ALPHAPROOF_NEXUS, BENCH_FULL, BENCH_LITE,
                         MODEL_LABELS, PROVIDER_RE, PROVIDERS)

LOGS = Path("logs")
OUT = Path("plots")
OUT.mkdir(exist_ok=True)

# --- collect data ---------------------------------------------------------
runs = {}  # eval_set_name -> (accuracy, stderr, n)
for scores_path in LOGS.glob("*/*/scores.json"):
    eval_set = scores_path.parent.parent.name
    data = json.loads(scores_path.read_text())
    (scorer,) = data
    m = scorer["metrics"]
    runs[eval_set] = (m["accuracy"]["value"], m["stderr"]["value"], scorer["scored_samples"])

VARIANT_LABELS = {"base": "base", "deep": "deep", "lit": "lit"}

def parse(name):
    m = re.match(rf"oeis-(full|lite)-(\d+usd)-(?:(deep|lit)-)?({PROVIDER_RE})-", name)
    task, budget, variant, provider = m.groups()
    return task, budget, variant or "base", provider

table = {}  # (task, variant, provider) -> (acc, err, n)
for name, vals in runs.items():
    task, budget, variant, provider = parse(name)
    table[(task, variant, provider)] = vals

# --- palette (dataviz reference, light mode) -------------------------------
SERIES = {"base": "#2a78d6", "deep": "#008300", "lit": "#e87ba4"}  # slots 1-3
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
BASELINE = "#c3c2b7"
SURFACE = "#fcfcfb"

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

def style_axis(ax, ymax=0.62):
    ax.set_ylim(0, ymax)
    ax.yaxis.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(BASELINE)
    ax.tick_params(length=0)
    ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")

fig, (ax1, ax2) = plt.subplots(
    1, 2, figsize=(13, 4.6), gridspec_kw={"width_ratios": [3, 2.1]}
)

# --- panel 1: lite, model x variant ----------------------------------------
variants = ["base", "deep", "lit"]
providers = [p for p in PROVIDERS
             if any(("lite", v, p) in table for v in variants)]
bar_w = 0.26
for j, variant in enumerate(variants):
    xs, ys, errs = [], [], []
    for i, prov in enumerate(providers):
        if ("lite", variant, prov) not in table:
            continue
        acc, err, _ = table[("lite", variant, prov)]
        xs.append(i + (j - 1) * (bar_w + 0.02))
        ys.append(acc)
        errs.append(err)
    bars = ax1.bar(xs, ys, width=bar_w, color=SERIES[variant], label=variant)
    ax1.errorbar(xs, ys, yerr=errs, fmt="none", ecolor=INK2, elinewidth=1, capsize=3)
    for x, y in zip(xs, ys):
        ax1.text(x, y + 0.055, f"{y:.0%}", ha="center", va="bottom",
                 fontsize=9, color=INK2)

ax1.set_xticks(range(len(providers)))
ax1.set_xticklabels([MODEL_LABELS[p] for p in providers], fontsize=10.5)
style_axis(ax1)
ax1.set_title(f"{BENCH_LITE} — accuracy by model and scaffold variant\n"
              "(n=100 conjectures, $200 budget/sample, ±1 s.e.)",
              fontsize=11, loc="left", color=INK)
ax1.legend(title="scaffold", frameon=False, fontsize=9.5, title_fontsize=9.5,
           loc="upper center", ncols=len(variants))

# --- panel 2: full, base scaffold ------------------------------------------
full_provs = [p for p in providers if ("full", "base", p) in table]
ys = [table[("full", "base", p)][0] for p in full_provs]
errs = [table[("full", "base", p)][1] for p in full_provs]
labels = [MODEL_LABELS[p].replace(" ", "\n", 1) for p in full_provs]
colors = ["#2a78d6"] * len(full_provs)

# External reported baseline: AlphaProof Nexus, 44/492 solved
apn_acc = 44 / 492
apn_err = (apn_acc * (1 - apn_acc) / 492) ** 0.5
ys.append(apn_acc)
errs.append(apn_err)
labels.append(f"{ALPHAPROOF_NEXUS}\n(reported)")
colors.append(MUTED)

xs = range(len(ys))
ax2.bar(xs, ys, width=0.5, color=colors)
ax2.errorbar(xs, ys, yerr=errs, fmt="none", ecolor=INK2, elinewidth=1, capsize=3)
for x, y in zip(xs, ys):
    ax2.text(x, y + 0.025, f"{y:.1%}", ha="center", va="bottom",
             fontsize=9, color=INK2)
ax2.set_xticks(list(xs))
ax2.set_xticklabels(labels, fontsize=9.5)
style_axis(ax2)
n_full = table[("full", "base", full_provs[0])][2]
ax2.set_title(f"{BENCH_FULL} — accuracy\n(n={n_full}, $50 budget/sample, ±1 s.e.)",
              fontsize=11, loc="left", color=INK)
missing = [p for p in providers if ("full", "base", p) not in table]
if missing:
    ax2.text(0.98, 0.97, f"{', '.join(MODEL_LABELS[p] for p in missing)}:\nno full run downloaded",
             transform=ax2.transAxes, ha="right", va="top", fontsize=8.5, color=MUTED)

fig.tight_layout(w_pad=3)
fig.savefig(OUT / "accuracy.png", dpi=200)
print("wrote", OUT / "accuracy.png")
