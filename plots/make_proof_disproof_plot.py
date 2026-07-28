"""Solve rate split into proofs vs disproofs, per model.

A solve counts as a disproof when the accepted Submission/Spec.lean contains a
`.disproof` theorem (the harness's mechanism for settling a conjecture by
refutation)."""

import glob
import json
import re
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams

from bench_names import BENCH_FULL, BENCH_LITE

LOGS = Path("logs")
OUT = Path("plots")

MODEL_LABELS = {"ant": "Claude Opus 4.8", "oai": "GPT-5.5", "gdm": "Gemini 3.5 Flash"}
PROVIDERS = ["ant", "oai", "gdm"]

PROOF = "#2a78d6"
DISPROOF = "#eb6834"
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

# per (eval set kind, provider): per-sample fraction proved / disproved,
# averaged over that kind's runs (full: 1 run; lite: base/deep/lit pooled)
acc = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))  # kind->prov->sample->list
for run in glob.glob(str(LOGS / "oeis-*" / "*_plaintext")):
    es = Path(run).parent.name
    prov = re.search(r"-(ant|gdm|oai)-[a-z0-9]+$", es).group(1)
    kind = "full" if "-full-" in es else "lite"
    for sd in Path(run).iterdir():
        if not sd.is_dir():
            continue
        sc = json.loads((sd / "scores.json").read_text())["proof_scorer"]
        if sc["value"] == "C":
            spec = sd / "Submission" / "Spec.lean"
            is_dis = spec.exists() and ".disproof" in spec.read_text(errors="replace")
            acc[kind][prov][sd.name].append("disproof" if is_dis else "proof")
        else:
            acc[kind][prov][sd.name].append("fail")

def shares(kind, prov):
    per = acc[kind][prov]
    pr = [sum(v == "proof" for v in vs) / len(vs) for vs in per.values()]
    di = [sum(v == "disproof" for v in vs) / len(vs) for vs in per.values()]
    n = len(per)
    mean_p, mean_d = sum(pr) / n, sum(di) / n
    tot = [p + d for p, d in zip(pr, di)]
    mean_t = sum(tot) / n
    err_t = (sum((t - mean_t) ** 2 for t in tot) / n / n) ** 0.5
    return mean_p, mean_d, err_t, n

PANELS = [
    ("lite", f"{BENCH_LITE} — solve rate by outcome\n"
             "(100 conjectures, $200 cap, pooled over base/deep/lit agent runs, ±1 s.e.)"),
    ("full", f"{BENCH_FULL} — solve rate by outcome\n"
             "(492 conjectures, $50 cap, ±1 s.e.)"),
]

fig, axes = plt.subplots(1, 2, figsize=(10.5, 4.6))
for ax, (kind, title) in zip(axes, PANELS):
    xs = range(len(PROVIDERS))
    for i, p in enumerate(PROVIDERS):
        mean_p, mean_d, err_t, n = shares(kind, p)
        ax.bar(i, mean_p, width=0.52, color=PROOF)
        ax.bar(i, mean_d, width=0.52, bottom=mean_p, color=DISPROOF)
        ax.errorbar(i, mean_p + mean_d, yerr=err_t, fmt="none", ecolor=INK2,
                    elinewidth=1, capsize=3)
        ax.text(i, mean_p + mean_d + 0.03, f"{mean_p + mean_d:.0%}", ha="center",
                fontsize=9.5, color=INK)
        ax.text(i, mean_p / 2, f"{mean_p:.0%}", ha="center", va="center",
                fontsize=8.5, color=SURFACE)
        ax.text(i, mean_p + mean_d / 2, f"{mean_d:.0%}", ha="center", va="center",
                fontsize=8.5, color=SURFACE)
    ax.set_xticks(list(xs))
    ax.set_xticklabels([MODEL_LABELS[p].replace(" ", "\n", 1) for p in PROVIDERS],
                       fontsize=9.5)
    ax.set_ylim(0, 0.5)
    ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")
    ax.yaxis.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(BASELINE)
    ax.tick_params(length=0)
    ax.set_title(title, fontsize=10.5, loc="left", color=INK)

axes[0].bar(0, 0, color=PROOF, label="proved")
axes[0].bar(0, 0, color=DISPROOF, label="disproved")
axes[0].legend(frameon=False, fontsize=9, loc="upper right")
fig.tight_layout(w_pad=3)
fig.savefig(OUT / "proof_disproof.png", dpi=200)
print("wrote", OUT / "proof_disproof.png")
