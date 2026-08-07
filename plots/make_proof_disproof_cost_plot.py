"""ECDF of solve cost for proofs vs disproofs, one panel per eval-set kind.

Disproofs are much cheaper to find than proofs; a heavy sub-$1 mass of
disproofs (many unanimous across models) is a misformalization signal, since
statements that are false as formalized fall to edge-case counterexamples."""

import glob
import json
import re
import statistics
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams

from bench_names import BENCH_FULL, BENCH_LITE, PROVIDER_RE

LOGS = Path("logs")
OUT = Path("plots")

PROOF = "#2a78d6"
DISPROOF = "#eb6834"
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

data = {"lite": {"proof": [], "disproof": []}, "full": {"proof": [], "disproof": []}}
provs = defaultdict(set)
n_runs = defaultdict(int)
for run in glob.glob(str(LOGS / "oeis-*" / "*_plaintext")):
    kind = "full" if "-full-" in Path(run).parent.name else "lite"
    provs[kind].add(re.search(rf"-({PROVIDER_RE})-[a-z0-9]+$",
                              Path(run).parent.name).group(1))
    n_runs[kind] += 1
    for sd in Path(run).iterdir():
        if not sd.is_dir():
            continue
        if json.loads((sd / "scores.json").read_text())["proof_scorer"]["value"] != "C":
            continue
        info = json.loads((sd / "info.json").read_text())
        cost = max(sum(u.get("total_cost", 0)
                       for u in (info.get("model_usage") or {}).values()), 0.01)
        spec = sd / "Submission" / "Spec.lean"
        is_dis = spec.exists() and ".disproof" in spec.read_text(errors="replace")
        data[kind]["disproof" if is_dis else "proof"].append(cost)

def ecdf(xs):
    xs = sorted(xs)
    n = len(xs)
    return xs, [(i + 1) / n for i in range(n)]

PANELS = [
    ("lite", f"{BENCH_LITE} — solve-cost ECDF by outcome\n"
             f"(100 conjectures, $200 cap, {n_runs['lite']} runs pooled over "
             f"{len(provs['lite'])} models)", 220),
    ("full", f"{BENCH_FULL} — solve-cost ECDF by outcome\n"
             f"(492 conjectures, $50 cap, {len(provs['full'])} models)", 60),
]

fig, axes = plt.subplots(1, 2, figsize=(11.5, 4.9))
for ax, (kind, title, xmax) in zip(axes, PANELS):
    for outcome, label, color in [("proof", "proofs", PROOF),
                                  ("disproof", "disproofs", DISPROOF)]:
        x, y = ecdf(data[kind][outcome])
        ax.step([x[0]] + x, [0] + y, where="post", color=color, linewidth=2,
                label=f"{label} (n={len(x)})")
    for outcome, color, ytxt in [("proof", PROOF, 0.53), ("disproof", DISPROOF, 0.44)]:
        m = statistics.median(data[kind][outcome])
        ax.axvline(m, color=color, linewidth=0.9, linestyle=(0, (2, 2)), alpha=0.7)
        ax.text(m * 1.12, ytxt, f"median ${m:.2f}", color=color, fontsize=8.5)
    ax.set_xscale("log")
    ticks = [t for t in [0.03, 0.1, 0.3, 1, 3, 10, 30, 100, 200] if t <= xmax]
    ax.set_xticks(ticks)
    ax.set_xticklabels([f"${t:g}" if t >= 1 else f"${t:.2f}" for t in ticks], fontsize=9)
    ax.set_ylim(0, 1.02)
    ax.set_xlim(0.03, xmax)
    ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")
    ax.yaxis.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(BASELINE)
    ax.tick_params(length=0)
    ax.set_xlabel("sample cost at solve (log scale)", fontsize=9.5, color=INK2)
    ax.set_title(title, fontsize=10, loc="left", color=INK)
axes[0].legend(frameon=False, fontsize=9.5, loc="lower right")
fig.tight_layout(w_pad=3)
fig.savefig(OUT / "proof_disproof_cost.png", dpi=200)
print("wrote", OUT / "proof_disproof_cost.png")
