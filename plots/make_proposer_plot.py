"""Conjectures per proposer (from apn/data/oeis/conjecture_provenance.jsonl)
with solve outcomes, one plot per eval set (OEIS OP-lite and OP-full)."""

import json
import glob
from collections import Counter, defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams
from matplotlib.patches import Rectangle

LOGS = Path("logs")
OUT = Path("plots")

INK = "#0b0b0b"
INK2 = "#52514e"
BASELINE = "#c3c2b7"
SURFACE = "#fcfcfb"
NEUTRAL = "#f0efec"
BLUE = "#2a78d6"

rcParams.update({
    "font.family": ["Helvetica Neue", "Arial", "DejaVu Sans"],
    "figure.facecolor": SURFACE,
    "axes.facecolor": SURFACE,
    "savefig.facecolor": SURFACE,
    "text.color": INK,
    "axes.edgecolor": BASELINE,
    "xtick.color": INK2,
    "ytick.color": INK2,
})

proposer_of = {}
for line in open("apn/data/oeis/conjecture_provenance.jsonl"):
    d = json.loads(line)
    proposer_of[d["theorem_name"]] = d.get("proposer") or "(unknown)"

def outcomes(glob_pat):
    """sample -> solved by >=1 run matching glob_pat"""
    solved = defaultdict(bool)
    for run in glob.glob(str(LOGS / glob_pat / "*_plaintext")):
        for sd in Path(run).iterdir():
            if not sd.is_dir():
                continue
            sc = json.loads((sd / "scores.json").read_text())["proof_scorer"]
            solved[sd.name] |= sc["value"] == "C"
    return dict(solved)

def proposer_plot(solved, top_n, title, fname):
    counts = Counter(proposer_of[s] for s in solved)
    top = [p for p, _ in counts.most_common(top_n)]
    rows = []
    for p in top:
        members = [s for s in solved if proposer_of[s] == p]
        rows.append((p, len(members), sum(solved[s] for s in members)))
    rest = [s for s in solved if proposer_of[s] not in top]
    rows.append((f"{len(counts) - top_n} other proposers", len(rest),
                 sum(solved[s] for s in rest)))

    fig, ax = plt.subplots(figsize=(8.2, 0.42 * len(rows) + 1.8))
    xmax = max(n for _, n, _ in rows)
    gap = xmax * 0.005
    for i, (name, n, k) in enumerate(rows):
        y = len(rows) - 1 - i
        ax.add_patch(Rectangle((0, y + 0.18), k, 0.64, facecolor=BLUE,
                               edgecolor="none"))
        ax.add_patch(Rectangle((k + (gap if k else 0), y + 0.18), n - k, 0.64,
                               facecolor=NEUTRAL, edgecolor="none"))
        ax.text(n + xmax * 0.017, y + 0.5, f"{k}/{n} solved ({k / n:.0%})",
                va="center", fontsize=8.5, color=INK2)
    ax.set_xlim(0, xmax * 1.35)
    ax.set_ylim(0, len(rows) + 1.1)
    ax.set_yticks([len(rows) - 1 - i + 0.5 for i in range(len(rows))])
    ax.set_yticklabels([r[0] for r in rows], fontsize=9.5)
    ax.xaxis.grid(True, color="#e1e0d9", linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(BASELINE)
    ax.tick_params(length=0)
    lx = 0.02
    for color, lbl in [(BLUE, "solved by ≥1 run"), (NEUTRAL, "never solved")]:
        ax.add_patch(Rectangle((ax.get_xlim()[1] * lx, len(rows) + 0.25),
                               ax.get_xlim()[1] * 0.02, 0.45,
                               facecolor=color, edgecolor="none"))
        ax.text(ax.get_xlim()[1] * (lx + 0.028), len(rows) + 0.47, lbl,
                va="center", fontsize=8.5, color=INK2)
        lx += 0.028 + 0.011 * len(lbl) + 0.03
    ax.set_xlabel("conjectures", fontsize=9.5, color=INK2)
    ax.set_title(title, fontsize=11, loc="left", color=INK, pad=10)
    fig.tight_layout()
    fig.savefig(OUT / fname, dpi=200, bbox_inches="tight")
    print("wrote", OUT / fname)

proposer_plot(
    outcomes("oeis-full-*"), 12,
    "OEIS OP-full — conjectures by proposer\n"
    "(solved = ≥1 of the 3 full runs, \\$50/sample)",
    "proposer_solve_rate_full.png")
proposer_plot(
    outcomes("oeis-lite-*"), 8,
    "OEIS OP-lite — conjectures by proposer\n"
    "(solved = ≥1 of the 9 lite runs, \\$200/sample)",
    "proposer_solve_rate_lite.png")
