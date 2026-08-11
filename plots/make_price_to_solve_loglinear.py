"""Price-to-solve, Kaplan-Meier with log-linear trend only (no cure model).

Simplified variant of make_price_to_solve.py for readability: per model, the
KM estimate of P(price-to-solve <= x) and a log-linear trend (slope fit to KM
on [$10, $200], anchored at KM(200)) extrapolated past the data.
"""

import glob
import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams

from bench_names import BENCH, MODEL_LABELS, PROVIDERS, SERIES

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

# --- collect one (time, event) pair per conjecture per model ----------------
def read_run(run_glob):
    out = {}
    for run in glob.glob(str(LOGS / run_glob / "*_plaintext")):
        for sd in Path(run).iterdir():
            if not sd.is_dir():
                continue
            sc = json.loads((sd / "scores.json").read_text()).get("proof_scorer") or {}
            info = json.loads((sd / "info.json").read_text())
            cost = sum(u.get("total_cost", 0)
                       for u in (info.get("model_usage") or {}).values())
            out[sd.name] = (max(cost, 0.01), sc.get("value") == "C")
    return out

data = {}  # provider -> list of (time, event)
for p in PROVIDERS:
    full = read_run(f"oeis-full-*-{p}-*")
    lite = read_run(f"oeis-lite-*usd-{p}-*")  # base scaffold only (no deep/lit infix)
    if full:  # full run as backbone, lite run overriding its 100 conjectures
        data[p] = [lite[s] if s in lite else full[s] for s in full]
    elif lite:  # lite-only models (Fable 5, GPT-5.6 Sol): n=100, censored at $200
        data[p] = list(lite.values())

# --- Kaplan-Meier ------------------------------------------------------------
def kaplan_meier(obs):
    """Returns step curve (xs, ys) for P(solve <= x) = 1 - S(x)."""
    events = sorted({t for t, e in obs if e})
    xs, ys = [0.4], [0.0]
    surv = 1.0
    for t in events:
        n_risk = sum(1 for u, _ in obs if u >= t)
        d = sum(1 for u, e in obs if e and u == t)
        surv *= 1 - d / n_risk
        xs += [t, t]
        ys += [ys[-1], 1 - surv]
    return xs, ys

# --- plot ---------------------------------------------------------------------
fig, ax = plt.subplots(figsize=(8.6, 5.2))
X_MAX = 10_000
notes = []
for p in data:
    obs = data[p]
    xs, ys = kaplan_meier(obs)
    km200 = ys[-1]
    ax.plot(xs + [200], ys + [ys[-1]], color=SERIES[p], linewidth=2,
            label=f"{MODEL_LABELS[p]}  (KM, n={len(obs)})")

    # log-linear trend (dotted): slope of KM vs log10(x) on [$10, $200],
    # anchored at KM(200)
    def km_at(x):
        f = 0.0
        for xi, yi in zip(xs, ys):
            if xi <= x:
                f = yi
        return f
    pts = [(math.log10(10) + i * (math.log10(200) - math.log10(10)) / 60)
           for i in range(61)]
    vals = [km_at(10 ** lx) for lx in pts]
    mlx = sum(pts) / len(pts)
    mv = sum(vals) / len(vals)
    slope = (sum((lx - mlx) * (v - mv) for lx, v in zip(pts, vals))
             / sum((lx - mlx) ** 2 for lx in pts))
    grid = [10 ** (math.log10(0.4) + i * (math.log10(X_MAX) - math.log10(0.4)) / 400)
            for i in range(401)]
    trend_y = [min(max(km200 + slope * math.log10(x / 200), 0), 1) for x in grid]
    ax.plot(grid, trend_y, color=SERIES[p], linewidth=1.4,
            linestyle=(0, (1, 1.6)), alpha=0.85)

    p1k_trend = km200 + slope * math.log10(1000 / 200)
    notes.append(f"{MODEL_LABELS[p]}:  slope {slope:+.0%}/decade, "
                 f"P(solve ≤ \\$1k) {p1k_trend:.0%}")
    print(f"{p}: KM(200)={km200:.3f} slope={slope*100:.1f}pts/decade "
          f"P(<=1k) trend={p1k_trend:.3f}")

ax.set_xscale("log")
ax.set_xticks([1, 3, 10, 50, 200, 1000, 10_000])
ax.set_xticklabels(["$1", "$3", "$10", "$50", "$200", "$1k", "$10k"], fontsize=9)
ax.set_xlim(0.4, X_MAX)
ax.set_ylim(0, 0.75)
ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")
ax.yaxis.grid(True, color=GRID, linewidth=0.8)
ax.set_axisbelow(True)
for side in ("top", "right", "left"):
    ax.spines[side].set_visible(False)
ax.tick_params(length=0)
for cap, lbl in [(50, "$50 cap\n(392 obs)"), (200, "$200 cap\n(100 obs)")]:
    ax.axvline(cap, color=GRID, linewidth=0.8, zorder=0)
    ax.text(cap, 0.745, lbl, ha="center", va="top", fontsize=7.5, color=MUTED)
ax.text(0.985, 0.03, "\n".join(notes), transform=ax.transAxes, ha="right",
        va="bottom", fontsize=8.5, color=INK2, linespacing=1.6)
ax.set_xlabel("hypothetical price to solve (log scale)", fontsize=9.5, color=INK2)
ax.set_title(f"{BENCH} — price-to-solve, Kaplan–Meier (solid, one obs per\n"
             "conjecture, censored at \\$50 or \\$200) with log-linear trend\n"
             "(dotted, slope fit to KM on [\\$10, \\$200])",
             fontsize=10.5)
from matplotlib.lines import Line2D
handles, labels_ = ax.get_legend_handles_labels()
handles += [Line2D([], [], color=INK2, linewidth=1.4, linestyle=(0, (1, 1.6)))]
labels_ += ["log-linear trend"]
ax.legend(handles, labels_, frameon=False, fontsize=9, loc="upper left")
fig.tight_layout()
fig.savefig(OUT / "price_to_solve_loglinear.png", dpi=200)
print("wrote", OUT / "price_to_solve_loglinear.png")
