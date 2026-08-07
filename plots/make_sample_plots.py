"""Sample-level plots from per-sample scores.json / info.json in logs.

Only runs with a top-level scores.json are included (a missing one means the
download is incomplete). Rerun after new runs finish downloading.
"""

import json
import re
from collections import Counter, defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams
from matplotlib.patches import Rectangle

from bench_names import (BENCH_FULL, BENCH_LITE, MODEL_LABELS, PROVIDER_RE,
                         PROVIDERS, SERIES)

LOGS = Path("logs")
OUT = Path("plots")
OUT.mkdir(exist_ok=True)

VARIANTS = ["base", "deep", "lit"]

# palette (dataviz reference, light mode)
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
BASELINE = "#c3c2b7"
SURFACE = "#ffffff"
NEUTRAL = "#f0efec"

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

# --- collect ---------------------------------------------------------------
def parse(eval_set):
    m = re.match(rf"oeis-(full|lite)-(\d+)usd-(?:(deep|lit)-)?({PROVIDER_RE})-", eval_set)
    task, budget, variant, provider = m.groups()
    return task, int(budget), variant or "base", provider

samples = defaultdict(dict)  # run key -> sample name -> record
runs = {}                    # run key -> (task, budget, variant, provider)
for top in sorted(LOGS.glob("*/*_plaintext/scores.json")):
    run_dir = top.parent
    key = parse(run_dir.parent.name)
    (scorer,) = json.loads(top.read_text())
    expected = scorer["scored_samples"] + scorer["unscored_samples"]
    sample_dirs = [sd for sd in sorted(run_dir.iterdir()) if sd.is_dir()]
    if len(sample_dirs) < expected:
        print(f"skipping incomplete download: {run_dir.parent.name} "
              f"({len(sample_dirs)}/{expected} samples)")
        continue
    runs[key] = key
    for sd in sample_dirs:
        sc = json.loads((sd / "scores.json").read_text())["proof_scorer"]
        info = json.loads((sd / "info.json").read_text())
        md = sc.get("metadata") or {}
        modes = set()
        report = md.get("safeverify_report") or []
        for entry in report if isinstance(report, list) else []:
            if not (isinstance(entry, list) and len(entry) == 2 and isinstance(entry[1], dict)):
                continue
            fm = entry[1].get("failureMode")
            if isinstance(fm, dict):
                modes.update(fm.keys())
            elif fm == "axioms":
                # split by the disallowed axiom(s) the submission relies on
                # (propext / Classical.choice / Quot.sound are permitted)
                std = {"propext", "Classical.choice", "Quot.sound"}
                used = set(((entry[1].get("solutionInfo") or {}).get("axioms")) or [])
                if "sorryAx" in used:
                    modes.add("axioms · sorryAx")
                if used - std - {"sorryAx"}:
                    modes.add("axioms · other")
            elif fm is not None:
                modes.add(str(fm))
        samples[key][sd.name] = dict(
            solved=sc["value"] == "C",
            stage=md.get("stage"),
            modes=sorted(modes),
            cost=sum(u.get("total_cost", 0) for u in (info.get("model_usage") or {}).values()),
            oeis_id=info.get("oeis_id") or sd.name,
        )

lite_keys = [("lite", 200, v, p) for p in PROVIDERS for v in VARIANTS if ("lite", 200, v, p) in samples]
full_keys = sorted((k for k in samples if k[0] == "full"),
                   key=lambda k: PROVIDERS.index(k[3]))

def run_label(key, multiline=False):
    task, budget, variant, provider = key
    sep = "\n" if multiline else " "
    return f"{MODEL_LABELS[provider]}{sep}{variant}" if task == "lite" else f"{MODEL_LABELS[provider]}{sep}(full)"

# === plot 1: solve matrix ===================================================
lite_by_model = {p: [k for k in lite_keys if k[3] == p] for p in PROVIDERS}
lite_provs = [p for p in PROVIDERS if lite_by_model[p]]
lite_samples = sorted(samples[lite_keys[0]])
# per sample, per model: how many of that model's agent configs solved it
nsolved = {s: {p: sum(samples[k][s]["solved"] for k in lite_by_model[p])
               for p in lite_provs} for s in lite_samples}
ever = [s for s in lite_samples if any(nsolved[s].values())]
never = [s for s in lite_samples if not any(nsolved[s].values())]
# sort by mean cost across all solving runs, cheapest first
def mean_solve_cost(s):
    costs = [samples[k][s]["cost"] for k in lite_keys if samples[k][s]["solved"]]
    return sum(costs) / len(costs)

ever.sort(key=lambda s: (mean_solve_cost(s), -sum(nsolved[s].values())))

ids = [samples[lite_keys[0]][s]["oeis_id"] for s in ever]
counts = Counter(ids)
seen = Counter()
labels = []
for s, i in zip(ever, ids):
    seen[i] += 1
    labels.append(i if counts[i] == 1 else f"{i} ({seen[i]})")

def mix(hex_color, frac, base=NEUTRAL):
    a = plt.matplotlib.colors.to_rgb(base)
    b = plt.matplotlib.colors.to_rgb(hex_color)
    return tuple(x + frac * (y - x) for x, y in zip(a, b))

# shade by the fraction of that model's configs that solved it (1/3 palest,
# all of them full strength); models with a single config always show full
def shade(n, p):
    frac = n / len(lite_by_model[p])
    return 0.42 + (frac - 1 / 3) * 0.87

ncol, nrow = len(lite_provs), len(ever)
fig, ax = plt.subplots(figsize=(5.2, 0.19 * nrow + 2.4))
def luminance(rgb):
    r, g, b = (ch / 12.92 if ch <= 0.04045 else ((ch + 0.055) / 1.055) ** 2.4
               for ch in rgb)
    return 0.2126 * r + 0.7152 * g + 0.0722 * b

for r, s in enumerate(ever):
    for c, p in enumerate(lite_provs):
        n = nsolved[s][p]
        color = NEUTRAL if n == 0 else mix(SERIES[p], shade(n, p))
        ax.add_patch(Rectangle((c + 0.06, nrow - 1 - r + 0.06), 0.88, 0.88,
                               facecolor=color, edgecolor="none"))
        if n > 0:
            solve_costs = [samples[k][s]["cost"] for k in lite_by_model[p]
                           if samples[k][s]["solved"]]
            mean_cost = sum(solve_costs) / len(solve_costs)
            cost_txt = f"${mean_cost:,.0f}" if mean_cost >= 0.95 else "<$1"
            ax.text(c + 0.82, nrow - 1 - r + 0.5, cost_txt,
                    ha="right", va="center", fontsize=6.5,
                    color=SURFACE if luminance(color) < 0.35 else INK)
ax.set_xlim(0, ncol)
ax.set_ylim(-1.6, nrow)
ax.set_aspect("auto")
ax.set_yticks([nrow - 1 - r + 0.5 for r in range(nrow)])
ax.set_yticklabels(labels, fontsize=6.8, color=INK2)
ax.set_xticks([c + 0.5 for c in range(ncol)])
ax.set_xticklabels([MODEL_LABELS[p].replace(" ", "\n", 1) for p in lite_provs],
                   fontsize=9)
ax.text(ncol / 2, -1.0,
        f"+ {len(never)} of {len(lite_samples)} conjectures solved by no run",
        ha="center", fontsize=9, color=MUTED)
for side in ("top", "right", "left", "bottom"):
    ax.spines[side].set_visible(False)
ax.tick_params(length=0)
ax.set_title(f"{BENCH_LITE} — which conjectures each model solved\n"
             f"({len(ever)} conjectures solved by ≥1 run; paler shade = solved\n"
             f"by fewer of that model's agent configs; cell label = mean cost\n"
             f"of the solving runs; rows sorted by mean solve cost; $200\n"
             f"budget/sample)",
             fontsize=10.5, pad=14)
fig.tight_layout()
fig.savefig(OUT / "solve_matrix.png", dpi=200, bbox_inches="tight")
print("wrote", OUT / "solve_matrix.png")

# === plot 2: solved fraction vs spend ======================================
fig, ax = plt.subplots(figsize=(8.2, 4.8))
# full runs individually; lite runs pooled over the 3 agent configs per model
curves = [([k], f"{BENCH_FULL} · {MODEL_LABELS[k[3]]}", "-") for k in full_keys]
curves += [(lite_by_model[p],
            f"{BENCH_LITE} · {MODEL_LABELS[p]}"
            + (f", {len(lite_by_model[p])}-agent avg" if len(lite_by_model[p]) > 1 else ""),
            (0, (4, 2)))
           for p in PROVIDERS if lite_by_model[p]]
for keys, label, style in curves:
    n = sum(len(samples[k]) for k in keys)
    n_txt = f"{len(keys)}×{len(samples[keys[0]])}" if len(keys) > 1 else f"{n}"
    costs = sorted(max(r["cost"], 0.01)
                   for k in keys for r in samples[k].values() if r["solved"])
    xs, ys = [0.4], [0.0]
    for i, c in enumerate(costs):
        xs += [c, c]
        ys += [ys[-1], (i + 1) / n]
    cap = keys[0][1]
    xs.append(cap)
    ys.append(ys[-1])
    color = SERIES[keys[0][3]]
    ax.plot(xs, ys, color=color, linestyle=style, linewidth=2,
            label=f"{label}  (n={n_txt}, ${cap} cap)")
    ax.plot([cap], [ys[-1]], marker="o", ms=5, color=color)
    ax.annotate(f"{ys[-1]:.0%}", (cap, ys[-1]), textcoords="offset points",
                xytext=(6, -3), fontsize=9, color=INK2)

ax.set_xscale("log")
ax.set_xticks([0.5, 1, 3, 10, 30, 50, 100, 200])
ax.set_xticklabels(["$0.50", "$1", "$3", "$10", "$30", "$50", "$100", "$200"], fontsize=9)
ax.set_xlim(0.4, 320)
ax.set_ylim(0, 0.45)
ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")
ax.yaxis.grid(True, color=GRID, linewidth=0.8)
ax.set_axisbelow(True)
for side in ("top", "right", "left"):
    ax.spines[side].set_visible(False)
ax.tick_params(length=0)
for cap in {keys[0][1] for keys, _, _ in curves}:
    ax.axvline(cap, color=GRID, linewidth=0.8, zorder=0)
ax.set_xlabel("cost spent on sample at time of solve (log scale)", fontsize=9.5, color=INK2)
ax.set_title("Fraction of samples solved with spend ≤ x")
ax.legend(frameon=False, fontsize=9, loc="upper left")
fig.tight_layout()
fig.savefig(OUT / "solve_cost_curves.png", dpi=200)
print("wrote", OUT / "solve_cost_curves.png")

# === plot 3: scoring metadata for incorrect samples ========================
# blocks of rows: lite pooled over the 3 agent configs per model, full runs as-is
lite_rows = [(lite_by_model[p], MODEL_LABELS[p]) for p in PROVIDERS if lite_by_model[p]]
full_rows = [([k], MODEL_LABELS[k[3]]) for k in full_keys]
blocks = [(f"{BENCH_LITE} · $200 cap · pooled over base/deep/lit agent runs", lite_rows),
          (f"{BENCH_FULL} · $50 cap", full_rows)]
row_defs = lite_rows + full_rows

def pooled_shares(keys, extract):
    """Counts pooled over the runs, as a share of the pooled denominator."""
    total = Counter()
    denom = 0
    for k in keys:
        counts, n = extract(samples[k])
        total.update(counts)
        denom += n
    return {c: v / denom for c, v in total.items()}

def stage_extract(recs):
    fails = [r for r in recs.values() if not r["solved"]]
    return Counter(r["stage"] for r in fails), len(fails)

def mode_extract(recs):
    sv = [r for r in recs.values() if not r["solved"] and r["stage"] == "safeverify"]
    return Counter(m for r in sv for m in (r["modes"] or ["(none recorded)"])), len(sv)

stage_counts = [pooled_shares(keys, stage_extract) for keys, _ in row_defs]
mode_counts = [pooled_shares(keys, mode_extract) for keys, _ in row_defs]

def col_order(rows):
    """Columns by total share, but variants of one key ("x · a", "x · b") stay adjacent."""
    totals = Counter()
    for d in rows:
        totals.update(d)
    groups = Counter()
    for c, v in totals.items():
        groups[c.split(" · ")[0]] += v
    return sorted(totals, key=lambda c: (-groups[c.split(" · ")[0]],
                                         c.split(" · ")[0], -totals[c]))

stages = col_order(stage_counts)
modes = col_order(mode_counts)

HEADER_H, ROW_H, GAP_H = 0.9, 1.0, 0.5

def count_matrix(ax, cols, rows, title, xlabel):
    nc = len(cols)
    maxv = max(v for d in rows for v in d.values())
    total_h = sum(HEADER_H + len(rws) * ROW_H for _, rws in blocks) \
        + GAP_H * (len(blocks) - 1)
    y = total_h
    ridx = 0
    yticks, ylabels = [], []
    for header, rws in blocks:
        y -= HEADER_H
        ax.text(0.05, y + 0.22, header, fontsize=8.5, color=INK,
                fontweight="bold", ha="left")
        for _, label in rws:
            y -= ROW_H
            d = rows[ridx]
            for c, col in enumerate(cols):
                v = d.get(col, 0)
                if v:
                    frac = (v / maxv) ** 0.4  # perceptual-ish ramp for skewed shares
                    color = plt.matplotlib.colors.to_rgb("#2a78d6")
                    bg = tuple(1 - frac * (1 - ch) for ch in color)
                    txt = f"{v:.0%}" if v >= 0.005 else "<1%"
                    ax.add_patch(Rectangle((c + 0.05, y + 0.05), 0.9, 0.9,
                                           facecolor=bg, edgecolor="none"))
                    ax.text(c + 0.5, y + 0.5, txt, ha="center", va="center",
                            fontsize=8, color=SURFACE if frac > 0.62 else INK)
                else:
                    ax.add_patch(Rectangle((c + 0.05, y + 0.05), 0.9, 0.9,
                                           facecolor=NEUTRAL, edgecolor="none"))
            yticks.append(y + 0.5)
            ylabels.append(label)
            ridx += 1
        y -= GAP_H
    ax.set_xlim(0, nc)
    ax.set_ylim(0, total_h)
    ax.set_yticks(yticks)
    ax.set_yticklabels(ylabels, fontsize=8.5)
    ax.set_xticks([c + 0.5 for c in range(nc)])
    ax.set_xticklabels(cols, fontsize=8, rotation=35, ha="right")
    for side in ("top", "right", "left", "bottom"):
        ax.spines[side].set_visible(False)
    ax.tick_params(length=0)
    ax.set_title(title, fontsize=10.5, loc="left", color=INK)
    ax.set_xlabel(xlabel, fontsize=9, color=INK2)

nrows_drawn = len(row_defs) + len(blocks) * HEADER_H + (len(blocks) - 1) * GAP_H
fig, (axa, axb) = plt.subplots(1, 2, figsize=(13.5, 0.42 * nrows_drawn + 2.6),
                               gridspec_kw={"width_ratios": [len(stages), len(modes) + 1.5]})
count_matrix(axa, stages, stage_counts,
             "Incorrect samples by scorer stage — % of run's incorrect samples",
             "stage (scores.json metadata)")
count_matrix(axb, modes, mode_counts,
             'Stage "safeverify" failures by failureMode key — % of safeverify failures\n'
             "(a sample can record several keys, so rows can exceed 100%)",
             "failureMode key (safeverify_report)")
fig.tight_layout(w_pad=3)
fig.savefig(OUT / "failure_stages.png", dpi=200, bbox_inches="tight")
print("wrote", OUT / "failure_stages.png")
