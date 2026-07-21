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

LOGS = Path("logs")
OUT = Path("plots")
OUT.mkdir(exist_ok=True)

MODEL_LABELS = {"ant": "Claude Opus 4.8", "oai": "GPT-5.5", "gdm": "Gemini 3.5 Flash"}
PROVIDERS = ["ant", "oai", "gdm"]
VARIANTS = ["base", "deep", "lit"]

# palette (dataviz reference, light mode)
SERIES = {"ant": "#2a78d6", "oai": "#008300", "gdm": "#e87ba4"}
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
BASELINE = "#c3c2b7"
SURFACE = "#fcfcfb"
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
    m = re.match(r"oeis-(full|lite)-(\d+)usd-(?:(deep|lit)-)?(ant|gdm|oai)-", eval_set)
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
full_keys = [k for k in samples if k[0] == "full"]

def run_label(key, multiline=False):
    task, budget, variant, provider = key
    sep = "\n" if multiline else " "
    return f"{MODEL_LABELS[provider]}{sep}{variant}" if task == "lite" else f"{MODEL_LABELS[provider]}{sep}(full)"

# === plot 1: solve matrix ===================================================
lite_by_model = {p: [k for k in lite_keys if k[3] == p] for p in PROVIDERS}
lite_samples = sorted(samples[lite_keys[0]])
# per sample, per model: how many of the 3 agent configs solved it
nsolved = {s: {p: sum(samples[k][s]["solved"] for k in lite_by_model[p])
               for p in PROVIDERS} for s in lite_samples}
ever = [s for s in lite_samples if any(nsolved[s].values())]
never = [s for s in lite_samples if not any(nsolved[s].values())]
ever.sort(key=lambda s: (-sum(nsolved[s].values()),
                         tuple(-nsolved[s][p] for p in PROVIDERS)))

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

SHADE = {0: None, 1: 0.42, 2: 0.68, 3: 1.0}
ncol, nrow = len(PROVIDERS), len(ever)
fig, ax = plt.subplots(figsize=(5.2, 0.19 * nrow + 2.4))
for r, s in enumerate(ever):
    for c, p in enumerate(PROVIDERS):
        n = nsolved[s][p]
        color = NEUTRAL if n == 0 else mix(SERIES[p], SHADE[n])
        ax.add_patch(Rectangle((c + 0.06, nrow - 1 - r + 0.06), 0.88, 0.88,
                               facecolor=color, edgecolor="none"))
        if 0 < n < 3:
            ax.text(c + 0.5, nrow - 1 - r + 0.5, f"{n}/3", ha="center",
                    va="center", fontsize=6.5, color=INK)
ax.set_xlim(0, ncol)
ax.set_ylim(-1.6, nrow)
ax.set_aspect("auto")
ax.set_yticks([nrow - 1 - r + 0.5 for r in range(nrow)])
ax.set_yticklabels(labels, fontsize=6.8, color=INK2)
ax.set_xticks([c + 0.5 for c in range(ncol)])
ax.set_xticklabels([MODEL_LABELS[p].replace(" ", "\n", 1) for p in PROVIDERS],
                   fontsize=9)
ax.text(ncol / 2, -1.0,
        f"+ {len(never)} of {len(lite_samples)} conjectures solved by no run",
        ha="center", fontsize=9, color=MUTED)
for side in ("top", "right", "left", "bottom"):
    ax.spines[side].set_visible(False)
ax.tick_params(length=0)
ax.set_title(f"OEIS-lite — which conjectures each model solved\n"
             f"({len(ever)} conjectures solved by ≥1 run; cell = how many of the\n"
             f"3 agent configs (base/deep/lit) solved it; $200 budget/sample)",
             fontsize=10.5, loc="left", color=INK, pad=14)
fig.tight_layout()
fig.savefig(OUT / "solve_matrix.png", dpi=200, bbox_inches="tight")
print("wrote", OUT / "solve_matrix.png")

# === plot 2: solved fraction vs spend ======================================
fig, ax = plt.subplots(figsize=(8.2, 4.8))
# full runs individually; lite runs pooled over the 3 agent configs per model
curves = [([k], f"{MODEL_LABELS[k[3]]} (full)", "-") for k in full_keys]
curves += [(lite_by_model[p], f"{MODEL_LABELS[p]} lite, 3-agent avg", (0, (4, 2)))
           for p in PROVIDERS if lite_by_model[p]]
for keys, label, style in curves:
    n = sum(len(samples[k]) for k in keys)
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
            label=f"{label}  (n={n}, ${cap} cap)")
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
ax.set_title("Fraction of samples solved with spend ≤ x\n"
             "(each curve ends at its run's per-sample budget cap)",
             fontsize=11, loc="left", color=INK)
ax.legend(frameon=False, fontsize=9, loc="upper left")
fig.tight_layout()
fig.savefig(OUT / "solve_cost_curves.png", dpi=200)
print("wrote", OUT / "solve_cost_curves.png")

# === plot 3: scoring metadata for incorrect samples ========================
# rows: lite averaged over the 3 agent configs per model, full runs as-is
row_defs = [(lite_by_model[p], f"{MODEL_LABELS[p]} lite (3-agent avg)")
            for p in PROVIDERS if lite_by_model[p]]
row_defs += [([k], f"{MODEL_LABELS[k[3]]} (full)") for k in full_keys]

def mean_counts(keys, extract):
    total = Counter()
    for k in keys:
        total.update(extract(samples[k]))
    return {c: v / len(keys) for c, v in total.items()}

stage_counts = [mean_counts(keys, lambda recs: Counter(
                    r["stage"] for r in recs.values() if not r["solved"]))
                for keys, _ in row_defs]
mode_counts = [mean_counts(keys, lambda recs: Counter(
                    m for r in recs.values()
                    if not r["solved"] and r["stage"] == "safeverify"
                    for m in (r["modes"] or ["(none recorded)"])))
               for keys, _ in row_defs]

def col_order(rows):
    totals = Counter()
    for d in rows:
        totals.update(d)
    return [c for c, _ in totals.most_common()]

stages = col_order(stage_counts)
modes = col_order(mode_counts)

def count_matrix(ax, cols, rows, title, xlabel):
    nr, nc = len(rows), len(cols)
    maxv = max(v for d in rows for v in d.values())
    for r, d in enumerate(rows):
        for c, col in enumerate(cols):
            v = d.get(col, 0)
            if v:
                frac = (v / maxv) ** 0.4  # perceptual-ish ramp for skewed counts
                color = plt.matplotlib.colors.to_rgb("#2a78d6")
                bg = tuple(1 - frac * (1 - ch) for ch in color)
                txt = f"{v:.0f}" if abs(v - round(v)) < 1e-9 else f"{v:.1f}"
                ax.add_patch(Rectangle((c + 0.05, nr - 1 - r + 0.05), 0.9, 0.9,
                                       facecolor=bg, edgecolor="none"))
                ax.text(c + 0.5, nr - 1 - r + 0.5, txt, ha="center", va="center",
                        fontsize=8, color=SURFACE if frac > 0.62 else INK)
            else:
                ax.add_patch(Rectangle((c + 0.05, nr - 1 - r + 0.05), 0.9, 0.9,
                                       facecolor=NEUTRAL, edgecolor="none"))
    ax.set_xlim(0, nc)
    ax.set_ylim(0, nr)
    ax.set_yticks([nr - 1 - r + 0.5 for r in range(nr)])
    ax.set_yticklabels([label for _, label in row_defs], fontsize=8.5)
    ax.set_xticks([c + 0.5 for c in range(nc)])
    ax.set_xticklabels(cols, fontsize=8, rotation=35, ha="right")
    for side in ("top", "right", "left", "bottom"):
        ax.spines[side].set_visible(False)
    ax.tick_params(length=0)
    ax.set_title(title, fontsize=10.5, loc="left", color=INK)
    ax.set_xlabel(xlabel, fontsize=9, color=INK2)

fig, (axa, axb) = plt.subplots(1, 2, figsize=(13.5, 0.42 * len(row_defs) + 2.6),
                               gridspec_kw={"width_ratios": [len(stages), len(modes) + 1.5]})
count_matrix(axa, stages, stage_counts,
             "Incorrect samples by scorer stage\n(lite rows: mean count over base/deep/lit runs)",
             "stage (scores.json metadata)")
count_matrix(axb, modes, mode_counts,
             'Stage "safeverify" failures by failureMode key\n'
             "(a sample can record several; each counted once)",
             "failureMode key (safeverify_report)")
fig.tight_layout(w_pad=3)
fig.savefig(OUT / "failure_stages.png", dpi=200, bbox_inches="tight")
print("wrote", OUT / "failure_stages.png")
