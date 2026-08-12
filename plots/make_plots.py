"""Bar plots of top-level scores.json accuracy across OEIS eval runs.

Each accuracy bar is split into proofs (solid) and disproofs (pale tint of the
same hue). A solve counts as a disproof when the accepted Submission/Spec.lean
contains a `.disproof` theorem (the harness's mechanism for settling a
conjecture by refutation)."""

import json
import re
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib import rcParams

from bench_names import (ALPHAPROOF_NEXUS, BENCH_FULL, BENCH_LITE,
                         BENCH_FULL_BUDGETED, BENCH_LITE_BUDGETED,
                         MODEL_LABELS, PROVIDER_RE, PROVIDERS)

LOGS = Path("logs")
OUT = Path("plots")
OUT.mkdir(exist_ok=True)

# --- collect data ---------------------------------------------------------
runs = {}  # eval_set_name -> (accuracy, stderr, n, frac_proved, frac_disproved)
for scores_path in LOGS.glob("*/*/scores.json"):
    eval_set = scores_path.parent.parent.name
    # logs/ may also hold runs of other benchmarks (whose per-sample
    # scores.json files match this glob); only oeis-* eval sets belong here
    if not eval_set.startswith("oeis-"):
        continue
    data = json.loads(scores_path.read_text())
    (scorer,) = data
    m = scorer["metrics"]
    acc, err, n = m["accuracy"]["value"], m["stderr"]["value"], scorer["scored_samples"]
    proved = disproved = n_dirs = 0
    for sd in scores_path.parent.iterdir():
        if not sd.is_dir():
            continue
        n_dirs += 1
        sc = json.loads((sd / "scores.json").read_text()).get("proof_scorer")
        if sc is None:
            continue
        if sc["value"] == "C":
            spec = sd / "Submission" / "Spec.lean"
            is_dis = spec.exists() and ".disproof" in spec.read_text(errors="replace")
            disproved += is_dis
            proved += not is_dis
    if abs((proved + disproved) / n - acc) > 1e-9:
        raise RuntimeError(
            f"{eval_set}: per-sample solves ({proved}+{disproved})/{n} disagree "
            f"with scores.json accuracy {acc}; incomplete download?"
        )
    if n_dirs > n:  # unscored (errored) samples count as failures
        acc = (proved + disproved) / n_dirs
        err = (acc * (1 - acc) / (n_dirs - 1)) ** 0.5
        n = n_dirs
    runs[eval_set] = (acc, err, n, proved / n, disproved / n)

VARIANT_LABELS = {"base": "base agent", "deep": "DeepAgent", "lit": "literature"}

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

def style_axis(ax, ymax=0.62):
    ax.set_ylim(0, ymax)
    ax.yaxis.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(BASELINE)
    ax.tick_params(length=0, labelsize=8)
    ax.yaxis.set_major_formatter(lambda v, _: f"{v:.0%}")

# Drawn at the paper's true print size (\textwidth = 6.5in), so font sizes
# below are real point sizes on paper -- don't render large and shrink.
fig, (ax1, ax2) = plt.subplots(
    1, 2, figsize=(6.5, 3.0), gridspec_kw={"width_ratios": [5, 4]}
)

# pale tint of a series color for the disproof segment (same hue, lighter)
def tint(hex_color, frac=0.45):
    a = plt.matplotlib.colors.to_rgb(SURFACE)
    b = plt.matplotlib.colors.to_rgb(hex_color)
    return tuple(x + frac * (y - x) for x, y in zip(a, b))

def stacked_bar(ax, x, proved, disproved, color, width, label=None):
    """One solve-rate bar: solid proved segment, pale disproved on top.
    Identical edge stroke on both segments so they render the same width."""
    ax.bar(x, proved, width=width, color=color, label=label,
           edgecolor=SURFACE, linewidth=0.8)
    ax.bar(x, disproved, width=width, bottom=proved, color=tint(color),
           edgecolor=SURFACE, linewidth=0.8)

def outcome_legend(ax, colors, title=None, **kwargs):
    """proved/disproved legend whose chips show every hue present in the panel,
    so the solid/pale split visibly applies to all bars, not just one color.
    Pass a title only when another legend is present to disambiguate."""
    from matplotlib.legend_handler import HandlerTuple
    from matplotlib.patches import Patch
    solid = tuple(Patch(color=c) for c in colors)
    pale = tuple(Patch(color=tint(c)) for c in colors)
    return ax.legend(handles=[solid, pale], labels=["proved", "disproved"],
                     handler_map={tuple: HandlerTuple(ndivide=None, pad=0)},
                     title=title, frameon=False, fontsize=8,
                     title_fontsize=8, handlelength=1.2, handletextpad=0.5,
                     labelspacing=0.3, **kwargs)

# --- panel 1: lite, base agent only (variant comparison is its own figure) --
FULL_COLOR = "#2a78d6"
lite_provs = [p for p in PROVIDERS if ("lite", "base", p) in table]
for x, prov in enumerate(lite_provs):
    acc, err, _, proved, disproved = table[("lite", "base", prov)]
    stacked_bar(ax1, x, proved, disproved, FULL_COLOR, 0.5)
    ax1.errorbar([x], [acc], yerr=[err], fmt="none", ecolor=INK2,
                 elinewidth=0.8, capsize=2.5)
    ax1.text(x, acc + err + 0.012, f"{acc:.0%}", ha="center", va="bottom",
             fontsize=7, color=INK2)
    # segment labels: white on the solid fill, ink on the pale one
    if proved > 0.04:
        ax1.text(x, proved / 2, f"{proved:.0%}", ha="center", va="center",
                 fontsize=7, color=SURFACE)
    if disproved > 0.04:
        ax1.text(x, proved + disproved / 2, f"{disproved:.0%}", ha="center",
                 va="center", fontsize=7, color=INK)

ax1.set_xticks(range(len(lite_provs)))
ax1.set_xticklabels([MODEL_LABELS[p].replace(" ", "\n", 1) for p in lite_provs],
                    fontsize=8)
style_axis(ax1, ymax=0.56)
ax1.set_title(BENCH_LITE_BUDGETED, fontsize=9.5, loc="left", color=INK)
outcome_legend(ax1, [FULL_COLOR], loc="upper left", ncols=2)

# --- panel 2: full, base scaffold ------------------------------------------
full_provs = [p for p in PROVIDERS if ("full", "base", p) in table]
labels = [MODEL_LABELS[p].replace(" ", "\n", 1) for p in full_provs]
for x, prov in enumerate(full_provs):
    acc, err, _, proved, disproved = table[("full", "base", prov)]
    stacked_bar(ax2, x, proved, disproved, FULL_COLOR, 0.5)
    ax2.errorbar([x], [acc], yerr=[err], fmt="none", ecolor=INK2,
                 elinewidth=0.8, capsize=2.5)
    ax2.text(x, acc + 0.025, f"{acc:.0%}", ha="center", va="bottom",
             fontsize=7, color=INK2)
    # segment labels: white on the solid fill, ink on the pale one
    if proved > 0.04:
        ax2.text(x, proved / 2, f"{proved:.0%}", ha="center", va="center",
                 fontsize=6.5, color=SURFACE)
    if disproved > 0.04:
        ax2.text(x, proved + disproved / 2, f"{disproved:.0%}", ha="center",
                 va="center", fontsize=6.5, color=INK)

# External reported baseline: AlphaProof Nexus, 44/492 solved (all proofs; no
# disproof mechanism reported, so the bar is not split)
apn_x = len(full_provs)
apn_acc = 44 / 492
apn_err = (apn_acc * (1 - apn_acc) / 492) ** 0.5
ax2.bar(apn_x, apn_acc, width=0.5, color=MUTED)
ax2.errorbar([apn_x], [apn_acc], yerr=[apn_err], fmt="none", ecolor=INK2,
             elinewidth=0.8, capsize=2.5)
ax2.text(apn_x, apn_acc + 0.025, f"{apn_acc:.0%}", ha="center", va="bottom",
         fontsize=7, color=INK2)
labels.append(f"{ALPHAPROOF_NEXUS.replace(' ', chr(10))}\n(reported)")

outcome_legend(ax2, [FULL_COLOR], loc="upper center", ncols=2)
ax2.set_xticks(list(range(len(labels))))
ax2.set_xticklabels(labels, fontsize=7)
style_axis(ax2, ymax=0.56)
ax2.set_title(BENCH_FULL_BUDGETED, fontsize=9.5, loc="left", color=INK)
fig.tight_layout(w_pad=1.5)
fig.savefig(OUT / "accuracy.png", dpi=300)
print("wrote", OUT / "accuracy.png")

# --- appendix figure: lite, model x agent variant ---------------------------
# only models actually run with the non-base variants; lone base bars (Fable,
# Sol) say nothing about variants
figv, axv = plt.subplots(figsize=(6.5, 3.0))
variants = ["base", "deep", "lit"]
var_provs = [p for p in lite_provs
             if any(("lite", v, p) in table for v in variants[1:])]
bar_w = 0.26
for j, variant in enumerate(variants):
    first = True
    for i, prov in enumerate(var_provs):
        if ("lite", variant, prov) not in table:
            continue
        acc, err, _, proved, disproved = table[("lite", variant, prov)]
        x = i + (j - 1) * (bar_w + 0.02)
        stacked_bar(axv, x, proved, disproved, SERIES[variant], bar_w,
                    label=VARIANT_LABELS[variant] if first else None)
        first = False
        axv.errorbar([x], [acc], yerr=[err], fmt="none", ecolor=INK2,
                     elinewidth=0.8, capsize=2.5)
        axv.text(x, acc + err + 0.012, f"{acc:.0%}", ha="center", va="bottom",
                 fontsize=7, color=INK2)
        # segment labels: white on the solid fill, ink on the pale one
        if proved > 0.04:
            axv.text(x, proved / 2, f"{proved:.0%}", ha="center", va="center",
                     fontsize=7, color=SURFACE)
        if disproved > 0.04:
            axv.text(x, proved + disproved / 2, f"{disproved:.0%}", ha="center",
                     va="center", fontsize=7, color=INK)

axv.set_xticks(range(len(var_provs)))
axv.set_xticklabels([MODEL_LABELS[p] for p in var_provs], fontsize=8.5)
style_axis(axv, ymax=0.68)
axv.set_title(f"{BENCH_LITE}, by agent variant", fontsize=9.5, loc="left",
              color=INK)
variant_legend = axv.legend(
    title="agent variant", frameon=False, fontsize=8, title_fontsize=8,
    loc="upper right", bbox_to_anchor=(1, 1), ncols=len(variants),
    handlelength=1.2, handletextpad=0.5, columnspacing=1.0)
axv.add_artist(variant_legend)
outcome_legend(axv, [SERIES[v] for v in variants], title="outcome",
               loc="upper left")
figv.tight_layout()
figv.savefig(OUT / "accuracy_variants.png", dpi=300)
print("wrote", OUT / "accuracy_variants.png")

# --- standalone full-set plot (social media, not the paper) -----------------
fig2, ax = plt.subplots(figsize=(6.2, 4.6))
for x, prov in enumerate(full_provs):
    acc, err, _, proved, disproved = table[("full", "base", prov)]
    stacked_bar(ax, x, proved, disproved, FULL_COLOR, 0.55)
    ax.errorbar([x], [acc], yerr=[err], fmt="none", ecolor=INK2,
                elinewidth=1, capsize=3)
    ax.text(x, acc + 0.018, f"{acc:.0%}", ha="center", va="bottom",
            fontsize=12, color=INK)
    if proved > 0.04:
        ax.text(x, proved / 2, f"{proved:.0%}", ha="center", va="center",
                fontsize=10, color=SURFACE)
    if disproved > 0.04:
        ax.text(x, proved + disproved / 2, f"{disproved:.0%}", ha="center",
                va="center", fontsize=10, color=INK)
ax.set_xticks(range(len(full_provs)))
ax.set_xticklabels([MODEL_LABELS[p] for p in full_provs], fontsize=12)
style_axis(ax, ymax=0.4)
ax.set_title(f"{BENCH_FULL}: share of 492 open conjectures resolved\n"
             "(\\$50 budget per conjecture)", fontsize=12, loc="left", color=INK)
outcome_legend(ax, [FULL_COLOR], loc="upper right")
fig2.tight_layout()
fig2.savefig(OUT / "accuracy_full_simple.png", dpi=200)
print("wrote", OUT / "accuracy_full_simple.png")
