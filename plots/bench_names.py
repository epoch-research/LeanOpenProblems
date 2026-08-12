"""Display names for the benchmark, in one place because the name may change.

Current names follow the paper draft: the full 492-conjecture set is plain
"OEIS Open"; the 100-conjecture subset is "OEIS Open Lite".
"""

BENCH = "OEIS Open"
BENCH_FULL = BENCH
BENCH_LITE = f"{BENCH} Lite"
ALPHAPROOF_NEXUS = "AlphaProof Nexus"

# Per-attempt budget annotations for figure titles. The dollar signs are
# backslash-escaped so matplotlib renders them literally instead of opening
# mathtext.
FULL_BUDGET = r"\$50 per attempt"
LITE_BUDGET = r"\$200 per attempt"
BENCH_FULL_BUDGETED = f"{BENCH_FULL} ({FULL_BUDGET})"
BENCH_LITE_BUDGETED = f"{BENCH_LITE} ({LITE_BUDGET})"

# Providers as tagged in eval-set names (oeis-<kind>-<budget>usd[-<variant>]-<provider>-<id>).
# Not every provider has every run kind; scripts must skip providers with no data.
MODEL_LABELS = {
    "ant": "Claude Opus 4.8",
    "oai": "GPT-5.5",
    "gdm": "Gemini 3.5 Flash",
    "fable": "Claude Fable 5",
    "sol": "GPT-5.6 Sol",
}
PROVIDERS = ["ant", "oai", "gdm", "fable", "sol"]
PROVIDER_RE = "|".join(PROVIDERS)
SERIES = {"ant": "#2a78d6", "oai": "#008300", "gdm": "#e87ba4", "fable": "#4a3aa7", "sol": "#eb6834"}
