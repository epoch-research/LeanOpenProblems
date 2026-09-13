#!/usr/bin/env bash
# Canonical proof-summarization run for one downloaded eval set.
#
# Generates the concise summary and full natural-language proof for every
# accepted sample of <run> (a directory under logs/ holding the *_plaintext
# extraction), with the settings used for the published results:
#
#   model        openai/gpt-5.6-sol
#   token limit  5,000,000 per sample (a safety net, not a target: the
#                summarizer explores the proof and Mathlib freely; at 500k
#                roughly one sample in 300 ran out before submitting)
#   metadata     the results repository's metadata/oeis (sequence and
#                conjecture descriptions the prompts quote)
#   sandbox      the locally built agent image, 8 concurrent sandboxes
#
# Usage:
#   scripts/summarize/summarize_proofs.sh <run> [inspect eval args...]
#
# Extra arguments go to `inspect eval`, e.g. `--sample-id <id>__full_proof`
# for a patch-up of one sample (pass the resulting .eval to collect.py after
# the main one; later logs win).
#
# Then materialize metadata.json beside each accepted proof:
#   python scripts/summarize/collect.py proofs --run-dir logs/<run> \
#       --subset lite --eval logs/summarize/<proofs>.eval
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"

if [ $# -lt 1 ]; then
  echo "Usage: $0 <run> [inspect eval args...]" >&2
  exit 1
fi
run="$1"
shift

: "${SUMMARIZE_MODEL:=openai/gpt-5.6-sol}"
: "${SUMMARIZE_SUBSET:=lite}"
: "${SUMMARIZE_TOKEN_LIMIT:=5000000}"
: "${RESULTS_REPO:=/Users/t/repos/github.com/epoch-research/LeanOpenProblems-results}"
: "${SUMMARIZE_METADATA_DIR:=$RESULTS_REPO/metadata/oeis}"

if [ ! -d "$repo_root/logs/$run" ]; then
  echo "Error: run directory not found: $repo_root/logs/$run" >&2
  exit 1
fi
if [ ! -f "$SUMMARIZE_METADATA_DIR/conjectures.json" ]; then
  echo "Error: no conjectures.json in $SUMMARIZE_METADATA_DIR" >&2
  exit 1
fi

# The task's compose file names the image after apn.__version__; build it
# locally under the default repository rather than the ECR name in .env.
export LEAN_OPEN_PROBLEMS_IMAGE_NAME=leanopenproblems

inspect_cmd="inspect"
if [ -x "$repo_root/.venv/bin/inspect" ]; then
  inspect_cmd="$repo_root/.venv/bin/inspect"
fi

cd "$repo_root"
exec "$inspect_cmd" eval scripts/summarize/task.py@summarize_proofs \
  -T run_dir="logs/$run" \
  -T subset="$SUMMARIZE_SUBSET" \
  -T metadata_dir="$SUMMARIZE_METADATA_DIR" \
  -T token_limit="$SUMMARIZE_TOKEN_LIMIT" \
  --model "$SUMMARIZE_MODEL" \
  --log-dir logs/summarize \
  --max-sandboxes 8 \
  --max-connections 8 \
  "$@"
