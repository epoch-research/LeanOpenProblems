#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"

usage() {
  echo "Usage: $0 <eval-set-config> [hawk eval-set args...]" >&2
}

if [ $# -lt 1 ]; then
  usage
  exit 1
fi

eval_set_config_path="$1"
shift

if [ ! -f "$eval_set_config_path" ]; then
  echo "Error: eval-set config not found: $eval_set_config_path" >&2
  exit 1
fi

if [ -f "$repo_root/.env" ]; then
  set -a
  source "$repo_root/.env"
  set +a
fi

if [ -z "${LEAN_OPEN_PROBLEMS_IMAGE_NAME:-}" ]; then
  echo "Error: LEAN_OPEN_PROBLEMS_IMAGE_NAME must be set" >&2
  exit 1
fi

hawk_cmd="hawk"
if [ -x "$repo_root/.venv/bin/hawk" ]; then
  hawk_cmd="$repo_root/.venv/bin/hawk"
fi

secret_args=(--secret LEAN_OPEN_PROBLEMS_IMAGE_NAME)
for secret_name in \
  ANTHROPIC_API_KEY \
  OPENAI_API_KEY \
  GOOGLE_API_KEY; do
  if [ -n "${!secret_name:-}" ]; then
    secret_args+=(--secret "$secret_name")
  fi
done

hawk_output_file="$(mktemp)"
cleanup() {
  rm -f "$hawk_output_file"
}
trap cleanup EXIT

if "$hawk_cmd" eval-set "$eval_set_config_path" "${secret_args[@]}" "$@" \
  >"$hawk_output_file" 2>&1; then
  cat "$hawk_output_file"
else
  status=$?
  cat "$hawk_output_file" >&2
  exit "$status"
fi

eval_set_id="$(sed -nE 's/^Eval set ID: ([^[:space:]]+).*$/\1/p' "$hawk_output_file" | tail -n 1)"

if [ -z "$eval_set_id" ]; then
  echo "Warning: hawk eval-set succeeded, but no eval set ID was found; not saving config history." >&2
  exit 0
fi

history_dir="$repo_root/configs/history"
history_timestamp="$(date -u +%Y-%m-%dT%H-%M-%S)"
history_path="$history_dir/${history_timestamp}_${eval_set_id}.yaml"

mkdir -p "$history_dir"
cp "$eval_set_config_path" "$history_path"
tmp_history_path="$(mktemp)"
awk '!/^[[:space:]]*eval_set_id:[[:space:]]*/' "$history_path" >"$tmp_history_path"
printf '\neval_set_id: %s\n' "$eval_set_id" >>"$tmp_history_path"
mv "$tmp_history_path" "$history_path"
echo "Saved eval set config to $history_path"
