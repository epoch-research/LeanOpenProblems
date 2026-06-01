#!/usr/bin/env bash
# Build the Lean sandbox images: a shared base (Lean v4.27 + Mathlib + the
# FormalConjectures library), the agent workspace (warm PyPantograph v0.3.13 +
# python/sympy/numpy), and the separate scorer (v4.27 SafeVerify).
set -euo pipefail
cd "$(dirname "$0")"

image_name="${LEAN_OPEN_PROBLEMS_IMAGE_NAME:-leanopenproblems}"
image_version="$(sed -nE 's/^__version__ = "([^"]+)"/\1/p' ../__init__.py)"
if [ -z "$image_version" ]; then
  echo "Could not read apn.__version__" >&2
  exit 1
fi
git_hash="$(git -C ../.. rev-parse HEAD 2>/dev/null || printf 'local')"

image_tag() {
  printf 'LeanOpenProblems_%s_%s_%s' "$1" "$image_version" "$git_hash"
}

base_tag="$(image_tag base)"
agent_tag="$(image_tag agent)"
scorer_tag="$(image_tag scorer)"

docker build \
  -t apn-lean-base \
  -t "${image_name}:${base_tag}" \
  -f Dockerfile.base \
  .
docker build \
  -t apn-agent \
  -t "${image_name}:${agent_tag}" \
  -f Dockerfile.agent \
  .
docker build \
  -t apn-scorer \
  -t "${image_name}:${scorer_tag}" \
  -f Dockerfile.scorer \
  .

echo "Built apn-lean-base, apn-agent, apn-scorer."
echo "Tagged ${image_name}:${base_tag}"
echo "Tagged ${image_name}:${agent_tag}"
echo "Tagged ${image_name}:${scorer_tag}"
