#!/usr/bin/env bash
# Build the Lean sandbox images: a shared base (Lean v4.27 + Mathlib + the
# FormalConjectures library), the agent workspace (warm PyPantograph v0.3.13 +
# python/sympy/numpy), and the separate scorer (v4.27 SafeVerify).
set -euo pipefail
cd "$(dirname "$0")"

docker build -t apn-lean-base -f Dockerfile.base .
docker build -t apn-agent     -f Dockerfile.agent .
docker build -t apn-scorer    -f Dockerfile.scorer .

echo "Built apn-lean-base, apn-agent, apn-scorer."
