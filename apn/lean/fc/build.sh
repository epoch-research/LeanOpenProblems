#!/usr/bin/env bash
# Build the Formal Conjectures (Lean v4.27) sandbox images: a shared base (Lean
# v4.27 + Mathlib + the FormalConjectures library), the agent workspace (warm
# PyPantograph v0.3.13), and the separate scorer (v4.27 SafeVerify).
#
# The build context is the parent directory (apn/lean) so the agent/scorer images
# can COPY the shared apn_lean.py / apn_safeverify.py helpers.
set -euo pipefail
cd "$(dirname "$0")/.."   # apn/lean

docker build -t apn-fc-base   -f fc/Dockerfile.base   fc
docker build -t apn-fc-agent  -f fc/Dockerfile.agent  .
docker build -t apn-fc-scorer -f fc/Dockerfile.scorer .

echo "Built apn-fc-base, apn-fc-agent, apn-fc-scorer."
