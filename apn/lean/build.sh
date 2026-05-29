#!/usr/bin/env bash
# Build the Lean sandbox images: a shared base, the agent workspace, and the
# (separate) scorer. Run from anywhere.
set -euo pipefail
cd "$(dirname "$0")"

docker build -t apn-lean-base -f Dockerfile.base .
docker build -t apn-agent -f Dockerfile.agent .
docker build -t apn-scorer -f Dockerfile.scorer .

echo "Built apn-lean-base, apn-agent, apn-scorer."
