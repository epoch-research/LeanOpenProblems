#!/bin/bash
# Wrapper for the Loogle CLI (built in the Dockerfile's loogle_build stage).
# Loogle ignores LEAN_PATH -- its --path flags REPLACE the compiled-in search
# path entirely -- so every olean root is listed explicitly: the FC project's
# packages (Mathlib and its deps; the same rev loogle was built against), the
# project's own build, loogle's modules, and the toolchain's stdlib (derived
# from the project's lean-toolchain: "leanprover/lean4:vX" installs under
# "leanprover--lean4---vX"). The prebuilt index skips index construction, not
# the ~30s Mathlib import -- batch queries via `loogle -i` reading stdin.
set -euo pipefail
ARGS=()
for p in /workspace/leanproject/.lake/packages/*/.lake/build/lib/lean; do
    ARGS+=(--path "$p")
done
ARGS+=(--path /workspace/leanproject/.lake/build/lib/lean)
ARGS+=(--path /opt/loogle/lib/lean)
tc_dir="$(sed 's|/|--|g; s|:|---|g' /workspace/leanproject/lean-toolchain)"
ARGS+=(--path "/root/.elan/toolchains/${tc_dir}/lib/lean")
exec /opt/loogle/bin/loogle "${ARGS[@]}" --read-index /opt/loogle/loogle.index "$@"
