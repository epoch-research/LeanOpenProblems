# Lean 4 + Mathlib + Pantograph sandbox image for AlphaProof Nexus.
#
# Pins Lean v4.29.1 / Mathlib v4.29.1 to match the toolchain that PyPantograph's
# bundled `pantograph-repl` is compiled against. Building Mathlib from source is
# avoided by fetching the community `.olean` cache (`lake exe cache get`).
FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=/root/.elan/bin:$PATH \
    ELAN_HOME=/root/.elan \
    APN_LEAN_PROJECT=/workspace/leanproject

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential libgmp-dev \
        python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*

ARG LEAN_VERSION=v4.29.1
RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh -o elan-init.sh \
    && sh elan-init.sh -y --default-toolchain "leanprover/lean4:${LEAN_VERSION}" \
    && rm elan-init.sh

# Resolve the Mathlib dependency and pull its prebuilt olean cache. This is the
# expensive layer; it is kept separate so edits to the helper script below do
# not invalidate it.
WORKDIR /workspace/leanproject
COPY lean-toolchain lakefile.toml ApnProject.lean ./
RUN lake update \
    && lake exe cache get \
    && lake build

# PyPantograph ships a prebuilt linux repl matching the toolchain above.
RUN pip3 install --break-system-packages --no-cache-dir pantograph

COPY apn_lean.py /opt/apn/apn_lean.py
RUN chmod +x /opt/apn/apn_lean.py

# Keep the container alive; the Inspect sample's setup step starts the daemon.
CMD ["sleep", "infinity"]
