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
# not invalidate it. No `lake build` is needed: Pantograph imports Mathlib
# directly and only requires its oleans on LEAN_PATH.
WORKDIR /workspace/leanproject
COPY lean-toolchain lakefile.toml ./
RUN lake update \
    && lake exe cache get

# PyPantograph (the Lean<->Python bridge) is NOT the PyPI `pantograph` package;
# install it from source, pinned to a commit whose bundled repl targets the same
# Lean toolchain (v4.29.1) as Mathlib above. Its build runs `lake build repl`, so
# elan/lake (installed above) must be on PATH.
ARG PYPANTOGRAPH_COMMIT=ffa7f243824d2762825abddb1e9f6e939ede761f
RUN git clone https://github.com/lenianiva/PyPantograph.git /opt/PyPantograph \
    && cd /opt/PyPantograph \
    && git checkout "${PYPANTOGRAPH_COMMIT}" \
    && git submodule update --init --recursive \
    && pip3 install --break-system-packages --no-cache-dir .

COPY apn_lean.py /opt/apn/apn_lean.py
RUN chmod +x /opt/apn/apn_lean.py

# Keep the container alive; the Inspect sample's setup step starts the daemon.
CMD ["sleep", "infinity"]
