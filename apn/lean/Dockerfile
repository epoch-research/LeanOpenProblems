# Multi-stage build for the LeanOpenProblems sandbox images (PortBench's
# pattern: docker compose builds the stages on demand, no manual image
# management):
#
#   - base   -- Lean v4.27.0 + Mathlib (olean cache) + the FormalConjectures
#               library, so that a problem file importing
#               `FormalConjectures.Util.ProblemImports` compiles. Shared by the
#               two service images; not a service itself.
#   - agent  -- the agent's workspace: base + PyPantograph + numerical Python
#               libs. Deliberately does NOT contain SafeVerify.
#   - scorer -- the trusted checker: base + SafeVerify. Runs in a separate
#               sandbox the agent never writes to.
#
# Lean v4.27.0 matches the Formal Conjectures Erdős/OEIS datasets (oleans are
# version-specific, so the repl and SafeVerify are all built at this version).
#
# The builder stage clones the whole formal-conjectures repo and builds the
# library; base copies in ONLY the toolchain, the lake build artifacts
# (oleans), and the proving-library source. The conjecture corpus (other OEIS
# problems, the Erdős/Arxiv/etc. sets -- which contain real proofs and
# axioms), the library test suite, and repo tooling/docs/.git never reach the
# agent's sandbox, so there is no contamination to strip after the fact.

# --------------------------------------------------------------------------- #
# Builder: clone + build the FC library (everything here is discarded).        #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS builder

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=/root/.elan/bin:$PATH \
    ELAN_HOME=/root/.elan

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

ARG LEAN_VERSION=v4.27.0
ARG ELAN_VERSION=v4.2.3
RUN curl -sSfL "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-$(uname -m)-unknown-linux-gnu.tar.gz" \
        | tar xz -C /tmp \
    && /tmp/elan-init -y --default-toolchain "leanprover/lean4:${LEAN_VERSION}" \
    && rm /tmp/elan-init

ARG FC_BRANCH=auto_oeis
ARG FC_COMMIT=67338a157bbb8d87e9a349d662f82a868bda6327
RUN git clone --filter=blob:none --branch "${FC_BRANCH}" \
        https://github.com/google-deepmind/formal-conjectures /workspace/leanproject \
    && git -C /workspace/leanproject checkout "${FC_COMMIT}"

WORKDIR /workspace/leanproject

# Fetch Mathlib's prebuilt oleans, then build only the ProblemImports closure
# (the FC Util/* support modules + FormalConjecturesForMathlib). The hundreds of
# problem files are NOT built.
RUN lake exe cache get \
    && lake build FormalConjectures.Util.ProblemImports

# NOTE: `Submission/` is deliberately NOT registered as a lean_lib. The agent's
# proof is a single file, `Submission/Spec.lean`, compiled standalone with
# `lake env lean -o` (which derives the module name `Submission.Spec` from the
# path -- no lib registration needed). Registering a lib and building it
# graph-aware with `lake build` would let the agent split its proof across
# imported helper modules, whose constants safe_verify *trusts* rather than
# kernel-replays (it replays only the file it is handed) -- a soundness hole.
# Keep proofs single-file; do not add a `[[lean_lib]] name = "Submission"` here.
# The `Submission/` directory and its `Spec.lean` are created at *runtime* by the
# Python scaffold -- the solver writes the entry module before the agent runs,
# and the checker clears and recreates it on every call (see apn.solver /
# apn.checker).

# --------------------------------------------------------------------------- #
# base: copy in only what runtime needs.                                       #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS base

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=/root/.elan/bin:$PATH \
    ELAN_HOME=/root/.elan \
    APN_LEAN_PROJECT=/workspace/leanproject

# Runtime libs for the Lean toolchain, plus the build tools the derived images
# need (the agent builds PyPantograph; the scorer builds SafeVerify) and python3
# (the agent uses it to drive PyPantograph and as a numerical scratchpad; the
# scorer runs SafeVerify through it).
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential libgmp-dev \
        python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*

# The Lean/lake toolchain (binaries + the v4.27.0 toolchain). The image ENV PATH
# above covers non-login execs (how ``sandbox().exec`` and the agent's PyPantograph
# subprocess run); add a profile snippet so *login* shells (e.g. ``bash -lc``)
# also find lake/lean.
COPY --from=builder /root/.elan /root/.elan
RUN echo 'export PATH=/root/.elan/bin:$PATH' > /etc/profile.d/elan.sh

WORKDIR /workspace/leanproject

# Lake project metadata + all build artifacts: the FC library oleans and the full
# Mathlib/dependency set under .lake/packages. Imports resolve from these oleans.
COPY --from=builder /workspace/leanproject/lakefile.toml \
                    /workspace/leanproject/lean-toolchain \
                    /workspace/leanproject/lake-manifest.json ./
COPY --from=builder /workspace/leanproject/.lake ./.lake

# Note: the `Submission/` directory is NOT copied in. It carries no baked
# content -- the Python scaffold creates it and the entry module at runtime (the
# solver writes Spec.lean before the agent runs; the checker clears and recreates
# it on every call). Both runtime writers `mkdir -p` the directory, so it need
# not pre-exist in the image.

# The proving-library SOURCE the agent legitimately proves *with* (imported into
# every problem's scope, like Mathlib). The conjecture problem files and the
# library test suite are deliberately NOT copied.
COPY --from=builder /workspace/leanproject/FormalConjectures/Util \
                    ./FormalConjectures/Util
COPY --from=builder /workspace/leanproject/FormalConjecturesForMathlib \
                    ./FormalConjecturesForMathlib
COPY --from=builder /workspace/leanproject/FormalConjecturesForMathlib.lean \
                    ./FormalConjecturesForMathlib.lean

CMD ["sleep", "infinity"]

# --------------------------------------------------------------------------- #
# agent: the agent's workspace.                                                #
# --------------------------------------------------------------------------- #
FROM base AS agent

# PyPantograph commit b8608f3 pins Pantograph v0.3.13, whose repl targets Lean
# v4.27.0 -- matching this track's Mathlib + FormalConjectures oleans. (The repl
# must be built with the same toolchain that produced the oleans it loads.)
# The clone is removed after install so the only importable `pantograph` is the
# installed package (a lingering source tree would shadow it for any python
# started inside /opt/PyPantograph, and the source tree lacks the built repl).
ARG PYPANTOGRAPH_COMMIT=b8608f3
RUN git clone https://github.com/lenianiva/PyPantograph.git /opt/PyPantograph \
    && cd /opt/PyPantograph \
    && git checkout "${PYPANTOGRAPH_COMMIT}" \
    && git submodule update --init --recursive \
    && pip3 install --break-system-packages --no-cache-dir . \
    && cd / && rm -rf /opt/PyPantograph

# In-sandbox references for the agent (the sandbox has no network), vendored
# version-matched to the installed package: PyPantograph docs + examples at the
# pinned commit, and Pantograph's repl protocol reference at the submodule
# commit that pin builds.
COPY pypantograph-docs /opt/pypantograph-docs
COPY pantograph-docs /opt/pantograph-docs

# Numerical/symbolic scratchpad for the agent (the `bash` tool runs python3 in
# this image). The sandbox has no network, so everything is baked in here.
#   - sagemath: a full computer algebra system on the `sage` command, bundling
#     PARI/GP, FLINT, Maxima, GAP and Singular -- far stronger than sympy for
#     number theory (factoring, modular arithmetic, elliptic curves, continued
#     fractions) and the dialect much of OEIS's own reference code is written in.
#   - python3-{numpy,sympy,mpmath}: importable directly from `python3` (sympy =
#     exact symbolic, mpmath = arbitrary precision with pslq/identify). Pulled
#     from apt alongside sagemath so all versions resolve mutually consistent
#     (a pip --break-system-packages upgrade could outrun what Sage expects).
# This ~1.5 GB install is its own cached layer.
RUN apt-get update && apt-get install -y --no-install-recommends \
        sagemath python3-numpy python3-sympy python3-mpmath \
    && rm -rf /var/lib/apt/lists/*

# CLI tools for the agent's `bash` tool (git is already in `base`): jq for JSON,
# ripgrep for fast search (`rg`). In `agent` so both run conditions get them and
# the agent can be prompted to use `rg` consistently whether or not /corpus is
# present. A cheap layer kept after the sagemath layer so editing it never busts
# that cache.
RUN apt-get update && apt-get install -y --no-install-recommends jq ripgrep \
    && rm -rf /var/lib/apt/lists/*

CMD ["sleep", "infinity"]

# --------------------------------------------------------------------------- #
# corpus: build the offline arXiv-math grep corpus from two pinned public HF    #
# datasets at build time (network is needed only here; the runtime sandbox stays #
# airgapped). Four stages, split so the work caches at the right granularity:    #
#   1-2. corpus_fetch_src / corpus_fetch_meta -- pure downloads (~9 GB), one per  #
#        source, each cached on its own; nothing but fetch.py runs here.          #
#   3.   corpus_build -- reads the two downloads and does the explode + join.     #
#        Editing the join logic re-runs ONLY this stage; the downloads stay       #
#        cached (the COPY --from layers precede the script COPY).                 #
#   4.   corpus -- FROM scratch, carrying only /corpus. This is the artifact       #
#        image agent_corpus copies from; built once and pushed like `base`.       #
# huggingface_hub is pinned <1.0 (requests/urllib3, not the 1.x httpx line):      #
# httpx's strict URL parser crashes on an IPv6 CIDR in a NO_PROXY env var (e.g.    #
# the one OrbStack injects into builds), whereas urllib3 tolerates it.            #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS corpus_fetch_src
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        python3 python3-pip ca-certificates \
    && rm -rf /var/lib/apt/lists/*
RUN pip3 install --break-system-packages --no-cache-dir "huggingface_hub<1.0"
COPY fetch.py /tmp/fetch.py
RUN python3 /tmp/fetch.py --repo proofpile --dest /shards --cache-dir /tmp/hfcache \
    && rm -rf /tmp/hfcache /root/.cache

FROM debian:bookworm-slim AS corpus_fetch_meta
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        python3 python3-pip ca-certificates \
    && rm -rf /var/lib/apt/lists/*
RUN pip3 install --break-system-packages --no-cache-dir "huggingface_hub<1.0"
COPY fetch.py /tmp/fetch.py
RUN python3 /tmp/fetch.py --repo metadata --dest /meta --cache-dir /tmp/hfcache \
    && rm -rf /tmp/hfcache /root/.cache

FROM debian:bookworm-slim AS corpus_build
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*
RUN pip3 install --break-system-packages --no-cache-dir pyarrow
# COPY the downloads first so they stay cached when only the join script changes.
COPY --from=corpus_fetch_src /shards /shards
COPY --from=corpus_fetch_meta /meta /meta
COPY build_corpus.py /tmp/build_corpus.py
RUN python3 /tmp/build_corpus.py --shards-dir /shards --meta-dir /meta --out /corpus

FROM scratch AS corpus
COPY --from=corpus_build /corpus /corpus

# --------------------------------------------------------------------------- #
# agent_corpus: the agent workspace + the offline literature corpus at /corpus. #
# Used for the `literature` run condition; the plain `agent` image has no       #
# /corpus, so the closed-book condition is hermetic. The ~13 GB COPY is its own #
# layer, cached independently of the agent layers. ripgrep (for fast grep over  #
# the corpus) is inherited from `agent`.                                        #
# --------------------------------------------------------------------------- #
FROM agent AS agent_corpus

COPY --from=corpus /corpus /corpus

CMD ["sleep", "infinity"]

# --------------------------------------------------------------------------- #
# scorer: SafeVerify, built with the v4.27.0 toolchain so it can replay/verify  #
# v4.27.0 oleans. No Pantograph here.                                          #
# --------------------------------------------------------------------------- #
FROM base AS scorer

# The host-side checker (apn/checker.py) drives the build product directly:
# it compiles target/submission with `lake env lean -o` and runs safe_verify
# on the oleans, one sandbox exec per step.
COPY safeverify /opt/apn/safeverify
# No manifest is vendored; resolve Cli (v4.27.0) and build.
RUN cd /opt/apn/safeverify && lake update && lake build safe_verify

CMD ["sleep", "infinity"]

# --------------------------------------------------------------------------- #
# generate: vendor-time stage holding the declaration-range extractor that      #
# scripts/generate_oeis_isolated.py drives to rebuild apn/data/oeis/Isolated/. Not  #
# a runtime service and kept separate from `scorer` so the scored image stays    #
# minimal. Source-only COPY (no host .lake); imports only Lean core, so it        #
# builds offline with no `lake update`. Run via:                                 #
#   docker build --target generate -t apn-generate apn/lean                      #
#   docker run --rm -v "$PWD":/repo apn-generate \                               #
#     python3 /repo/scripts/generate_oeis_isolated.py --container '' ...         #
# (in practice: build the extractor into a container with the repo mounted).     #
# --------------------------------------------------------------------------- #
FROM base AS generate

COPY extract_ranges/lakefile.lean extract_ranges/lean-toolchain \
     extract_ranges/ExtractRanges.lean /opt/apn/extract_ranges/
RUN cd /opt/apn/extract_ranges && lake build extract_ranges

CMD ["sleep", "infinity"]
