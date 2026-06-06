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
RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh -o elan-init.sh \
    && sh elan-init.sh -y --default-toolchain "leanprover/lean4:${LEAN_VERSION}" \
    && rm elan-init.sh

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

# Python libraries for the agent's numerical scratchpad (the `bash` tool runs
# python3 in this image). sympy/numpy are very useful for the number-theory
# problems; the sandbox has no network, so they must be baked in here.
RUN pip3 install --break-system-packages --no-cache-dir numpy sympy

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
# layer (cached independently of the agent layers); ripgrep makes grep fast.    #
# --------------------------------------------------------------------------- #
FROM agent AS agent_corpus

RUN apt-get update && apt-get install -y --no-install-recommends ripgrep \
    && rm -rf /var/lib/apt/lists/*
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
