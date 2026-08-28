# Multi-stage build for the LeanOpenProblems sandbox images (PortBench's
# pattern: docker compose builds the stages on demand, no manual image
# management):
#
#   - base       -- Lean + Mathlib (olean cache) + the FormalConjectures
#                   library, so that a problem file importing the FC util
#                   module (`FormalConjectures.Util.ProblemImports` on
#                   old-layout pins, `FormalConjecturesUtil` after upstream's
#                   rename -- the builder detects which from the checkout)
#                   compiles. Shared by the two service images; not a service
#                   itself.
#   - agent      -- the agent's workspace: base + a declared compute stack.
#                   One locked conda-forge env at /opt/env (python + Sage +
#                   the python stack + solver binaries; spec in
#                   compute-env.yaml, built in `compute_build`), apt tools
#                   conda-forge lacks, source-built solvers (`solvers_build`),
#                   the Loogle Mathlib-search CLI (`loogle_build`), and
#                   vendored per-tool docs at /opt/docs. Deliberately contains
#                   NO verifier tooling (no comparator, no lean4export, no
#                   landrun).
#   - comparator -- the trusted verifier: base + the Comparator binary + the
#                   lean4export binary + landrun + the pristine workspace tree.
#                   Replaces the former `compile` + `scorer` pair: the
#                   untrusted `lake build Solution` is confined by landrun
#                   (Landlock) *inside* this container, whose scoring execs
#                   run as a non-privileged user (comparator README
#                   assumption 6; the image itself stays root for Inspect).
#
# Version story (comparator-migration-plan.md §2). Four version-bearing
# artifacts, deliberately NOT all on one toolchain:
#
#   - The FC project (statements, Mathlib, oleans) is pinned by the dataset's
#     FC_COMMIT and builds with its own lean-toolchain (v4.27.0 today). This is
#     dataset identity; anything that importModules-loads oleans (lean4export,
#     Loogle) must be built at this toolchain (oleans load only under the
#     toolchain that built them).
#   - The lean4export *binary* (the runtime exporter) `importModules`-loads the
#     project's oleans in-process, so it MUST be built at the project
#     toolchain. Upstream's rev at that toolchain emits an export format the
#     comparator cannot read, so we clone the exact rev comparator's own
#     manifest pins (LEAN4EXPORT_COMMIT) and overwrite its lean-toolchain with
#     the project's before building -- an unmodified source tree, only the
#     toolchain file changes (plan §2.2). Emitter and parser then agree on the
#     format by construction.
#   - The Comparator binary never loads project oleans (it parses lean4export's
#     *text* output and replays it through its embedded kernel), so it is built
#     at its own pinned toolchain (v4.34.0-rc2 today) and merely needs that
#     toolchain's shared libraries present at runtime. Soundness fixes land at
#     comparator tip only, so its pin tracks the newest tag, not the project
#     toolchain (plan §2.1).
#
# On an FC-pin bump: the exporter's and Loogle's builds move with it (Loogle
# is dependency-free and merely rebuilt at the pin's toolchain, with its
# Mathlib search index rebaked; see `loogle_build`).
# On a comparator bump: move LEAN4EXPORT_COMMIT to the rev in comparator's
# lake-manifest.json, re-verify the toolchain-override build, and re-run the
# primitive-constants check (plan §2.3; the gold-proof suite exercises it).
#
# The agent's compute stack is DECLARED, not accreted: the conda-forge env
# spec (compute-env.yaml) plus the explicit install lines in `compute_build`,
# `solvers_build`, and the `agent` stage are the source of truth for what the
# agent can run; tests/test_agent_image.py contract-tests the roster and
# apn/prompts.py advertises it. Loogle is the one deliberately pin-tied
# addition outside the base layer; everything else in the compute stack is
# Lean-agnostic.
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

# The dataset's FC pin (apn/data/<dataset>/fc_commit). Required: there is
# deliberately no default a stale build could silently fall back to
ARG FC_COMMIT
RUN git clone --filter=blob:none \
        https://github.com/google-deepmind/formal-conjectures /workspace/leanproject \
    && git -C /workspace/leanproject checkout "${FC_COMMIT}"

WORKDIR /workspace/leanproject

# Every dataset's FC pin must be on this track's Lean toolchain (see the header
# comment); fail the build outright if the checkout disagrees, instead of
# producing an image whose repl/lean4export/extract_ranges toolchains mismatch
# the oleans.
RUN test "$(cat lean-toolchain)" = "leanprover/lean4:${LEAN_VERSION}" \
    || { echo "FC pin ${FC_COMMIT} uses $(cat lean-toolchain), not leanprover/lean4:${LEAN_VERSION}" >&2; exit 1; }

# Register the comparator's Challenge/Solution scratch libraries BEFORE any
# lake invocation, so lake's workspace configuration (which hashes the
# lakefile) is settled exactly once at image build and never re-resolved at
# scoring time. The stubs import the pin's util module (layout-detected below)
# so the warm build settles the libs' traces too; at scoring time the checker
# overwrites run/*.lean with the real challenge/solution and content hashes
# force the rebuild. FC's style linters (package-level [leanOptions]) are
# switched off for these libs only: they would spam every check's verifier
# output with copyright/namespace warnings about files that are not FC
# contributions.
RUN printf '%s\n' \
        '' \
        '[[lean_lib]]' \
        'name = "Challenge"' \
        'srcDir = "run"' \
        '[lean_lib.leanOptions]' \
        'weak.linter.style.copyright.formalConjectures = false' \
        'weak.linter.style.namespace = false' \
        '' \
        '[[lean_lib]]' \
        'name = "Solution"' \
        'srcDir = "run"' \
        '[lean_lib.leanOptions]' \
        'weak.linter.style.copyright.formalConjectures = false' \
        'weak.linter.style.namespace = false' \
        >> lakefile.toml \
    && mkdir -p run \
    && if [ -f FormalConjecturesUtil.lean ]; then \
           UTIL_MODULE=FormalConjecturesUtil; \
       else \
           UTIL_MODULE=FormalConjectures.Util.ProblemImports; \
       fi \
    && echo "import ${UTIL_MODULE}" > run/Challenge.lean \
    && echo "import ${UTIL_MODULE}" > run/Solution.lean

# Fetch Mathlib's prebuilt oleans, then build only the util-module closure (the
# FC support modules + FormalConjecturesForMathlib) and the two scratch-lib
# stubs. The hundreds of problem files are NOT built. The lib entry point
# depends on the checkout's layout -- `FormalConjecturesUtil` after upstream's
# rename, `FormalConjectures.Util.ProblemImports` before it -- and the builder
# has the checkout, so it detects which (both layouts are live requirements
# across the datasets' pins; the host-side registry `apn.dataset._FC_PROFILES`
# states the same fact for the code that has no checkout).
RUN lake exe cache get \
    && if [ -f FormalConjecturesUtil.lean ]; then \
           lake build FormalConjecturesUtil; \
       else \
           lake build FormalConjectures.Util.ProblemImports; \
       fi \
    # Stub build: broken scratch-lib plumbing fails here, not at the first check.
    && lake build Challenge Solution

# `COPY` can't branch on layout, so stage the proving-library SOURCE (the files
# the agent legitimately proves *with*, imported into every problem's scope
# like Mathlib) into one directory for the base stage's single COPY. The
# conjecture problem files and the library test suite are deliberately NOT
# staged.
RUN mkdir /staged \
    && if [ -f FormalConjecturesUtil.lean ]; then \
           cp FormalConjecturesUtil.lean /staged/ \
           && cp -r FormalConjecturesUtil /staged/FormalConjecturesUtil; \
       else \
           mkdir /staged/FormalConjectures \
           && cp -r FormalConjectures/Util /staged/FormalConjectures/Util; \
       fi \
    && cp FormalConjecturesForMathlib.lean /staged/ \
    && cp -r FormalConjecturesForMathlib /staged/FormalConjecturesForMathlib

# NOTE: `Submission/` is deliberately NOT registered as a lean_lib. The agent's
# proof is a single file, `Submission/Spec.lean`; the comparator checker copies
# exactly that file to `run/Solution.lean` and scores it. An
# `import Submission.…` of an agent helper module therefore fails to resolve
# (no such lib is registered) -- with Comparator this single-file layout is a
# *policy* choice rather than a soundness requirement (the full solution
# closure is kernel-replayed either way), but do not relax it here; see
# comparator-migration-plan.md §3.2. The `Submission/` directory and its
# `Spec.lean` are created at *runtime* by the Python scaffold in the agent
# sandbox (see apn.solver).

# --------------------------------------------------------------------------- #
# base: copy in only what runtime needs.                                       #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS base

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=/root/.elan/bin:$PATH \
    ELAN_HOME=/root/.elan \
    APN_LEAN_PROJECT=/workspace/leanproject

# Runtime libs for the Lean toolchain, plus the build tools the derived images
# need (the loogle_build and lean4export_build stages compile Lean projects)
# and python3 (loogle_build reads the baked manifest with it; the `generate`
# stage drives repo scripts with it). The agent's own python is NOT this one:
# the agent image puts its /opt/env python first on PATH.
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential libgmp-dev \
        python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*

# The Lean/lake toolchain (binaries + the project toolchain). The image ENV PATH
# above covers non-login execs (plain ``sandbox().exec`` calls); add a profile
# snippet so *login* shells (``bash --login -c``, how the agent's bash tool
# execs) also find lake/lean.
COPY --from=builder /root/.elan /root/.elan
RUN echo 'export PATH=/root/.elan/bin:$PATH' > /etc/profile.d/elan.sh

WORKDIR /workspace/leanproject

# Lake project metadata + all build artifacts: the FC library oleans and the full
# Mathlib/dependency set under .lake/packages. Imports resolve from these oleans.
COPY --from=builder /workspace/leanproject/lakefile.toml \
                    /workspace/leanproject/lean-toolchain \
                    /workspace/leanproject/lake-manifest.json ./
COPY --from=builder /workspace/leanproject/.lake ./.lake

# Note: neither the `Submission/` nor the `run/` directory is copied in. They
# carry no baked content -- the Python scaffold creates the agent's
# `Submission/Spec.lean` at runtime, and the comparator checker recreates
# `run/` and stages `run/Challenge.lean`/`run/Solution.lean` per check.

# The proving-library SOURCE the agent legitimately proves *with* (imported into
# every problem's scope, like Mathlib), staged by the builder per the checkout's
# layout. The conjecture problem files and the library test suite are
# deliberately NOT copied.
COPY --from=builder /staged ./

CMD ["sleep", "infinity"]

# --------------------------------------------------------------------------- #
# compute_build: the agent's conda-forge compute env at /opt/env (python +     #
# Sage + the python stack + solver binaries; spec: compute-env.yaml). Built    #
# in its own stage so the multi-GB env is one cached layer COPY'd into agent,  #
# re-run only when the spec or the pip pins change. The pip layer installs     #
# into the SAME env (no second python): PyPI-only packages, pinned here.       #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS compute_build

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates bzip2 \
    && rm -rf /var/lib/apt/lists/*

ARG MICROMAMBA_VERSION=2.9.0
RUN arch="$(uname -m)" \
    && case "$arch" in x86_64) plat=linux-64 ;; aarch64) plat=linux-aarch64 ;; *) echo "unsupported arch $arch" >&2; exit 1 ;; esac \
    && curl -sSfL "https://micro.mamba.pm/api/micromamba/${plat}/${MICROMAMBA_VERSION}" \
        | tar -xj -C /usr/local bin/micromamba

COPY compute-env.yaml /tmp/compute-env.yaml
RUN micromamba create -y -p /opt/env -f /tmp/compute-env.yaml \
    && micromamba clean -afy

# PyPI-only packages (prebuilt wheels), into the same env. snappy is SnapPy
# (3-manifold topology), not the compression lib.
RUN /opt/env/bin/pip install --no-cache-dir \
        python-sat==1.9.dev15 \
        cvc5==1.3.4 \
        ortools==9.15.6755 \
        snappy==3.3.2 \
    && find /opt/env -name '__pycache__' -type d -prune -exec rm -rf {} +

# --------------------------------------------------------------------------- #
# solvers_build: tools with no conda-forge or bookworm packaging, built from   #
# pinned sources (plus the pinned official cvc5 static binary -- its PyPI      #
# wheel in compute_build carries only the python API). Everything lands in    #
# /out/bin and links only libc/libm from the shared bookworm userland (flint/  #
# gmp/mpfr are linked statically), so the binaries drop straight into agent.   #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS solvers_build

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates build-essential unzip m4 \
        libgmp-dev libmpfr-dev \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir -p /out/bin

# kissat: state-of-the-art CDCL SAT solver (DIMACS in/out).
ARG KISSAT_VERSION=rel-4.0.4
RUN curl -sSfL "https://github.com/arminbiere/kissat/archive/refs/tags/${KISSAT_VERSION}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/kissat-* \
    && ./configure && make -j"$(nproc)" \
    && install -m 755 build/kissat /out/bin/kissat \
    && rm -rf /tmp/kissat-*

# plantri: planar-graph generator (Brinkmann & McKay).
ARG PLANTRI_VERSION=55
RUN curl -sSfL "https://users.cecs.anu.edu.au/~bdm/plantri/plantri${PLANTRI_VERSION}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/plantri* \
    && make plantri \
    && install -m 755 plantri /out/bin/plantri \
    && rm -rf /tmp/plantri*

# prover9/mace4: first-order theorem prover + finite-model finder. Upstream
# (cs.unm.edu LADR-2009-11A) has no releases and Debian dropped the package;
# built from a pinned commit of the ai4reason mirror of that final release.
ARG PROVER9_COMMIT=cdca95a51d3c3459b8fd2ebbb5ac1504be2172e3
RUN curl -sSfL "https://github.com/ai4reason/Prover9/archive/${PROVER9_COMMIT}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/Prover9-* \
    && make all \
    && install -m 755 bin/prover9 bin/mace4 bin/interpformat bin/prooftrans /out/bin/ \
    && rm -rf /tmp/Prover9-*

# msolve: multivariate polynomial system solver (Groebner bases). Needs
# FLINT >= 3, which bookworm lacks -- both are built here, FLINT static so
# nothing but the msolve binaries ship.
ARG FLINT_VERSION=3.6.0
ARG MSOLVE_VERSION=0.10.1
RUN curl -sSfL "https://github.com/flintlib/flint/releases/download/v${FLINT_VERSION}/flint-${FLINT_VERSION}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/flint-* \
    && ./configure --disable-shared --prefix=/usr/local \
    && make -j"$(nproc)" && make install \
    && rm -rf /tmp/flint-*
RUN curl -sSfL "https://github.com/algebraic-solving/msolve/releases/download/v${MSOLVE_VERSION}/msolve-${MSOLVE_VERSION}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/msolve-* \
    && ./configure --disable-shared \
    && make -j"$(nproc)" \
    && install -m 755 msolve /out/bin/msolve \
    && rm -rf /tmp/msolve-*

# cvc5: SMT solver, official pinned static release binary (matches the pip
# bindings' version in compute_build).
ARG CVC5_VERSION=1.3.4
RUN arch="$(uname -m)" \
    && case "$arch" in x86_64) a=x86_64 ;; aarch64) a=arm64 ;; *) echo "unsupported arch $arch" >&2; exit 1 ;; esac \
    && curl -sSfL -o /tmp/cvc5.zip \
        "https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-Linux-${a}-static.zip" \
    && unzip -q /tmp/cvc5.zip -d /tmp/cvc5 \
    && install -m 755 /tmp/cvc5/*/bin/cvc5 /out/bin/cvc5 \
    && rm -rf /tmp/cvc5 /tmp/cvc5.zip

# --------------------------------------------------------------------------- #
# loogle_build: the Loogle type-pattern Mathlib search CLI. Upstream's        #
# "Running locally" contract: the binary is dependency-free, must merely be   #
# built with the TARGET project's toolchain, and then searches any Lake       #
# project via `lake env loogle --module <M> "<query>"` (it reads LEAN_PATH).  #
# The first query builds a search index cached next to the module's .olean    #
# and auto-invalidated when the oleans change; running one here bakes that    #
# index (and smoke-tests the build), so agents get fast queries.              #
# --------------------------------------------------------------------------- #
FROM base AS loogle_build

ARG LOOGLE_COMMIT=9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0
RUN git clone https://github.com/nomeata/loogle.git /opt/loogle \
    && git -C /opt/loogle checkout --detach "${LOOGLE_COMMIT}" \
    && cp /workspace/leanproject/lean-toolchain /opt/loogle/lean-toolchain \
    && cd /opt/loogle \
    && lake build \
    && cd /workspace/leanproject \
    && lake env /opt/loogle/.lake/build/bin/loogle --module Mathlib "Nat.Prime" > /dev/null

# --------------------------------------------------------------------------- #
# agent: the agent's workspace. Layer order is big/stable first (the conda     #
# env), then apt, then the small solver binaries, then Loogle, then docs       #
# (which churn most).                                                          #
# --------------------------------------------------------------------------- #
FROM base AS agent

# The compute env (see compute-env.yaml). /opt/env/bin goes FIRST on PATH so
# the env's python IS the agent's `python3` (and sage, gp, gap, z3, ... all
# resolve there); the profile.d snippet covers login shells (`bash --login
# -c`, how apn.tools execs), the ENV covers plain execs.
COPY --from=compute_build /opt/env /opt/env
ENV PATH=/opt/env/bin:$PATH
RUN echo 'export PATH=/opt/env/bin:$PATH' > /etc/profile.d/compute-env.sh

# Tools conda-forge lacks, from bookworm: polymake (polyhedral geometry),
# Macaulay2 (commutative algebra), regina-normal (low-dimensional topology;
# `regina-python`), cryptominisat (SAT, newer here than conda-forge's),
# coinor-csdp (semidefinite programming, `csdp`), jq + ripgrep for the bash
# tool (git is already in `base`), libmpfr6 (msolve's one non-static runtime
# link besides gmp, which base's libgmp-dev already provides).
RUN apt-get update && apt-get install -y --no-install-recommends \
        polymake macaulay2 regina-normal cryptominisat coinor-csdp \
        jq ripgrep libmpfr6 \
    && rm -rf /var/lib/apt/lists/*

# Source-built solvers (kissat, plantri, prover9/mace4, msolve, cvc5).
COPY --from=solvers_build /out/bin/ /usr/local/bin/

# Loogle: the dependency-free binary, plus the Mathlib search index it baked
# next to Mathlib.olean (COPY preserves mtimes, and this stage shares base's
# layers with loogle_build, so the index stays valid; were it ever judged
# stale, loogle transparently rebuilds it). Invocation, per upstream's docs
# (vendored at /opt/docs/loogle): from the project,
#   lake env loogle --module Mathlib "<query>"
COPY --from=loogle_build /opt/loogle/.lake/build/bin/loogle /usr/local/bin/loogle
COPY --from=loogle_build \
     /workspace/leanproject/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.loogle-index \
     /workspace/leanproject/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.loogle-index

# In-sandbox references (the sandbox has no network): vendored, version-matched
# docs for the tools whose syntax the agent is unlikely to know cold. Last:
# docs churn more than any layer above.
COPY docs /opt/docs

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
# landrun_build: the Landlock sandboxing launcher Comparator confines the      #
# untrusted solution build/export with. Upstream's README requires building    #
# from the main branch's source; we pin a commit (tags are not cut). Built     #
# static (CGO off) so the binary drops into the bookworm-slim runtime image.   #
# --------------------------------------------------------------------------- #
FROM golang:1.24-bookworm AS landrun_build

ARG LANDRUN_COMMIT=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
RUN git clone https://github.com/Zouuup/landrun.git /src/landrun \
    && git -C /src/landrun checkout --detach "${LANDRUN_COMMIT}" \
    && cd /src/landrun \
    && CGO_ENABLED=0 go build -trimpath -o /out/landrun ./cmd/landrun

# --------------------------------------------------------------------------- #
# comparator_build: build the Comparator binary at ITS OWN pinned toolchain    #
# (v4.34.0-rc2 today; see the header's version story). `lake build` resolves   #
# `Export.Parse` from comparator's lake-manifest.json -- the same              #
# LEAN4EXPORT_COMMIT rev the runtime exporter below is built from (the         #
# coupled-pin invariant, plan §2.3). The build runs under /root/.elan so the   #
# binary's RPATH points where the runtime image installs the toolchain.        #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS comparator_build

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=/root/.elan/bin:$PATH \
    ELAN_HOME=/root/.elan

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

ARG ELAN_VERSION=v4.2.3
RUN curl -sSfL "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-$(uname -m)-unknown-linux-gnu.tar.gz" \
        | tar xz -C /tmp \
    && /tmp/elan-init -y --default-toolchain none \
    && rm /tmp/elan-init

# Pin the commit, not the tag (tags are mutable): 19e111e = tag v4.34.0-rc2.
ARG COMPARATOR_COMMIT=19e111e2141cf333c7daff0f64c5f24acc91dd2e
RUN git clone https://github.com/leanprover/comparator.git /opt/comparator \
    && git -C /opt/comparator checkout --detach "${COMPARATOR_COMMIT}" \
    && elan toolchain install "$(cat /opt/comparator/lean-toolchain)" \
    && cd /opt/comparator \
    && lake build comparator

# --------------------------------------------------------------------------- #
# lean4export_build: the runtime exporter. It importModules-loads the          #
# project's oleans in-process, so it is built at the PROJECT toolchain -- an   #
# unmodified upstream clone at the rev comparator's manifest pins, with only   #
# the lean-toolchain file overwritten (plan §2.2: no upstream rev has the new  #
# export format *and* the project toolchain, and the exe's compile surface is  #
# old-API enough to build cleanly). FROM base so the project toolchain and     #
# build tools are already present and the toolchain file is copied from the    #
# project itself (byte-exact match by construction).                           #
# --------------------------------------------------------------------------- #
FROM base AS lean4export_build

# Must equal the lean4export rev in the pinned comparator's lake-manifest.json.
ARG LEAN4EXPORT_COMMIT=cacf989bd75f608700820f6afc595f32e7a99a4d
RUN git clone https://github.com/leanprover/lean4export.git /opt/lean4export \
    && git -C /opt/lean4export checkout --detach "${LEAN4EXPORT_COMMIT}" \
    && cp /workspace/leanproject/lean-toolchain /opt/lean4export/lean-toolchain \
    && cd /opt/lean4export \
    && lake build lean4export

# --------------------------------------------------------------------------- #
# comparator: the trusted verifier image (compose service `comparator`).       #
# Carries TWO toolchains by design (plan §2.3): the project toolchain (from    #
# base) runs everything at scoring time -- `lake env`, the challenge/solution  #
# builds, lean4export -- while the comparator binary's own toolchain exists    #
# solely so that binary's shared-library RPATH resolves. No lake/lean          #
# invocation ever dispatches to the second toolchain.                          #
#                                                                              #
# Scoring runs as the non-privileged `comparator` user (comparator README      #
# assumption 6) -- not via a USER directive (the image stays root for          #
# Inspect; see the note at the end of this stage) but per exec: the checker    #
# passes user=COMPARATOR_USER on every command except the root .lake reset.    #
# landrun (Landlock) confines the untrusted solution build to writes in        #
# .lake, and /opt/apn/reset-dotlake.sh restores a pristine .lake before every  #
# check (comparator-migration-plan.md §3.1).                                   #
# --------------------------------------------------------------------------- #
FROM base AS comparator

# Resolve lake/lean straight from the project toolchain, bypassing the elan
# shims: the shims may want to touch elan state (e.g. gc bookkeeping) under
# /root on dispatch, which the non-privileged runtime user cannot write. The
# elan-managed install is still what ships the toolchain; only PATH resolution
# changes.
ARG LEAN_VERSION=v4.27.0
ENV PATH=/root/.elan/toolchains/leanprover--lean4---${LEAN_VERSION}/bin:$PATH

# The comparator binary + its own toolchain (merged into /root/.elan alongside
# the project's -- the binary's RPATH points into this path).
COPY --from=comparator_build /opt/comparator/.lake/build/bin/comparator \
                             /opt/apn/comparator/bin/comparator
COPY --from=comparator_build /root/.elan/toolchains /root/.elan/toolchains

# The runtime exporter (project toolchain; RPATH resolves via base's install)
# and landrun, installed on PATH where comparator's default resolution finds
# them (its README's preferred setup) -- no COMPARATOR_* env overrides needed.
COPY --from=lean4export_build /opt/lean4export/.lake/build/bin/lean4export \
                              /usr/local/bin/lean4export
COPY --from=landrun_build /out/landrun /usr/local/bin/landrun

COPY reset-dotlake.sh /opt/apn/reset-dotlake.sh
RUN chmod 755 /opt/apn/reset-dotlake.sh

# Stage the pristine workspace tree the reset script restores from:
#   /opt/pristine/dot-lake  -- the project .lake minus packages/ (lake config
#                              cache + the FC build artifacts, tens of MB;
#                              copied into .lake on every reset). The builder's
#                              Challenge/Solution stub artifacts ride along:
#                              staged files hash differently, so lake rebuilds
#                              them (and reuse on a byte-identical file is the
#                              same compilation).
#   /opt/pristine/packages  -- the heavy Mathlib/dependency artifacts; stay
#                              root-owned outside .lake (and so outside the
#                              landrun write grant) and are symlinked into the
#                              fresh .lake (never copied, never writable).
# Neither .lake nor run/ is recreated here: the reset script rebuilds .lake
# and the checker rebuilds run/ before every check, so the image need not
# carry either.
RUN mkdir -p /opt/pristine \
    && mv /workspace/leanproject/.lake/packages /opt/pristine/packages \
    && mv /workspace/leanproject/.lake /opt/pristine/dot-lake

# The non-privileged runtime user (comparator README assumption 6). It owns
# exactly the project dir, in which the reset script recreates .lake and the
# checker recreates run/ per check. Everything else -- binaries, toolchains,
# /opt/pristine -- stays root-owned and unwritable. The baked toolchains live
# under /root/.elan (the PATH pin above, and the comparator binary's RPATH),
# so /root becomes traverse-only (711: x permits path resolution; no listing,
# no writes).
RUN useradd --create-home --shell /bin/bash comparator \
    && chown comparator /workspace/leanproject \
    && chmod 711 /root

# Lake validates the manifest by reading each package's git remote; git
# refuses repos owned by another uid (safe.directory, CVE-2022-24765), and
# lake treats the failed read as "URL has changed" -- attempting to delete and
# re-clone the root-owned pristine packages. The baked repos are trusted, so
# mark everything safe for the runtime user. (The untrusted build gains
# nothing: it already controls its own child processes' GIT_CONFIG_* env.)
RUN git config --system --add safe.directory '*'

# The image deliberately stays root (no USER directive): Inspect's sandbox
# plumbing assumes the container's default user can write anywhere
# (write_file's tee/mkdir run as that user), and k8s_sandbox implements the
# per-exec `user=` switch with runuser(1), which only root may invoke. The
# privilege drop happens per command instead: the checker passes
# user=COMPARATOR_USER (apn/checker.py) on every exec against this sandbox
# except the .lake reset, which stays root so its rm can clear permission
# traps the untrusted build may leave in .lake (see reset-dotlake.sh). All
# other scoring work runs as `comparator` -- both backends resolve its HOME
# from the passwd entry (docker exec --user and runuser alike). Staged inputs
# written as root land 0644, readable by the comparator user; run/ and .lake
# are (re)created as the comparator user (the reset drops to it for the
# copy), so it owns everything it must write.

CMD ["sleep", "infinity"]

# --------------------------------------------------------------------------- #
# generate: vendor-time stage holding the declaration-range extractor that      #
# scripts/generate_*_isolated.py drives to rebuild apn/data/*/Isolated/, plus   #
# the disproof-declaration certifier the isolation suites run over the          #
# committed files. Not a runtime service and kept separate from `comparator`    #
# so the scored image stays minimal. Source-only COPY (no host .lake); imports  #
# only Lean core, so it builds offline with no `lake update`. Run via:          #
#   docker build --target generate -t apn-generate \                            #
#     --build-arg FC_COMMIT="$(cat apn/data/<dataset>/fc_commit)" apn/lean       #
#   docker run --rm -v "$PWD":/repo apn-generate \                              #
#     python3 /repo/scripts/generate_oeis_isolated.py --container '' ...        #
# (in practice: build the extractor into a container with the repo mounted).    #
# --------------------------------------------------------------------------- #
FROM base AS generate

COPY extract_ranges/lakefile.lean extract_ranges/lean-toolchain \
     extract_ranges/ExtractRanges.lean extract_ranges/CertifyDisproof.lean \
     /opt/apn/extract_ranges/
RUN cd /opt/apn/extract_ranges && lake build extract_ranges certify_disproof

CMD ["sleep", "infinity"]
