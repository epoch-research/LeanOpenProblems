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
#   - agent      -- the agent's workspace: base + the compute stack, assembled
#                   from independent chunks (see "The agent's compute stack"
#                   below). Deliberately contains NO verifier tooling (no
#                   comparator, no lean4export, no landrun).
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
# Mathlib search index rebaked; see `loogle`).
# On a comparator bump: move LEAN4EXPORT_COMMIT to the rev in comparator's
# lake-manifest.json, re-verify the toolchain-override build, and re-run the
# primitive-constants check (plan §2.3; the gold-proof suite exercises it).
#
# The agent's compute stack. Each chunk is built in its own stage(s),
# independent of the others, and hands `agent` one directory at its final
# path; `agent` assembles them with COPY --from lines plus one apt line and
# exposes commands by symlink. tests/test_agent_image.py contract-tests the
# assembled image and apn/prompts.py advertises it. Loogle is the one chunk
# tied to the FC pin; everything else is Lean-agnostic.
#
#   stage       members                            delivers         exposed as
#   sage        Sage + its optional backends       /opt/sage        sage gp gap
#               (sage.yaml, sage/*.sh)                              Singular maxima
#   conda       anything with a conda-forge or     /opt/env         python3, pip and
#               PyPI package (conda.yaml)                           the CLI tools in
#                                                                   agent-commands
#   unpackaged  no conda-forge/apt/PyPI package;   bin/ share/doc/  copied into
#               one stage per tool (unpackaged/)                    /usr/local
#   walnut      one product (walnut.sh)            /opt/walnut      the path the
#                                                                   prompt names
#   julia       one product (julia.sh)             /opt/julia       julia
#                                                  /root/.julia
#   loogle      tied to the FC pin                 binary, index,   loogle; README in
#                                                  README           /usr/local/share/doc
#   apt line    bookworm packages conda-forge      in place         on PATH already
#               lacks
#
# Rules of thumb, applied with judgment:
#   1. Each tool has one authoritative recipe: its version, checksum, build,
#      install destination and docs live in one script or one env-spec entry.
#      This file references recipes and does not restate their contents.
#   2. Each chunk hands over one directory at its final path (julia's two and
#      loogle's binary + index are the known exceptions).
#   3. Where two declarations must agree, prefer one declaration; otherwise
#      assert the agreement somewhere automatic (tests/test_agent_image.py
#      holds the integration checks: agent-commands resolution, the cvc5
#      binary/wheel agreement, the ldd sweep). A stage may still fail fast on
#      a missing or malformed artifact where that is the natural place.
#   4. Exposure is explicit: agent-commands lists every command the agent
#      gets from the envs, one absolute path per line, linked into
#      /usr/local/bin. No PATH edits, /etc/profile.d snippets or depot
#      variables (base's elan snippet predates this and is Lean-side).
#
# The builder stage clones the whole formal-conjectures repo and builds the
# library; base copies in ONLY the toolchain, the lake build artifacts
# (oleans), and the proving-library source. The conjecture corpus (other OEIS
# problems, the Erdős/Arxiv/etc. sets -- which contain real proofs and
# axioms), the library test suite, and repo tooling/docs/.git never reach the
# agent's sandbox, so there is no contamination to strip after the fact.

# micromamba, for the two conda-forge env stages (inherited by `conda_base`).
ARG MICROMAMBA_VERSION=2.9.0

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
# need (the loogle and lean4export_build stages compile Lean projects) and
# python3 (loogle reads the baked manifest with it; the `generate` stage drives
# repo scripts with it). The agent's own python3 is NOT this one: the agent
# stage links /opt/env's python3 into /usr/local/bin, ahead of /usr/bin on PATH.
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
# conda_base: bookworm-slim + micromamba, the shared parent of the two        #
# conda-forge env stages (sage, conda). build-essential and pkg-config serve  #
# the builds those stages run inside their envs (sagemath-giac, the compiled  #
# GAP packages, graphillion's sdist); the compiler does not ship.             #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS conda_base

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates bzip2 build-essential pkg-config \
    && rm -rf /var/lib/apt/lists/*

ARG MICROMAMBA_VERSION
RUN arch="$(uname -m)" \
    && case "$arch" in x86_64) plat=linux-64 ;; aarch64) plat=linux-aarch64 ;; *) echo "unsupported arch $arch" >&2; exit 1 ;; esac \
    && curl -sSfL "https://micro.mamba.pm/api/micromamba/${plat}/${MICROMAMBA_VERSION}" \
        | tar -xj -C /usr/local bin/micromamba

# --------------------------------------------------------------------------- #
# sage: Sage and its optional backends, alone in a conda-forge env at         #
# /opt/sage (spec: sage.yaml). Backends that exist as no package at all       #
# follow from their upstreams' own distributions, one script each under       #
# sage/: sagemath-giac, GAP packages, Sage's database tarballs. Only the five #
# launchers listed in agent-commands reach the agent; Sage's python is        #
# reached through `sage` itself (`sage -c`, `sage <file.py>`) and is not the  #
# agent's python3 (the conda stage), so Sage's pins constrain nothing else.   #
# --------------------------------------------------------------------------- #
FROM conda_base AS sage

COPY sage.yaml /build/sage.yaml
RUN micromamba create -y -p /opt/sage -f /build/sage.yaml \
    && micromamba clean -afy

COPY sage/giac.sh /build/
RUN /build/giac.sh
COPY sage/gap-packages.sh /build/
RUN /build/gap-packages.sh
COPY sage/databases.sh /build/
RUN /build/databases.sh

# --------------------------------------------------------------------------- #
# conda: the agent's python3 and every CLI tool that has a conda-forge or     #
# PyPI package, one locked env at /opt/env (spec: conda.yaml, whose `pip:`    #
# section micromamba installs into the same env). Reached only through the    #
# commands listed in agent-commands.                                          #
# --------------------------------------------------------------------------- #
FROM conda_base AS conda

COPY conda.yaml /build/conda.yaml
RUN micromamba create -y -p /opt/env -f /build/conda.yaml \
    && micromamba clean -afy

# --------------------------------------------------------------------------- #
# unpackaged: tools with no conda-forge, bookworm, or PyPI packaging. Each    #
# has one script (unpackaged/<tool>.sh: pinned source or official release     #
# binary, checksum, build, docs from the same archive) and its own stage from #
# build_base, so scripts cannot interact, an edit rebuilds one tool, BuildKit #
# builds them concurrently, and `docker build --target <tool> apn/lean`       #
# builds one alone. Scripts install into /out (bin/, share/doc/<tool>/); the  #
# scratch collector merges the trees and agent copies the result into         #
# /usr/local. Binaries link only the libc family, libstdc++, libgomp, zlib,   #
# gmp and mpfr from the bookworm userland (base's build-essential and         #
# libgmp-dev bring all but mpfr; the agent apt line adds libmpfr6); the       #
# contract test's ldd sweep checks this in the assembled image.               #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS build_base

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates build-essential unzip m4 \
        cmake git subversion p7zip perl zlib1g-dev \
        libboost-graph-dev libboost-program-options-dev \
        libgmp-dev libmpfr-dev \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir /out

FROM build_base AS kissat
COPY unpackaged/kissat.sh /build/
RUN /build/kissat.sh

FROM build_base AS plantri
COPY unpackaged/plantri.sh /build/
RUN /build/plantri.sh

FROM build_base AS prover9
COPY unpackaged/prover9.sh /build/
RUN /build/prover9.sh

FROM build_base AS msolve
COPY unpackaged/msolve.sh /build/
RUN /build/msolve.sh

FROM build_base AS cvc5
COPY unpackaged/cvc5.sh /build/
RUN /build/cvc5.sh

FROM build_base AS vampire
COPY unpackaged/vampire.sh /build/
RUN /build/vampire.sh

FROM build_base AS drat_trim
COPY unpackaged/drat-trim.sh /build/
RUN /build/drat-trim.sh

FROM build_base AS cake_lpr
COPY unpackaged/cake_lpr.sh /build/
RUN /build/cake_lpr.sh

FROM build_base AS breakid
COPY unpackaged/breakid.sh /build/
RUN /build/breakid.sh

FROM build_base AS sms
COPY unpackaged/sms.sh /build/
RUN /build/sms.sh

FROM build_base AS march_cu
COPY unpackaged/march_cu.sh /build/
RUN /build/march_cu.sh

FROM build_base AS msieve
COPY unpackaged/msieve.sh /build/
RUN /build/msieve.sh

FROM build_base AS kamis
COPY unpackaged/kamis.sh /build/
RUN /build/kamis.sh

FROM build_base AS gclc
COPY unpackaged/gclc.sh /build/
RUN /build/gclc.sh

FROM build_base AS primality
COPY unpackaged/primality.sh /build/
RUN /build/primality.sh

FROM scratch AS unpackaged
COPY --from=kissat    /out /
COPY --from=plantri   /out /
COPY --from=prover9   /out /
COPY --from=msolve    /out /
COPY --from=cvc5      /out /
COPY --from=vampire   /out /
COPY --from=drat_trim /out /
COPY --from=cake_lpr  /out /
COPY --from=breakid   /out /
COPY --from=sms       /out /
COPY --from=march_cu  /out /
COPY --from=msieve    /out /
COPY --from=kamis     /out /
COPY --from=gclc      /out /
COPY --from=primality /out /

# --------------------------------------------------------------------------- #
# walnut: Walnut, the decision procedure for automatic sequences / base-k     #
# digit statements (Buechi arithmetic), built by walnut.sh and shipped as the #
# /opt/walnut tree; run via upstream's launcher /opt/walnut/walnut.sh. The    #
# JRE it needs comes from the agent stage's apt line (default-jre-headless).  #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS walnut

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates openjdk-17-jdk-headless git \
    && rm -rf /var/lib/apt/lists/*

COPY walnut.sh /build/
RUN /build/walnut.sh

# --------------------------------------------------------------------------- #
# julia: Julia + OSCAR/Hecke (computer algebra: Galois groups, number fields, #
# group theory) as a fully precompiled, offline-usable depot (julia.sh). Two  #
# directories are handed over: /opt/julia (the release) and /root/.julia (the #
# depot, at Julia's default location, so the agent image needs no             #
# JULIA_DEPOT_PATH plumbing). NEVER build this stage under qemu emulation:    #
# precompilation crashes there (native-only, both arches verified).           #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS julia

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY julia.sh /build/
RUN /build/julia.sh

# --------------------------------------------------------------------------- #
# loogle: the Loogle type-pattern Mathlib search CLI. Upstream's "Running     #
# locally" contract: the binary is dependency-free, must merely be built with #
# the TARGET project's toolchain, and then searches any Lake project via      #
# `lake env loogle --module <M> "<query>"` (it reads LEAN_PATH). The first    #
# query builds a search index cached next to the module's .olean and          #
# auto-invalidated when the oleans change; running one here bakes that index  #
# (and smoke-tests the build), so agents get fast queries.                    #
# --------------------------------------------------------------------------- #
FROM base AS loogle

ARG LOOGLE_COMMIT=9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0
RUN git clone https://github.com/nomeata/loogle.git /opt/loogle \
    && git -C /opt/loogle checkout --detach "${LOOGLE_COMMIT}" \
    && cp /workspace/leanproject/lean-toolchain /opt/loogle/lean-toolchain \
    && cd /opt/loogle \
    && lake build \
    && cd /workspace/leanproject \
    && lake env /opt/loogle/.lake/build/bin/loogle --module Mathlib "Nat.Prime" > /dev/null

# --------------------------------------------------------------------------- #
# agent: the agent's workspace, assembled from the chunks above (the header's #
# stage table). Layer order is big/stable first.                              #
# --------------------------------------------------------------------------- #
FROM base AS agent

# bookworm packages conda-forge lacks: polymake (polyhedral geometry), Macaulay2
# (commutative algebra), cryptominisat (SAT), coinor-csdp (semidefinite
# programming, `csdp`), topcom (triangulations), cadabra2 (tensor algebra),
# minizinc (CP modeling), berkeley-abc (Boolean networks), eprover (first-order
# ATP), mpsolve (certified polynomial roots); default-jre-headless runs Walnut;
# jq + ripgrep serve the bash tool (git is already in base); man-db + less make
# the packages' man pages readable; libmpfr6 is msolve's one runtime link the
# image would otherwise lack (gmp comes with base's libgmp-dev). bookworm-slim
# configures dpkg to drop /usr/share/doc and man pages; that rule goes first so
# these packages keep their documentation.
RUN rm /etc/dpkg/dpkg.cfg.d/docker \
    && apt-get update && apt-get install -y --no-install-recommends \
        polymake macaulay2 cryptominisat coinor-csdp \
        topcom cadabra2 minizinc berkeley-abc eprover mpsolve \
        default-jre-headless jq ripgrep man-db less libmpfr6 \
    && rm -rf /var/lib/apt/lists/*

# The chunks, each at its final path. Nothing in the two envs is on PATH; the
# agent reaches them through the symlinks made below.
COPY --from=conda      /opt/env     /opt/env
COPY --from=sage       /opt/sage    /opt/sage
COPY --from=julia      /opt/julia   /opt/julia
COPY --from=julia      /root/.julia /root/.julia
COPY --from=walnut     /opt/walnut  /opt/walnut
COPY --from=unpackaged /            /usr/local/

# Loogle: the dependency-free binary, its README, and the Mathlib search index
# it baked next to Mathlib.olean (COPY preserves mtimes, and this stage shares
# base's layers with loogle, so the index stays valid; were it ever judged
# stale, loogle transparently rebuilds it).
COPY --from=loogle /opt/loogle/.lake/build/bin/loogle /usr/local/bin/loogle
COPY --from=loogle /opt/loogle/README.md /usr/local/share/doc/loogle/README.md
COPY --from=loogle \
     /workspace/leanproject/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.loogle-index \
     /workspace/leanproject/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.loogle-index

# Exposure (header rule 4): agent-commands lists every command the agent gets
# from the envs, one absolute path per line, linked into /usr/local/bin. That
# directory precedes /usr/bin both in the image's PATH and in the PATH that
# Debian's /etc/profile resets login shells to (how the bash tool execs), so
# the links win over Debian's own python3/pip, which are present regardless
# (base installs python3-pip; cadabra2 depends on python3). `ln -s` refuses a
# name that already exists, so a collision between chunks fails the build;
# that every link resolves is asserted by tests/test_agent_image.py.
COPY agent-commands /build/agent-commands
RUN xargs -I{} ln -s {} /usr/local/bin/ < /build/agent-commands

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
