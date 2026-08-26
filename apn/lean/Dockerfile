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
#   - agent      -- the agent's workspace: base + PyPantograph + numerical
#                   Python libs. Deliberately contains NO verifier tooling (no
#                   comparator, no lean4export, no landrun).
#   - comparator -- the trusted verifier: base + the Comparator binary + the
#                   lean4export binary + landrun + the pristine workspace tree.
#                   Replaces the former `compile` + `scorer` pair: the
#                   untrusted `lake build Solution` is confined by landrun
#                   (Landlock) *inside* this container, which runs as a
#                   non-privileged user (comparator README assumption 6).
#
# Version story (comparator-migration-plan.md §2). Four version-bearing
# artifacts, deliberately NOT all on one toolchain:
#
#   - The FC project (statements, Mathlib, oleans) is pinned by the dataset's
#     FC_COMMIT and builds with its own lean-toolchain (v4.27.0 today). This is
#     dataset identity; PyPantograph's repl must match it (oleans load only
#     under the toolchain that built them).
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
# On an FC-pin bump: PyPantograph and the exporter's toolchain move with it.
# On a comparator bump: move LEAN4EXPORT_COMMIT to the rev in comparator's
# lake-manifest.json, re-verify the toolchain-override build, and re-run the
# primitive-constants check (plan §2.3; the gold-proof suite exercises it).
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
# need (the agent builds PyPantograph; the comparator image builds lean4export)
# and python3 (the agent uses it to drive PyPantograph and as a numerical
# scratchpad).
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential libgmp-dev \
        python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*

# The Lean/lake toolchain (binaries + the project toolchain). The image ENV PATH
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
# Runs as the non-privileged `comparator` user (comparator README assumption   #
# 6): landrun (Landlock) confines the untrusted solution build to writes in    #
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

# The runtime exporter (project toolchain; RPATH resolves via base's install).
COPY --from=lean4export_build /opt/lean4export/.lake/build/bin/lean4export \
                              /opt/apn/lean4export/bin/lean4export

COPY --from=landrun_build /out/landrun /usr/local/bin/landrun

# Comparator resolves its helper binaries through these (see its README); the
# checker also passes them explicitly on every exec.
ENV COMPARATOR_LEAN4EXPORT=/opt/apn/lean4export/bin/lean4export \
    COMPARATOR_LANDRUN=/usr/local/bin/landrun

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

USER comparator
ENV HOME=/home/comparator

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
