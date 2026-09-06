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
#                   conda-forge lacks, source-built and release-pinned solvers
#                   (`solvers_build`), Walnut (`walnut_build`), Julia with
#                   OSCAR/Hecke (`julia_build`), the Loogle Mathlib-search CLI
#                   (`loogle_build`), and per-tool docs downloaded from pinned
#                   upstream sources (`docs_fetch`) at /opt/docs. Deliberately
#                   contains NO verifier tooling (no comparator, no
#                   lean4export, no landrun).
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

# Shared pins: tools whose install AND whose /opt/docs documentation (the
# `docs_fetch` stage) must come from the SAME revision. Declared once here;
# stages redeclare `ARG <NAME>` (no value) to inherit these defaults, so a
# bump moves the tool and its docs together. Docs for tools pinned elsewhere
# (compute-env.yaml, bookworm's package table, the pip layer) hardcode the
# matching revision in docs_fetch with a comment naming the pin they mirror.
ARG MSOLVE_VERSION=0.10.1
ARG PLANTRI_VERSION=55
ARG DRATTRIM_VERSION=v05.22.2023
ARG BREAKID_VERSION=3.1.3
ARG SMS_VERSION=v2.1.1
ARG CAKE_LPR_COMMIT=a36874a8b750b43fe4b385b8ddbf5b033e46a3fa
ARG KAMIS_VERSION=v3.2
ARG GCLC_VERSION=v2026.1
ARG MSIEVE_VERSION=1.53

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

# build-essential: graphillion has no cp313 wheel, so its pip install below
# compiles the sdist (stage-local; the compiler does not ship).
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates bzip2 build-essential \
    && rm -rf /var/lib/apt/lists/*

ARG MICROMAMBA_VERSION=2.9.0
RUN arch="$(uname -m)" \
    && case "$arch" in x86_64) plat=linux-64 ;; aarch64) plat=linux-aarch64 ;; *) echo "unsupported arch $arch" >&2; exit 1 ;; esac \
    && curl -sSfL "https://micro.mamba.pm/api/micromamba/${plat}/${MICROMAMBA_VERSION}" \
        | tar -xj -C /usr/local bin/micromamba

COPY compute-env.yaml /tmp/compute-env.yaml
RUN micromamba create -y -p /opt/env -f /tmp/compute-env.yaml \
    && micromamba clean -afy

# PyPI-only packages, into the same env. snappy is SnapPy (3-manifold
# topology), not the compression lib. pyscipopt's wheel bundles libscip
# (SCIP via conda is impossible: every scip/soplex build wants a boost newer
# than the sage stack's pin). graphillion compiles from sdist (no cp313
# wheel; verified clean on py3.13, both arches).
RUN /opt/env/bin/pip install --no-cache-dir \
        python-sat==1.9.dev15 \
        cvc5==1.3.4 \
        ortools==9.15.6755 \
        snappy==3.3.2 \
        pysindy==2.1.0 \
        hypothesis==6.165.10 \
        libsemigroups_pybind11==1.4.4 \
        pymanopt==2.2.1 \
        graphillion==2.1 \
        pyscipopt==6.2.1 \
    && find /opt/env -name '__pycache__' -type d -prune -exec rm -rf {} +

# --------------------------------------------------------------------------- #
# solvers_build: tools with no conda-forge or bookworm packaging, built from   #
# pinned sources (plus pinned official release binaries: cvc5 static, whose    #
# PyPI wheel in compute_build carries only the python API; vampire; cake_lpr;  #
# and the x86-only LLR/PFGW primality provers). Everything lands in /out/bin   #
# and links only the libc family, libstdc++, and zlib from the shared          #
# bookworm userland (flint/gmp/mpfr are linked statically), so the binaries    #
# drop straight into agent.                                                    #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS solvers_build

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates build-essential unzip m4 \
        cmake git subversion p7zip perl zlib1g-dev \
        libboost-graph-dev libboost-program-options-dev \
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
ARG PLANTRI_VERSION
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
ARG MSOLVE_VERSION
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

# vampire: superposition first-order prover + finite-model builder (--mode
# fmb), official pinned release binaries (link only libc/libstdc++).
ARG VAMPIRE_VERSION=v5.1.0
RUN arch="$(uname -m)" \
    && case "$arch" in \
         x86_64)  z=vampire-Linux-X64.zip;   sha=495828dc76cb17a27080d62dedce755e46de96f47f06f5f0ad4be9cdaf6f968f ;; \
         aarch64) z=vampire-Linux-ARM64.zip; sha=7abc39224fdf41bdb2c241f8b180a80b7c1a4bce1e46dc79df02cfea2798ad5c ;; \
         *) echo "unsupported arch $arch" >&2; exit 1 ;; \
       esac \
    && curl -sSfL -o /tmp/vampire.zip \
        "https://github.com/vprover/vampire/releases/download/${VAMPIRE_VERSION}/${z}" \
    && echo "${sha}  /tmp/vampire.zip" | sha256sum -c - \
    && unzip -q /tmp/vampire.zip -d /tmp/vampire \
    && install -m 755 "$(find /tmp/vampire -type f -name vampire)" /out/bin/vampire \
    && rm -rf /tmp/vampire /tmp/vampire.zip

# drat-trim + lrat-check: proof checkers for SAT solvers' UNSAT certificates
# (DRAT from kissat/cryptominisat; DRAT->LRAT conversion).
ARG DRATTRIM_VERSION
RUN curl -sSfL "https://github.com/marijnheule/drat-trim/archive/refs/tags/${DRATTRIM_VERSION}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/drat-trim-* \
    && make \
    && install -m 755 drat-trim lrat-check /out/bin/ \
    && rm -rf /tmp/drat-trim-*

# cake_lpr: formally verified LRAT proof checker (CakeML); built from the
# repo's pre-generated per-arch assembly with one gcc call.
ARG CAKE_LPR_COMMIT
RUN curl -sSfL "https://github.com/tanyongkiam/cake_lpr/archive/${CAKE_LPR_COMMIT}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/cake_lpr-* \
    && case "$(uname -m)" in x86_64) s=cake_lpr.S ;; aarch64) s=cake_lpr_arm8.S ;; esac \
    && gcc -O2 -std=c99 basis_ffi.c "$s" -o /out/bin/cake_lpr \
    && rm -rf /tmp/cake_lpr-*

# BreakID: static CNF symmetry breaking (preprocessor for SAT searches).
ARG BREAKID_VERSION
RUN git clone --depth 1 --branch "release/${BREAKID_VERSION}" \
        https://github.com/meelgroup/breakid /tmp/breakid \
    && cmake -S /tmp/breakid -B /tmp/breakid/build -DCMAKE_BUILD_TYPE=Release \
    && cmake --build /tmp/breakid/build -j"$(nproc)" \
    && install -m 755 /tmp/breakid/build/breakid /out/bin/breakid \
    && rm -rf /tmp/breakid

# SMS (smsg): SAT-modulo-symmetries graph search -- find/enumerate graphs with
# a property, modulo isomorphism. CaDiCaL is bundled as a pinned submodule.
ARG SMS_VERSION
RUN git clone --depth 1 --branch "${SMS_VERSION}" --recurse-submodules \
        https://github.com/markirch/sat-modulo-symmetries /tmp/sms \
    && cd /tmp/sms/cadical_sms && ./configure -fPIC && make -j"$(nproc)" \
    && cd /tmp/sms \
    # static boost so the binary keeps to the shared bookworm userland
    && cmake -B build -S . -DCMAKE_BUILD_TYPE=Release -DBoost_USE_STATIC_LIBS=ON \
    && cmake --build build -j"$(nproc)" \
    && install -m 755 build/src/smsg /out/bin/smsg \
    && rm -rf /tmp/sms

# march_cu: cube-and-conquer splitter for hard SAT instances (Heule's CnC;
# no tags upstream, commit-pinned). -fcommon: pre-C99 tentative definitions.
ARG MARCH_CU_COMMIT=705b60c6491ef2b61988b3ce6ac674be1b90571d
RUN curl -sSfL "https://github.com/marijnheule/CnC/archive/${MARCH_CU_COMMIT}.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/CnC-*/march_cu \
    && make CFLAGS='-O3 -fno-strict-aliasing -Wall -DNDEBUG -fcommon' \
    && install -m 755 march_cu /out/bin/march_cu \
    && rm -rf /tmp/CnC-*

# msieve: SIQS/NFS integer factorization past gmp-ecm's reach. OPT_FLAGS
# overrides the Makefile's -march=native so the binary is portable.
ARG MSIEVE_VERSION
RUN curl -sSfL "https://downloads.sourceforge.net/project/msieve/msieve/Msieve%20v${MSIEVE_VERSION}/msieve$(echo "${MSIEVE_VERSION}" | tr -d .)_src.tar.gz" \
        | tar xz -C /tmp \
    && cd /tmp/msieve-* \
    && make all -j"$(nproc)" OPT_FLAGS='-O3 -fomit-frame-pointer -D_FILE_OFFSET_BITS=64 -DNDEBUG' \
    && install -m 755 msieve /out/bin/msieve \
    && rm -rf /tmp/msieve-*

# redumis (KaMIS): near-optimal maximum independent sets at scales exact
# solvers can't reach (KaHIP is vendored in the release tarball).
ARG KAMIS_VERSION
RUN curl -sSfL "https://github.com/KarlsruheMIS/KaMIS/archive/refs/tags/${KAMIS_VERSION}.tar.gz" \
        | tar xz -C /tmp \
    && cmake -S /tmp/KaMIS-* -B /tmp/kamis-build -DCMAKE_BUILD_TYPE=Release \
    && cmake --build /tmp/kamis-build -j"$(nproc)" --target redumis \
    && install -m 755 /tmp/kamis-build/redumis /out/bin/redumis \
    && rm -rf /tmp/KaMIS-* /tmp/kamis-build

# gclc: automated Euclidean geometry proving (area/Wu methods; CLI only).
ARG GCLC_VERSION
RUN git clone --depth 1 --branch "${GCLC_VERSION}" https://github.com/janicicpredrag/gclc /tmp/gclc \
    && cmake -S /tmp/gclc -B /tmp/gclc/build -DCMAKE_BUILD_TYPE=Release -Dgui=OFF \
    && cmake --build /tmp/gclc/build -j"$(nproc)" \
    && install -m 755 /tmp/gclc/build/gclc /out/bin/gclc \
    && rm -rf /tmp/gclc

# The special-form primality toolchain, amd64 images only (CI/production):
# srsieve2 sieves k*b^n+-c candidate grids (mtsieve suite; SourceForge SVN,
# revision-pinned; its makefile only knows x86 and 32-bit ARM), then sllr64
# (LLR) and pfgw64 (OpenPFGW) prove primality at 10^5..10^7 digits (gwnum is
# x86-64 assembly -- no arm route exists).
ARG MTSIEVE_SVN_REV=469
ARG LLR_VERSION=407
ARG PFGW_VERSION=4.1.8
RUN if [ "$(uname -m)" = x86_64 ]; then \
      svn checkout -q -r "${MTSIEVE_SVN_REV}" https://svn.code.sf.net/p/mtsieve/svn/ /tmp/mtsieve \
      && cd /tmp/mtsieve \
      && make -j"$(nproc)" srsieve2 \
      && install -m 755 srsieve2 /out/bin/srsieve2 \
      && rm -rf /tmp/mtsieve; \
    fi
RUN if [ "$(uname -m)" = x86_64 ]; then \
      # jpenne.free.fr is HTTP-only; integrity comes from the sha256 pin.
      curl -sSfL -o /tmp/llr.zip "http://jpenne.free.fr/llr4/llr${LLR_VERSION}slinux64.zip" \
      && echo "b92424d85d0d37788bb33613ec1af2b6d5cb1f5ce37be5ed062b0aad604a6ab3  /tmp/llr.zip" | sha256sum -c - \
      && unzip -q /tmp/llr.zip -d /tmp/llr \
      && install -m 755 "$(find /tmp/llr -type f -name sllr64)" /out/bin/sllr64 \
      && curl -sSfL -o /tmp/pfgw.7z "https://downloads.sourceforge.net/project/openpfgw/pfgw_linux_${PFGW_VERSION}.7z" \
      && echo "aadf885e2d6489866bb7eeea2ba3f75a3fa02e679f1d6a86fd2632e042a99c99  /tmp/pfgw.7z" | sha256sum -c - \
      && 7zr x -o/tmp/pfgw /tmp/pfgw.7z >/dev/null \
      && install -m 755 /tmp/pfgw/pfgw64 /out/bin/pfgw64 \
      && rm -rf /tmp/llr /tmp/llr.zip /tmp/pfgw /tmp/pfgw.7z; \
    fi

# --------------------------------------------------------------------------- #
# walnut_build: Walnut, the decision procedure for automatic sequences /       #
# base-k digit statements (Buechi arithmetic). Java; built once with the       #
# repo's own gradle wrapper, shipped as the /opt/walnut tree and run via       #
# upstream's launcher: /opt/walnut/walnut.sh (JRE comes from the agent         #
# stage's default-jre-headless).                                               #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS walnut_build

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates openjdk-17-jdk-headless git \
    && rm -rf /var/lib/apt/lists/*

# Upstream's build.sh is its gradle invocation + chmod, followed by an
# interactive "Press enter" prompt that exits 1 in a non-interactive build --
# so run those two commands directly.
ARG WALNUT_VERSION=v7.1.0
RUN curl -sSfL "https://github.com/Walnut-Theorem-Prover/Walnut/archive/refs/tags/${WALNUT_VERSION}.tar.gz" \
        | tar xz -C /opt \
    && mv /opt/Walnut-* /opt/walnut \
    && cd /opt/walnut \
    && ./gradlew clean customFatJar \
    && chmod +x walnut.sh \
    && rm -rf /root/.gradle

# --------------------------------------------------------------------------- #
# julia_build: Julia + OSCAR/Hecke (computer algebra: Galois groups, number    #
# fields, group theory) as a fully precompiled, offline-usable depot. The      #
# multi-target JULIA_CPU_TARGET (the same lists the official binaries use)     #
# makes the baked pkgimages load on any deploy CPU. NEVER build this stage     #
# under qemu emulation: precompilation crashes there (native-only, both        #
# arches verified for artifact coverage).                                      #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS julia_build

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# sha256s from https://julialang-s3.julialang.org/bin/checksums/julia-1.12.7.sha256
ARG JULIA_VERSION=1.12.7
RUN arch="$(uname -m)" \
    && case "$arch" in \
         x86_64)  a=x64/1.12/julia-${JULIA_VERSION}-linux-x86_64.tar.gz; \
                  sha=4e7e9e776634d24835250de67cde39b0d4af15bc432eb20697e6be6c28ea69e8 ;; \
         aarch64) a=aarch64/1.12/julia-${JULIA_VERSION}-linux-aarch64.tar.gz; \
                  sha=9243c0b524c7f300883240a1ee5ea3916a30e070bff718acf8ccaee31a731ef2 ;; \
         *) echo "unsupported arch $arch" >&2; exit 1 ;; \
       esac \
    && curl -fsSL "https://julialang-s3.julialang.org/bin/linux/${a}" -o /tmp/julia.tar.gz \
    && echo "${sha}  /tmp/julia.tar.gz" | sha256sum -c - \
    && mkdir -p /opt/julia \
    && tar -xzf /tmp/julia.tar.gz -C /opt/julia --strip-components=1 \
    && rm /tmp/julia.tar.gz

ENV JULIA_DEPOT_PATH=/opt/julia-depot
ARG OSCAR_VERSION=1.8.1
ARG HECKE_VERSION=0.39.22
RUN case "$(uname -m)" in \
         x86_64)  export JULIA_CPU_TARGET='generic;sandybridge,-xsaveopt,clone_all;haswell,-rdrnd,base(1);x86-64-v4,-rdrnd,base(1)' ;; \
         aarch64) export JULIA_CPU_TARGET='generic;cortex-a57;thunderx2t99;carmel,clone_all;apple-m1,base(3);neoverse-512tvb,-rand,-fpac,base(3)' ;; \
       esac \
    && /opt/julia/bin/julia -e "using Pkg; Pkg.add([ \
           PackageSpec(name=\"Oscar\", version=\"${OSCAR_VERSION}\"), \
           PackageSpec(name=\"Hecke\", version=\"${HECKE_VERSION}\")]); \
         Pkg.precompile(); Pkg.gc()" \
    # The depot must be complete: loading may not touch the network.
    && JULIA_PKG_OFFLINE=true /opt/julia/bin/julia -e \
         'using Oscar; using Hecke; println("Oscar ", Oscar.VERSION_NUMBER)'

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
# docs_fetch: in-sandbox references at /opt/docs/<tool>, DOWNLOADED at build   #
# from pinned sources (never vendored in the repo, never PDFs, always the     #
# upstream files verbatim). Each fetch is pinned to the revision the image    #
# actually installs: shared ARGs (top of file) where the install is ARG-      #
# pinned, hardcoded matching revisions (with the mirrored pin named in a      #
# comment) where the install pin lives in compute-env.yaml / bookworm / the   #
# pip layer. Tools whose only docs are PDFs or mutable webpages ship          #
# undocumented (their --help still works).                                    #
# --------------------------------------------------------------------------- #
FROM debian:bookworm-slim AS docs_fetch

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates git \
    && rm -rf /var/lib/apt/lists/*

# Single-file fetches from pinned raw URLs.
ARG DRATTRIM_VERSION
ARG BREAKID_VERSION
ARG CAKE_LPR_COMMIT
ARG KAMIS_VERSION
ARG GCLC_VERSION
ARG MSOLVE_VERSION
# Must equal loogle_build's LOOGLE_COMMIT.
ARG LOOGLE_DOCS_COMMIT=9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0
RUN set -e; \
    fetch() { mkdir -p "/opt/docs/$1" && curl -sSfL -o "/opt/docs/$1/$2" "$3"; }; \
    fetch loogle README.md "https://raw.githubusercontent.com/nomeata/loogle/${LOOGLE_DOCS_COMMIT}/README.md"; \
    fetch loogle blurb.md "https://raw.githubusercontent.com/nomeata/loogle/${LOOGLE_DOCS_COMMIT}/blurb.md"; \
    fetch msolve msolve-tutorial.tex "https://raw.githubusercontent.com/algebraic-solving/msolve/v${MSOLVE_VERSION}/doc/msolve-tutorial.tex"; \
    fetch drat-trim README.md "https://raw.githubusercontent.com/marijnheule/drat-trim/${DRATTRIM_VERSION}/README.md"; \
    fetch breakid README.md "https://raw.githubusercontent.com/meelgroup/breakid/release/${BREAKID_VERSION}/README.md"; \
    fetch cake_lpr README.md "https://raw.githubusercontent.com/tanyongkiam/cake_lpr/${CAKE_LPR_COMMIT}/README.md"; \
    fetch kamis README.md "https://raw.githubusercontent.com/KarlsruheMIS/KaMIS/${KAMIS_VERSION}/README.md"; \
    fetch gclc gclc_man.tex "https://raw.githubusercontent.com/janicicpredrag/gclc/${GCLC_VERSION}/manual/gclc_man.tex"; \
    # matches bookworm coinor-csdp 6.2.0-4
    fetch csdp csdpuser.tex "https://raw.githubusercontent.com/coin-or/Csdp/releases/6.2.0/doc/csdpuser.tex"; \
    # matches the pip layer's graphillion==2.1
    fetch graphillion README.md "https://raw.githubusercontent.com/takemaru/graphillion/v2.1/README.md"; \
    # matches compute-env.yaml 4ti2=1.6.15
    for f in 4ti2_manual 4ti2_manual_beginner 4ti2_manual_advanced 4ti2_manual_ref 4ti2_manual_api; do \
        fetch 4ti2 "$f.tex" "https://raw.githubusercontent.com/4ti2/4ti2/Release_1_6_15/doc/$f.tex"; \
    done

# Tag-pinned clones where the docs are a file set.
ARG SMS_VERSION
RUN set -e; \
    clonedocs() { git clone -q --depth 1 --branch "$2" "$1" /tmp/d && mkdir -p "/opt/docs/$3"; }; \
    # matches solvers_build's SMS_VERSION
    clonedocs https://github.com/markirch/sat-modulo-symmetries "${SMS_VERSION}" sms \
        && cp /tmp/d/docs/*.md /opt/docs/sms/ && rm -rf /tmp/d; \
    # matches compute-env.yaml normaliz=3.11.0
    clonedocs https://github.com/Normaliz/Normaliz v3.11.0 normaliz \
        && cp /tmp/d/doc/*.tex /tmp/d/README.md /opt/docs/normaliz/ && rm -rf /tmp/d; \
    # matches the pip layer's snappy==3.3.2 (SnapPy)
    clonedocs https://github.com/3-manifolds/SnapPy 3.3.2_as_released snappy \
        && cp /tmp/d/doc_src/*.rst /opt/docs/snappy/ && rm -rf /tmp/d; \
    # matches compute-env.yaml python-flint=0.8.0
    clonedocs https://github.com/flintlib/python-flint 0.8.0 python-flint \
        && cp /tmp/d/doc/source/*.rst /opt/docs/python-flint/ && rm -rf /tmp/d; \
    # matches bookworm regina-normal 7.3 (handbook source; DocBook is text)
    clonedocs https://github.com/regina-normal/regina regina-7.3 regina \
        && cp /tmp/d/qtui/doc/regina/*.docbook /opt/docs/regina/ && rm -rf /tmp/d

# Tarball-shipped docs (same tarballs the installs use).
ARG PLANTRI_VERSION
RUN set -e; \
    mkdir -p /opt/docs/plantri /opt/docs/lrslib /opt/docs/msieve; \
    curl -sSfL "https://users.cecs.anu.edu.au/~bdm/plantri/plantri${PLANTRI_VERSION}.tar.gz" | tar xz -C /tmp \
        && cp /tmp/plantri*/plantri-guide.txt /opt/docs/plantri/ && rm -rf /tmp/plantri*; \
    # matches compute-env.yaml lrslib=73.a
    curl -sSfL "https://cgm.cs.mcgill.ca/~avis/C/lrslib/archive/lrslib-073a.tar.gz" | tar xz -C /tmp \
        && cp -r /tmp/lrslib-073a/man/html /opt/docs/lrslib/man-html \
        && cp /tmp/lrslib-073a/README /opt/docs/lrslib/ && rm -rf /tmp/lrslib-073a; \
    curl -sSfL "https://downloads.sourceforge.net/project/msieve/msieve/Msieve%20v1.53/msieve153_src.tar.gz" | tar xz -C /tmp \
        && cp /tmp/msieve-*/Readme* /opt/docs/msieve/ && rm -rf /tmp/msieve-*

# Walnut's per-command help ships inside the same build the image runs.
COPY --from=walnut_build /opt/walnut/README.md /opt/docs/walnut/README.md
COPY --from=walnut_build ["/opt/walnut/Help Documentation/Commands", "/opt/docs/walnut/commands"]

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

# Julia with the precompiled OSCAR/Hecke depot (see julia_build). The depot
# path must match the build-time one or every load re-precompiles.
COPY --from=julia_build /opt/julia /opt/julia
COPY --from=julia_build /opt/julia-depot /opt/julia-depot
ENV JULIA_DEPOT_PATH=/opt/julia-depot
RUN ln -s /opt/julia/bin/julia /usr/local/bin/julia \
    && echo 'export JULIA_DEPOT_PATH=/opt/julia-depot' > /etc/profile.d/julia.sh

# Tools conda-forge lacks, from bookworm: polymake (polyhedral geometry),
# Macaulay2 (commutative algebra), regina-normal (low-dimensional topology;
# `regina-python`), cryptominisat (SAT, newer here than conda-forge's),
# coinor-csdp (semidefinite programming, `csdp`), topcom (triangulations),
# cadabra2 (tensor algebra), minizinc (CP modeling), berkeley-abc (Boolean
# networks), eprover (first-order ATP), mpsolve (certified polynomial roots),
# default-jre-headless (runs Walnut), jq + ripgrep for the bash tool (git is
# already in `base`), libmpfr6 (msolve's one non-static runtime link besides
# gmp, which base's libgmp-dev already provides).
RUN apt-get update && apt-get install -y --no-install-recommends \
        polymake macaulay2 regina-normal cryptominisat coinor-csdp \
        topcom cadabra2 minizinc berkeley-abc eprover mpsolve \
        default-jre-headless jq ripgrep libmpfr6 \
    && rm -rf /var/lib/apt/lists/*

# Source-built and release-pinned solver binaries (see solvers_build).
COPY --from=solvers_build /out/bin/ /usr/local/bin/

# Walnut (automatic-sequence decision procedure): upstream's own tree and
# launcher, run as /opt/walnut/walnut.sh (java from apt above).
COPY --from=walnut_build /opt/walnut /opt/walnut

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

# In-sandbox references (the sandbox has no network): version-matched upstream
# docs, downloaded at build (see docs_fetch). Last: docs churn more than any
# layer above.
COPY --from=docs_fetch /opt/docs /opt/docs

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
