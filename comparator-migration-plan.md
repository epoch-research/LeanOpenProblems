# Plan: switch proof verification from SafeVerify to Comparator

Status: proposal, 2026-08-21; last updated 2026-08-24 (resolved decisions in
§8, in-file disproofs in §4). Written against `apn` at a08ae16 and the local
`reference_sources/` checkouts of Comparator (19e111e, tag v4.34.0-rc2),
lean4export (cacf989, master), and SafeVerify.

## 0. Why switch (recap)

- The paper already commits to it: "Future versions of this benchmark will use
  Comparator."
- Comparator is maintained by Lean FRO with an explicit adversarial threat
  model (built for AIMO/Kaggle), has an actively fixed soundness history, and
  a second-kernel (nanoda) option.
- It structurally avoids SafeVerify's worst operational problem (TODO.md bug
  #1): SafeVerify materializes the full Mathlib environment ~4x via
  `importModules` (~27 GiB) and deep-copies proof terms without memoization
  (unbounded; 43 GiB seen in production; `mem_limit: 50g`). Comparator never
  loads oleans in the trusted process: it consumes lean4export's *text* export,
  which serializes terms as a shared DAG (every subterm emitted once, by
  index), and replays that through the kernel. The two proofs SafeVerify
  rejected only on resource limits passed under Comparator.
- Comparator's design lets us drop the separate `compile` container: the
  untrusted build is confined by landrun (Landlock) *inside* the verifier
  container, which is exactly the consolidation to 2 containers we want.

## 1. How Comparator verifies (what we're adopting)

Per check, `comparator config.json` (run under the project's `lake env`, cwd =
project root) does:

1. `lake build Challenge` in a landrun sandbox (read+exec everything, write
   only `.lake` and `/dev`).
2. `lean4export Challenge -- <targets>` in a landrun sandbox (no writes) →
   challenge export (text, held in comparator's memory). Targets = the
   configured `theorem_names` + `permitted_axioms` + builtin/primitive
   constants (`Nat`, `Quot.*`, `Nat.add..Nat.shiftRight`, `String.ofList`,
   `Char.ofNat`, `List`, `eagerReduce`, ...).
3. Same two steps for `Solution`. Ordering matters: everything trusted is
   built and exported *before* any agent code runs.
4. `compareAt`: for each target theorem, challenge and solution must both be
   theorems with BEq-equal name/levelParams/type. Then it walks the statement
   closure (types *and* definition values, transitively, via
   `runForUsedConsts`): every reachable constant must be **fully identical**
   (values included) between the two environments. So redefining anything the
   statement depends on is caught; the statement's meaning is pinned, not just
   its surface type.
5. `checkAxioms`: the transitive closure of the solution theorem's proof may
   use only `permitted_axioms` (so `sorryAx`, `Lean.ofReduceBool`
   (native_decide), and custom axioms all reject).
6. Kernel replay: the entire solution export (statement + proof closure,
   i.e. the used slice of Mathlib too) is replayed through the Lean kernel
   embedded in the comparator binary (`Kernel.Environment.replay`), with a
   post-check that the `Quot` constants match the replayed ones (the
   "quot trick" fix). Optionally also through external kernels (nanoda).

Verdict = exit code 0 and it prints "Your solution is okay!". Any failure
throws with a message on stderr and a nonzero exit.

Key structural differences from SafeVerify, all deliberate:

| | SafeVerify (current) | Comparator |
|---|---|---|
| Input | two compiled oleans | Lean **sources**; it drives lake + lean4export itself |
| Statement match | every decl in the target *module*, by exact name (hence the same-module-name compile hack for private/mangled names) | closure of the *configured* theorem names only; module names of challenge/solution differ by design |
| Def bodies | equal, `sorry` stubs fillable | equal (holes only via explicit `definition_names`, which we don't use) |
| Disproofs | built-in `foo.disproof`, checked by **kernel defeq** against `mkNot type` | none — we must construct the negated challenge ourselves; match is **syntactic** (BEq on export-parsed terms, mdata stripped) |
| Import discipline | submission imports ⊆ target imports enforced | not needed: everything reachable is replayed, extra imports can't taint the target's closure |
| Unsafe/partial consts | rejected outright | unsafe decls aren't exported (inert); sound because kernel replay covers everything reachable |
| Kernel replay scope | the two modules' own decls (imports trusted from local oleans) | the full exported closure, incl. the used slice of Mathlib |
| Untrusted-code confinement | separate throwaway `compile` container | landrun (Landlock) sandbox inside the verifier container |

## 2. The version matrix (the core reasoning)

There are **four** version-bearing artifacts and they cannot all be the same
version. Getting this wrong silently breaks either soundness or everything.

| Artifact | Pin | Toolchain it's built with | Why |
|---|---|---|---|
| FC project (statements, Mathlib, oleans) | `fc_commit` = 67338a15 per dataset (unchanged) | **v4.27.0** | Dataset identity. The benchmark's statements are frozen at this pin; changing it is a new dataset version, out of scope. |
| lean4export **binary** (runtime exporter) | upstream cacf989, unmodified; `lean-toolchain` overwritten to the FC toolchain at image build | **v4.27.0** | It `importModules`-loads the project's oleans in-process. Oleans are loadable only by the exact toolchain that built them. Non-negotiable. |
| Comparator binary | 19e111e (= tag v4.34.0-rc2; pin the commit, tags are mutable) | **v4.34.0-rc2** (its own `lean-toolchain`) | See "why not v4.27.0 tag" below. It never loads project oleans (parses text, `mkEmptyEnvironment` only), so it does not need the project toolchain. |
| lean4export **library** (`Export.Parse`, compiled into comparator) | cacf989, pinned by comparator's own `lake-manifest.json` | v4.34.0-rc2 | Comes with the comparator build; defines the export format the comparator can read. |

### 2.1 Why comparator cannot be the toolchain-matched v4.27.0 tag

Comparator has per-Lean-release tags (v4.25.0-rc2 … v4.34.0-rc2), so
"pin comparator@v4.27.0, everything on one toolchain" looks attractive. It is
wrong:

- Tags are cut along master; **v4.27.0 (2026-01-24) is 93 commits behind** and
  predates a series of soundness fixes: the opaque-value fix (a4f6968), the
  `Char.ofNat` redefinition fix (8c0e44e), the Quot-trick fix (#74, landed
  between v4.34.0-rc1 and rc2), fixes for issues #64/#67/#68/#71, the
  `proj_trick` and `def_hole_kind_mismatch` classes, delayed kernel rejection,
  and the definition-hole feature. Running a verifier with known, publicly
  documented soundness holes is disqualifying. Because fixes land at tip only
  (no backport branches), **the comparator pin is effectively forced to the
  newest tag**, today v4.34.0-rc2.
- v4.27.0-tag comparator also predates the new export format (it still carried
  its own 526-line `Parser.lean`, deleted in "upgrade to new export format",
  83a2c98), so it would additionally chain us to the old format.

### 2.2 Why the exporter is built with a toolchain override (the format trap)

This is **not a fork** — it is compiling an unmodified upstream lean4export
commit under the project's (older) toolchain. Why some bridging is needed at
all:

- The exporter must be built at v4.27.0 (olean loading, above). Upstream's
  `bump_to_v4.27.0` branch **emits format 3.0.0** (`axiomInfo`/`quotInfo`
  keys, `def` as a mixed array, etc.).
- Comparator@19e111e parses with `Export.Parse`@cacf989, which **hard-fails on
  3.0.0 shapes** ("Unknown export object with keys …"): it matches only the
  3.1.0 keys (`axiom`, `def`, `thm`, `opaque`, `quot`, `inductive`). It does
  *not* check the metadata version line (skips it blindly) — the shapes are
  the contract.
- No unmodified upstream commit threads the needle: the format restructure
  (a6a63cc, 2026-02-03) landed with the repo already on v4.28.0-rc1, and
  Export.lean is unchanged from d17578b (v4.31.0-rc1 era) through cacf989. So
  there is no rev with the new format *and* a v4.27.0 toolchain file.
- Resolution: **clone upstream at cacf989 (the exact rev comparator's
  manifest pins) and overwrite `lean-toolchain` with the dataset toolchain at
  image build** (one `echo`, from the existing `LEAN_VERSION` build arg), then
  `lake build lean4export`. Emitter and parser then agree byte-for-byte by
  construction. The compile surface is small and old-API — the exe target
  builds only Main.lean + Export.lean (Export/Parse.lean is not in the exe's
  import closure), and most of Export.lean is shared verbatim with the 4.27
  branch. A clean 4.27 build is likely and verified in minutes at first image
  build. Only if it breaks do we patch — and only then does repo policy
  require vendoring the modified source.

### 2.3 Compile-time vs runtime, spelled out

Two images ship (§3): the **agent image** (compose service `default`) and the
**comparator image** (compose service `comparator`, the trusted verifier).
The agent image carries exactly one toolchain — the project's v4.27.0 — and
none of the verifier tooling (no comparator binary, no lean4export, no
landrun), unchanged from today. Everything below is about the **comparator
image**, which carries **two** toolchains:

- **In the comparator image, the project toolchain (v4.27.0) is what runs at
  scoring time** for: `lake env` (the wrapper the checker invokes the
  comparator binary under), `lake build Challenge/Solution` (elan resolves
  via the project's `lean-toolchain` file; `lake env` also puts that
  toolchain's bin first on PATH), `lean --print-prefix` (comparator's
  `queryLeanPrefix`), and the lean4export binary (built at v4.27.0; finds its
  libleanshared via its RPATH and its sysroot via PATH).
- **The comparator image additionally contains the comparator binary's own
  toolchain (v4.34.0-rc2), solely so that binary can run**: lake-built
  executables link the building toolchain's shared libraries (verify once
  with `ldd`; keep the toolchain installed via elan regardless — ~1.5 GB, the
  binary's RPATH points into the elan toolchain path where it was built, so
  build it in-image at that same path). Nothing else in the comparator image
  uses v4.34.0-rc2, and no `lake`/`lean` invocation at scoring time resolves
  to it (elan dispatches by the project's `lean-toolchain`; the comparator
  binary is invoked by absolute path). Two toolchains in the comparator image
  is correct and necessary, not an accident to "fix". The v4.34.0-rc2
  toolchain never appears in the agent image.
- **Kernel replay is cross-version** (inside the comparator binary, in the
  comparator image): the v4.34.0-rc2 kernel checks an environment elaborated
  by v4.27.0. Soundness-wise this is the safe
  direction (the checking kernel is ours and newer; it re-derives everything).
  The residual risk is **false negatives** (newer kernel stricter on some
  corner). Evidence it's fine: the paper's own cross-check re-verified all
  Claude Opus 4.8 submissions with a ~v4.33-era comparator against the v4.27
  environments (144 accepts). We re-validate over the full historical corpus
  (§7) anyway.
- **Primitive-constants invariant** (a real trap we checked, currently fine):
  comparator's `primitiveTargets`/`builtinTargets` (`eagerReduce`,
  `Char.ofNat`, `String.ofList`, `List`, `Nat.*`, `Quot.*`, …) are looked up
  in *both* environments and export is asked for them by name; a missing one
  fails **every** check (lean4export even panics on missing constants —
  comparator does not pass `--ignore-missing`). `eagerReduce` entered Lean
  core in Aug 2025 (kernel proof-by-reflection hint, lean4 #9865), well before
  v4.27.0 (Jan 2026), so all of today's list exists at 4.27.
  **Invariant to document and test: on every comparator bump, assert every
  primitive/builtin target resolves in the dataset toolchain's environment**
  (cheap: run the gold-proof suite; a violation rejects everything loudly).
- **Coupled-pin invariant**: the exporter's pinned rev must equal the rev in
  comparator's `lake-manifest.json` (today cacf989). On a comparator bump,
  move the exporter pin with it (the format may move, e.g. 3.1.0 → 3.2.0) and
  re-verify the toolchain-override build. When a future dataset's FC pin
  reaches a toolchain whose upstream lean4export state already emits the
  format comparator reads, the override becomes a no-op — check on each
  dataset bump.

## 3. Target architecture: two containers

Compose services (per sample, no network, as today):

- **`default` (agent)** — unchanged image and UX. The agent still works on
  `/workspace/leanproject/Submission/Spec.lean`; prompts, tools, Pantograph,
  Sage all unchanged. It never contains comparator/lean4export/landrun.
- **`comparator` (trusted verifier)** — replaces both `compile` and `scorer`.
  Contents (new Dockerfile stage `comparator` FROM `base`):
  - the FC project + prebuilt `.lake` (from `base`, as today);
  - lakefile registered with two extra libs, done in the **builder** before
    `lake build` so lake's config cache and traces are settled at image build:
    `[[lean_lib]] name = "Challenge" srcDir = "run"` and likewise `Solution`
    (plus stub `run/Challenge.lean`/`run/Solution.lean` and a warm
    `lake build Challenge Solution` so runtime never re-resolves config);
  - comparator binary built at its own toolchain (clone at pinned commit
    19e111e, `lake build comparator` — pulls `Export.Parse`@cacf989 as a dep;
    network only in the build stage, per existing practice for FC/PyPantograph);
  - lean4export binary: upstream clone at the pinned rev, toolchain file
    overwritten to the project toolchain, `lake build lean4export` (§2.2);
  - `landrun` built from pinned source in a Go builder stage (pin a commit;
    README requires main-branch builds);
  - both toolchains under elan; the `reset-workspace.sh` helper script; the
    `/opt/pristine/` tree (see below).

### 3.1 Trust story and why 2 containers is sound

The 3-container design existed because compiling the submission executes
arbitrary agent code (compile-time `#eval`), and SafeVerify's verdict had to
live where agent code never ran. Comparator internalizes that boundary:
`lake build Solution` runs under landrun with writes confined to `.lake` (+
`/dev`), and Landlock also denies ptrace out of the sandbox domain. The
verdict process (comparator), the challenge source, the binaries, and the
already-computed challenge export are out of reach **within a check**, because
the trusted build+export of Challenge complete before any agent code runs.

Three gaps remain. The plan mitigates the first, records the second as an
upstream lifecycle limitation, and relies on deployment validation for the
third:

1. **Cross-attempt filesystem poisoning via `.lake`.** Landrun *grants* writes
   to `.lake`, including `.lake/packages` (Mathlib oleans). A malicious attempt
   N could poison Mathlib so that attempt N+1's *challenge* elaborates to a
   trivial statement (both sides then match — unsound). Within one check the
   ordering protects us; across checks nothing does. Fix, kernel-enforced and
   cheap:
   - run the comparator service with **`read_only: true` rootfs**;
   - `tmpfs` mounts at the only mutable spots: `/workspace/leanproject/.lake`,
     `/workspace/leanproject/run`, `/tmp`;
   - image bakes `/opt/pristine/`: the project `.lake` *skeleton* + the FC
     lib build artifacts (small, tens of MB) + `packages/` (heavy, stays on
     the read-only rootfs);
   - a trusted `reset-workspace.sh` runs **before every check**: wipe the
     tmpfs dirs, recreate `.lake` from the skeleton, `ln -s
     /opt/pristine/packages .lake/packages`, copy the FC build artifacts into
     `.lake/build`. Seconds per check; heavy packages are never copied and
     never writable.
   This removes stale writable filesystem contents between checks and keeps
   packages immutable. It does **not** terminate processes left behind by the
   preceding attempt, so it is not by itself a complete cross-attempt
   boundary; see the next item.
2. **Cross-attempt processes — known P0 Inspect lifecycle limitation.** Inspect
   creates each `SandboxEnvironment` service once per sample, while APN's
   gated submissions produce multiple checks inside that sample. The public
   sandbox API has sample-level `sample_init`/`sample_cleanup`, but no way for
   the checker to replace just `sandbox("comparator")`. A submission can
   therefore leave a detached process in the comparator service after its
   `exec` returns. `reset-workspace.sh` cannot reliably revoke that process;
   it can continue running, race the next reset, or rewrite the newly created
   tmpfs state.

   The sound fix is a fresh comparator service instance for every check
   (a new Compose service container locally and a replacement service Pod on
   k8s), with readiness awaited before inputs are written. This lifecycle
   primitive belongs in Inspect rather than in backend-specific APN code and
   is tracked by the open
   [Inspect issue #5034, "SandboxEnvironment: add a `restart` method?"](https://github.com/UKGovernmentBEIS/inspect_ai/issues/5034).
   This plan deliberately does not reach into Docker/k8s provider-private
   internals as a workaround. Until Inspect exposes the primitive and APN uses
   it before each check, cross-attempt process isolation remains a known
   limitation and the migration must not claim full cross-attempt soundness.
   Once available, service replacement becomes the boundary; the pristine
   workspace setup remains only initialization of the new instance and no
   adversarial process-cleanup logic is needed.
3. **Silent landrun degradation — known problem, upstream fix of record.**
   Comparator hardcodes landrun's `--best-effort`, whose documented behavior
   on kernels without (adequate) Landlock is "no restrictions (sandbox
   disabled)" — silently. On such a host the entire within-check boundary
   would evaporate with no error. This is an upstream Comparator bug and is
   filed as **https://github.com/leanprover/comparator/issues/83**
   ("Comparator calls landrun with `--best-effort`", ours, open) with two fix
   options: keep `--best-effort` but refuse to run below a minimum kernel, or
   drop `--best-effort`. The fix is upstream's; **we add no harness-side
   mitigation** — when a fix lands, advancing our comparator pin picks it up
   and comparator itself fails closed. Until then, the exposure is bounded by
   validating each deployment environment once (§7). Facts already checked:
   the three `landlock_*` syscalls are in the current moby default seccomp
   allowlist, so recent Docker needs no `security_opt` (old engines ship older
   profiles); the VM kernels of Docker Desktop/OrbStack and the k8s node
   kernels (e.g. EKS AL2 = 5.10, no Landlock; AL2023 = 6.1+) vary. Landrun
   wants 5.13+ for basic FS rules (6.2+ for truncate support; target 6.2+).

Residual accepted risks (documented, not new): Landlock doesn't scope signals
until 6.12 (worst case: agent build kills comparator → nonzero exit → reject:
fail-closed); abstract unix sockets pre-7.1 (nothing listens in the
container); kernel exploits — on docker, the default seccomp profile stays ON
(it allows the `landlock_*` syscalls, so we never need `seccomp=unconfined`);
on Hawk/k8s at `standard` isolation, pods run seccomp-Unconfined because
that's the cluster default the deployment ships (§7.6) — a wider node-side
syscall surface that is Hawk's posture, not something this plan sets.
Optional hardening: run the comparator container as a
non-root user (comparator README assumption 6) — do it if it doesn't fight
elan paths; it's defense-in-depth, not load-bearing.

### 3.2 Per-check flow (new `apn/checker.py`)

`SandboxComparator.check(spec: str, submission_tar: bytes,
claim: Literal["proof", "disproof"])` — `spec` is the sample's sketch (the
Isolated file text), which serves both claims:

1. Claim declaration: `claim` comes from the agent's own `submit_proof` tool,
   which gains a required `claim: "proof" | "disproof"` argument — the tool
   records it in the sample store, and the scorer passes it through to the
   checker. No sniffing of submission content; a wrong declaration simply
   fails its check (the same opaque INCORRECT as any wrong submission). If no
   claim was ever recorded (e.g. the sample hit its limits and is scored
   without a submission), default to `"proof"` — deterministic, and such
   samples reject anyway.
2. Host-side: extract exactly `Submission/Spec.lean` from the agent tar with
   Python `tarfile` (size-capped, single member — no `tar(1)` on untrusted
   input in the trusted container; the throwaway compile container used to
   absorb that risk). Missing member ⇒ stage `entry_missing`.
3. `exec(["/opt/apn/reset-workspace.sh"])` (trusted filesystem reset, §3.1;
   it does not terminate cross-attempt processes pending Inspect issue #5034).
4. Write via sandbox API:
   - `run/Challenge.lean` = the sample's committed `Isolated/` file, verbatim
     — the same file for both claims; it states both the theorem and its
     disproof target (§4), and only `theorem_names` below differs by claim.
     Nothing is composed at scoring time;
   - `run/Solution.lean` = the agent's file, verbatim;
   - `run/config.json` = `{challenge_module: "Challenge", solution_module:
     "Solution", theorem_names: [<decl> | <decl>.disproof] per claim,
     permitted_axioms: [propext, Quot.sound, Classical.choice]}`.
5. `exec(["lake", "env", COMPARATOR_BIN, "<proj>/run/config.json"],
   cwd=<proj>, env={COMPARATOR_LEAN4EXPORT: ..., COMPARATOR_LANDRUN: ...},
   timeout=...)`. Verdict = exit 0. Map failures to stages for metadata by
   phase markers in output ("Building Solution", "Exporting", compare/axiom
   messages, kernel verdict lines); timeouts/exit≥128 → resource stages, as
   today.

Notes: single-file submission policy is kept (an `import Submission.…` fails
to resolve because no such lib is registered — same rejection as today; with
comparator this is now a *policy* choice, not a soundness requirement, since
the closure replay would cover helper files — do not relax it in this change).
The theorem name comes from the sample id; add a vendor-time/CI assertion
(via the existing extract_ranges tooling in the isolation suites) that each
Isolated spec declares exactly `<id>` as its target plus the appended
`<id>.disproof` (§4), for all three datasets (erdos/fc100 already document
id = fully-qualified decl name).

### 3.3 Module-sensitive declarations — known fail-closed limitation

Comparator deliberately builds different `Challenge` and `Solution` modules
and compares the configured target closure by exact exported names/terms. Lean
bakes the source module name into `private` declaration names and some
compiler-generated names, so byte-identical source can elaborate to different
closures. This is not hypothetical: the exact pins in §2 reproduce a faithful
private dependency failing at `statement` with `Const does not match`; the
self-checking repro is in `repros/comparator-private-name/`.

The same broader limitation is already open upstream:

- [comparator#58](https://github.com/leanprover/comparator/issues/58) shows an
  anonymous instance receiving different generated names in Challenge and
  Solution;
- [comparator#59](https://github.com/leanprover/comparator/issues/59) shows a
  dependent statement changing when elaboration chooses a different proof,
  despite proof irrelevance.

Giving both inputs the same explicit module identity would address the
particular module-derived anonymous-instance name in #58 (and the
module-derived `private` names in our repro), but is not a general fix. As
[noted upstream](https://github.com/leanprover/comparator/issues/58#issuecomment-5407090008),
differences in the files' contents can make Lean generate different matcher
and auxiliary declarations even under the same module name.

Upstream recommends putting statement material in a shared `Statement.lean`
module imported by both sides. We do **not** adopt that workaround in v1: it
would turn APN's single editable file into a multi-file/wrapper contract and
would touch dataset generation, prompts, checker staging, and historical proof
replay.

**Amendment (2026-08-25).** This plan originally also rejected removing
`private` as a shortcut. That stance was revised after the corpus census
(`scripts/comparator_drift.py`, which pins its results): 20 of 928
committed specs were empirically confirmed to false-reject faithful
submissions, and 19 of those were caused solely by `private` name mangling.
The **OEIS** generator now strips the `private` modifier at generation time
(`scripts.isolation.strip_private` in `generate_oeis_isolated.py`), fixing
that dataset's 14 confirmed cases. In a self-contained isolated spec, privacy
has no semantic effect beyond name visibility/mangling; the risks called out
originally are gated loudly rather than silently (name/instance conflicts are
compile errors caught by the isolation suites, and the gold sweep's
formerly-rejected `oeis_A258667_conjecture_0` proof is the fix's regression
guard). The strip is deliberately scoped to OEIS -- the 5 erdos/fc100open
`private` cases stay unstripped -- and does **not** address #58's
non-`private` generated names (one confirmed instance-collision case remains);
all remaining false-reject ids are pinned in
`scripts.comparator_drift.CONFIRMED_REJECT_IDS`. #59's proof-term drift is
likewise untouched.

Those remaining cases are fail-closed (faithful submissions can be rejected;
invalid ones are not accepted) and stay documented rather than worked around.
Keep the current single-file layout; the only source rewriting is the
mechanical OEIS isolation-time `private` strip. The eventual fix must be
upstream and robust to generated-declaration drift in general; canonicalizing
only the top-level module identity is insufficient. Advancing the pin can
remove this limitation once Comparator implements such a fix, without changing
APN's task format.

## 4. Disproofs: the one mechanism Comparator lacks

Current contract: agent may delete `theorem foo … := sorry` and prove
`theorem foo.disproof : ¬(original type)`; SafeVerify checks the type against
`mkNot ∘ cleanupAnnotations` of the target's elaborated type — by **kernel
defeq**. The prompt embeds `negateExpr` verbatim.

Comparator plan: state the disproof target **inside each Isolated file
itself**. Every `Isolated/<id>.lean` gains one final, mechanically derived
line (vendor-time, committed, certified — the lifecycle `Isolated/` already
has):

```lean
theorem A055487_conjecture.disproof : ¬ (type_of% @A055487_conjecture) := sorry
```

One committed file is then simultaneously the agent's sketch, the proof
challenge, and the disproof challenge: the checker sends it verbatim for both
claims and only `theorem_names` differs (§3.2). Nothing is composed at
scoring time, there is no sibling-file pairing or naming to manage, and the
task becomes self-documenting — the agent sees both targets stated in the
file it edits and replaces the `sorry` of exactly one of them. The negation
lives at the expression level (no text munging of ~930 statements — 492 OEIS
+ 350 Erdős + 86 FC100 — where binders, `let`s and implicit arguments make
source-level negation a bug farm). Namespace robustness: 7 of the 928
Isolated files (all Erdős, one open level each; census 2026-08-24) end
inside an open `namespace` — the isolation cut dropped the trailing `end`
that upstream FC always has (its lint style closes every namespace). The
append step first restores those dropped `end` lines, then appends the plain
fully-qualified declaration at top level — no `_root_.` anywhere, and for
the other 921 files the appended content is exactly the one line. A wrong
namespace accounting fails certification loudly ("Const not found" /
exact-name assertion).

`type_of%` is a **Lean core** term elaborator (`Lean.Parser.Term.typeOf`):
it elaborates `@foo` to the bare constant (`@` suppresses implicit-argument
insertion) and returns its stored type — so the declaration's type elaborates
to `Not (<foo's elaborated statement type>)`, i.e. exactly SafeVerify's
`negateExpr` result. For a universe-polymorphic `foo`, `type_of% @foo`
instantiates `foo` at fresh universe metavariables and declaration elaboration
generalizes them into the disproof theorem's own `levelParams`; their binder
names may differ from `foo`'s, but they correspond positionally and express the
same universe-polymorphic type. This is handled by the vendor-time certificate
below, not by runtime code. `cleanupAnnotations` parity is moot at compare time
because lean4export strips mdata, so comparator's BEq sees mdata-free terms on
both sides. Nothing here is our metaprogramming: the elaboration machinery is
upstream core, and the idiom is already exercised *in FormalConjectures itself
at our pinned commit*
(e.g. `type_of% selfridge_seq_conjecture`, `type_of%
generalized_riemann_hypothesis`). Scope note: the formalized *statements*
are untouched — the appended declaration is derived and content-neutral, and
git history shows exactly what changed in each file. §8.1's resolution (no
fixes or exclusions of formalizations) concerns the statements and is
unaffected. Challenge-side `sorryAx` is
irrelevant (axioms are checked on the solution only; the statement's type
closure doesn't contain proof values).

Certification (vendor-time + CI, against the committed files): for every
Isolated file, build it and independently compute
`mkNot ∘ cleanupAnnotations ∘ (·.type)` of the target via a throwaway
metaprogram. First assert that target and disproof have the same number of
`levelParams`; then instantiate both parameter lists positionally with the
same fresh canonical levels and assert that the canonicalized disproof type is
BEq-identical to `mkNot` of the canonicalized target type. (For monomorphic
targets this reduces to the previous exact comparison.) This treats universe
parameter names as binders while still failing on an arity, ordering, or type
mismatch. It is **certification-only**: runtime Comparator remains unchanged
and performs its ordinary exact Challenge/Solution comparison; because the
agent keeps the committed declaration and only fills its `sorry`, both sides
elaborate the same disproof `levelParams`. Two independent mechanisms agreeing
on every statement in all three datasets, plus the historical gold-disproof
corpus (§7), pins the semantics. The `run_cmd`
`getConstInfo`/`mkNot`/`mkSorry`/`addDecl` postlude survives only inside that
certification test — not in the scoring path. If `type_of%` ever diverges on
some statement, the postlude is the ready fallback for the scoring path too.

Agent contract, radically simplified: "replace the `sorry` of exactly one of
the two theorems in the file, and declare which via the submit tool" — the
old negateExpr contract disappears from the prompt entirely, and
binder-restatement mistakes become impossible by default (the agent keeps the
file's own `type_of%` line, whose type elaborates identically to the
challenge's by construction). Inertness both ways: in a disproof check the
kept `foo := sorry` is not a config target and not in `foo.disproof`'s export
closure (the elaborated type contains P's constants, not the constant `foo`),
so its `sorryAx` never surfaces — symmetrically for the kept
`foo.disproof := sorry` in a proof check. One constraint for the prompt: the
disproof's *proof* must not reference `foo` (that would pull `sorryAx` into
its axiom closure and correctly reject). And the challenge side anchors
everything: a tampered agent-side `foo` just produces a type mismatch.

Alternatives considered and rejected:
- *Runtime `run_cmd` metaprogram* (getConstInfo/mkNot/mkSorry/addDecl appended
  to the challenge at scoring time): our own trusted metaprogramming in every
  disproof check. Survives only as the independent second mechanism inside
  the certification test.
- *Runtime `type_of%` composition*: right content, wrong lifecycle — the
  challenge should be a committed, reviewable artifact, not composed per check.
- *Sibling files* (`Isolated/<id>.disproof.lean` = statement + the line,
  statement files untouched): the conservative variant and this plan's
  previous iteration. Superseded by the in-file form: one artifact instead of
  a paired two, no sibling naming (the Erdős case-collision overrides need no
  second filename), and the agent sees both targets in the file it edits.
  Cost accepted: a mechanism defect in the appended line would break the
  whole file rather than only the disproof side — fully absorbed at vendor
  time, since certification compiles every committed file before it lands.
- *Vendored fully-explicit negation text* (delaborate `¬ (∀ …)` and commit
  that, no `type_of%`): most human-readable, but pretty-print → re-elaborate
  round-tripping is fragile across ~930 statements; would need the same
  certification and hand-fixes for failures. Possible later upgrade for
  readability; the certification harness is identical.
- *Source-level textual negation* (mechanically rewrite binders into
  `¬ (∀ …)`): the bug farm — binder forms, instance implicits, `let` in
  conclusions.
- *FC's def-hole form* (`answer(sorry) ↔ P` with `definition_names`):
  comparator-native, but upstream's own README says def-holes are gameable
  (fill the hole with `P`, prove by `Iff.rfl`) and demand an additional
  verifier — so custom trusted code moves into the *accept* path (checking
  the filled value is literally `True`/`False`), with a TOCTOU wrinkle (the
  check would run on a re-export made after the untrusted build, not on the
  artifact comparator verified). Also requires changing statements back to
  the `answer ↔` form — barred by §8.1 — and changes the agent-facing task.
- *Keeping SafeVerify's kernel-defeq slack for disproof types*: would mean
  forking comparator's compare logic (syntactic BEq by design). Instead we
  accept the tightening, quantify it on the historical corpus (§7), and
  neutralize it via the `type_of%` idiom in the prompt.
- *Dropping disproofs entirely*: not an option — false conjectures must
  remain solvable tasks (core motivation of the benchmark).

Longer term, the zero-custom-code end state is upstream support: propose a
`negated_theorem_names` config field to Comparator (Lean FRO) — challenge
holds `foo`, solution must prove BEq-`mkNot` of its type. Prove-or-disprove
is FC's own task shape, so the feature is not niche to us. Until/unless that
lands, the one-liner above is the whole mechanism.

**Semantic delta to flag in review and validate on the corpus:** the match
becomes syntactic (BEq over export-parsed, mdata-stripped terms) instead of
kernel defeq. An agent that fills the file's own `sorry` is unaffected by
construction; the delta bites only an agent that *rewrites* the disproof
declaration — e.g. `theorem foo.disproof (h : ∀ …) : False` (defeq, not
syntactically `Not _`) passed SafeVerify but will fail Comparator; and
binder-name sensitivity of a rewritten `¬ (∀ …)` depends on `Expr`'s BEq
(alpha-sensitivity) and must be pinned by a test, not by memory. Actions:
(a) the prompt's contract is "fill the sorry, don't restate" — `prompts.py`'s
`NEGATE_EXPR_SOURCE` and its negation explanation are deleted outright;
(b) measure the real-world delta by re-scoring all historical accepted
disproofs (§7), which were written against the old restate-it-yourself
contract; (c) add accept/reject tests for the near-miss rewritten forms.

## 5. Repo changes (file by file)

- `apn/lean/Dockerfile`
  - drop stage `scorer` (and the vendored-safeverify COPY/build) after
    cutover; add stages: `landrun_build` (golang image, pinned commit),
    `comparator_build` (elan + v4.34.0-rc2, clone comparator at 19e111e,
    `lake build comparator`), and runtime stage `comparator` (FROM base:
    COPY comparator + its toolchain, lean4export toolchain-override build,
    landrun binary,
    pristine tree, scripts). Builder stage ordering: append the
    Challenge/Solution libs to lakefile.toml *before any* `lake build` (the
    config hash must be settled once), then build ProblemImports, then
    warm-build the `run/` stubs (they import ProblemImports), then stage
    `/opt/pristine`. The pristine `.lake` skeleton includes lake's config
    cache and lock structure — everything except `packages/` (symlinked from
    the RO rootfs at reset) and stale stub artifacts (harmless: content
    hashes force a rebuild when real files land in `run/`).
  - rewrite the header comment: the version story is §2 of this doc
    (project toolchain from FC pin; comparator toolchain independent;
    exporter = comparator's pinned lean4export rev built at the project
    toolchain via the override; on FC-pin bump only PyPantograph + exporter
    toolchain move; on comparator bump move the exporter pin with the manifest
    + run the primitives check).
- lean4export — no repo files: the Dockerfile clones upstream at the pinned
  commit (cacf989) and overwrites `lean-toolchain` from `LEAN_VERSION` before
  building (§2.2). Vendor only if a 4.27 build ever needs source patches.
- `apn/lean/comparator/` — likewise no vendoring (unmodified upstream, cloned
  at a pinned commit at build time, like FC/PyPantograph). If we ever patch
  either project, vendor then.
- `apn/lean/reset-workspace.sh` — new, baked to `/opt/apn/`; filesystem reset
  only, not process cleanup (§3.1 and Inspect issue #5034).
- `apn/checker.py` — replace `SandboxSafeVerify` with `SandboxComparator`
  (`check()` per §3.2, protocol renamed `ProofChecker`); tarfile member
  extraction host-side; stages: `entry_missing`, `reset`, `comparator`,
  `comparator_timeout`, `comparator_resource`. Keep
  the compile/verify split of *reference vs submission* error handling
  (reference steps raise, submission-attributable failures score INCORRECT).
- `apn/scorer.py` — reads the declared claim from the sample store (written
  by the submit tool) and passes it to the checker; metadata key
  `safeverify_report` → something checker-agnostic (`verifier_output`); keep
  sidecar tars.
- `apn/solver.py` — the `submit` tool gains a required
  `claim: "proof" | "disproof"` argument whose execute() records it in the
  sample store (§3.2 step 1; Inspect's tool-arg validation makes the model
  retry a malformed call); update `_RESOURCE_STAGES` to the new stage names;
  prompt text via `prompts.py` update (per §4: fill the `sorry` of exactly
  one of the file's two theorems, keep both declarations, the disproof's
  proof must not reference the original theorem, declare the claim at submit
  time; delete `NEGATE_EXPR_SOURCE` and the negateExpr explanation);
  everything else unchanged.
- `scripts/generate_*_isolated.py` / a shared negation step — append the
  derived disproof declaration to every committed `Isolated/<id>.lean` (§4),
  for all three datasets; the isolation/certification suites gate the result
  in CI, and git history shows the per-file diff.
- Knock-ons of the sketch now containing the disproof declaration:
  `apn/dataset.py` docstrings describe the sketch as "the definitions plus the
  single target theorem" — update them; and the isolation oracle suites
  (`tests/test_*_isolation.py`), which certify Isolated content against the
  upstream sources, must treat the final appended line as *expected* derived
  content rather than a deviation from the source cut (e.g. strip exactly one
  trailing `<id>.disproof` declaration before the oracle comparison).
- `apn/task.py` — generates **two sandbox configs directly, one per backend,
  no conversion between them** (no bank shots: each artifact states its
  backend's keys in that backend's native vocabulary, and nothing
  security-relevant survives a translation layer):
  - `compose.yaml` (docker backend: local runs, CI tests): two services;
    comparator service gets `read_only: true`, `tmpfs:` for `.lake`, `run`,
    `/tmp` (with explicit `size=` caps — tmpfs is RAM-backed, and an
    untrusted build filling it must hit a bounded ceiling; likewise
    `sizeLimit` on the k8s emptyDirs), `mem_limit` (start 16g, set from §7
    measurements), `network_mode: none`, image tag kind `comparator`;
  - `values.yaml` (k8s/Hawk backend): chart-native agent-env values with the
    same two services — `securityContext: {readOnlyRootFilesystem: true}`,
    `emptyDir` volumes+mounts at `.lake`/`run`/`/tmp`, `networkIsolated: true`,
    `dnsRecord: true`, resources limits, and an explicit
    `runtimeClassName: CLUSTER_DEFAULT` pin (§7.6);
  shared Python constants (image tags, memory, paths) feed both writers so
  they cannot drift semantically. Backend chosen by an explicit task arg
  (`sandbox_backend: "docker" | "k8s"`, set in the eval-set config's task
  args), not sniffed from the environment. Delete the `compile` service
  everywhere.
- `apn/layout.py` — agent-side paths unchanged; add the comparator-side
  paths (`run/Challenge.lean` etc.) or keep them local to checker.py.
- `prompts.py` — as §4.
- Dataset manifests — no schema change needed if the "id == target decl name"
  assertion (new test) holds for all rows; otherwise add `decl_name`.
- Docs: README, TODO.md (close bug #1 with a pointer to this change).

## 6. Tests (port + new)

Re-derive expectations from Comparator's model — do not blind-port:

- `test_gold_proofs.py` / erdos gold proofs: same corpus, new checker path.
  (Gold files rename `target_theorem_0` as today.)
- `test_lean_vuln_e2e.py`: keep all attacker inputs;
  - unchanged verdicts: sorry/native_decide/custom axiom/weakened/missing
    statement/entry `skipKernelTC` injection (kernel replay catches it)/helper
    imports (unresolved module ⇒ build failure)/honest accepts/honest disproof.
  - `import_superset_violation` and `unsafe_constant_in_entry`: now ACCEPT
    under comparator's model (extra imports and inert unsafe decls are sound —
    the closure replay covers what matters). Rewrite as documented
    accept-cases explaining *why* this is sound, so the suite encodes the new
    model rather than fossilizing SafeVerify's.
  - `root_exec_overwrites_safe_verify` → retarget: compile-time `#eval` tries
    to overwrite the lean4export binary / challenge source / a Mathlib olean
    under `.lake/packages` (a symlink into the RO rootfs). With landrun+RO
    rootfs the writes fail; assert the **verdict stays reject** — not that
    the build fails, since an attacker can catch the IO exception and let the
    build succeed. This doubles as the **landrun canary**.
  - NEW `cross_attempt_filesystem_poisoning`: check #1's submission plants a
    poisoned artifact (e.g. tries to pre-bake
    `.lake/build/lib/lean/Challenge.olean`, rewrite a package olean, or
    **replace the `.lake/packages` symlink with a poisoned real directory** —
    `.lake` itself is writable, so the swap succeeds within a check and must be
    undone by the reset), check #2
    submits a proof that verifies iff the poison survived. This asserts only
    the quiescent filesystem-reset + RO-rootfs story; it is intentionally not
    evidence that hostile processes were removed.
  - NEW `cross_attempt_process_survival`: check #1 starts a detached process
    that waits until the next reset and then writes a marker into the fresh
    tmpfs; check #2 observes it. Keep this as an explicit reproduction of the
    known limitation while Inspect issue #5034 is open. When Inspect gains
    per-service restart, invert the expectation (the marker and originating
    process must be absent) and make that regression test a cutover gate for
    claiming full cross-attempt isolation.
  - NEW upstream limitation fixtures: reproduce comparator#58 (anonymous
    instance names differ by module) and comparator#59 (an added simp theorem
    changes a proof embedded in a dependent statement). Both remain documented
    rejects until fixed upstream; they guard against accidentally claiming
    that the identical-source inventory covers all elaboration drift.
  - NEW disproof-shape cases: exact `¬ (∀ …)` accepts; `(h : ∀ …) : False`
    form — pin whatever the empirical verdict is; binder-renamed variant —
    pin alpha-sensitivity. Add one- and two-universe-parameter fixtures that
    exercise the certification's positional level normalization while the
    runtime Challenge/Solution comparison remains exact.
  - NEW statement-with-sorry'd-def fixture (the suspected "unusual defect"
    class, §7): document comparator's rejection of a faithful solution.
    Note the harness cannot distinguish this from an agent's own sorry at
    check time (both surface as an illegal `sorryAx`); the identification
    belongs at vendor time — a per-statement axiom scan of the statement's
    defs (also how §7.3's five get confirmed), not in the scoring path.
- `test_checker.py`/`test_singlefile_proof.py`: port plumbing (oversize,
  missing entry, timeout mapping, claim plumbing from submit tool to checker).
- The disproof-declaration certification suite (§4) runs in CI against the
  committed Isolated files.
- New unit test: every `primitiveTargets`/`builtinTargets` name resolves in
  the dataset environment (buildable as part of the gold-proof container
  session; guards comparator bumps, §2.3).
- New certification/inventory: for every committed Isolated spec, build and
  export the same source as both Challenge and Solution and classify any
  declaration/statement mismatch that occurs before the expected `sorryAx`
  rejection. This detects module-derived private/generated-name drift, not
  arbitrary solution-side elaboration changes such as comparator#59 (covered
  by its fixture and historical-proof replay). Pin the affected-id list in CI
  so false rejects cannot appear silently on dataset, Lean, exporter, or
  Comparator bumps (§3.3).

## 7. Validation phase (before cutover)

1. **Bring-up smoke** (day 1, local): build images; `ldd` the comparator
   binary; run one known-good OEIS proof and one disproof through the full
   scorer path. Check *early* (one-off) that the local Docker VM kernel
   (OrbStack/Docker Desktop) has Landlock and that landrun enforces under it —
   until comparator#83 is fixed upstream, an environment without Landlock
   runs comparator silently unsandboxed (§3.1), so this environment fact
   gates local test validity (CI runners likewise).
2. **Full-corpus replay**: every historical *accepted* submission (logs/ +
   the results repo, all models — not just Opus) and a sample of rejected
   ones through the new checker. Deliverables:
   - discrepancy list vs SafeVerify verdicts (expect: the paper's 5 defect
     conjectures re-identified, the 2 resource-rescued proofs accepted, no
     new unexplained flips — especially zero *accept-flips* on disproofs);
   - runtime and peak-RSS percentiles per phase (challenge build, exports,
     replay) → set `timeout` (today 30 min; expect to raise toward 45–60 min)
     and `mem_limit` (expect ≤16g; the DAG-shaped export kills the
     rebuildExpr blowup — confirm on the `(a+b+c)^16` ring case from TODO.md).
3. **The 5 defective formalizations**: identify from the discrepancy list and
   diagnose (leading hypothesis: statement depends on a sorry'd def —
   SafeVerify tolerated it via its `sorryAx ∉ target.axioms` carve-out;
   comparator's axiom walk correctly rejects every solution).
   **Resolved 2026-08-21: no dataset action in this change.** The formalized
   statements are not modified (the appended disproof declaration of §4 is a
   separate, content-neutral matter) and no rows are excluded; the five stay
   scoreable and the
   denominator stays 492, matching the paper's 144/492 framing. Accepted
   consequence: runs spend budget on conjectures that are likely unsolvable
   under Comparator (bounded by 5 × the per-sample cap per full run). The
   validation deliverable here is identification + diagnosis + documentation
   only; any fix or exclusion would be a separate dataset-versioning
   decision, out of scope.
4. **Gated-loop economics**: comparator runs challenge build+export on every
   attempt (no caching in upstream). Measure per-attempt scoring latency and
   confirm it's acceptable under gated submission (agents re-submit many
   times). If it dominates, options: accept; or patch/fork comparator later
   to reuse a cached challenge export (not in v1).
5. **Module-sensitive closure inventory** (§3.3): run the identical-source
   Challenge/Solution certification over all 492 samples and report every
   mismatch attributable to private/generated names. Combine it with the
   historical accepted-submission replay in step 2 to expose solution-induced
   elaboration drift such as comparator#59. This is an explicit cutover
   artifact, not a source-rewrite step. Re-run it on every Lean, exporter,
   Comparator, or dataset bump.
6. **k8s/Hawk: resolved from source 2026-08-21** (METR/hawk main 209cbff0,
   `hawk/hawk/runner/run_eval_set.py`; agent-env chart in inspect_k8s_sandbox —
   re-confirm against METR's pinned fork rev c551ce98 at implementation):
   - Hawk's compose path silently drops only `build`/`init`/`secrets`; any
     other unknown compose key (`read_only`, `tmpfs`, `security_opt`)
     hard-fails the k8s_sandbox converter — loud, never a silent loss of
     protections. So compose cannot carry the k8s hardening; we don't try.
   - The direct route exists and is first-class: a task may pass
     `sandbox=("k8s", K8sSandboxEnvironmentConfig(values=...))` with a
     chart-native values.yaml. Hawk's models are `extra="allow"`, and the
     agent-env chart renders free-form per-service `securityContext`
     (→ `readOnlyRootFilesystem: true`) and `volumes`/`volumeMounts`
     (→ `emptyDir` for the tmpfs mounts) — all chart-documented surface, no
     conversion layer of ours in between (see the task.py bullet in §5).
   - Runtime class: our configs use isolation level `standard` (the default).
     There, services that don't pin a runtime get the deployment default, and
     METR's stg/prd deliberately do *not* make gVisor the fleet default
     (`hawk/api/settings.py`: `runner_sandbox_runtime_class_name` unset keeps
     the node's default runtime) → sandbox pods run under runc on the node
     kernel. No seccompProfile is set at `standard` → k8s default Unconfined →
     the `landlock_*` syscalls are not filtered. Our values.yaml pins
     `runtimeClassName: CLUSTER_DEFAULT` explicitly per service so this does
     not depend on a deployment default staying unset.
   - `isolation: strict` interaction, documented: strict forces the hardened
     runtime (gvisor) plus RuntimeDefault seccomp and drop-ALL caps. gVisor's
     sentry does not implement the Landlock syscalls (ENOSYS) → landrun is
     inert there, and until comparator#83 is fixed upstream that failure is
     *silent* (§3.1) — so running this eval at `strict` is forbidden, not
     merely unsupported. This eval runs at `standard`, where the
     comparator container's landrun + RO-rootfs is itself the hardening. If
     strict ever becomes mandatory, the within-pod boundary needs the
     UID-separation fallback (run the solution build as a second,
     unprivileged uid via a `COMPARATOR_LANDRUN` wrapper; classic DAC +
     ptrace uid checks — works under gVisor). Hawk strict's
     `read_only_root`/`non_root` opt-ins already match the comparator image's
     design (a cooperating image), so convergence later is natural.
   - **The one remaining unknown is the node kernel's Landlock support**
     (Karpenter-provisioned EKS; AMI/kernel config not in the repos). Settle
     it with the direct check before building anything big: a 1-sample smoke
     eval-set at `standard` whose solver runs `uname -r`,
     `cat /sys/kernel/security/lsm`, and (with a landrun binary in the image)
     a one-off landrun enforcement check, inside a sandbox pod. This is
     environment validation, not scoring machinery — there is no runtime
     mitigation (§3.1); an environment that fails this check cannot host the
     eval until comparator#83 is fixed.
   - Then the usual small smoke eval-set (e.g. 5 samples, $1 caps) before any
     production run.

## 8. Decision points (need sign-off)

1. ~~Exclude the defective formalizations vs keep-as-unsolvable.~~
   **Resolved 2026-08-21: keep.** The formalized statements are not modified
   or excluded as part of this change (see §7.3; the appended disproof
   declaration of §4 is separate and content-neutral).
2. nanoda as a second kernel (`external_kernels`): recommended **defer** —
   adds a Rust build + the nanoda-compat quirks; comparator's builtin-kernel
   path is the load-bearing one. Revisit once stable.
3. Non-root comparator container: recommended if elan cooperates; not
   load-bearing.
4. ~~Disproof claim routing by regex vs always-try-both.~~
   **Resolved 2026-08-24: neither** — the agent declares proof vs disproof
   via a required argument on the submit tool (§3.2 step 1).
5. Naming/metadata: `verifier_output` metadata key and new stage names —
   check `scripts/summarize`/`eval_cost.py` for consumers of the old
   `safeverify_report`/stage strings before renaming.

## 9. What explicitly does NOT change

- Datasets, FC pins, statements, sample ids, subsets. The formalized
  statements are unchanged and every row stays scoreable — including the five
  that Comparator rejects — with no fixes and no exclusions (resolved, §8.1).
  (The Isolated files do gain the appended disproof declaration of §4; the
  statements within them are untouched.)
- Agent image and tools — with one agent-visible exception: the submit tool
  gains a required `claim: "proof" | "disproof"` argument (§3.2). Prompts
  keep the task framing; the disproof wording changes (fill-one-sorry
  contract, §4) and verifier-name mentions go.
- Task shape: prove `foo` or prove `foo.disproof`; single-file submission;
  three permitted axioms; gated submission; opaque INCORRECT feedback with
  the resource-limit carve-out.
- Inspect scaffolding, Hawk configs (beyond image/service names, limits, and
  the new `sandbox_backend` task arg in eval-set configs, §5).
