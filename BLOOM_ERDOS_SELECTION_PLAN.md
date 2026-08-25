# Plan: switch the Erdős dataset to the Bloom statement selection

Replace the current Erdős dataset (the Tsoukalas paper's 350 attempted statements,
pinned at FC `67338a15`) with the 48-problem selection recorded in
[ERDOS_PROBLEM_STATEMENT_SELECTION.md](ERDOS_PROBLEM_STATEMENT_SELECTION.md)
(committed alongside this plan; C2 moves it to its permanent home), and
parameterize the generic harness code by FC commit so both FC repo layouts
(pre- and post-`FormalConjecturesUtil` rename) are supported.

## Context for a fresh agent

- "FC" is [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
  the upstream Lean repo the datasets are vendored from. Every commit id in
  this plan not prefixed with a path is an FC commit; to inspect them, use a
  local clone of that repo (do not add it as a dependency of committed code —
  vendor anything the code or tests need).
- Dataset architecture (see `apn/data/erdos/NOTICE.md`, `apn/dataset.py`, and
  `scripts/generate_erdos_isolated.py` docstrings): each dataset dir under
  `apn/data/` holds an `fc_commit` pin, vendored `Sources/` (FC files at the
  pin), generated per-target `Isolated/` specs, a `samples.jsonl` manifest
  (the universe = census of `Sources/`), and `subsets/` (benchmark lineage).
  Sandbox images are built from `apn/lean/Dockerfile` per pin; there is no
  local Lean toolchain — everything Lean runs in containers.
- The three datasets are `erdos`, `oeis`, `fc100open`. Only the **erdos** pin
  moves in this plan; oeis/fc100open stay at old-layout `67338a15`, which is
  why both FC layouts must be supported simultaneously.
- This plan targets `main` (SafeVerify scoring). A separate in-flight branch
  (`comparator`) is migrating the scorer — see Risks.

## Decisions (settled with Tom, 2026-08-25)

1. **New erdos pin: `488aade228ec37880b8fec178c173c07d279bb53`** — the last FC
   commit on Lean v4.27.0, 21 commits before the review commit
   `56534c04092446f2fd549d2865f2496924812da8` (which is on v4.33.1). Rationale:
   - All 48 selected declarations are **textually identical** between the two
     commits. The residual diffs in 8 of the 48 files (5, 20, 23, 74, 89, 107,
     184, 595) touch only variant/test-lemma proofs, a `formal_proof` URL
     attribute, and `open scoped Classical in` on variants — never a selected
     statement. A scripted certificate re-verifies this at vendor time (C6).
   - Pinning the review commit itself would force a v4.27.0→v4.33.1 toolchain
     migration: porting SafeVerify and extract_ranges, and Pantograph has no
     release supporting v4.33 (max v4.31.0), blocking the agent image.
   - `488aade2` already uses the renamed `FormalConjecturesUtil` layout
     (`FormalConjectures/Util` is gone there), so the parameterization work is
     exercised either way — oeis/fc100open stay at old-layout `67338a15`.
2. **Problem 508 ships as an excluded row.** Its selected statement
   `HadwigerNelsonProblem` is `χ(ℝ²) = answer(sorry)` — value-typed, sorryAx in
   the statement type, unscoreable by SafeVerify — and 508.lean has no other
   `research open` statement. Consistent with existing policy (fc100open's 14
   value-typed exclusions). The runnable selection is therefore **47 samples**.
3. **The Tsoukalas set is replaced in place**; git history is the archive of the
   old `Sources/`, `Isolated/`, manifest, and `tsoukalas_attempted` subset.

## Verified facts this plan relies on

- Current pin `67338a15` is a WIP branch commit (off `cc4ee602`); 4 selected
  files (5, 821, 829, 1057) don't exist there and 2 selected statements
  (`erdos_128`, `erdos_952`) differ substantively — the pin **must** move.
- At `488aade2`: lean-toolchain `v4.27.0`, mathlib `v4.27.0` (same as the
  current images, PyPantograph pin `b8608f3`→v0.3.13, vendored
  safeverify/extract_ranges toolchains — none of these move).
- The FC library entry is now the `FormalConjecturesUtil` lake lib
  (`FormalConjecturesUtil.lean` + `FormalConjecturesUtil/`); problem files say
  `import FormalConjecturesUtil`. Note `FormalConjecturesUtil.lean` uses the
  Lean module system (`module` / `public import`) already at v4.27.0 — FC CI
  builds it, but our container flow must be smoke-tested (Workstream B).
- All 48 selected declarations at the new pin carry `research open`; 33 are
  `answer(sorry) ↔ P` (the certified-rewrite path), 14 are plain `P`, and 1
  (508) is value-typed.

## Workstream A — parameterize generic code by FC commit

Goal: everything generic (Dockerfile, extractor, prompts, isolation plumbing)
takes the FC commit (or a profile derived from it) and does the right thing for
that commit's layout. Land this **first**, with all pins unchanged, so the
existing oeis/fc100open/erdos suites prove no regression.

### A1. FC profile registry (`apn/dataset.py` or new `apn/fc.py`)

```python
@dataclass(frozen=True)
class FCProfile:
    util_module: str  # the import that pulls Mathlib + FC utils

_FC_PROFILES = {
    "67338a157bbb8d87e9a349d662f82a868bda6327": FCProfile("FormalConjectures.Util.ProblemImports"),
    "488aade228ec37880b8fec178c173c07d279bb53": FCProfile("FormalConjecturesUtil"),
}

def fc_profile(commit: str) -> FCProfile: ...  # KeyError with a pointed message on unknown pins
```

An explicit registry (not layout sniffing host-side) because Python has no FC
checkout at runtime; an unknown pin fails loudly at task-construction time,
forcing a conscious registry update whenever any pin moves.
`tests/test_fc_pins.py` gains: every dataset pin resolves to a profile.

### A2. `apn/lean/Dockerfile` — layout auto-detect in the builder

The builder *does* have the checkout, so it detects the layout itself (keeps
the CI workflow's plain `--build-arg FC_COMMIT=` builds working unchanged):

- Guard: `test "$(cat lean-toolchain)" = "leanprover/lean4:${LEAN_VERSION}"` —
  the comment already declares this invariant; make it fail the build.
- Build step: `if [ -f FormalConjecturesUtil.lean ]; then lake build
  FormalConjecturesUtil; else lake build FormalConjectures.Util.ProblemImports; fi`.
- `COPY` can't branch, so the builder stages the proving-library sources into
  one directory (`/staged/`): old layout → `FormalConjectures/Util`; new layout
  → `FormalConjecturesUtil.lean` + `FormalConjecturesUtil/`; both →
  `FormalConjecturesForMathlib{,.lean}`. The `base` stage does a single
  `COPY --from=builder /staged ./`.
- Update the header comment (the `ProblemImports` references).

This layout conditional is not a fallback: both layouts are live requirements
(erdos on the new pin, oeis/fc100open on the old), and the branch selects on
the checkout — the ground truth. The registry (A1) and this detection state
the same fact in two places; drift between them is caught because the
isolation tests run the registry's `util_module` against the built image.

### A3. `extract_ranges` — util module as a required CLI flag

`ExtractRanges.lean` hardcodes `importModules #[FormalConjectures.Util.ProblemImports]`.
Replace with `--util-module NAME`, **required, no default** — named after the
same fact as `FCProfile.util_module` (the import that pulls Mathlib + FC
utils), and required so every caller states it explicitly; a caller that
forgets fails immediately instead of silently extracting against the wrong
layout. Update the module docstring.

### A4. Thread the module through the isolation plumbing

- `scripts/isolation.py::run_extractor(files, container, exe, util_module)`
  passes the flag; `tests/lean_sandbox.py::extract(...)` likewise — both
  required parameters, no defaults.
- Callers (`scripts/generate_{oeis,fc100,erdos}_isolated.py`,
  `tests/test_*_isolation.py`) pass `fc_profile(fc_commit(<DIR>)).util_module`.

### A5. Prompt + solver threading

- `apn/prompts.py::user_prompt(path, token_limit, literature, util_module)` —
  the "do not add or remove `import` statements" sentence names the profile's
  module instead of the hardcoded `FormalConjectures.Util.ProblemImports`.
- `apn/solver.py::lean_prover(...)` gains `util_module` (passed to
  `user_prompt`); each task in `apn/task.py` supplies
  `fc_profile(fc_commit(<DIR>)).util_module`.

**Gate A:** full existing test suite green with pins untouched (pure refactor).

## Workstream B — new-pin image smoke test (run FIRST, before any code changes)

The one real unknown is the module-system `FormalConjecturesUtil` inside our
container flow at v4.27.0. De-risk before writing any workstream-A code, using
a throwaway build context (a scratchpad copy of `apn/lean` with the three
layout-specific lines hand-patched — the repo tree stays untouched):

1. `docker build --target scorer` (and `generate`) at
   `FC_COMMIT=488aade2...` — exercises `lake exe cache get`, the conditional
   `lake build`, and the staging COPY.
2. In the scorer image: write a trivial spec (`import FormalConjecturesUtil`,
   one `theorem ... := by trivial`), compile via `lake env lean -o`, run
   `safe_verify` target-vs-target — proves compile + kernel replay work with
   module-built oleans in the import closure.
3. In the generate image: run the (now flag-aware) extractor with
   `--util-module FormalConjecturesUtil` over one problem file — proves
   `importModules` + `loadExts` handle the module-system lib.

These probes are spikes: they decide the implementation before it is written,
and the shipped code has exactly one path. If a probe fails, the design is
revised and this plan updated (e.g. if step 3's `importModules` cannot load
the module-system lib, the extractor's approach changes for all pins) — the
code never carries an alternate branch for the failing case.

**Gate B: PASSED (2026-08-25, run before workstream A).** All three probes
green against images built at `488aade2` from a throwaway copy of `apn/lean`
with the three layout lines hand-patched — the `lake build` target (A2's
conditional, hardcoded to the new branch), the base stage's COPY paths, and
the extractor's `importModules` module. The throwaway context was session
scratch and is gone, but the patches are exactly what A2/A3 implement, and
the docker layer cache plus the local images `apn-spike-scorer` /
`apn-spike-generate` remain on the machine that ran the spike, so the real
builds in A/C will be fast there:

1. `scorer` and `generate` images build: toolchain guard holds, `lake exe
   cache get` + `lake build FormalConjecturesUtil` succeed, safeverify builds
   unchanged.
2. Trivial target (`sorry`) and submission (`norm_num`) specs with `import
   FormalConjecturesUtil` compile via `lake env lean -o`; `safe_verify
   --disproofs` replays both and passes (rc=0, report shows `sorryAx` target
   vs `propext` submission). Note: FC's style linters now *warn* on submission
   files (e.g. `linter.style.moduleDocstring`) — warnings only, no behavior
   change.
3. The extractor (patched to `importModules #[FormalConjecturesUtil]`)
   elaborates `61.lean` at the pin with zero errors and full declaration
   records (kinds, names, elaborated types) — the module-system lib loads fine
   under `importModules` + `loadExts` at v4.27.0.

## Workstream C — replace the dataset

### C1. Pin

`apn/data/erdos/fc_commit` → `488aade228ec37880b8fec178c173c07d279bb53`.

### C2. Sources

Delete the 236 old `Sources/*.lean`; vendor the 48 selected files from FC at
the new pin: 1, 3, 5, 7, 20, 23, 28, 30, 39, 41, 52, 61, 66, 68, 74, 89, 97,
101, 107, 120, 126, 128, 138, 172, 184, 208, 213, 241, 242, 324, 364, 371,
376, 406, 508, 564, 595, 647, 672, 723, 812, 821, 829, 952, 972, 975, 1003,
1057. Vendor the selection doc itself to
`apn/data/erdos/metadata/ERDOS_PROBLEM_STATEMENT_SELECTION.md` (provenance).

### C3. `scripts/erdos_isolation.py` constants

- `SORRY_ALLOWLIST_FILES`: none of the current entries (295/633/697/961/1055)
  are among the 48 → empty it; re-add only what generation reports (each
  addition is a task-addition-time decision, per the existing comment).
- `VERDICT_PROSE`: generation fails loudly on snippets matching nothing, so
  prune to what the 48 files actually contain, then re-audit the kept files'
  doc prose for *new* verdict-leaking passages (the census counts + the
  existing agentic-audit procedure). Expect far fewer entries — most current
  snippets reference files that are leaving.
- Module docstring: universe = census of the Bloom-selection files.

### C4. Regenerate

Run `scripts/generate_erdos_isolated.py` in the generate container at the new
pin (per its setup docstring, now with the A4 flag). Expected output:
- `samples.jsonl`: one row per research-category statement in the 48 files —
  the 48 selected ids plus their research-category variants; solved variants
  with in-file complete proofs → `PROVED_IN_FILE_REASON` exclusions;
  `Erdos508.HadwigerNelsonProblem` → `VALUE_TYPED_REASON` exclusion (decision 2).
- `Isolated/<id>.lean` for every kept row, license-stripped, categories
  stripped, `answer(...) ↔` certified-rewritten.

### C5. Subsets + task default

- Delete `subsets/tsoukalas_attempted.json`.
- Add `subsets/bloom_selection.json`: the **47** scoreable selected ids
  (48 minus 508). Description records: the selection doc, review commit
  `56534c04`, vendored pin `488aade2`, the statement-identity certificate (C6),
  and 508's exclusion.
- `apn/task.py::apn_erdos`: default `subset="bloom_selection"` (bare
  `apn_erdos` = the selection; the census variants stay reachable by explicit
  subset/none only if we want them — simplest: `subset=None` keeps meaning
  "all non-excluded rows", documented as the census, while the default changes
  to the selection). Rewrite the docstring (currently describes Tsoukalas).

### C6. Fidelity certificate vs the review commit

Vendor-time script (one-off, committed under `scripts/` or recorded in the
subset description): for each of the 48 selected declarations, extract the
declaration command's source span (attribute list + statement + `sorry` body)
at `488aade2` and at `56534c04` and assert byte-equality. Record the result
(and the 8 files' variant-only residual diffs) in `NOTICE.md`. This is the
auditable link between "reviewed at 56534c04" and "vendored at 488aade2".

### C7. Docs

- Rewrite `apn/data/erdos/NOTICE.md` (upstream = Bloom's statement-selection
  review; 70 problems → 48 formalized → 47 scoreable; pin story; certificate).
- `apn/dataset.py::erdos_dataset` docstring; `generate_erdos_isolated.py`
  docstring ("curated down to the attempted set" language goes away — the
  vendored sources now *are* the curation).
- `metadata/snapshots/` (erdosproblems.com scrapes) stay — keyed by problem
  number, still valid.

## Workstream D — tests

- `tests/test_fc_pins.py`: + profile resolution per dataset (A1).
- `tests/test_erdos.py`: rewrite census invariants — 47 kept selected ids each
  `research open` and non-excluded; 508 excluded with the value-typed reason;
  every selected id's `erdos_number` unique; subset loads; sketches carry no
  `answer(`, no `@[category`, no verdict-prose markers; sorry-count invariants
  against the (new, likely empty) allowlist.
- `tests/test_erdos_isolation.py`: the per-form census constants
  (currently 85/249/7/6/3) → recompute from the new manifest; everything else
  is keyed off the manifest and re-derives.
- One end-to-end score at the new pin: a `test_singlefile_proof`-style case
  compiling + safe_verify-ing a trivial submission against one Bloom sample in
  the new scorer image (institutionalizes Gate B).
- `pytest` full suite green, container suites included.

## Rollout order

1. **B** (image smoke at `488aade2`, throwaway context) → Gate B. Run first:
   if it fails, the design is revised before any code is written.
2. **A** (parameterization, pins unchanged) → Gate A → this could merge alone.
3. **C1–C4** (pin + sources + regenerate) → run `test_erdos_isolation.py`.
4. **C5–C7 + D** (subsets, task default, docs, tests) → full suite.
5. Merge; CI (`build-docker-images.yaml`) auto-builds the new pin's image tags
   (keyed `version + fc_<pin>`; oeis/fc100open keep sharing the old-pin tags).
   No workflow changes needed thanks to A2's in-Dockerfile detection.
   `apn.__version__` bump not required for images (pin changes the tag) —
   bump anyway iff we want a version marker for the dataset semantics change.

## Risks / coordination

- **Module-system lib at v4.27.0** in our container flow — the plan's one real
  technical unknown; front-loaded as Gate B so a failure revises the design
  before any code or data lands.
- **Comparator branch**: the main checkout is migrating scoring
  SafeVerify→Comparator (e.g. appends derived disproof declarations to every
  Isolated spec). This plan is written against `main` (SafeVerify). Whichever
  lands second rebases: the Isolated/ regeneration here would need the
  comparator's disproof-appending step re-run, and `prompts.py` conflicts are
  likely. Keep the A-workstream commit separable to ease that rebase.
- **Selection doc drift**: if the review is ever redone at a newer FC commit,
  the certificate (C6) is the thing to re-run; the registry (A1) is the thing
  that refuses silently-unknown pins.
