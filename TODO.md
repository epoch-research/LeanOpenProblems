# TODO / Known Bugs

## Known bugs

### 1. SafeVerify peak memory is effectively unbounded on legitimate proofs (un-memoized `rebuildExpr`)

**Severity:** medium — causes deterministic scorer OOM kills (infra errors / lost samples),
not mis-scoring. Already documented in code; tracked here for visibility.

**Detail** (see `apn/task.py:96-121` and `apn/checker.py:36-44`):
- `safe_verify` has a large fixed footprint (~27 GiB peak RSS), attributed almost
  entirely to four `importModules` calls (two in the import-superset check, one per
  replayed file), each materializing the full Mathlib environment and never freeing it.
- On top of that, proof *content* is unbounded: `rebuildExpr` deep-copies proof terms
  **without memoization**, expanding pointer-shared DAGs (which tactics like `ring`
  produce routinely) into trees. Measured: `(a+b+c)^16 = (c+b+a)^16 := by ring` compiles
  agent-side in 3.5s at 6.4 GiB but blew past a 34 GiB limit in safe_verify before being
  OOM-killed. Real submissions have reached ~43 GiB in production. `mem_limit` is set to
  `50g` to cover the worst observation, but no limit can make scorer OOMs impossible.
- Agent-side compile success does **not** bound the scorer's cost.

**Possible fixes** (in vendored `safeverify`):
- Memoize `rebuildExpr` so shared sub-terms are copied once.
- Skip the redundant `importModules` in the import-superset check.
