# TODO / Known Bugs

## Known bugs

### 1. SafeVerify peak memory is effectively unbounded on legitimate proofs (un-memoized `rebuildExpr`) — RESOLVED by the Comparator migration

**Status:** resolved on the `comparator` branch (see `comparator-migration-plan.md`).
The verifier no longer materializes the full Mathlib environment or deep-copies
proof terms: Comparator consumes lean4export's *text* export, which serializes
terms as a shared DAG (every subterm emitted once, by index) and replays that
through its kernel. There is no `importModules` in the trusted process and no
un-memoized `rebuildExpr`, so the two failure sources below are gone. The
comparator service starts at `mem_limit: 16g` (down from `50g`), to be confirmed
by the §7 peak-RSS measurement — in particular re-running the `(a+b+c)^16` ring
case and the three formerly resource-bound gold proofs
(`RESOURCE_BOUND_STEMS` in `tests/test_gold_proofs.py`).

**Original detail** (SafeVerify, now retired):
- `safe_verify` had a large fixed footprint (~27 GiB peak RSS), attributed almost
  entirely to four `importModules` calls (two in the import-superset check, one per
  replayed file), each materializing the full Mathlib environment and never freeing it.
- On top of that, proof *content* was unbounded: `rebuildExpr` deep-copied proof terms
  **without memoization**, expanding pointer-shared DAGs (which tactics like `ring`
  produce routinely) into trees. Measured: `(a+b+c)^16 = (c+b+a)^16 := by ring` compiled
  agent-side in 3.5s at 6.4 GiB but blew past a 34 GiB limit in safe_verify before being
  OOM-killed. Real submissions reached ~43 GiB in production.
- Agent-side compile success did **not** bound the scorer's cost.
