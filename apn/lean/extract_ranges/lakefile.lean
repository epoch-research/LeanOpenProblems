import Lake

open Lake DSL

-- Self-contained vendor-time tooling: the declaration-range extractor the
-- isolation pipeline drives, and the disproof-declaration certifier the
-- isolation suites run over the committed Isolated/ files. Both import only
-- Lean core; Mathlib + FormalConjectures are supplied at runtime via
-- `lake env` from `/workspace/leanproject`, so they are not build dependencies
-- here. No Cli dependency: argv is parsed by hand, so `lake build` runs fully
-- offline (no `lake update`).
package «extract_ranges»

@[default_target]
lean_exe extract_ranges where
  root := `ExtractRanges
  supportInterpreter := true

lean_exe certify_disproof where
  root := `CertifyDisproof
  supportInterpreter := true
