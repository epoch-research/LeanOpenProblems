import Lake

open Lake DSL

-- A self-contained range extractor (kept separate from the vendored
-- `safeverify/` project so that stays pristine). Like SafeVerify it imports
-- only Lean core; Mathlib + FormalConjectures are supplied at runtime via
-- `lake env` from `/workspace/leanproject`, so they are not build dependencies
-- here. Unlike SafeVerify it needs no Cli: argv is parsed by hand, so `lake
-- build` runs fully offline (no `lake update`).
package «extract_ranges»

@[default_target]
lean_exe extract_ranges where
  root := `ExtractRanges
  supportInterpreter := true
