import Lake

open Lake DSL

abbrev safeVerifyLeanOptions : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
]

package SafeVerify

-- SafeVerify itself imports only Lean core + Cli (not Mathlib). Mathlib is
-- supplied on LEAN_PATH at runtime (we run the exe via `lake env` from the
-- Mathlib project), so it is not a build dependency here.
require Cli from git
  "https://github.com/leanprover/lean4-cli.git" @ "v4.27.0"

@[default_target]
lean_lib SafeVerify where
  leanOptions := safeVerifyLeanOptions
  -- globs := #[.submodules `SafeVerify]

-- SafeVerifyTest contains intentionally broken lean files for testing
-- They should not be compiled with lake build, but tested via scripts/run_tests.sh
-- @[test_driver]
-- lean_lib SafeVerifyTest where
--   globs := #[.submodules `SafeVerifyTest]

lean_exe safe_verify where
  root := `Main
  supportInterpreter := true
