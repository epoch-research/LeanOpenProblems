/-
Vendor-time/CI certifier for the appended disproof declarations
(comparator-migration-plan.md §4).

Every committed `Isolated/<id>.lean` ends with one mechanically derived line:

  theorem <target>.disproof : ¬ (type_of% @<target>) := sorry

The scoring path relies on that declaration's elaborated type being *exactly*
the negation of the target's statement: Comparator compares the challenge and
solution declarations by BEq over export-parsed (mdata-free) terms, so the
committed line is what pins the disproof task's meaning. This tool is the
independent second mechanism that certifies it: for each input file it
elaborates the source through the Lean frontend and then recomputes the
expected disproof type from the *target's* stored type via
`mkNot ∘ cleanupAnnotations` -- SafeVerify's old `negateExpr`, deliberately not
via `type_of%` -- and asserts the declared disproof type is BEq-identical.

Universe polymorphism: `type_of% @foo` instantiates `foo` at fresh universe
metavariables which declaration elaboration re-generalizes, so the disproof's
`levelParams` correspond to the target's positionally but may be *named*
differently. The check therefore first asserts equal `levelParams` arity, then
instantiates both sides' parameters positionally with the same fresh canonical
levels before comparing -- names are treated as binders; arity/order/type
mismatches still fail.

mdata: lean4export strips mdata, so Comparator's runtime BEq sees mdata-free
terms; the in-process comparison here strips mdata recursively from both sides
to certify exactly the comparison the verifier will make.

Usage:
  certify_disproof FILE.lean [FILE.lean ...]
Emits a JSON array to stdout: one object per input file
  { "file", "target", "disproof", "ok", "error" }
with `target`/`disproof` the fully-qualified names found (empty on discovery
failure). Elaboration errors in the file itself are reported too (`ok = false`),
so a certified file is in particular a compiling file. Run under `lake env`
from the FC/Mathlib project so the import resolves.
-/

import Lean
import Lean.Elab.Frontend

open Lean Elab Frontend

structure FileVerdict where
  file : String
  target : String
  disproof : String
  ok : Bool
  error : String
deriving ToJson

/-- Strip `mdata` wrappers everywhere (not just at the top level, which is all
`Expr.cleanupAnnotations` does): the export format Comparator parses carries no
mdata, so the certified comparison must not see any either. -/
partial def eraseMData : Expr → Expr
  | .mdata _ b => eraseMData b
  | .app f a => .app (eraseMData f) (eraseMData a)
  | .lam n t b bi => .lam n (eraseMData t) (eraseMData b) bi
  | .forallE n t b bi => .forallE n (eraseMData t) (eraseMData b) bi
  | .letE n t v b nd => .letE n (eraseMData t) (eraseMData v) (eraseMData b) nd
  | .proj s i b => .proj s i (eraseMData b)
  | e => e

/-- Render the error-severity messages in a log (the `sorry` warning is not an
error and is dropped). Mirrors ExtractRanges.collectErrors. -/
def collectErrors (msgs : MessageLog) : IO (Array String) := do
  let mut out := #[]
  for msg in msgs.toList do
    match msg.severity with
    | .error => out := out.push (← msg.toString)
    | _ => pure ()
  return out

/-- Parse + elaborate one source file against a pre-imported base environment
(the header is parsed for positions but not re-imported; all Isolated files
share the single ProblemImports import). Returns the final environment and any
elaboration errors. Mirrors ExtractRanges.processFile, but only the final
state is needed so the loop is core's `IO.processCommands`. -/
def processFile (baseEnv : Environment) (path : String) : IO (Environment × Array String) := do
  let content ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext content path
  let (_header, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := Command.mkState baseEnv messages {}
  let frontendState ← IO.processCommands inputCtx parserState cmdState
  let errors ← collectErrors frontendState.commandState.messages
  return (frontendState.commandState.env, errors)

/-- The single source-ranged `<target>.disproof` theorem the file declares,
paired with its target (also declared in the file). Errors unless there is
exactly one such declaration and both are theorems. -/
def findPair (env : Environment) (fileName : String) (fileMap : FileMap) :
    IO (Except String (TheoremVal × TheoremVal)) := do
  let metaM : MetaM (Except String (TheoremVal × TheoremVal)) := do
    -- Only source-ranged declarations count (the same filter ExtractRanges uses
    -- to exclude compiler auxiliaries).
    let disproofs ← env.constants.map₂.foldlM (init := #[]) fun acc name _ => do
      if name.isStr && name.getString! == "disproof" && (← findDeclarationRanges? name).isSome then
        return acc.push name
      else
        return acc
    if disproofs.size != 1 then
      return .error
        s!"expected exactly one declared *.disproof, found {disproofs.map (·.toString)}"
    let disproofName := disproofs[0]!
    let targetName := disproofName.getPrefix
    let some (.thmInfo disproofInfo) := env.constants.map₂.find? disproofName
      | return .error s!"'{disproofName}' is not a theorem"
    let some (.thmInfo targetInfo) := env.constants.map₂.find? targetName
      | return .error s!"disproof target '{targetName}' is not a theorem declared in this file"
    return .ok (targetInfo, disproofInfo)
  let result ← (metaM.run' |>.run' { fileName, fileMap } { env }).toBaseIO
  match result with
  | .ok r => return r
  | .error e => throw <| IO.userError (← e.toMessageData.toString)

/-- The certification proper: `disproof.type` must be BEq-identical to
`mkNot target.type.cleanupAnnotations` after positional universe-parameter
canonicalization and recursive mdata erasure. -/
def certify (targetInfo disproofInfo : TheoremVal) : Except String Unit := do
  if targetInfo.levelParams.length != disproofInfo.levelParams.length then
    throw s!"universe parameter arity mismatch: target has \
      {targetInfo.levelParams.map (·.toString)} but disproof has \
      {disproofInfo.levelParams.map (·.toString)}"
  let canonical := (List.range targetInfo.levelParams.length).map
    fun i => Level.param (Name.mkSimple s!"_certify_u{i}")
  let expected := eraseMData <|
    (mkNot targetInfo.type.cleanupAnnotations).instantiateLevelParams
      targetInfo.levelParams canonical
  let actual := eraseMData <|
    disproofInfo.type.instantiateLevelParams disproofInfo.levelParams canonical
  if expected != actual then
    throw s!"disproof type is not the target's negation:\n  \
      expected: {expected}\n  actual:   {actual}"

def verdictFor (baseEnv : Environment) (path : String) : IO FileVerdict := do
  let content ← IO.FS.readFile path
  let fileMap := FileMap.ofString content
  let (env, errors) ← processFile baseEnv path
  if errors.size > 0 then
    return { file := path, target := "", disproof := "",
             ok := false, error := s!"elaboration errors: {errors}" }
  match ← findPair env path fileMap with
  | .error e =>
    return { file := path, target := "", disproof := "", ok := false, error := e }
  | .ok (targetInfo, disproofInfo) =>
    match certify targetInfo disproofInfo with
    | .ok () =>
      return { file := path, target := targetInfo.name.toString,
               disproof := disproofInfo.name.toString, ok := true, error := "" }
    | .error e =>
      return { file := path, target := targetInfo.name.toString,
               disproof := disproofInfo.name.toString, ok := false, error := e }

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- Source is parsed (not olean-replayed), so imported notation/parser
  -- extensions must be live -- same setup as ExtractRanges.
  enableInitializersExecution
  let baseEnv ← importModules #[{ module := `FormalConjectures.Util.ProblemImports }]
    (opts := {}) (trustLevel := 1) (loadExts := true)
  let mut verdicts : Array FileVerdict := #[]
  for path in args do
    verdicts := verdicts.push (← verdictFor baseEnv path)
  IO.println (toJson verdicts).compress
  return 0
