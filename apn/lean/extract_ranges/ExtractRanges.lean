/-
Authoritative top-level-declaration range extractor.

Given Lean source files (which `import FormalConjectures.Util.ProblemImports`),
parse and elaborate each one through the Lean *frontend* one command at a time,
and for every command emit its byte span in the original source together with
the new, source-ranged declarations it introduced (their fully-qualified names
and kinds). A downstream Python assembler uses this to delete the source spans
of the non-target `theorem`/`lemma` commands and keep everything else verbatim.

Why elaborate rather than pattern-match the text: Lean 4's surface syntax is
environment-extensible (Mathlib notation, custom elaborators), so only Lean's
own parser/elaborator can reliably identify declarations and their extents.
This mirrors SafeVerify's `replayFile` (it replays oleans; we must read source,
which oleans do not carry) and Pantograph's frontend `CompilationStep` loop:
diff the environment before/after each command and keep the new constants that
have a `findDeclarationRanges?` (this filters compiler auxiliaries such as
`._eq`/`.match` while keeping the user's declarations).

Usage:
  extract_ranges FILE.lean [FILE.lean ...]
Emits a JSON array to stdout: one object per input file
  { "file": "<path>", "commands": [ { "startByte", "endByte", "decls": [...] } ] }
Run under `lake env` from the FC/Mathlib project so the import resolves.
-/

import Lean
import Lean.Elab.Frontend

open Lean Elab Command Frontend

/-- The declaration kind as a string. Mirrors SafeVerify's `ConstantInfo.kind`
(we don't import SafeVerify; it is reproduced here to keep the projects separate). -/
def constKind : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

structure DeclRec where
  name : String
  kind : String
  /-- Whether this declaration is a registered instance. A `Prop`-valued class
  instance (e.g. `instance : Fact (Nat.Prime 3)`) has kind "theorem" but is part
  of the spec's *definitions*, not a conjecture to cut, so the assembler keeps
  it. -/
  isInstance : Bool
  /-- The *file-local* constants this declaration references in its type/value
  (constants defined earlier in the same file). Lets the assembler keep any
  `theorem`/`lemma` that a kept declaration depends on -- e.g. a nonemptiness
  `lemma` passed to `Finset.min'` inside a sequence `def` is a definitional
  dependency, not a conjecture/test lemma, so it must survive isolation. -/
  deps : Array String
  /-- For theorems, the elaborated statement as a raw `Expr` string (independent
  of `pp` options, so it is comparable across files); "" for other kinds. Used
  for the oracle cross-check against the paper's published challenge files. -/
  type : String
deriving ToJson

structure CmdRec where
  /-- Byte offset where this command's leading trivia begins (the parser's
  `cmdPos`; the previous command's tail trivia is attributed here). -/
  startByte : Nat
  /-- Byte offset of the command syntax's first token -- the doc-comment if
  present, else the keyword (`stx.getPos?`). Plain `--` comments before it live
  in `[startByte, declStart)`. -/
  declStart : Nat
  /-- Byte offset just past the command's last token (`stx.getTailPos?`), before
  any trailing trivia. -/
  declEnd : Nat
  /-- Byte offset where the next command's leading trivia begins (the parser's
  position after this command; includes this command's trailing trivia). -/
  endByte : Nat
  decls : Array DeclRec
deriving ToJson

structure FileRec where
  file : String
  commands : Array CmdRec
  /-- Error-severity messages from elaborating this file (sorry is a *warning*,
  not an error, so it does not appear here). An isolated file is valid only if
  this is empty, which makes re-extraction a full elaboration gate. -/
  errors : Array String
deriving ToJson

/-- The type/value expressions of a constant, for dependency analysis. -/
def declExprs : ConstantInfo → Array Expr
  | .defnInfo v => #[v.type, v.value]
  | .thmInfo v => #[v.type, v.value]
  | .opaqueInfo v => #[v.type, v.value]
  | .axiomInfo v => #[v.type]
  | .inductInfo v => #[v.type]
  | .ctorInfo v => #[v.type]
  | .recInfo v => #[v.type]
  | .quotInfo v => #[v.type]

/-- The file-local constants `ci` references (defined earlier in this file, hence
present in `after`'s local constant map `map₂`), excluding itself. Lean forbids
forward references, so a declaration's local dependencies are always already in
`map₂` when it is elaborated. -/
def localDeps (after : Environment) (name : Name) (ci : ConstantInfo) : Array String := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array String := #[]
  for e in declExprs ci do
    for c in e.getUsedConstants do
      if c != name && !seen.contains c && (after.constants.map₂.find? c).isSome then
        seen := seen.insert c
        out := out.push c.toString
  return out

/-- The new, source-ranged declarations introduced going from `before` to
`after`. A constant is "new" if it is in `after`'s local constant map but not
`before`, and "source-ranged" if `findDeclarationRanges?` finds it (this is what
distinguishes the user's declarations from compiler auxiliaries). -/
def newRangedDecls (before after : Environment) (fileName : String) (fileMap : FileMap) :
    IO (Array DeclRec) := do
  let metaM : MetaM (Array DeclRec) := do
    after.constants.map₂.foldlM (init := #[]) fun acc name ci => do
      if before.contains name then
        return acc
      match (← findDeclarationRanges? name) with
      | some _ =>
        let kind := constKind ci
        -- `isInstance`/`type` only matter for theorem-kind decls (the cut's
        -- candidates), so we only pay for them there.
        let isInstance ← if kind == "theorem" then Lean.Meta.isInstance name else pure false
        let type := if kind == "theorem" then toString ci.type else ""
        let deps := localDeps after name ci
        return acc.push { name := name.toString, kind, isInstance, deps, type }
      | none => return acc
  let result ← (metaM.run' |>.run' { fileName, fileMap } { env := after }).toBaseIO
  match result with
  | .ok decls => return decls
  | .error e => throw <| IO.userError (← e.toMessageData.toString)

/-- Process one command via the core frontend, returning its byte span, the
declarations it added, and whether it was the terminal command. -/
def processOne : FrontendM (CmdRec × Bool) := do
  let before := (← getCommandState).env
  let done ← processCommand
  let st ← get
  let after := st.commandState.env
  let inputCtx := (← read).inputCtx
  let decls ← newRangedDecls before after inputCtx.fileName inputCtx.fileMap
  let stx := st.commands.back!
  let cmdRec : CmdRec := {
    startByte := st.cmdPos.byteIdx
    declStart := (stx.getPos?.getD st.cmdPos).byteIdx
    declEnd := (stx.getTailPos?.getD st.parserState.pos).byteIdx
    endByte := st.parserState.pos.byteIdx
    decls := decls
  }
  return (cmdRec, done)

partial def collectAll (acc : Array CmdRec) : FrontendM (Array CmdRec) := do
  let (cmdRec, done) ← processOne
  let acc := acc.push cmdRec
  if done then return acc else collectAll acc

/-- Render the error-severity messages in a log to strings (warnings, e.g. the
`sorry` warning, are dropped). -/
def collectErrors (msgs : MessageLog) : IO (Array String) := do
  let mut out := #[]
  for msg in msgs.toList do
    match msg.severity with
    | .error => out := out.push (← msg.toString)
    | _ => pure ()
  return out

/-- Parse + elaborate one source file against a pre-imported base environment
(reused across files; the header is parsed for byte offsets but not re-imported)
and collect the per-command records plus any elaboration errors. -/
def processFile (baseEnv : Environment) (path : String) : IO (Array CmdRec × Array String) := do
  let content ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext content path
  let (_header, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := Command.mkState baseEnv messages {}
  let frontendCtx : Frontend.Context := { inputCtx }
  let frontendState : Frontend.State := {
    commandState := cmdState
    parserState := parserState
    cmdPos := parserState.pos
  }
  let (recs, finalState) ← (collectAll #[]).run frontendCtx |>.run frontendState
  let errors ← collectErrors finalState.commandState.messages
  return (recs, errors)

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- We PARSE source (not just replay oleans), so the imported notation/parser
  -- extensions must be live: `enableInitializersExecution` runs module
  -- initializers and `loadExts := true` applies the environment-extension
  -- entries (which include the notation/parser tables). Without `loadExts`,
  -- trailing notation like `^`/`↔`/`∣` is missing and declarations parse only
  -- up to the first infix operator. (Mirrors Pantograph's frontend setup.)
  enableInitializersExecution
  -- All target files share this single import; build the environment once and
  -- reuse it for every file.
  let baseEnv ← importModules #[{ module := `FormalConjectures.Util.ProblemImports }]
    (opts := {}) (trustLevel := 1) (loadExts := true)
  let mut fileRecs : Array FileRec := #[]
  for path in args do
    let (commands, errors) ← processFile baseEnv path
    fileRecs := fileRecs.push { file := path, commands, errors }
  IO.println (toJson fileRecs).compress
  return 0
