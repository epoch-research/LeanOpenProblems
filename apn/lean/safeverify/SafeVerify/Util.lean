import SafeVerify.Types
import Lean

open Lean SafeVerify

/-
From Lean.Environment
Check if two theorems have the same type and name
-/
def equivThm (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  let .thmInfo tval₁ := cinfo₁ | false
  let .thmInfo tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all

/-
Check if two definitions have the same type and name.
If checkVal is true, then also check their values are the same
-/
def equivDefn (ctarget cnew : ConstantInfo) (checkVal : Bool := false) : Bool := Id.run do
  let .defnInfo tval₁ := ctarget | false
  let .defnInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value == tval₂.value else true)

/-
Check if two opaque constants are the same
-/
def equivOpaq (ctarget cnew : ConstantInfo) : Bool := Id.run do
  let .opaqueInfo tval₁ := ctarget | false
  let .opaqueInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.isUnsafe == tval₂.isUnsafe
    && tval₁.value == tval₂.value

/-
Check if two constructors are the same
-/
def equivCtor (ctarget cnew : ConstantInfo) : Bool := Id.run do
  let .ctorInfo tval₁ := ctarget | false
  let .ctorInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.induct == tval₂.induct
    && tval₁.cidx == tval₂.cidx
    && tval₁.numParams == tval₂.numParams
    && tval₁.numFields == tval₂.numFields
    && tval₁.isUnsafe == tval₂.isUnsafe

/-
Check if two inductive types are the same.
Takes a lookup function to retrieve constructor ConstantInfo by name.
-/
def equivInduct (ctarget cnew : ConstantInfo)
    (lookupTarget lookupNew : Name → Option ConstantInfo) : Bool := Id.run do
  let .inductInfo tval₁ := ctarget | false
  let .inductInfo tval₂ := cnew | false

  -- Check basic fields
  unless tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.numParams == tval₂.numParams
    && tval₁.numIndices == tval₂.numIndices
    && tval₁.all == tval₂.all
    && tval₁.ctors == tval₂.ctors
    && tval₁.isRec == tval₂.isRec
    && tval₁.isReflexive == tval₂.isReflexive
    && tval₁.isUnsafe == tval₂.isUnsafe
  do return false

  -- Check each constructor using equivCtor
  for ctorName in tval₁.ctors do
    let some ctor₁ := lookupTarget ctorName | return false
    let some ctor₂ := lookupNew ctorName | return false
    unless equivCtor ctor₁ ctor₂ do return false

  return true

open Elab Meta Term Tactic

/-- The negation of `e`, i.e. `¬ e`, with metavariables instantiated and
annotations cleaned up first so the result is a plain `Not` application.

Disproving a conjecture means proving its negation, and `¬ e` *is* that negation
by construction -- so `checkNegatedTheorem` can trust this without trusting any
syntactic rewrite. This used to push `not` inwards to negation-normal form (e.g.
`¬ ∀ a, p a` to `∃ a, ¬ p a`), but that hand-written transform was something the
soundness of the disproof check had to trust, and it forced the agent to match
one exact encoding; a `push_neg` in the proof body recovers the NNF goal anyway,
so plain `¬` is both safer and easier to target. -/
private def negateExpr (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).cleanupAnnotations
  return mkNot e

def checkNegatedTheorem {m} [Monad m] [MonadLiftT CoreM m]
    (ctarget cnew : ConstantInfo) : m Bool :=
  -- We run in MetaM but don't really need any context
  Lean.Meta.MetaM.run' do
  unless ctarget.levelParams == cnew.levelParams do return false
  let targetType := ctarget.type
  let negatedType ← negateExpr targetType
  match Lean.Kernel.isDefEq (← getEnv) (← getLCtx) negatedType cnew.type with
  | .error _ =>  return false
  | .ok bool => return bool
