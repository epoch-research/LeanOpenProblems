/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Problems in loop theory and quasigroup theory

The Wikipedia list of unsolved problems in mathematics has the entry "Problems in loop theory and
quasigroup theory consider generalizations of groups", pointing to the article below. This file
states the open problems of that article that have a statable proposition.

Mathlib has no theory of loops, so the file introduces the needed notions: loops, subloops,
normal subloops, the centre, central nilpotency and solvability, the multiplication and inner
mapping groups, isotopy, the free Moufang loop, and laws of a loop.

*References:*
- [Wikipedia, Problems in loop theory and quasigroup
  theory](https://en.wikipedia.org/wiki/Problems_in_loop_theory_and_quasigroup_theory)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- R. H. Bruck, *A survey of binary systems*, Springer (1958), for the standard loop-theoretic
  notions used below.
-/

namespace ProblemsInLoopTheoryAndQuasigroupTheory

noncomputable section

universe u v

/-- A *loop* is a set with a binary operation `*` and a two-sided identity `1` in which
every equation `a * x = b` and `y * a = b` has a unique solution, i.e. all left and right
translations are bijections. -/
class Loop (Q : Type u) extends MulOneClass Q where
  mul_left_bijective (a : Q) : Function.Bijective (a * ·)
  mul_right_bijective (a : Q) : Function.Bijective (· * a)

namespace Loop

variable {Q : Type u} [Loop Q]

/-- The left translation `L_a : x ↦ a * x` as a permutation of the loop. -/
def leftMul (a : Q) : Equiv.Perm Q := Equiv.ofBijective _ (mul_left_bijective a)

/-- The right translation `R_a : x ↦ x * a` as a permutation of the loop. -/
def rightMul (a : Q) : Equiv.Perm Q := Equiv.ofBijective _ (mul_right_bijective a)

@[simp, category API, AMS 20]
lemma leftMul_apply (a x : Q) : leftMul a x = a * x := rfl

@[simp, category API, AMS 20]
lemma rightMul_apply (a x : Q) : rightMul a x = x * a := rfl

/-- Left division: `a ⧵ b` is the unique solution `x` of `a * x = b`. -/
def ldiv (a b : Q) : Q := (leftMul a).symm b

/-- Right division: `a / b` is the unique solution `y` of `y * b = a`. -/
instance : Div Q := ⟨fun a b => (rightMul b).symm a⟩

@[inherit_doc] scoped infixl:70 " ⧵ " => ldiv

@[simp, category API, AMS 20]
lemma mul_ldiv (a b : Q) : a * (a ⧵ b) = b := (leftMul a).apply_symm_apply b

@[simp, category API, AMS 20]
lemma ldiv_mul (a b : Q) : a ⧵ (a * b) = b := (leftMul a).symm_apply_apply b

@[simp, category API, AMS 20]
lemma rdiv_mul (a b : Q) : a / b * b = a := (rightMul b).apply_symm_apply a

@[simp, category API, AMS 20]
lemma mul_rdiv (a b : Q) : a * b / b = a := (rightMul b).symm_apply_apply a

@[category API, AMS 20]
lemma mul_left_cancel {a b c : Q} (h : a * b = a * c) : b = c := (mul_left_bijective a).1 h

@[category API, AMS 20]
lemma mul_right_cancel {a b c : Q} (h : b * a = c * a) : b = c := (mul_right_bijective a).1 h

/-- The left inverse `x^λ = 1 / x` of `x`, the unique element with `x^λ * x = 1`. -/
def leftInv (x : Q) : Q := 1 / x

/-- The right inverse `x^ρ = x ⧵ 1` of `x`, the unique element with `x * x^ρ = 1`. -/
def rightInv (x : Q) : Q := x ⧵ 1

/-- Powers in a loop, bracketed to the left of the last factor: `x ^ 0 = 1` and
`x ^ (n + 1) = x * x ^ n`. In a power-associative loop (e.g. any Moufang loop) this agrees with
every other bracketing. -/
instance : Pow Q ℕ := ⟨fun x n => Nat.rec 1 (fun _ y => x * y) n⟩

@[simp, category API, AMS 20]
lemma pow_zero (x : Q) : x ^ 0 = 1 := rfl

@[simp, category API, AMS 20]
lemma pow_succ (x : Q) (n : ℕ) : x ^ (n + 1) = x * x ^ n := rfl

/-- A loop is a group if and only if it is associative. -/
def IsAssociative (Q : Type u) [Loop Q] : Prop := ∀ x y z : Q, x * y * z = x * (y * z)

/-- A loop is commutative if `x * y = y * x` for all `x`, `y`. -/
def IsCommutative (Q : Type u) [Loop Q] : Prop := ∀ x y : Q, x * y = y * x

/-- A loop is an abelian group if and only if it is associative and commutative. -/
def IsAbelianGroup (Q : Type u) [Loop Q] : Prop := IsAssociative Q ∧ IsCommutative Q

/-- A loop has *exponent `n`* if `x ^ n = 1` for every `x` (the exponent is not required to be
minimal). -/
def HasExponent (Q : Type u) [Loop Q] (n : ℕ) : Prop := ∀ x : Q, x ^ n = 1

/-- A loop is *torsion free* if no element other than `1` has finite order. -/
def IsTorsionFree (Q : Type u) [Loop Q] : Prop :=
  ∀ (x : Q) (k : ℕ), 0 < k → x ^ k = 1 → x = 1

/-- A *Moufang loop* is a loop satisfying the (left) Moufang identity
`x * (y * (x * z)) = ((x * y) * x) * z`. -/
class IsMoufang (Q : Type u) [Loop Q] : Prop where
  moufang (x y z : Q) : x * (y * (x * z)) = x * y * x * z

/-- A *left Bol loop* is a loop satisfying the left Bol identity
`x * (y * (x * z)) = (x * (y * x)) * z`. -/
class IsLeftBol (Q : Type u) [Loop Q] : Prop where
  left_bol (x y z : Q) : x * (y * (x * z)) = x * (y * x) * z

/-- A loop is *flexible* if `(x * y) * x = x * (y * x)` for all `x`, `y`. -/
def IsFlexible (Q : Type u) [Loop Q] : Prop := ∀ x y : Q, x * y * x = x * (y * x)

/-- A loop has the *antiautomorphic inverse property* if `(x * y)^λ = y^λ * x^λ` for all
`x`, `y`, where `x^λ` is the left inverse (this forces inverses to be two-sided). -/
def HasAntiautomorphicInverseProperty (Q : Type u) [Loop Q] : Prop :=
  ∀ x y : Q, leftInv (x * y) = leftInv y * leftInv x

/-- A loop is *Osborn* if it satisfies `x * ((y * z) * x) = (x^λ ⧵ y) * (z * x)`, where `x^λ` is
the left inverse of `x`. -/
def IsOsborn (Q : Type u) [Loop Q] : Prop :=
  ∀ x y z : Q, x * (y * z * x) = (leftInv x ⧵ y) * (z * x)

/-- Two loops `Q` and `Q'` are *isotopic* if there are bijections `α β γ : Q → Q'` with
`γ (x * y) = α x * β y` for all `x`, `y`; `Q'` is then called a (loop) isotope of `Q`. -/
def IsIsotope (Q : Type u) (Q' : Type v) [Loop Q] [Loop Q'] : Prop :=
  ∃ α β γ : Q ≃ Q', ∀ x y : Q, γ (x * y) = α x * β y

/-- A loop is *universally flexible* if every one of its loop isotopes is flexible. -/
def IsUniversallyFlexible (Q : Type u) [Loop Q] : Prop :=
  ∀ (Q' : Type u) [Loop Q'], IsIsotope Q Q' → IsFlexible Q'

/-- A loop is *middle Bol* if every one of its loop isotopes has the antiautomorphic inverse
property. -/
def IsMiddleBol (Q : Type u) [Loop Q] : Prop :=
  ∀ (Q' : Type u) [Loop Q'], IsIsotope Q Q' → HasAntiautomorphicInverseProperty Q'

end Loop

open Loop

/-- A *subloop* of a loop `Q` is a subset containing `1` and closed under multiplication and both
divisions. -/
structure Subloop (Q : Type u) [Loop Q] where
  /-- The underlying set of the subloop. -/
  carrier : Set Q
  one_mem' : (1 : Q) ∈ carrier
  mul_mem' {a b : Q} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  ldiv_mem' {a b : Q} : a ∈ carrier → b ∈ carrier → a ⧵ b ∈ carrier
  div_mem' {a b : Q} : a ∈ carrier → b ∈ carrier → a / b ∈ carrier

namespace Subloop

variable {Q : Type u} [Loop Q]

instance : SetLike (Subloop Q) Q where
  coe := carrier
  coe_injective' := by
    rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
    congr

@[category API, AMS 20]
lemma one_mem (S : Subloop Q) : (1 : Q) ∈ S := S.one_mem'

@[category API, AMS 20]
lemma mul_mem (S : Subloop Q) {a b : Q} (ha : a ∈ S) (hb : b ∈ S) : a * b ∈ S :=
  S.mul_mem' ha hb

@[category API, AMS 20]
lemma ldiv_mem (S : Subloop Q) {a b : Q} (ha : a ∈ S) (hb : b ∈ S) : a ⧵ b ∈ S :=
  S.ldiv_mem' ha hb

@[category API, AMS 20]
lemma div_mem (S : Subloop Q) {a b : Q} (ha : a ∈ S) (hb : b ∈ S) : a / b ∈ S :=
  S.div_mem' ha hb

/-- A subloop is itself a loop. -/
instance (S : Subloop Q) : Loop S where
  mul a b := ⟨a * b, S.mul_mem a.2 b.2⟩
  one := ⟨1, S.one_mem⟩
  one_mul a := Subtype.ext (one_mul (a : Q))
  mul_one a := Subtype.ext (mul_one (a : Q))
  mul_left_bijective a :=
    ⟨fun _ _ h => Subtype.ext (mul_left_cancel (congrArg Subtype.val h)),
      fun b => ⟨⟨a ⧵ b, S.ldiv_mem a.2 b.2⟩, Subtype.ext (mul_ldiv (a : Q) b)⟩⟩
  mul_right_bijective a :=
    ⟨fun _ _ h => Subtype.ext (mul_right_cancel (congrArg Subtype.val h)),
      fun b => ⟨⟨b / a, S.div_mem b.2 a.2⟩, Subtype.ext (rdiv_mul (b : Q) a)⟩⟩

/-- The whole loop, as a subloop of itself. -/
instance : Top (Subloop Q) :=
  ⟨{ carrier := Set.univ
     one_mem' := trivial
     mul_mem' := fun _ _ => trivial
     ldiv_mem' := fun _ _ => trivial
     div_mem' := fun _ _ => trivial }⟩

/-- The trivial subloop `{1}`. -/
instance : Bot (Subloop Q) :=
  ⟨{ carrier := {1}
     one_mem' := rfl
     mul_mem' := fun ha hb => by simp_all
     ldiv_mem' := fun ha hb => by
       simp only [Set.mem_singleton_iff] at *
       subst ha hb
       simpa using ldiv_mul (1 : Q) 1
     div_mem' := fun ha hb => by
       simp only [Set.mem_singleton_iff] at *
       subst ha hb
       simpa using mul_rdiv (1 : Q) 1 }⟩

instance : OrderTop (Subloop Q) where
  le_top _ _ _ := trivial

@[ext, category API, AMS 20]
lemma ext {S T : Subloop Q} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

@[simp, category API, AMS 20]
lemma mem_top (x : Q) : x ∈ (⊤ : Subloop Q) := trivial

@[simp, category API, AMS 20]
lemma mem_bot {x : Q} : x ∈ (⊥ : Subloop Q) ↔ x = 1 := Iff.rfl

/-- A subloop `N` of `Q` is *normal* if `x N = N x`, `(x N) y = x (N y)` and `x (y N) = (x y) N`
for all `x y : Q` (Bruck). -/
def IsNormal (N : Subloop Q) : Prop :=
  ∀ x y : Q,
    (fun n => x * n) '' N = (fun n => n * x) '' N ∧
    (fun n => x * n * y) '' N = (fun n => x * (n * y)) '' N ∧
    (fun n => x * (y * n)) '' N = (fun n => x * y * n) '' N

end Subloop

namespace Loop

variable {Q : Type u} [Loop Q]

/-- A set `s` *generates* the loop `Q` if no proper subloop contains it. -/
def IsGeneratedBy (s : Set Q) : Prop := ∀ S : Subloop Q, s ⊆ S → S = ⊤

/-- A loop is *finitely generated* if it is generated by a finite set. -/
def IsFinitelyGenerated (Q : Type u) [Loop Q] : Prop := ∃ s : Finset Q, IsGeneratedBy (s : Set Q)

/-- A loop is *simple* if it is nontrivial and its only normal subloops are `⊥` and `⊤`. -/
def IsSimple (Q : Type u) [Loop Q] : Prop :=
  Nontrivial Q ∧ ∀ N : Subloop Q, N.IsNormal → N = ⊥ ∨ N = ⊤

/-- The *Frattini subloop* `Φ(Q)`: the intersection of all maximal subloops of `Q` (the whole
loop `Q` if there are none). -/
def frattini (Q : Type u) [Loop Q] : Subloop Q where
  carrier := {x | ∀ S : Subloop Q, IsCoatom S → x ∈ S}
  one_mem' _ _ := Subloop.one_mem _
  mul_mem' ha hb S hS := S.mul_mem (ha S hS) (hb S hS)
  ldiv_mem' ha hb S hS := S.ldiv_mem (ha S hS) (hb S hS)
  div_mem' ha hb S hS := S.div_mem (ha S hS) (hb S hS)

/-- The *center* `Z(Q)` of a loop: the elements that commute and associate with all elements. -/
def center (Q : Type u) [Loop Q] : Set Q :=
  {a | ∀ x y : Q, a * x = x * a ∧ a * x * y = a * (x * y) ∧ x * a * y = x * (a * y) ∧
    x * y * a = x * (y * a)}

/-- A multiplicative map `φ : Q → Q'` from a loop `Q` (a loop homomorphism, when `Q'` is a loop)
*realises `Q'` as the quotient loop `Q / N`* if it is surjective with kernel `N`. -/
def IsQuotientHom {Q' : Type v} [MulOneClass Q'] (N : Set Q) (φ : Q →ₙ* Q') : Prop :=
  Function.Surjective φ ∧ ∀ x, φ x = 1 ↔ x ∈ N

/-- `IsNilpotentOfClassLE n Q` says that the loop `Q` is centrally nilpotent of class at most `n`:
`Q` is trivial when `n = 0`, and for `n + 1` the quotient `Q / Z(Q)` (realised as any
surjective homomorphic image with kernel `Z(Q)`) is nilpotent of class at most `n`. -/
def IsNilpotentOfClassLE : ℕ → (Q : Type u) → [Loop Q] → Prop
  | 0, Q, _ => Subsingleton Q
  | n + 1, Q, _ => ∃ (Q' : Type u) (_ : Loop Q') (φ : Q →ₙ* Q'),
      IsQuotientHom (center Q) φ ∧ IsNilpotentOfClassLE n Q'

/-- A loop is (centrally) *nilpotent* if it is nilpotent of some finite class. -/
def IsNilpotent (Q : Type u) [Loop Q] : Prop := ∃ n, IsNilpotentOfClassLE n Q

/-- `IsSolvableOfLengthLE n Q` says that the loop `Q` has a subnormal series of length at most `n`
with abelian group factors: `Q` is trivial when `n = 0`, and for `n + 1` there is a normal
subloop `N` such that `Q / N` is an abelian group and `N` is solvable of length at most `n`. -/
def IsSolvableOfLengthLE : ℕ → (Q : Type u) → [Loop Q] → Prop
  | 0, Q, _ => Subsingleton Q
  | n + 1, Q, _ => ∃ (N : Subloop Q) (Q' : Type u) (_ : Loop Q') (φ : Q →ₙ* Q'),
      IsQuotientHom (N : Set Q) φ ∧ IsAbelianGroup Q' ∧ IsSolvableOfLengthLE n N

/-- A loop is *solvable* if it has a finite subnormal series with abelian group factors. -/
def IsSolvable (Q : Type u) [Loop Q] : Prop := ∃ n, IsSolvableOfLengthLE n Q

/-- The *multiplication group* `Mlt(Q)`: the permutation group generated by all left and right
translations. -/
def multiplicationGroup (Q : Type u) [Loop Q] : Subgroup (Equiv.Perm Q) :=
  Subgroup.closure (Set.range leftMul ∪ Set.range rightMul)

/-- The *inner mapping group* `Inn(Q)`: the stabiliser of `1` in the multiplication group. -/
def innerMappingGroup (Q : Type u) [Loop Q] : Subgroup (Equiv.Perm Q) :=
  multiplicationGroup Q ⊓ MulAction.stabilizer (Equiv.Perm Q) (1 : Q)

/-- An *automorphic loop* is a loop all of whose inner mappings are automorphisms. -/
def IsAutomorphic (Q : Type u) [Loop Q] : Prop :=
  ∀ θ ∈ innerMappingGroup Q, ∀ x y : Q, θ (x * y) = θ x * θ y

/-- The *distance* between two loop structures on the same set: the number of pairs `(a, b)` at
which the two multiplication tables differ. -/
def tableDist (L₁ L₂ : Loop Q) : ℕ :=
  Nat.card {p : Q × Q // L₁.mul p.1 p.2 ≠ L₂.mul p.1 p.2}

/-- A class `P` of loops is *quadratic* if there is `α > 0` such that any two loops from the
class on the same finite set of order `n` at distance `< α n²` are isomorphic. -/
def IsQuadraticClass (P : ∀ Q : Type, Loop Q → Prop) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ (Q : Type) [Finite Q] (L₁ L₂ : Loop Q), P Q L₁ → P Q L₂ →
    (tableDist L₁ L₂ : ℝ) < α * (Nat.card Q : ℝ) ^ 2 →
      Nonempty (@MulEquiv Q Q L₁.toMul L₂.toMul)

end Loop

/-- Terms in the language of loops (`1`, `*`, left division `⧵`, right division `/`) with
variables from `α`. -/
inductive Term (α : Type) : Type
  | var : α → Term α
  | one : Term α
  | mul : Term α → Term α → Term α
  | ldiv : Term α → Term α → Term α
  | div : Term α → Term α → Term α

namespace Term

variable {α : Type} {Q : Type u} [Loop Q]

/-- Evaluate a term in a loop `Q` under an assignment `f` of the variables. -/
def eval (f : α → Q) : Term α → Q
  | var a => f a
  | one => 1
  | mul s t => eval f s * eval f t
  | ldiv s t => eval f s ⧵ eval f t
  | div s t => eval f s / eval f t

/-- Two terms are *Moufang equivalent* if they take the same value under every assignment in
every Moufang loop, i.e. `s = t` is an identity of the variety of Moufang loops. -/
instance moufangSetoid (α : Type) : Setoid (Term α) where
  r s t := ∀ (M : Type) [Loop M] [IsMoufang M] (f : α → M), s.eval f = t.eval f
  iseqv :=
    { refl := fun _ _ _ _ _ => rfl
      symm := fun h M _ _ f => (h M f).symm
      trans := fun h₁ h₂ M _ _ f => (h₁ M f).trans (h₂ M f) }

end Term

/-- The *free Moufang loop* `MF(α)` on the set `α` of free generators: the loop of all terms
modulo the identities of Moufang loops. -/
def FreeMoufangLoop (α : Type) : Type := Quotient (Term.moufangSetoid α)

namespace FreeMoufangLoop

variable {α : Type}

instance : Loop (FreeMoufangLoop α) where
  one := ⟦.one⟧
  mul := Quotient.map₂ .mul fun _ _ h₁ _ _ h₂ M _ _ f => by
    simp only [Term.eval, h₁ M f, h₂ M f]
  one_mul a := Quotient.inductionOn a fun t => Quotient.sound fun M _ _ f => by
    simp [Term.eval]
  mul_one a := Quotient.inductionOn a fun t => Quotient.sound fun M _ _ f => by
    simp [Term.eval]
  mul_left_bijective a := Quotient.inductionOn a fun s => ⟨fun x y => by
      refine Quotient.inductionOn₂ x y fun t₁ t₂ h => Quotient.sound fun M _ _ f => ?_
      exact mul_left_cancel (Quotient.exact h M f),
    fun x => Quotient.inductionOn x fun t => ⟨⟦.ldiv s t⟧, Quotient.sound fun M _ _ f => by
      simp [Term.eval]⟩⟩
  mul_right_bijective a := Quotient.inductionOn a fun s => ⟨fun x y => by
      refine Quotient.inductionOn₂ x y fun t₁ t₂ h => Quotient.sound fun M _ _ f => ?_
      exact mul_right_cancel (Quotient.exact h M f),
    fun x => Quotient.inductionOn x fun t => ⟨⟦.div t s⟧, Quotient.sound fun M _ _ f => by
      simp [Term.eval]⟩⟩

instance : IsMoufang (FreeMoufangLoop α) where
  moufang x y z := Quotient.inductionOn₃ x y z fun _ _ _ => Quotient.sound fun M _ _ f => by
    simp only [Term.eval]
    exact IsMoufang.moufang _ _ _

/-- The free generators of the free Moufang loop. -/
def of (a : α) : FreeMoufangLoop α := ⟦.var a⟧

end FreeMoufangLoop

namespace Loop

/-- The identity `s = t` (in the language of loops, with variables indexed by `ℕ`) is a *law* of
the loop `Q` if it holds under every assignment of the variables in `Q`. -/
def IsLaw (Q : Type u) [Loop Q] (s t : Term ℕ) : Prop := ∀ f : ℕ → Q, s.eval f = t.eval f

/-- The laws of `Q` have a *finite basis* if there is a finite set `B` of laws of `Q` such that
every law of `Q` holds in every loop satisfying all identities in `B` (i.e. is a consequence
of `B`). -/
def HasFiniteBasisOfLaws (Q : Type u) [Loop Q] : Prop :=
  ∃ B : Finset (Term ℕ × Term ℕ), (∀ p ∈ B, IsLaw Q p.1 p.2) ∧
    ∀ s t : Term ℕ, IsLaw Q s t →
      ∀ (R : Type) [Loop R], (∀ p ∈ B, IsLaw R p.1 p.2) → IsLaw R s t

/-- A Moufang loop is flexible: `(x * y) * x = x * (y * x)`. -/
@[category API, AMS 20]
lemma IsMoufang.isFlexible (Q : Type u) [Loop Q] [IsMoufang Q] : IsFlexible Q := fun x y => by
  simpa using (IsMoufang.moufang x y (1 : Q)).symm

/-- Every Moufang loop is a left Bol loop. -/
@[category API, AMS 20]
lemma IsMoufang.isLeftBol (Q : Type u) [Loop Q] [IsMoufang Q] : IsLeftBol Q where
  left_bol x y z := by rw [IsMoufang.moufang, IsMoufang.isFlexible Q x y]

/-- A loop is nilpotent of class at most `0` if and only if it is trivial. -/
@[category test, AMS 20]
lemma isNilpotentOfClassLE_zero_iff (Q : Type u) [Loop Q] :
    IsNilpotentOfClassLE 0 Q ↔ Subsingleton Q := Iff.rfl

end Loop

/-- A (not necessarily associative) ring is *alternative* if it satisfies the left and right
alternative laws `(a * a) * b = a * (a * b)` and `(b * a) * a = b * (a * a)`. -/
def IsAlternative (A : Type u) [Mul A] : Prop :=
  (∀ a b : A, a * a * b = a * (a * b)) ∧ ∀ a b : A, b * a * a = b * (a * a)

/- ## Open problems (Moufang loops) -/

/--
**Abelian by cyclic groups resulting in Moufang loops, (i).**
Let $L$ be a Moufang loop with a normal abelian subgroup (associative subloop) $M$ of odd order
such that $L/M$ is a cyclic group of order bigger than $3$. Is $L$ a group?

The quotient $L/M$ is realised as any surjective homomorphic image of $L$ with kernel $M$; both
$M$ and $L/M$ are finite (`Nat.card` of an infinite type is `0`).
The hypothesis that $L/M$ has order bigger than $3$ is important: there is a commutative Moufang
loop of order $81$ with a normal commutative subgroup of order $27$.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.i :
    answer(sorry) ↔ ∀ (L : Type*) [Loop L] [IsMoufang L] (M : Subloop L), M.IsNormal →
      IsAbelianGroup M → Odd (Nat.card M) →
      ∀ (C : Type*) [Group C] [IsCyclic C] (φ : L →ₙ* C), IsQuotientHom (M : Set L) φ →
      3 < Nat.card C → IsAssociative L := by
  sorry

/--
**Abelian by cyclic groups resulting in Moufang loops, (ii).**
Let $L$ be a Moufang loop with a normal abelian subgroup (associative subloop) $M$ of odd order
such that $L/M$ is a cyclic group of order bigger than $3$. If the orders of $M$ and $L/M$ are
relatively prime, is $L$ a group?
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.i.variants.coprime :
    answer(sorry) ↔ ∀ (L : Type*) [Loop L] [IsMoufang L] (M : Subloop L), M.IsNormal →
      IsAbelianGroup M → Odd (Nat.card M) →
      ∀ (C : Type*) [Group C] [IsCyclic C] (φ : L →ₙ* C), IsQuotientHom (M : Set L) φ →
      3 < Nat.card C → Nat.Coprime (Nat.card M) (Nat.card C) → IsAssociative L := by
  sorry

/--
**Embedding CMLs of period 3 into alternative algebras.**
Conjecture: any finite commutative Moufang loop of period $3$ (i.e. $x^3 = 1$ for all $x$) can be
embedded into a commutative alternative algebra.

Here an embedding is an injective multiplicative map $L \to A$ sending $1$ to $1$, i.e. an
isomorphism of $L$ onto a subloop of the multiplicative loop of invertible elements of a unital
commutative alternative algebra $A$ over some field $F$.
-/
@[category research open, AMS 17 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.ii :
    ∀ (L : Type*) [Loop L] [IsMoufang L] [Finite L], Loop.IsCommutative L → HasExponent L 3 →
      ∃ (F : Type) (_ : Field F) (A : Type) (_ : NonAssocCommRing A) (_ : Module F A)
        (_ : IsScalarTower F A A) (_ : SMulCommClass F A A),
        IsAlternative A ∧ ∃ φ : L →ₙ* A, Function.Injective φ ∧ φ 1 = 1 := by
  sorry

/--
**Frattini subloop for Moufang loops.**
Conjecture: let $L$ be a finite Moufang loop and $\Phi(L)$ the intersection of all maximal
subloops of $L$. Then $\Phi(L)$ is a normal nilpotent subloop of $L$.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.iii :
    ∀ (L : Type*) [Loop L] [IsMoufang L] [Finite L],
      (Loop.frattini L).IsNormal ∧ Loop.IsNilpotent (Loop.frattini L) := by
  sorry

/--
**The restricted Burnside problem for Moufang loops.**
Conjecture: let $M$ be a finite Moufang loop of exponent $n$ with $m$ generators. Then there
exists a function $f(n, m)$ such that $|M| < f(n, m)$.

The exponent $n$ is a positive integer, and "$m$ generators" means that $M$ is generated by the
values of some map $\mathrm{Fin}\ m \to M$.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.iv :
    ∃ f : ℕ → ℕ → ℕ, ∀ (n m : ℕ), 0 < n →
      ∀ (M : Type*) [Loop M] [IsMoufang M] [Finite M], HasExponent M n →
        (∃ g : Fin m → M, IsGeneratedBy (Set.range g)) → Nat.card M < f n m := by
  sorry

/--
**The Sanov and M. Hall theorems for Moufang loops.**
Conjecture: let $L$ be a finitely generated Moufang loop of exponent $4$ or $6$. Then $L$ is
finite.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.v :
    ∀ (L : Type*) [Loop L] [IsMoufang L], IsFinitelyGenerated L →
      (HasExponent L 4 ∨ HasExponent L 6) → Finite L := by
  sorry

/--
**Torsion in free Moufang loops.**
Let $MF_n$ be the free Moufang loop with $n$ generators.
Conjecture: $MF_3$ is torsion free but $MF_n$ with $n > 4$ is not.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.vi :
    IsTorsionFree (FreeMoufangLoop (Fin 3)) ∧
      ∀ n : ℕ, 4 < n → ¬ IsTorsionFree (FreeMoufangLoop (Fin n)) := by
  sorry

/- ## Open problems (Bol loops) -/

/--
**Are two Bol loops with similar multiplication tables isomorphic?**
Let $(Q, *)$, $(Q, +)$ be two quasigroups defined on the same underlying set $Q$. The distance
$d(*, +)$ is the number of pairs $(a, b)$ in $Q \times Q$ such that $a * b \neq a + b$. Call a
class of finite quasigroups quadratic if there is a positive real number $\alpha$ such that any
two quasigroups $(Q, *)$, $(Q, +)$ of order $n$ from the class satisfying $d(*, +) < \alpha n^2$
are isomorphic. Are Moufang loops quadratic?

Drápal proved that groups are quadratic with $\alpha = 1/9$.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.vii :
    answer(sorry) ↔ IsQuadraticClass fun Q L => @IsMoufang Q L := by
  sorry

/--
**Are two Bol loops with similar multiplication tables isomorphic?**
Are (left) Bol loops quadratic, in the sense of
`problems_in_loop_theory_and_quasigroup_theory.parts.vii`?
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.vii.variants.bol :
    answer(sorry) ↔ IsQuadraticClass fun Q L => @IsLeftBol Q L := by
  sorry

/--
**Universally flexible loop that is not middle Bol.**
A loop is universally flexible if every one of its loop isotopes is flexible, that is, satisfies
$(xy)x = x(yx)$. A loop is middle Bol if every one of its loop isotopes has the antiautomorphic
inverse property, that is, satisfies $(xy)^{-1} = y^{-1}x^{-1}$. Is there a finite, universally
flexible loop that is not middle Bol?
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.viii :
    answer(sorry) ↔ ∃ (Q : Type) (_ : Loop Q), Finite Q ∧ IsUniversallyFlexible Q ∧
      ¬ IsMiddleBol Q := by
  sorry

/- ## Open problems (nilpotency and solvability) -/

/--
**Niemenmaa's conjecture.**
Let $Q$ be a loop whose inner mapping group is nilpotent. Is $Q$ nilpotent?

The answer is affirmative if $Q$ is finite (Niemenmaa 2009); the general case is open.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.x :
    answer(sorry) ↔ ∀ (Q : Type*) [Loop Q],
      Group.IsNilpotent (innerMappingGroup Q) → Loop.IsNilpotent Q := by
  sorry

/--
**Niemenmaa's conjecture, solvable version.**
Let $Q$ be a loop whose inner mapping group is nilpotent. Is $Q$ solvable?
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.x.variants.solvable :
    answer(sorry) ↔ ∀ (Q : Type*) [Loop Q],
      Group.IsNilpotent (innerMappingGroup Q) → Loop.IsSolvable Q := by
  sorry

/--
**Loops with abelian inner mapping group.**
Let $Q$ be a loop with abelian inner mapping group. Is $Q$ nilpotent?

When the inner mapping group is finite and abelian, $Q$ is nilpotent (Niemenmaa–Kepka), so the
question is open only in the infinite case.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.xi :
    answer(sorry) ↔ ∀ (Q : Type*) [Loop Q],
      IsMulCommutative (innerMappingGroup Q) → Loop.IsNilpotent Q := by
  sorry

/--
**Loops with abelian inner mapping group, bounded class.**
Let $Q$ be a loop with abelian inner mapping group. If $Q$ is nilpotent, is there a bound on the
nilpotency class of $Q$? That is, is there $c$ such that every nilpotent loop with abelian inner
mapping group has nilpotency class at most $c$?
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.xi.variants.bounded_class :
    answer(sorry) ↔ ∃ c : ℕ, ∀ (Q : Type*) [Loop Q],
      IsMulCommutative (innerMappingGroup Q) → Loop.IsNilpotent Q →
        IsNilpotentOfClassLE c Q := by
  sorry

/--
**Loops with abelian inner mapping group, class higher than 3.**
Let $Q$ be a loop with abelian inner mapping group. Can the nilpotency class of $Q$ be higher
than $3$? That is, is there a nilpotent loop of nilpotency class at least $4$ with abelian inner
mapping group?

Nilpotent loops of class $3$ with abelian inner mapping group (loops of Csörgő type) exist, but
no such loop of class higher than $3$ is known.
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.xi.variants.class_gt_three :
    answer(sorry) ↔ ∃ (Q : Type) (_ : Loop Q), IsMulCommutative (innerMappingGroup Q) ∧
      Loop.IsNilpotent Q ∧ ¬ IsNilpotentOfClassLE 3 Q := by
  sorry

/--
**A finite nilpotent loop without a finite basis for its laws.**
Construct a finite nilpotent loop with no finite basis for its laws (Vaughan-Lee, Kourovka
Notebook), i.e. does there exist a finite nilpotent loop whose laws are not finitely based?

There is a finite loop with no finite basis for its laws (Vaughan-Lee 1979), but it is not
nilpotent.
-/
@[category research open, AMS 8 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.xii :
    answer(sorry) ↔ ∃ (Q : Type) (_ : Loop Q), Finite Q ∧ Loop.IsNilpotent Q ∧
      ¬ HasFiniteBasisOfLaws Q := by
  sorry

/- ## Open problems (miscellaneous) -/

/--
**Finite simple nonassociative automorphic loop.**
Find a nonassociative finite simple automorphic loop, if such a loop exists; i.e. does there
exist a nonassociative finite simple automorphic loop?

Such a loop cannot be commutative (Grishkov, Kinyon and Nagy 2013) nor have odd order (Kinyon,
Kunen, Phillips and Vojtěchovský 2013).
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.xiii :
    answer(sorry) ↔ ∃ (Q : Type) (_ : Loop Q), Finite Q ∧ IsSimple Q ∧ IsAutomorphic Q ∧
      ¬ IsAssociative Q := by
  sorry

/--
**Universality of Osborn loops.**
A loop is Osborn if it satisfies the identity $x((yz)x) = (x^\lambda \backslash y)(zx)$, where
$x^\lambda$ is the left inverse of $x$. Is every Osborn loop universal, that is, is every isotope
of an Osborn loop Osborn?
-/
@[category research open, AMS 20]
theorem problems_in_loop_theory_and_quasigroup_theory.parts.xiv :
    answer(sorry) ↔ ∀ (Q : Type*) [Loop Q], IsOsborn Q →
      ∀ (Q' : Type*) [Loop Q'], IsIsotope Q Q' → IsOsborn Q' := by
  sorry

end

end ProblemsInLoopTheoryAndQuasigroupTheory
