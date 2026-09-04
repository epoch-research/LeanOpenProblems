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
# Stable field conjecture

The stable field conjecture states that every infinite field with a stable first-order theory
is separably closed. Here the first-order theory of a field $K$ is its complete theory
$\mathrm{Th}(K)$ in the language of rings $\{+, \cdot, -, 0, 1\}$.

Mathlib does not define stability of a first-order theory, so it is defined here. A theory $T$
is *stable* if no formula has the order property in $T$, i.e. there are no formula
$\varphi(\bar{x}, \bar{y})$ and sequences of tuples $(\bar{a}_i)_{i \in \mathbb{N}}$,
$(\bar{b}_j)_{j \in \mathbb{N}}$ in a model of $T$ such that $\varphi(\bar{a}_i, \bar{b}_j)$
holds if and only if $i \le j$. For a complete theory this is equivalent to $T$ being
$\kappa$-stable for some infinite cardinal $\kappa$.

Finite fields are excluded because every finite structure has a stable theory but a finite field
is not separably closed. The converse of the conjecture is a theorem of Wood: every separably
closed field has a stable theory.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Stable theory](https://en.wikipedia.org/wiki/Stable_theory)
-/

namespace StableFieldConjecture

open FirstOrder Language

universe u v

variable {L : FirstOrder.Language.{u, v}}

/-- A formula `φ(x̄, ȳ)`, with variables split as `Fin m ⊕ Fin n`, has the *order property* in
the theory `T` if there are a model `M` of `T` and sequences `(aᵢ)ᵢ`, `(bⱼ)ⱼ` of tuples
in `M` indexed by `ℕ` such that `φ(aᵢ, bⱼ)` holds in `M` if and only if `i ≤ j`.

The models are taken in `Type (max u v)`, as in `FirstOrder.Language.Theory.IsSatisfiable`;
by the downward Löwenheim–Skolem theorem this does not change the notion. -/
def HasOrderProperty (T : L.Theory) {m n : ℕ} (φ : L.Formula (Fin m ⊕ Fin n)) : Prop :=
  ∃ (M : Theory.ModelType.{u, v, max u v} T) (a : ℕ → Fin m → M) (b : ℕ → Fin n → M),
    ∀ i j, φ.Realize (Sum.elim (a i) (b j)) ↔ i ≤ j

/-- A theory `T` is *stable* if no formula has the order property in `T`. -/
def IsStable (T : L.Theory) : Prop :=
  ∀ {m n : ℕ} (φ : L.Formula (Fin m ⊕ Fin n)), ¬ HasOrderProperty T φ

/-- The complete theory of a finite structure is stable. -/
@[category API, AMS 3]
theorem isStable_completeTheory_of_finite (M : Type*) [L.Structure M] [Nonempty M] [Finite M] :
    IsStable (L.completeTheory M) := by
  rintro m n φ ⟨N, a, b, hab⟩
  have hN : Finite N := by
    have h := (realize_iff_of_model_completeTheory M N
      (Sentence.cardGe L (Nat.card M + 1)).not).2
    simp only [Sentence.realize_not, Sentence.realize_cardGe, not_le] at h
    have h' := h (by rw [← Nat.cast_card]; exact_mod_cast lt_add_one _)
    exact Cardinal.lt_aleph0_iff_finite.1 (h'.trans Cardinal.natCast_lt_aleph0)
  have ha : Function.Injective a := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := (hab i i).2 le_rfl
      rw [hij] at h1
      exact absurd ((hab j i).1 h1) (not_le.2 h)
    · have h1 := (hab j j).2 le_rfl
      rw [← hij] at h1
      exact absurd ((hab i j).1 h1) (not_le.2 h)
  exact not_injective_infinite_finite a ha

/-- The theory of dense linear orders without endpoints is not stable: the formula `x ≤ y` has
the order property, witnessed in `ℚ`. -/
@[category test, AMS 3]
theorem not_isStable_dlo : ¬ IsStable Language.order.dlo := by
  letI := orderStructure ℚ
  intro h
  refine h (leSymb.formula₂ (var (Sum.inl 0)) (var (Sum.inr 0)) :
    Language.order.Formula (Fin 1 ⊕ Fin 1)) ?_
  refine ⟨Theory.ModelType.of _ ℚ, fun i _ => (i : ℚ), fun j _ => (j : ℚ), fun i j => ?_⟩
  simp

/--
**Stable field conjecture.** Every infinite field $K$ whose complete first-order theory
$\mathrm{Th}(K)$ in the language of rings is stable is separably closed.

The hypothesis `CompatibleRing K` equips `K` with its `Language.ring`-structure in which the
symbols are interpreted by the field operations; every field admits such a structure
(`FirstOrder.Ring.compatibleRingOfRing`). The field must be infinite: finite fields have a
stable theory but are not separably closed.
-/
@[category research open, AMS 3 12]
theorem stable_field_conjecture (K : Type*) [Field K] [Infinite K] [Ring.CompatibleRing K]
    (hK : IsStable (Language.ring.completeTheory K)) : IsSepClosed K := by
  sorry

end StableFieldConjecture
