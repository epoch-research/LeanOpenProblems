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
# Generalized continuum hypothesis and diamond at successors of singular cardinals

The generalized continuum hypothesis (GCH) states that $2^\kappa = \kappa^+$ for every infinite
cardinal $\kappa$.

For an ordinal $\kappa$, a set $C \subseteq \kappa$ is a *club* in $\kappa$ if it is closed in
$\kappa$ and unbounded in $\kappa$, and a set $S \subseteq \kappa$ is *stationary* in $\kappa$ if it
meets every club in $\kappa$. For $S \subseteq \kappa$, the diamond principle $\diamondsuit(S)$
states that there is a sequence $\langle A_\alpha : \alpha < \kappa \rangle$ with
$A_\alpha \subseteq \alpha$ such that for every $A \subseteq \kappa$ the set
$\{\alpha \in S : A \cap \alpha = A_\alpha\}$ is stationary in $\kappa$.

Shelah proved that if $\lambda \geq \aleph_1$ and $2^\lambda = \lambda^+$, then $\diamondsuit(S)$
holds for every stationary $S \subseteq \{\delta < \lambda^+ :
\operatorname{cf}(\delta) \neq \operatorname{cf}(\lambda)\}$. This leaves open the set
$E^{\lambda^+}_{\operatorname{cf}(\lambda)} = \{\delta < \lambda^+ :
\operatorname{cf}(\delta) = \operatorname{cf}(\lambda)\}$. The problem asks whether GCH entails
$\diamondsuit(E^{\lambda^+}_{\operatorname{cf}(\lambda)})$ for every singular cardinal $\lambda$.

*References:*
- [Wikipedia, Continuum hypothesis (generalized continuum hypothesis)](https://en.wikipedia.org/wiki/generalized_continuum_hypothesis)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [S. Shelah, *Diamonds*, Proc. Amer. Math. Soc. 138 (2010), 2151–2161](https://arxiv.org/abs/0711.3030)
-/

namespace GeneralizedContinuumHypothesis

open Cardinal Ordinal Order Set

universe u

/-- The generalized continuum hypothesis: $2^\kappa = \kappa^+$ for every infinite cardinal
$\kappa$. Here `succ κ` is the successor cardinal $\kappa^+$. -/
def GCH : Prop :=
  ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → 2 ^ κ = succ κ

/-- GCH implies the continuum hypothesis $2^{\aleph_0} = \aleph_1$. -/
@[category test, AMS 3]
theorem GCH.two_power_aleph0 (h : GCH.{u}) : 2 ^ (ℵ₀ : Cardinal.{u}) = ℵ₁ := by
  rw [← succ_aleph0]
  exact h ℵ₀ le_rfl

/-- A set of ordinals `C` is *club* in the ordinal `κ` if `C ⊆ κ`, `C` is closed in `κ`
(it contains every accumulation point below `κ`), and `C` is unbounded in `κ`. -/
def IsClub (C : Set Ordinal.{u}) (κ : Ordinal.{u}) : Prop :=
  C ⊆ Iio κ ∧ IsClosedBelow C κ ∧ ∀ α < κ, ∃ β ∈ C, α < β

/-- A limit ordinal is club in itself. -/
@[category API, AMS 3]
theorem isClub_Iio {κ : Ordinal.{u}} (hκ : IsSuccLimit κ) : IsClub (Iio κ) κ :=
  ⟨le_rfl, isClosedBelow_iff.2 fun _ hp _ ↦ hp,
    fun α hα ↦ ⟨succ α, hκ.succ_lt hα, lt_succ α⟩⟩

/-- A set of ordinals `S` is *stationary* in the ordinal `κ` if it meets every set that is
club in `κ`. -/
def IsStationary (S : Set Ordinal.{u}) (κ : Ordinal.{u}) : Prop :=
  ∀ C, IsClub C κ → (S ∩ C).Nonempty

/-- A superset of a stationary set is stationary. -/
@[category API, AMS 3]
theorem IsStationary.mono {S T : Set Ordinal.{u}} {κ : Ordinal.{u}} (hST : S ⊆ T)
    (hS : IsStationary S κ) : IsStationary T κ :=
  fun C hC ↦ (hS C hC).mono (inter_subset_inter_left C hST)

/-- A stationary set in a limit ordinal `κ` is nonempty. -/
@[category API, AMS 3]
theorem IsStationary.nonempty {S : Set Ordinal.{u}} {κ : Ordinal.{u}} (hκ : IsSuccLimit κ)
    (hS : IsStationary S κ) : S.Nonempty :=
  (hS _ (isClub_Iio hκ)).mono inter_subset_left

/-- The diamond principle $\diamondsuit(S)$ for a set `S` of ordinals below `κ`: there is a
sequence `A α ⊆ α` (`α < κ`) such that for every `X ⊆ κ` the set
`{α ∈ S | X ∩ α = A α}` is stationary in `κ`. -/
def Diamond (S : Set Ordinal.{u}) (κ : Ordinal.{u}) : Prop :=
  ∃ A : Ordinal.{u} → Set Ordinal.{u}, (∀ α, A α ⊆ Iio α) ∧
    ∀ X ⊆ Iio κ, IsStationary {α ∈ S | X ∩ Iio α = A α} κ

/-- If $\diamondsuit(S)$ holds, then `S` is stationary. -/
@[category API, AMS 3]
theorem Diamond.isStationary {S : Set Ordinal.{u}} {κ : Ordinal.{u}} (h : Diamond S κ) :
    IsStationary S κ := by
  obtain ⟨A, -, hA⟩ := h
  exact (hA ∅ (empty_subset _)).mono fun α hα ↦ hα.1

/-- If $\diamondsuit(S)$ holds and `S ⊆ T`, then $\diamondsuit(T)$ holds. -/
@[category API, AMS 3]
theorem Diamond.mono {S T : Set Ordinal.{u}} {κ : Ordinal.{u}} (hST : S ⊆ T)
    (hS : Diamond S κ) : Diamond T κ := by
  obtain ⟨A, hA, h⟩ := hS
  exact ⟨A, hA, fun X hX ↦ (h X hX).mono fun α hα ↦ ⟨hST hα.1, hα.2⟩⟩

/-- The set $E^\kappa_\nu = \{\alpha < \kappa : \operatorname{cf}(\alpha) = \nu\}$ of ordinals
below `κ` of cofinality `ν`. -/
def E (κ : Ordinal.{u}) (ν : Cardinal.{u}) : Set Ordinal.{u} :=
  {α | α < κ ∧ α.cof = ν}

/-- `E κ ν` is a set of ordinals below `κ`. -/
@[category API, AMS 3]
theorem E_subset_Iio (κ : Ordinal.{u}) (ν : Cardinal.{u}) : E κ ν ⊆ Iio κ :=
  fun _ hα ↦ hα.1

/--
Does the generalized continuum hypothesis entail
$\diamondsuit(E^{\lambda^+}_{\operatorname{cf}(\lambda)})$ for every singular cardinal $\lambda$?

Here a cardinal $\lambda$ is singular if it is infinite and
$\operatorname{cf}(\lambda) < \lambda$, $\lambda^+$ is the successor cardinal of $\lambda$
(`succ μ`, viewed as an ordinal via `Cardinal.ord`), and
$E^{\lambda^+}_{\operatorname{cf}(\lambda)} =
\{\alpha < \lambda^+ : \operatorname{cf}(\alpha) = \operatorname{cf}(\lambda)\}$.
The Lean variable `μ` plays the role of $\lambda$, because `λ` is a reserved token in Lean.
-/
@[category research open, AMS 3]
theorem generalized_continuum_hypothesis :
    answer(sorry) ↔ (GCH.{u} → ∀ μ : Cardinal.{u}, ℵ₀ ≤ μ → μ.ord.cof < μ →
      Diamond (E (succ μ).ord μ.ord.cof) (succ μ).ord) := by
  sorry

end GeneralizedContinuumHypothesis
