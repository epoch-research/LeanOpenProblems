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

/-- A set of ordinals `C` is *club* in the ordinal `κ` if `C ⊆ κ`, `C` is closed in `κ`
(it contains every accumulation point below `κ`), and `C` is unbounded in `κ`. -/
def IsClub (C : Set Ordinal.{u}) (κ : Ordinal.{u}) : Prop :=
  C ⊆ Iio κ ∧ IsClosedBelow C κ ∧ ∀ α < κ, ∃ β ∈ C, α < β

/-- A set of ordinals `S` is *stationary* in the ordinal `κ` if it meets every set that is
club in `κ`. -/
def IsStationary (S : Set Ordinal.{u}) (κ : Ordinal.{u}) : Prop :=
  ∀ C, IsClub C κ → (S ∩ C).Nonempty

/-- The diamond principle $\diamondsuit(S)$ for a set `S` of ordinals below `κ`: there is a
sequence `A α ⊆ α` (`α < κ`) such that for every `X ⊆ κ` the set
`{α ∈ S | X ∩ α = A α}` is stationary in `κ`. -/
def Diamond (S : Set Ordinal.{u}) (κ : Ordinal.{u}) : Prop :=
  ∃ A : Ordinal.{u} → Set Ordinal.{u}, (∀ α, A α ⊆ Iio α) ∧
    ∀ X ⊆ Iio κ, IsStationary {α ∈ S | X ∩ Iio α = A α} κ

/-- The set $E^\kappa_\nu = \{\alpha < \kappa : \operatorname{cf}(\alpha) = \nu\}$ of ordinals
below `κ` of cofinality `ν`. -/
def E (κ : Ordinal.{u}) (ν : Cardinal.{u}) : Set Ordinal.{u} :=
  {α | α < κ ∧ α.cof = ν}

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
theorem generalized_continuum_hypothesis :
    (GCH.{u} → ∀ μ : Cardinal.{u}, ℵ₀ ≤ μ → μ.ord.cof < μ →
      Diamond (E (succ μ).ord μ.ord.cof) (succ μ).ord) := by
  sorry

end GeneralizedContinuumHypothesis

theorem GeneralizedContinuumHypothesis.generalized_continuum_hypothesis.disproof : ¬ (type_of% @GeneralizedContinuumHypothesis.generalized_continuum_hypothesis) := sorry
