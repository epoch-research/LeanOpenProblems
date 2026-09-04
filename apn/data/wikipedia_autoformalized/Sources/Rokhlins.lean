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
# Rokhlin's multiple mixing problem

Let $T$ be an invertible measure-preserving transformation of a standard probability space
$(X, \mu)$. The system is *strongly mixing* (mixing of order $2$) if
$$\lim_{n \to \infty} \mu(A \cap T^{-n}B) = \mu(A)\mu(B)$$
for all measurable sets $A, B$, and *strongly $3$-mixing* (mixing of order $3$) if
$$\lim_{m, n \to \infty} \mu(A \cap T^{-m}B \cap T^{-(m+n)}C) = \mu(A)\mu(B)\mu(C)$$
for all measurable sets $A, B, C$, where $m$ and $n$ tend to infinity independently.

Rokhlin (1949) asked whether every strongly mixing system is also strongly $3$-mixing. The
problem is open; Ledrappier (1978) showed that the analogous statement fails for
$\mathbb{Z}^2$-actions.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Vladimir Abramovich Rokhlin](https://en.wikipedia.org/wiki/Vladimir_Abramovich_Rokhlin)
- [Wikipedia, Mixing (mathematics)](https://en.wikipedia.org/wiki/Mixing_%28mathematics%29)
-/

open MeasureTheory Filter Topology

namespace Rokhlins

variable {X : Type*} [MeasurableSpace X] (T : X → X) (μ : Measure X)

/-- A transformation `T` of a measure space `(X, μ)` is *strongly mixing* (of order $2$) if
$$\lim_{n \to \infty} \mu(A \cap T^{-n}B) = \mu(A)\mu(B)$$
for all measurable sets $A, B$. -/
def StronglyMixing : Prop :=
  ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℕ => μ (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (μ A * μ B))

/-- A transformation `T` of a measure space `(X, μ)` is *strongly $3$-mixing* if
$$\lim_{m, n \to \infty} \mu(A \cap T^{-m}B \cap T^{-(m+n)}C) = \mu(A)\mu(B)\mu(C)$$
for all measurable sets $A, B, C$, where $m$ and $n$ tend to infinity independently. -/
def StronglyThreeMixing : Prop :=
  ∀ A B C : Set X, MeasurableSet A → MeasurableSet B → MeasurableSet C →
    Tendsto (fun mn : ℕ × ℕ => μ (A ∩ T^[mn.1] ⁻¹' B ∩ T^[mn.1 + mn.2] ⁻¹' C))
      (atTop ×ˢ atTop) (𝓝 (μ A * μ B * μ C))

variable {T μ}

/-- Strong $3$-mixing implies strong mixing (take $C = X$). -/
@[category API, AMS 37]
theorem StronglyThreeMixing.stronglyMixing [IsProbabilityMeasure μ]
    (h : StronglyThreeMixing T μ) : StronglyMixing T μ := by
  intro A B hA hB
  have := (h A B Set.univ hA hB MeasurableSet.univ).comp
    (tendsto_id.prodMk (tendsto_id (x := (atTop : Filter ℕ))))
  simpa [Function.comp_def] using this

/-- A strongly mixing measure-preserving transformation of a probability space is ergodic. -/
@[category API, AMS 37]
theorem StronglyMixing.ergodic [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (h : StronglyMixing T μ) : Ergodic T μ := by
  refine ⟨hT, ⟨fun s hs hs' => eventuallyConst_set'.mpr ?_⟩⟩
  have hiter : ∀ n : ℕ, T^[n] ⁻¹' s = s := fun n => by
    rw [Set.preimage_iterate_eq]
    exact Function.iterate_fixed hs' n
  have h1 : Tendsto (fun _ : ℕ => μ s) atTop (𝓝 (μ s * μ s)) := by
    simpa [hiter] using h s s hs hs
  have h2 : μ s = μ s * μ s := tendsto_nhds_unique tendsto_const_nhds h1
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · exact Or.inl (ae_eq_empty.mpr h0)
  · right
    rw [ae_eq_univ, prob_compl_eq_zero_iff hs]
    have h3 : μ s * 1 = μ s * μ s := by rw [mul_one]; exact h2
    exact ((ENNReal.mul_right_inj h0 (measure_ne_top μ s)).mp h3).symm

/-- **Rokhlin's multiple mixing problem.** Is every strongly mixing system also strongly
$3$-mixing? That is, for every invertible measure-preserving transformation $T$ of a standard
probability space $(X, \mu)$, does
$$\lim_{n \to \infty} \mu(A \cap T^{-n}B) = \mu(A)\mu(B) \quad \text{for all measurable } A, B$$
imply
$$\lim_{m, n \to \infty} \mu(A \cap T^{-m}B \cap T^{-(m+n)}C) = \mu(A)\mu(B)\mu(C)
\quad \text{for all measurable } A, B, C\,?$$
Here a system is a measurable bijection `T` of a standard Borel space `X` that preserves a
probability measure `μ`. -/
@[category research open, AMS 37]
theorem rokhlins :
    answer(sorry) ↔ ∀ (X : Type*) [MeasurableSpace X] [StandardBorelSpace X]
      (μ : Measure X) [IsProbabilityMeasure μ] (T : X ≃ᵐ X),
      MeasurePreserving T μ μ → StronglyMixing T μ → StronglyThreeMixing T μ := by
  sorry

end Rokhlins
