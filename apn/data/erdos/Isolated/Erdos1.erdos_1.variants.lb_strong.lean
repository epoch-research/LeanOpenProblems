/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1

*Reference:* [erdosproblems.com/1](https://www.erdosproblems.com/1)
-/

open Filter

open scoped Topology Real

namespace Erdos1

/--
A finite set of naturals $A$ is said to be a sum-distinct set for $N \in \mathbb{N}$ if
$A\subseteq\{1, ..., N\}$ and the sums $\sum_{a\in S}a$ are distinct for all $S\subseteq A$
-/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

/--
A number of improvements of the constant $\frac{1}{4}$ have been given, with the current
record $\sqrt{2 / \pi}$ first provided in unpublished work of Elkies and Gleason.
-/
theorem erdos_1.variants.lb_strong : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (√(2 / π) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  sorry

/--
A finite set of real numbers is said to be sum-distinct if all the subset sums differ by
at least $1$.
-/
abbrev IsSumDistinctRealSet (A : Finset ℝ) (N : ℕ) : Prop :=
  ↑A ⊆ Set.Ioc (0 : ℝ) N ∧ (A.powerset : Set (Finset ℝ)).Pairwise fun S₁ S₂ =>
    1 ≤ dist (S₁.sum id) (S₂.sum id)

end Erdos1

theorem Erdos1.erdos_1.variants.lb_strong.disproof : ¬ (type_of% @Erdos1.erdos_1.variants.lb_strong) := sorry
