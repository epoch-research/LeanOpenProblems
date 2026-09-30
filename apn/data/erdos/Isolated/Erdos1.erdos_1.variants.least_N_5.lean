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
A finite set of real numbers is said to be sum-distinct if all the subset sums differ by
at least $1$.
-/
abbrev IsSumDistinctRealSet (A : Finset ℝ) (N : ℕ) : Prop :=
  ↑A ⊆ Set.Ioc (0 : ℝ) N ∧ (A.powerset : Set (Finset ℝ)).Pairwise fun S₁ S₂ =>
    1 ≤ dist (S₁.sum id) (S₂.sum id)

/--
The minimal value of $N$ such that there exists a sum-distinct set with five
elements is $13$.

https://oeis.org/A276661

Mathematical proof:
1. Existence: The set A = {6, 9, 11, 12, 13} ⊆ {1, ..., 13} has card 5.
   Its 2^5 = 32 subset sums:
   {0, 6, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 38, 39, 40, 42, 45, 51}
   are strictly all distinct, so A is a sum-distinct set with max element 13.
2. Minimality: Exhaustive check of all (12 choose 5) = 792 subsets of {1, ..., 12}
   shows that every subset has at least one pair of subsets with identical sum.
   Hence 13 is the least element.
-/
theorem erdos_1.variants.least_N_5 :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 13 := by
  sorry

end Erdos1

theorem Erdos1.erdos_1.variants.least_N_5.disproof : ¬ (type_of% @Erdos1.erdos_1.variants.least_N_5) := sorry
