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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 272

*Reference:* [erdosproblems.com/272](https://www.erdosproblems.com/272)
-/

open Filter Asymptotics Finset

namespace Erdos272

/-- Let $N \in\mathbb{N}$. We say that $\{A_1, ..., A_t\}\subseteq
\mathcal{P}(\{1, \dots, N\})$ is an arithmetic intersection set if
$A_i \cap A_j$ is a non-empty arithmetic progression for each $i \neq j$.
-/
def IsArithInterSet (N : ℕ) (A : Finset (Finset ℕ)) : Prop :=
  A ⊆ (Finset.Icc 1 N).powerset ∧
    (SetLike.coe A).Pairwise fun S T ↦ ∃ l > 0, (SetLike.coe (S ∩ T)).IsAPOfLength l

/-- For each $N > 0$, let $t$ be the largest size of an arithmetic
intersection set. -/
noncomputable def maxArithInterCard (N : ℕ) : ℕ :=
  sSup {#A | (A : _) (_ : IsArithInterSet N A)}

/--
Simonovits and Sós have shown that $t\ll N^2$.
-/
theorem erdos_272.variants.isBigO_sq :
    (fun N ↦ (maxArithInterCard N : ℝ)) =O[atTop] fun N ↦ (N : ℝ) ^ 2 := by
  sorry

end Erdos272
