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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 145

*Reference:* [erdosproblems.com/145](https://www.erdosproblems.com/145)
-/

namespace Erdos145

open Filter
open scoped Topology

/-- Let $s_1 < s_2 < \cdots$ be the sequence of squarefree numbers. -/
noncomputable abbrev s (n : ℕ) : ℕ := Nat.nth Squarefree n

/-- Let $A(x)$ denote the set of indices $n$ for which $s_n \leq x$. -/
noncomputable abbrev A (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).preimage s (Nat.nth_injective Nat.squarefree_infinite).injOn

/--
Erdős [Er51] proved this for all $0\leq \alpha\leq 2$.

[Er51] Erdös, P., Some problems and results in elementary number theory.
  Publ. Math. Debrecen (1951), 103-109.
-/
theorem erdos_145.variants.le_two {α : ℝ} (hα : α ∈ Set.Icc 0 2) :
    ∃ β : ℝ,
      atTop.Tendsto (fun x : ℝ ↦ 1 / x * ∑ n ∈ A x, (s (n + 1) - s n : ℝ) ^ α) (𝓝 β) := by
  sorry

end Erdos145
