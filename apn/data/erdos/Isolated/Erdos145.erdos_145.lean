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
Let $s_1 < s_2 < \cdots$ be the sequence of squarefree numbers. Is it true that, for any
$\alpha\geq 0$,
$$
\lim_{x\to\infty} \frac{1}{x}\sum_{s_n\leq x}(s_{n+1}-s_n)^\alpha
$$
exists?
-/
theorem erdos_145 :
    ∀ α ≥ (0 : ℝ), ∃ β : ℝ,
      atTop.Tendsto (fun x : ℝ ↦ 1 / x * ∑ n ∈ A x, (s (n + 1) - s n : ℝ) ^ α) (𝓝 β) := by
  sorry

end Erdos145

theorem Erdos145.erdos_145.disproof : ¬ (type_of% @Erdos145.erdos_145) := sorry
