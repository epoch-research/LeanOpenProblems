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
# Erdős Problem 394

*References:*
- [erdosproblems.com/394](https://www.erdosproblems.com/394)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [ErHa78] Erdős, P. and Hall, R. R., On some unconventional problems on the divisors of integers.
  J. Austral. Math. Soc. Ser. A (1978), 479--485.
-/

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Erdos394

/--
Let $t_k(n)$ denote the least $m$ such that $n\mid m(m+1)(m+2)\cdots (m+k-1).$
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

/--
Is it true that, for $k\geq 2$, $\sum_{n\leq x}t_{k+1}(n) =o\left(\sum_{n\leq x}t_k(n)\right)?$
-/
theorem erdos_394.parts.ii :
    
      ∀ k ≥ 2, (fun (x : ℝ) ↦ ∑ n ∈ Icc 1 ⌊x⌋₊,
      (t (k + 1) n : ℝ)) =o[atTop]
      (fun (x : ℝ) ↦ ∑ n ∈ Icc 1 ⌊x⌋₊,
      (t k n : ℝ)) := by
  sorry

end Erdos394

theorem Erdos394.erdos_394.parts.ii.disproof : ¬ (type_of% @Erdos394.erdos_394.parts.ii) := sorry
