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
# Erdős Problem 1041

*Reference:* [erdosproblems.com/1041](https://www.erdosproblems.com/1041)
-/

open Polynomial MeasureTheory ENNReal Classical

namespace Erdos1041

variable (n : ℕ) (f : ℂ[X]) (hn : n ≥ 2) (hnum : f.natDegree = n)
variable (h_monic : f.Monic)
variable (h : f.rootSet ℂ ⊆ Metric.ball 0 1)
include hn hnum h h_monic

/--
The length of a subset $s$ of $\mathbb{C}$ is defined to be its 1-dimensional
Hausdorff measure $\mathcal{H}^1(s)$.
-/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/--
Let
$$ f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[x] $$
with $|z_i| < 1$ for all $i$.

Conjecture: Must there always exist a path of length less than 2 in
$$ \{ z \in \mathbb{C} \mid |f(z)| < 1 \} $$
which connects two of the roots of $f$?
-/
theorem erdos_1041 :
    ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
      Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ length (Set.range γ) < 2 := by
  sorry

end Erdos1041
