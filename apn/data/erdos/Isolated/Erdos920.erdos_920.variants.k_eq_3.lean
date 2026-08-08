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
# Erdős Problem 920

*References:*
- [erdosproblems.com/166](https://www.erdosproblems.com/166)
- [erdosproblems.com/920](https://www.erdosproblems.com/920)
- [erdosproblems.com/986](https://www.erdosproblems.com/986)
- [erdosproblems.com/1104](https://www.erdosproblems.com/1104)
- [GrYa68] Graver, Jack E. and Yackel, James, Some graph theoretic results associated with Ramsey's
  theorem. J. Combinatorial Theory (1968), 125--175.
- [MaVe23] Mattheus, S. and Verstraete, J., The asymptotics of $r(4,t)$. arXiv:2306.04007 (2023).
-/

open Real Filter

namespace Erdos920

/--
$f_k(n)$ is the maximum possible chromatic number of a graph with $n$ vertices
which contains no $K_k$.
-/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup {(G.chromaticNumber) | (G : SimpleGraph (Fin n)) (_ : G.CliqueFree k)}

/--
It is known that $f_3(n)\asymp (n/\log n)^{1/2}$ (see [erdosproblems.com/1104]).
-/
theorem erdos_920.variants.k_eq_3 :
    (fun n ↦ (f 3 n : ℝ)) =Θ[atTop] (fun n ↦ ((n : ℝ) / log n) ^ (1 / 2 : ℝ)) := by
  sorry

end Erdos920
