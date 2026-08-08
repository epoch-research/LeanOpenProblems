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
# Erdős Problem 978

*Reference:*
 - [erdosproblems.com/978](https://www.erdosproblems.com/978)
 - [Ho67] Hooley, C., On the power free values of polynomials. Mathematika (1967), 21--26.
 - [Br11] Browning, T. D., Power-free values of polynomials. Arch. Math. (Basel) (2011), 139--150.
 - [Er53] Erdős, P., Arithmetical properties of polynomials. J. London Math. Soc. (1953), 416--425.
-/

open Polynomial Set

namespace Erdos978

/-- If the degree `k` of `f` is larger than or equal to `9`, then the set of `n` such that `f n` is
`(k - 2)`-th power free has infinitely many elements. This result is proved in [Br11]. -/
theorem erdos_978.variants.sub_two {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree)
    (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)) :
    {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite := by
  sorry

end Erdos978
