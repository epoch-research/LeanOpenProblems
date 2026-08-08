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

/-- Let `f ∈ ℤ[X]` be an irreducible polynomial with positive leading coefficient. Suppose that the
degree `k` of `f` is larger than `2`, is not equal to a power of `2`, and `f n` has no fixed
`(k - 1)`-th power divisors other than `1`. Then the set of `n` such that `f n` is `(k - 1)`-th
power free has positive density, and this is proved in [Ho67]. -/
theorem erdos_978.parts.i {f : ℤ[X]} (hi : Irreducible f) (hd : 2 < f.natDegree)
    (hp2 : ∀ (x : ℕ), f.natDegree ≠ 2 ^ x) (hlc : 0 < f.leadingCoeff)
    (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)) :
    HasPosDensity {n : ℕ | Powerfree (f.natDegree - 1) (f.eval (n : ℤ))} := by
  sorry

end Erdos978
