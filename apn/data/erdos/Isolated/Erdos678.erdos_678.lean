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
# Erdős Problem 678
*References:*
- [erdosproblems.com/678](https://www.erdosproblems.com/678)
- [Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138
  (2024).
- [Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
- [Er92e] Erdős, Pál, Some Unsolved problems in Geometry, Number Theory and Combinatorics. Eureka
  (1992), 44-48.
-/

open Asymptotics Filter Finset

namespace Erdos678

/--
Write $M(n, k)$ be the least common multiple of $\{n+1, \dotsc, n+k\}$.
Let $k$ be sufficiently large. Are there infinitely many $m, n$ with $m \geq n + k$ such that
$$
M(n, k) > M(m, k + 1)
$$?
The answer is yes, as proved in a strong form by Cambie [Ca24].
[Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138 (2024).

This was formalized in Lean by Alexeev using Aristotle, conditional on asymptotic estimates for the
prime counting function (specifically `pi_alt` from the PNT+ project).
See the [formal proof](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos678.lean).
-/
theorem erdos_678 : 
    ∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite := by
  sorry

end Erdos678
