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
# Erdős Problem 517

*References:*
 - [erdosproblems.com/517](https://www.erdosproblems.com/517)
 - [Bi28] Biernacki, Miécislas, Sur les équations algébriques contenant des paramétres arbitraires.
    (1928), 145.
-/

open Set Filter Topology

namespace Erdos517

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function (with `aₖ ≠ 0` for all `k`) such that `nₖ / k → ∞`,
is it true that `f` assumes every value infinitely often? -/
theorem erdos_517 : ∀ {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : HasFabryGaps n)
    {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (z : ℂ),
    {x : ℂ | f x = z}.Infinite := by
  sorry

end Erdos517

theorem Erdos517.erdos_517.disproof : ¬ (type_of% @Erdos517.erdos_517) := sorry
