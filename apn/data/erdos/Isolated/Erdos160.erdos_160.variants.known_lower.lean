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
# Erdős Problem 160

*Reference:* [erdosproblems.com/160](https://www.erdosproblems.com/160)
-/

namespace Erdos160

/--
Let $h(n)$ be the smallest $k$ such that $\{1,\ldots,n\}$ can be coloured with $k$ colours
so that every four-term arithmetic progression must contain at least three distinct colours.
-/
noncomputable def erdos_160.h (n : ℕ) : ℕ :=
    sInf {k | ∃ (colouring : Finset.Icc 1 n → Fin k), ∀ (progression : Set ℕ),
    (progression ⊆ Finset.Icc 1 n ∧ progression.IsAPOfLength 4) →
    3 ≤ (colouring '' {k | (k : ℕ) ∈ progression}).ncard}

open Filter

open Real

/--
The observation of Zachary Hunter in [that question](https://mathoverflow.net/q/410808)
coupled with the bounds of Kelley-Meka [KeMe23](https://arxiv.org/abs/2302.05537) imply that
$$h(N) \gg \exp(c(\log N)^{\frac 1 {12}})$$
for some $c > 0$.
-/
theorem erdos_160.variants.known_lower :
    ∃ c > 0, (fun (n : ℕ) => exp (c * log (n : ℝ) ^ ((1 : ℝ) / 12)))
    =O[atTop] fun n => (erdos_160.h n : ℝ):= by
  sorry

end Erdos160
