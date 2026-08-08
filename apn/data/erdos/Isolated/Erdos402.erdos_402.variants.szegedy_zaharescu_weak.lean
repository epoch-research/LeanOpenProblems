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
# Erdős Problem 402

*Reference:* [erdosproblems.com/402](https://www.erdosproblems.com/402)
-/

open Filter

namespace Erdos402

/-- Proved for all sufficiently large sets (including the sharper version which
characterises the case of equality) independently by Szegedy [Sz86] and
Zaharescu [Za87]. The following is taken from [Sz86].

There exists an effectively computable $n_0$ with the following properties:
(i) if $n \ge n_0$ and $a_1, a_2, \dots, a_n$ are distinct natural numbers then
$\max_{i, j} \frac{a_i}{(a_i, a_j)} \ge n$.
(ii) If equality holds then the system $\{a_1, a_2, \dots, a_n\}$ is either of the
type $\{k, 2k, \dots, nk\}$ or of the type
$\left\{\frac{k}{1}, \frac{k}{2}, \dots, \frac{k}{n}\right\}$. -/
theorem erdos_402.variants.szegedy_zaharescu_weak : ∀ᶠ n in atTop,
    ∀ (A : Finset ℕ), A.card = n → 0 ∉ A →
      (n ≤ (A ×ˢ A).sup (fun x => x.1 / x.1.gcd x.2)) ∧
      (n = (A ×ˢ A).sup (fun x => x.1 / x.1.gcd x.2) ↔
        ∃ k > 0, A = (Finset.Icc 1 n).image (k * ·) ∨
          A = (Finset.Icc 1 n).image (k * (Finset.Icc 1 n).lcm id / ·)):= by
  sorry

end Erdos402
