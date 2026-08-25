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
# Erdős Problem 997

*References:*
- [erdosproblems.com/997](https://www.erdosproblems.com/997)
- [APSSV26] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant,
  [Short proofs in combinatorics and number theory](https://arxiv.org/abs/2603.29961).
  arXiv:2603.29961 (2026).
- [CLLW24] J. Champagne, T. Le, Y.-R. Liu, and T. D. Wooley, Well-distribution modulo one and the
  primes. arXiv:2406.19491 (2024).
- [Er64b] Erdős, P., Problems and results on diophantine approximations. Compositio Math. (1964),
  52-65.
- [Er85e] Erdős, P., Some problems and results in number theory. Number theory and combinatorics.
  Japan 1984 (Tokyo, Okayama and Kyoto, 1984) (1985), 65-87.
- [Hl55] Hlawka, Edmund, Zur formalen {T}heorie der {G}leichverteilung in kompakten {G}ruppen. Rend.
  Circ. Mat. Palermo (2) (1955), 33--47.
-/

open Set

namespace Erdos997

/--
Call $x_1,x_2,\ldots \in (0,1)$ well-distributed if, for every $\epsilon>0$, if $k$ is
sufficiently large then, for all $n>0$ and intervals $I\subseteq [0,1]$,
$\lvert \# \{ n < m\leq n+k : x_m\in I\} - \lvert I\rvert k\rvert < \epsilon k.$

The notion of a well-distributed sequence was introduced by Hlawka and Petersen [Hl55].
-/
def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ k in Filter.atTop, ∀ n : ℕ,
  ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    letI I := Ico a b
    let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
    abs ((count.card : ℝ) - (b - a) * k) < ε * k

/--
Is it true that, for every $\alpha$, the sequence $\{ \alpha p_n\}$ is not well-distributed,
if $p_n$ is the sequence of primes?
-/
theorem erdos_997 :
    
      ∀ α : ℝ, ¬ IsWellDistributed (fun n ↦ Int.fract (α * (n.nth Nat.Prime))) := by
  sorry

end Erdos997

theorem Erdos997.erdos_997.disproof : ¬ (type_of% @Erdos997.erdos_997) := sorry
