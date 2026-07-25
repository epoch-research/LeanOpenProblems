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
# Erdős Problem 539

In this problem, a function $h : \mathbb{N} \to\mathbb{N}$ is defined maximally by a specified
counting property.

The problem asks to estimate $h(n)$. This has been interpreted here as asking for $\Theta(h(n))$.
The principal version includes `answer(sorry)` for an unknown function. On the other hand, the best
known upper bound is $n^{2/3}$ and the best known lower bound is $\sqrt{n}$ so we
also provide these candidates as variants. Moreover, it suffices to show $O(h(n))$ and
$O(\sqrt{n})$ respectively for each, so further variants are provided for those.

In the source paper [Er73], Erdős also remarks that it should not be too difficult
to determine $\lim_{n\to\infty}\log(h(n))/\log(n)$. This does not appear on the website, and
it is not clear whether this remains open, but we include it here either way.

*References:*
- [erdosproblems.com/539](https://www.erdosproblems.com/539)
- [GR99] Granville, A., & Roesler, F. (1999). _The Set of Differences of a Given Set_. The American Mathematical Monthly, 106(4), 338–344.
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.
-/

open Filter

open scoped Asymptotics Finset

namespace Erdos539

/-- We say that $m$ is a cofactor lower bound for a given $n$ if, for every set $A$ of $n$
non-negative integers, there are at least $m$ cofactors $a / (a, b)$, where $a, b\in A$.-/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, #A = n →
  m ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b)

/-- The cofactor threshold $h(n)$, for every positive $n$, is the largest cofactor lower bound
for $n$. -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

/-- To prove `erdos_539.variants.sq` it suffices to show $$ h(n)\ll n^{1/2}$$. -/
@[category research open, AMS 5 11]
theorem erdos_539.variants.isBigO_sq :
    (fun n ↦ (cofactorThreshold n : ℝ)) =O[atTop] fun n ↦ √n := by
  sorry

end Erdos539
