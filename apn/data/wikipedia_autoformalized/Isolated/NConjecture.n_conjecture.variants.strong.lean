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

import FormalConjecturesUtil

/-!
# The $n$ conjecture

The $n$ conjecture of Browkin and Brzeziński (1994) is a generalization of the *abc* conjecture
to $n \geq 3$ integers. Given $n \geq 3$, one considers $n$-tuples of integers
$a_1, \dots, a_n$ such that
(i) $\gcd(a_1, \dots, a_n) = 1$,
(ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equals $0$.
The conjecture bounds $\max(|a_1|, \dots, |a_n|)$ by a power of the radical
$\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|)$; equivalently, it predicts the
limit superior of the qualities of such tuples.

The *strong* $n$ conjecture (attributed to Vojta (1998) by the Wikipedia article) replaces
setwise coprimality by pairwise coprimality and predicts the exponent $1 + \varepsilon$.
Hölzl, Kleine and Stephan (2025) refuted it for every $n \geq 5$; it remains open for $n = 3$
(the *abc* conjecture) and $n = 4$.

*References:*
- [Wikipedia, n conjecture](https://en.wikipedia.org/wiki/n_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J. Browkin, J. Brzeziński, *Some remarks on the abc-conjecture*, Math. Comp. 62 (1994),
  931–939. [doi:10.2307/2153551](https://doi.org/10.2307/2153551)
- P. Vojta, *A more general abc conjecture*, Int. Math. Res. Not. 1998 (1998), 1103–1116.
  [arXiv:math/9806171](https://arxiv.org/abs/math/9806171)
- R. Hölzl, S. Kleine, F. Stephan, *Improved lower bounds for strong n-conjectures*,
  J. Aust. Math. Soc. (2025). [arXiv:2409.13439](https://arxiv.org/abs/2409.13439)
-/

open Filter UniqueFactorizationMonoid

namespace NConjecture

/-- Condition (iii): no proper subsum of $a_1, \dots, a_n$ equals $0$, i.e.
$\sum_{i \in s} a_i \neq 0$ for every nonempty proper subset $s$ of the indices.
For $n \geq 2$ this forces every $a_i$ to be nonzero. -/
def HasNoVanishingProperSubsum {n : ℕ} (a : Fin n → ℤ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → s ≠ Finset.univ → ∑ i ∈ s, a i ≠ 0

/-- The set $A(n)$ of $n$-tuples of integers $(a_1, \dots, a_n)$ considered by the
$n$ conjecture: (i) $\gcd(a_1, \dots, a_n) = 1$, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equals $0$. -/
def admissibleSet (n : ℕ) : Set (Fin n → ℤ) :=
  {a | Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0 ∧ HasNoVanishingProperSubsum a}

/-- The set $R(n)$ of $n$-tuples of integers $(a_1, \dots, a_n)$ considered by the strong
$n$ conjecture: (i) $a_1, \dots, a_n$ are pairwise coprime, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equals $0$. -/
def strongAdmissibleSet (n : ℕ) : Set (Fin n → ℤ) :=
  {a | (Pairwise fun i j ↦ IsCoprime (a i) (a j)) ∧ ∑ i, a i = 0 ∧ HasNoVanishingProperSubsum a}

/-- The maximal absolute value $\max(|a_1|, \dots, |a_n|)$ of an $n$-tuple of integers. -/
def maxAbs {n : ℕ} (a : Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ (a i).natAbs

/-- The radical $\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|)$ of the product of
the absolute values of the entries of an $n$-tuple of integers, i.e. the product of the distinct
primes dividing $a_1 \cdot a_2 \cdot \ldots \cdot a_n$. -/
noncomputable def rad {n : ℕ} (a : Fin n → ℤ) : ℕ :=
  radical (∏ i, (a i).natAbs)

/-- The quality of an $n$-tuple of integers $(a_1, \dots, a_n)$:
$$q(a_1, \dots, a_n) = \frac{\log(\max(|a_1|, \dots, |a_n|))}
  {\log(\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|))}.$$
For $n \geq 3$ and every tuple in `admissibleSet n` or `strongAdmissibleSet n` the radical is
at least $2$, so the denominator is positive. -/
noncomputable def quality {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  Real.log (maxAbs a) / Real.log (rad a)

/-- The limit superior of the qualities $q(a_1, \dots, a_n)$ over a set $S$ of $n$-tuples of
integers, taken along the cofinite filter on $S$ (equivalently, for an infinite set $S$, along
any injective enumeration of $S$, or along $\max(|a_1|, \dots, |a_n|) \to \infty$ in $S$).
It is valued in `EReal` so that an unbounded set of qualities has limit superior $+\infty$. -/
noncomputable def limsupQuality {n : ℕ} (S : Set (Fin n → ℤ)) : EReal :=
  limsup (fun a : S ↦ (quality a.1 : EReal)) cofinite

/-- The **strong $n$ conjecture** (attributed to Vojta, 1998), first formulation. Let $n \geq 3$.
For every $\varepsilon > 0$ there is a constant $C_{n, \varepsilon}$ depending on $n$ and
$\varepsilon$ such that for all integers $a_1, \dots, a_n$ with
(i) $a_1, \dots, a_n$ pairwise coprime, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$, one has
$$\max(|a_1|, \dots, |a_n|)
  < C_{n, \varepsilon}
  \operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|)^{1 + \varepsilon}.$$

Hölzl, Kleine and Stephan (2025) showed that this statement is false for every $n \geq 5$
(see `NConjecture.n_conjecture.variants.strong_lower_bound_holzl_kleine_stephan`). It remains open
for $n = 3$ (where it is the *abc* conjecture) and for $n = 4$, so it is stated here only for
$n \in \{3, 4\}$. -/
theorem n_conjecture.variants.strong (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 4) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ a ∈ strongAdmissibleSet n,
      (maxAbs a : ℝ) < C * (rad a : ℝ) ^ (1 + ε) := by
  sorry

end NConjecture

theorem NConjecture.n_conjecture.variants.strong.disproof : ¬ (type_of% @NConjecture.n_conjecture.variants.strong) := sorry
