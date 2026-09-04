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

/-- The entries of a tuple with no vanishing proper subsum are nonzero, as soon as $n \geq 2$. -/
@[category API, AMS 11]
theorem HasNoVanishingProperSubsum.ne_zero {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℤ}
    (ha : HasNoVanishingProperSubsum a) (i : Fin n) : a i ≠ 0 := by
  have h : ({i} : Finset (Fin n)) ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  simpa using ha {i} (Finset.singleton_nonempty i) h

@[category test, AMS 11]
theorem maxAbs_example : maxAbs ![1, 8, -9] = 9 := by
  decide

@[category test, AMS 11]
theorem rad_example : rad ![1, 8, -9] = 6 := by
  rw [rad, show ∏ i, ((![1, 8, -9] : Fin 3 → ℤ) i).natAbs = 2 ^ 3 * 3 ^ 2 by decide,
    radical, primeFactors_eq_natPrimeFactors, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

@[category test, AMS 11]
theorem quality_example : quality ![1, 1, -2] = 1 := by
  have h : rad ![1, 1, -2] = 2 := by
    rw [rad, show ∏ i, ((![1, 1, -2] : Fin 3 → ℤ) i).natAbs = 2 by decide,
      radical_of_prime Nat.prime_two.prime, normalize_eq]
  rw [quality, h, show maxAbs ![1, 1, -2] = 2 by decide]
  norm_num

@[category test, AMS 11]
theorem mem_admissibleSet_example : ![1, 8, -9] ∈ admissibleSet 3 := by
  refine ⟨by decide, by decide, ?_⟩
  unfold HasNoVanishingProperSubsum
  decide

@[category test, AMS 11]
theorem mem_strongAdmissibleSet_example : ![1, 8, -9] ∈ strongAdmissibleSet 3 := by
  refine ⟨?_, by decide, ?_⟩
  · simp only [Pairwise, Int.isCoprime_iff_gcd_eq_one]
    decide
  · unfold HasNoVanishingProperSubsum
    decide

/-- The tuple $(1, -1, 2, -2)$ has the vanishing proper subsum $1 + (-1)$. -/
@[category test, AMS 11]
theorem not_mem_admissibleSet_example : ![1, -1, 2, -2] ∉ admissibleSet 4 := by
  rintro ⟨-, -, h⟩
  exact h {0, 1} (by decide) (by decide) (by decide)

/-- The tuple $(2, 2, -4)$ has $\gcd(2, 2, -4) = 2 \neq 1$. -/
@[category test, AMS 11]
theorem not_mem_admissibleSet_gcd_example : ![2, 2, -4] ∉ admissibleSet 3 := by
  rintro ⟨h, -, -⟩
  revert h
  decide

/-- The tuple $(3, 3, -1, -5)$ is setwise but not pairwise coprime. -/
@[category test, AMS 11]
theorem mem_admissibleSet_not_mem_strongAdmissibleSet_example :
    ![3, 3, -1, -5] ∈ admissibleSet 4 ∧ ![3, 3, -1, -5] ∉ strongAdmissibleSet 4 := by
  refine ⟨⟨by decide, by decide, by unfold HasNoVanishingProperSubsum; decide⟩,
    fun ⟨h, _, _⟩ ↦ ?_⟩
  have := h (i := 0) (j := 1) (by decide)
  simp [Int.isCoprime_iff_gcd_eq_one] at this

/-- The **$n$ conjecture** (Browkin–Brzeziński, 1994), first formulation. Let $n \geq 3$.
For every $\varepsilon > 0$ there is a constant $C_{n, \varepsilon}$ depending on $n$ and
$\varepsilon$ such that for all integers $a_1, \dots, a_n$ with
(i) $\gcd(a_1, \dots, a_n) = 1$, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$, one has
$$\max(|a_1|, \dots, |a_n|)
  < C_{n, \varepsilon}
  \operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|)^{2n - 5 + \varepsilon},$$
where $\operatorname{rad}(m)$ denotes the radical of $m$, i.e. the product of the distinct prime
factors of $m$. For $n = 3$ this is the *abc* conjecture. -/
@[category research open, AMS 11]
theorem n_conjecture (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ a ∈ admissibleSet n,
      (maxAbs a : ℝ) < C * (rad a : ℝ) ^ (2 * (n : ℝ) - 5 + ε) := by
  sorry

/-- The **$n$ conjecture** (Browkin–Brzeziński, 1994), second formulation. Let $n \geq 3$.
Over all integers $a_1, \dots, a_n$ with (i) $\gcd(a_1, \dots, a_n) = 1$,
(ii) $a_1 + \dots + a_n = 0$, and (iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$,
the limit superior of the qualities
$$q(a_1, \dots, a_n) = \frac{\log(\max(|a_1|, \dots, |a_n|))}
  {\log(\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|))}$$
equals $2n - 5$. The inequality $\limsup q \geq 2n - 5$ is a theorem of Browkin and Brzeziński
(1994, Theorem 1); the inequality $\limsup q \leq 2n - 5$ is open. -/
@[category research open, AMS 11]
theorem n_conjecture.variants.quality (n : ℕ) (hn : 3 ≤ n) :
    limsupQuality (admissibleSet n) = ((2 * (n : ℝ) - 5 : ℝ) : EReal) := by
  sorry

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
@[category research open, AMS 11]
theorem n_conjecture.variants.strong (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 4) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ a ∈ strongAdmissibleSet n,
      (maxAbs a : ℝ) < C * (rad a : ℝ) ^ (1 + ε) := by
  sorry

/-- The **strong $n$ conjecture** (attributed to Vojta, 1998), second formulation. Let $n \geq 3$.
Over all integers $a_1, \dots, a_n$ with (i) $a_1, \dots, a_n$ pairwise coprime,
(ii) $a_1 + \dots + a_n = 0$, and (iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$,
the limit superior of the qualities
$$q(a_1, \dots, a_n) = \frac{\log(\max(|a_1|, \dots, |a_n|))}
  {\log(\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|))}$$
equals $1$.

Hölzl, Kleine and Stephan (2025) showed that this statement is false for every $n \geq 5$
(see `NConjecture.n_conjecture.variants.strong_lower_bound_holzl_kleine_stephan`). It remains open
for $n = 3$ (where it is equivalent to the *abc* conjecture) and for $n = 4$, so it is stated
here only for $n \in \{3, 4\}$. -/
@[category research open, AMS 11]
theorem n_conjecture.variants.strong_quality (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 4) :
    limsupQuality (strongAdmissibleSet n) = 1 := by
  sorry

/-- Hölzl, Kleine and Stephan (2025) have shown that for $n \geq 5$ the limit superior of the
qualities $q(a_1, \dots, a_n)$ over all integers $a_1, \dots, a_n$ with
(i) $a_1, \dots, a_n$ pairwise coprime, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$, is at least $5/3$ for odd $n$ and at
least $5/4$ for even $n$ (so for even $n \geq 6$). In particular the strong $n$ conjecture fails
for every $n \geq 5$. -/
@[category research solved, AMS 11]
theorem n_conjecture.variants.strong_lower_bound_holzl_kleine_stephan (n : ℕ) (hn : 5 ≤ n) :
    (Odd n → ((5 / 3 : ℝ) : EReal) ≤ limsupQuality (strongAdmissibleSet n)) ∧
    (Even n → ((5 / 4 : ℝ) : EReal) ≤ limsupQuality (strongAdmissibleSet n)) := by
  sorry

/-- Is there a common constant upper bound $K$, valid for all $n \geq 3$, for the limit superior
of the qualities $q(a_1, \dots, a_n)$ over all integers $a_1, \dots, a_n$ with
(i) $a_1, \dots, a_n$ pairwise coprime, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$? -/
@[category research open, AMS 11]
theorem n_conjecture.variants.strong_uniform_bound :
    answer(sorry) ↔
      ∃ K : ℝ, ∀ n : ℕ, 3 ≤ n → limsupQuality (strongAdmissibleSet n) ≤ (K : EReal) := by
  sorry

end NConjecture
