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
# Goodman's conjecture on coefficients of $p$-valent functions

A regular (analytic) function is **$p$-valent** on the unit disk if it assumes each value at most
$p$ times there, and some value exactly $p$ times. For such a function $f(z) = \sum_{n \ge 1} b_n z^n$
(so $f(0) = 0$), **Goodman's conjecture** (1948) asserts that its coefficients satisfy
$$|b_n| \le \sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|
\qquad (n > p).$$
This generalises the classical coefficient bounds for univalent functions (the case $p = 1$,
where the bound reads $|b_n| \le n\,|b_1|$, i.e. $|b_n| \le n$ under the classical normalisation
$b_1 = 1$) to $p$-valent functions. It has been verified in several special cases, including
$p$-valent typically-real functions.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Goodman%27s_conjecture)
- Goodman, A. W., *On some determinants related to $p$-valent functions*,
  Trans. Amer. Math. Soc. 63 (1948), 175–192.
-/

open Complex Set

namespace GoodmanConjecture

/-- A function `f : ℂ → ℂ` is **$p$-valent** on the open unit disk $\mathbb{D} = \{z : |z| < 1\}$
if it is analytic there, attains every value at most $p$ times, and attains some value exactly
$p$ times. Here $p \ge 1$.
Values are counted at distinct points. For a non-constant analytic function this agrees with
counting with multiplicity: near a point where $f - w$ has a zero of order $m$, every value close
to $w$ is attained at $m$ distinct points, so the maximal number of distinct preimages equals the
maximal number of preimages counted with multiplicity. -/
structure IsPValent (f : ℂ → ℂ) (p : ℕ) : Prop where
  one_le_p   : 1 ≤ p
  analyticOn : AnalyticOn ℂ f (Metric.ball 0 1)
  /-- Every value $w$ is attained at most $p$ times on the disk. -/
  atMost     : ∀ w : ℂ, {z ∈ Metric.ball 0 1 | f z = w}.encard ≤ p
  /-- Some value $w$ is attained exactly $p$ times on the disk. -/
  exactly    : ∃ w : ℂ, {z ∈ Metric.ball 0 1 | f z = w}.encard = p

/-- The $n$-th Taylor coefficient of $f$ at $0$, i.e. $b_n = f^{(n)}(0) / n!$. -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

/-- Goodman's normalisation $f(z) = \sum_{n \ge 1} b_n z^n$, i.e. $f(0) = 0$. -/
structure IsNormalized (f : ℂ → ℂ) : Prop where
  map_zero   : f 0 = 0

/-- The Goodman bound
$$\sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|,$$
the conjectured upper bound for $|b_n|$. -/
noncomputable def goodmanBound (f : ℂ → ℂ) (p n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 p,
    (2 * k * (n + p).factorial : ℝ) /
      ((p - k).factorial * (p + k).factorial * (n - p - 1).factorial * ((n : ℝ) ^ 2 - k ^ 2)) *
      ‖coeff f k‖

/--
**Goodman's conjecture.** For every $p$-valent normalised function $f$ on the unit disk and every
$n > p$, the $n$-th coefficient is bounded by the Goodman bound:
$$|b_n| \le \sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|.$$
-/
theorem goodman_conjecture (f : ℂ → ℂ) (p n : ℕ) (hf : IsPValent f p)
    (hf' : IsNormalized f) (hn : p < n) :
    ‖coeff f n‖ ≤ goodmanBound f p n := by
  sorry

end GoodmanConjecture

theorem GoodmanConjecture.goodman_conjecture.disproof : ¬ (type_of% @GoodmanConjecture.goodman_conjecture) := sorry
