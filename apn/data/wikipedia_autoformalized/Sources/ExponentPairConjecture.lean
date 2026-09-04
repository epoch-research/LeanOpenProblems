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
# Exponent pair conjecture

The method of exponent pairs gives estimates for exponential sums $\sum_{a \le n \le b} e(f(n))$,
where $e(x) = e^{2\pi i x}$, over functions $f$ on $[a, b] \subseteq [N, 2N]$ whose derivatives
behave like those of $x \mapsto \frac{T}{1-s} x^{1-s}$ (or $T \log x$ when $s = 1$), i.e.
$f^{(r+1)}(x) \approx (-1)^r s(s+1)\cdots(s+r-1) T x^{-s-r}$. A pair $(k, l)$ with
$0 \le k \le 1/2 \le l \le 1$ is an *exponent pair* if such sums are $\ll (T / N^s)^k N^l$
uniformly over this class of functions.

The exponent pair conjecture states that $(\varepsilon, 1/2 + \varepsilon)$ is an exponent pair
for every $\varepsilon > 0$. It implies the Lindelöf hypothesis.

*References:*
- [Wikipedia, Van der Corput's method § Exponent pairs](https://en.wikipedia.org/wiki/Van_der_Corput%27s_method%23Exponent_pairs)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [GK91] Graham, S. W. and Kolesnik, G., *Van der Corput's Method of Exponential Sums*,
  London Mathematical Society Lecture Note Series 126, Cambridge University Press (1991),
  Chapter 3.
- [Iv85] Ivić, A., *The Riemann zeta-function. The theory of the Riemann zeta-function with
  applications*, John Wiley & Sons (1985), Section 2.3.
- [Mo94] Montgomery, H. L., *Ten lectures on the interface between analytic number theory and
  harmonic analysis*, CBMS Regional Conference Series in Mathematics 84, American Mathematical
  Society (1994), Chapter 3.
-/

open scoped ExponentialSum

namespace ExponentPairConjecture

/--
The class of phase functions to which the method of exponent pairs applies, with parameters
$R, T, s, \delta$ on the interval $[a, b]$ [GK91, Chapter 3].

`IsAdmissible R T s δ a b f` says that `f` is `R` times continuously differentiable and that
for all $0 \le r < R$ and all $x \in [a, b]$
$$\left|f^{(r+1)}(x) - (-1)^r s(s+1)\cdots(s+r-1)\, T x^{-s-r}\right|
  \le \delta\, s(s+1)\cdots(s+r-1)\, T x^{-s-r}.$$
Here $s(s+1)\cdots(s+r-1) = \prod_{i < r} (s + i)$ is the rising factorial, with the empty
product equal to $1$ when $r = 0$, so the first condition reads
$|f'(x) - T x^{-s}| \le \delta T x^{-s}$. These are exactly the constants for which the model
function with $f'(x) = T x^{-s}$ satisfies every condition with $\delta = 0$. (The Wikipedia
article prints the product with $r + 1$ factors, which is not the derivative sequence of any
function.)

Smoothness is imposed on all of `ℝ` rather than only on `[a, b]`. This gives the same class of
exponential sums, since a function that is `R` times continuously differentiable on `[a, b]`
extends to such a function on `ℝ` with the same derivatives on `[a, b]`.
-/
def IsAdmissible (R : ℕ) (T s δ : ℝ) (a b : ℕ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ R f ∧
    ∀ r < R, ∀ x ∈ Set.Icc (a : ℝ) b,
      |iteratedDeriv (r + 1) f x -
          (-1) ^ r * (∏ i ∈ Finset.range r, (s + i)) * T * x ^ (-s - r)| ≤
        δ * (∏ i ∈ Finset.range r, (s + i)) * T * x ^ (-s - r)

/--
A pair of real numbers $(k, l)$ with $0 \le k \le 1/2 \le l \le 1$ is an *exponent pair* if for
each $s > 0$ there exist $\delta > 0$, an integer $R$ and a constant $C$, depending only on
$k$, $l$ and $s$, such that
$$\left|\sum_{n=a}^{b} e(f(n))\right| \le C \left(\frac{T}{N^s}\right)^k N^l$$
for all $N \ge 1$, all $T \ge N^s$, all $[a, b] \subseteq [N, 2N]$ and all functions $f$ in the
class `IsAdmissible R T s δ a b`, where $e(x) = e^{2\pi i x}$.

The condition $T \ge N^s$ (i.e. $f'$ has size at least $1$ on $[a, b]$) is the standard
normalisation of the theory of exponent pairs [GK91, Chapter 3]. Without it no pair other than
$(0, 1)$ could satisfy the estimate: for $T N^{-s} \le 1/N$ the phases $e(f(n))$ are essentially
constant and the sum has size comparable to $b - a$.
-/
def IsExponentPair (k l : ℝ) : Prop :=
  0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧
    ∀ s > 0, ∃ δ > 0, ∃ (R : ℕ) (C : ℝ), ∀ (N T : ℝ) (a b : ℕ) (f : ℝ → ℝ),
      1 ≤ N → N ^ s ≤ T → N ≤ a → b ≤ 2 * N → IsAdmissible R T s δ a b f →
        ‖∑ n ∈ Finset.Icc a b, e (f n)‖ ≤ C * (T / N ^ s) ^ k * N ^ l

/-- The trivial bound $|\sum_{n=a}^b e(f(n))| \le b - a + 1 \le 2N$ shows that $(0, 1)$ is an
exponent pair. -/
@[category test, AMS 11]
theorem isExponentPair_zero_one : IsExponentPair 0 1 := by
  refine ⟨le_rfl, by norm_num, by norm_num, le_rfl, fun s _ => ⟨1, one_pos, 0, 2, ?_⟩⟩
  intro N T a b f hN hT ha hb _
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos (by linarith) s).trans_le hT
  have hF : 0 < T / N ^ s := by positivity
  rw [Real.rpow_zero, Real.rpow_one, mul_one]
  calc ‖∑ n ∈ Finset.Icc a b, e (f n)‖
      ≤ ∑ n ∈ Finset.Icc a b, ‖e (f n)‖ := norm_sum_le _ _
    _ = (Finset.Icc a b).card := by
        simp only [additiveChar, Complex.norm_exp_ofReal_mul_I, Finset.sum_const, nsmul_eq_mul,
          mul_one]
    _ ≤ 2 * N := by
        rw [Nat.card_Icc]
        rcases Nat.lt_or_ge (b + 1) a with h | h
        · rw [Nat.sub_eq_zero_of_le h.le]
          simp only [Nat.cast_zero]
          linarith
        · rw [Nat.cast_sub h]
          push_cast
          linarith

/--
**Exponent pair conjecture.** For all $\varepsilon > 0$, is the pair
$(\varepsilon, 1/2 + \varepsilon)$ an exponent pair?

Since an exponent pair $(k, l)$ satisfies $k \le 1/2 \le l \le 1$ by definition, the question is
only meaningful for $0 < \varepsilon \le 1/2$; for $\varepsilon \ge 1/2$ the corresponding estimate
$\ll (T / N^s)^{\varepsilon} N^{1/2 + \varepsilon}$ already follows from the trivial bound.
The conjectured answer is yes; this would imply the Lindelöf hypothesis.
-/
@[category research open, AMS 11]
theorem exponent_pair_conjecture :
    answer(sorry) ↔ ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), IsExponentPair ε (1 / 2 + ε) := by
  sorry

end ExponentPairConjecture
