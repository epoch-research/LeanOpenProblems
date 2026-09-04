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
# Goodman's conjecture

Goodman's conjecture (1948) on the coefficients of multivalent ($p$-valent) functions in the
unit disc. Let
$$f(z) = \sum_{n=1}^{\infty} b_n z^n$$
be analytic and $p$-valent in the unit disc, i.e. $f$ takes no value more than $p$ times there.
The conjecture claims that for every $n \geq p + 1$,
$$|b_n| \leq \sum_{k=1}^{p} \frac{2k\,(n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)}\,|b_k|.$$
For $p = 1$ this is the Bieberbach conjecture $|b_n| \leq n |b_1|$ (de Branges' theorem).

*References:*
- [Wikipedia, Goodman's conjecture](https://en.wikipedia.org/wiki/Goodman%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Go48] Goodman, A. W. "On some determinants related to $p$-valent functions."
  Trans. Amer. Math. Soc. 63 (1948), 175–192.
  [doi:10.1090/S0002-9947-1948-0023910-X](https://doi.org/10.1090/S0002-9947-1948-0023910-X)
- [LS78] Lyzzaik, A., Styer, D. "Goodman's conjecture and the coefficients of univalent
  functions." Proc. Amer. Math. Soc. 69 (1978), 111–114.
  [doi:10.1090/S0002-9939-1978-0460619-7](https://doi.org/10.1090/S0002-9939-1978-0460619-7)
- [Gr97] Grinshpan, A. Z. "On the Goodman conjecture and related functions of several complex
  variables." Algebra i Analiz 9 (1997), no. 3, 198–204.
- [Gr02] Grinshpan, A. Z. "Logarithmic Geometry, Exponentiation, and Coefficient Bounds in the
  Theory of Univalent Functions and Nonoverlapping Domains." Handbook of Complex Analysis:
  Geometric Function Theory, Vol. 1 (2002), 273–332.
  [doi:10.1016/S1874-5709(02)80012-9](https://doi.org/10.1016/S1874-5709(02)80012-9)
-/

namespace GoodmansConjecture

open Metric Polynomial Set

/-- A function `f` is **`p`-valent on `s`** if it takes no value more than `p` times on `s`, i.e.
for every `w` the equation `f z = w` has at most `p` solutions `z ∈ s`.

Solutions are counted as points, not with multiplicity. For a function that is analytic on an
open set `s ⊆ ℂ` this agrees with the classical definition in which the roots of `f z = w` are
counted with multiplicity: a root of multiplicity `m` splits into `m` distinct simple roots of
`f z = w'` for `w' ≠ w` close to `w`. Constant functions are not `p`-valent on an open set for
any `p`, under either convention. -/
def IsPValentOn {α β : Type*} (f : α → β) (p : ℕ) (s : Set α) : Prop :=
  ∀ w, {z ∈ s | f z = w}.encard ≤ p

@[category API, AMS 30]
theorem IsPValentOn.mono {α β : Type*} {f : α → β} {p q : ℕ} {s : Set α} (hpq : p ≤ q)
    (hf : IsPValentOn f p s) : IsPValentOn f q s :=
  fun w => (hf w).trans (by exact_mod_cast hpq)

/-- Being `1`-valent on `s` is the same as being injective (univalent) on `s`. -/
@[category API, AMS 30]
theorem isPValentOn_one_iff {α β : Type*} {f : α → β} {s : Set α} :
    IsPValentOn f 1 s ↔ InjOn f s := by
  simp only [IsPValentOn, Nat.cast_one, encard_le_one_iff, mem_setOf_eq]
  constructor
  · intro h x hx y hy hxy
    exact h (f x) x y ⟨hx, rfl⟩ ⟨hy, hxy.symm⟩
  · rintro h w a b ⟨ha, rfl⟩ ⟨hb, hab⟩
    exact h ha hb hab.symm

@[category test, AMS 30]
theorem isPValentOn_id {α : Type*} (s : Set α) : IsPValentOn id 1 s :=
  isPValentOn_one_iff.mpr (injOn_id s)

/-- A constant function is not `p`-valent on the unit disc for any `p`: it takes its value
infinitely often. -/
@[category test, AMS 30]
theorem not_isPValentOn_const (p : ℕ) (c : ℂ) :
    ¬ IsPValentOn (fun _ : ℂ => c) p (ball 0 1) := by
  intro h
  have hinf : {z ∈ ball (0 : ℂ) 1 | (fun _ => c) z = c}.Infinite := by
    simp only [setOf_and, setOf_mem_eq, setOf_true, inter_univ]
    exact infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 one_pos)
  have := h c
  rw [hinf.encard_eq] at this
  exact (ENat.coe_lt_top p).not_ge this

open scoped Nat in
/-- Goodman's coefficients
$$A_{nk}(p) = \frac{2k\,(n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)},$$
meaningful for `1 ≤ k ≤ p < n`, where the natural number subtractions do not truncate and
`n ^ 2 - k ^ 2 ≠ 0`. -/
noncomputable def goodmanCoeff (p n k : ℕ) : ℝ :=
  2 * k * (n + p)! / ((p - k)! * (p + k)! * (n - p - 1)! * ((n : ℝ) ^ 2 - (k : ℝ) ^ 2))

/-- For `p = 1` the coefficient `A_{n1}(1)` equals `n`, so that Goodman's bound reduces to the
Bieberbach bound `|b_n| ≤ n |b_1|`. -/
@[category test, AMS 30]
theorem goodmanCoeff_one (n : ℕ) (hn : 2 ≤ n) : goodmanCoeff 1 n 1 = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [goodmanCoeff, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, Nat.factorial_succ]
  push_cast
  have h1 : ((m : ℝ) + 2) ^ 2 - 1 ^ 2 = (m + 2 + 1) * (m + 1) := by ring
  have h2 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [h1]
  field_simp
  ring

@[category test, AMS 30]
theorem goodmanCoeff_two_three_one : goodmanCoeff 2 3 1 = 5 := by
  norm_num [goodmanCoeff, Nat.factorial]

@[category test, AMS 30]
theorem goodmanCoeff_two_three_two : goodmanCoeff 2 3 2 = 4 := by
  norm_num [goodmanCoeff, Nat.factorial]

/-- **Goodman's conjecture** [Go48]. Let $p \geq 1$ and let
$f(z) = \sum_{n=1}^{\infty} b_n z^n$ be $p$-valent in the unit disc $|z| < 1$, i.e. $f$ is
analytic there and takes no value more than $p$ times. Then for every $n \geq p + 1$,
$$|b_n| \leq \sum_{k=1}^{p} \frac{2k\,(n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)}\,|b_k|.$$

Here $f$ is encoded by its coefficient sequence `b` with `b 0 = 0` (the sum starts at $n = 1$),
the power series converging to `f z` at every point `z` of the unit disc; analyticity of `f` in
the disc follows. The range $n \geq p + 1$ is needed for $(n-p-1)!$ and $n^2 - k^2 \neq 0$ to
make sense. For $p = 1$ this is the Bieberbach bound $|b_n| \leq n |b_1|$ (de Branges). -/
@[category research open, AMS 30]
theorem goodmans_conjecture (p : ℕ) (hp : 1 ≤ p) (f : ℂ → ℂ) (b : ℕ → ℂ)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (f z)) (hb₀ : b 0 = 0)
    (hf : IsPValentOn f p (ball 0 1)) (n : ℕ) (hn : p + 1 ≤ n) :
    ‖b n‖ ≤ ∑ k ∈ Finset.Icc 1 p, goodmanCoeff p n k * ‖b k‖ := by
  sorry

/-- For $p = 2$ [LS78] and $p = 3$ (Grinshpan, see [Gr97] and [Gr02]), Goodman's conjecture is
known to hold for functions of the form $f = P \circ \varphi$, where $P$ is a polynomial of degree
at most $p$ (so that $f$ is $p$-valent) and $\varphi$ is univalent, i.e. analytic and injective,
in the unit disc: if $P(\varphi(z)) = \sum_{n=1}^{\infty} b_n z^n$ for $|z| < 1$, then for every
$n \geq p + 1$,
$$|b_n| \leq \sum_{k=1}^{p} \frac{2k\,(n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)}\,|b_k|.$$ -/
@[category research solved, AMS 30]
theorem goodmans_conjecture.variants.polynomial_of_univalent_p_two_three (p : ℕ)
    (hp : p = 2 ∨ p = 3) (P : ℂ[X]) (hP : P.natDegree ≤ p) (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ (ball 0 1)) (hφ' : InjOn φ (ball 0 1)) (b : ℕ → ℂ)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => b n * z ^ n) (P.eval (φ z)))
    (hb₀ : b 0 = 0) (n : ℕ) (hn : p + 1 ≤ n) :
    ‖b n‖ ≤ ∑ k ∈ Finset.Icc 1 p, goodmanCoeff p n k * ‖b k‖ := by
  sorry

end GoodmansConjecture
