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
# Newman–Shanks–Williams primes

*References:*
 - [Wikipedia, Newman–Shanks–Williams prime](https://en.wikipedia.org/wiki/Newman%E2%80%93Shanks%E2%80%93Williams_prime)
 - [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
 - [A001333](https://oeis.org/A001333), [A088165](https://oeis.org/A088165),
   [A005850](https://oeis.org/A005850)
 - [NSW80] Newman, M., Shanks, D. and Williams, H. C., *Simple groups of square order and an
   interesting sequence of primes*. Acta Arithmetica 38 (1980), 129–140.

Let $S_0 = 1$, $S_1 = 1$ and $S_n = 2 S_{n-1} + S_{n-2}$ for $n \geq 2$, so that
$$S_n = \frac{(1 + \sqrt 2)^n + (1 - \sqrt 2)^n}{2}.$$
The first few terms are $1, 1, 3, 7, 17, 41, 99, \ldots$ ([A001333](https://oeis.org/A001333)).
Each term is half the corresponding companion Pell number.

A *Newman–Shanks–Williams prime* (NSW prime) is a prime number of the form $S_{2m+1}$, that is,
a prime term of odd index in this sequence. The first few NSW primes are
$7, 41, 239, 9369319, 63018038201, \ldots$ ([A088165](https://oeis.org/A088165)), with indices
$3, 5, 7, 19, 29, \ldots$ ([A005850](https://oeis.org/A005850)). The odd-index restriction
matters: $S_2 = 3$, $S_4 = 17$ and $S_8 = 577$ are prime but are not NSW primes.

The question asks whether there are infinitely many NSW primes.
-/

namespace NewmanShanksWilliamsPrime

/-- The sequence $S_n$ defined by $S_0 = 1$, $S_1 = 1$ and $S_{n+2} = 2 S_{n+1} + S_n$
([A001333](https://oeis.org/A001333)). Its terms of odd index are the candidates for
Newman–Shanks–Williams primes. -/
def nswSeq : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 1 + 1 => 2 * nswSeq (n + 1) + nswSeq n

@[category test, AMS 11]
theorem nswSeq_zero : nswSeq 0 = 1 := rfl

@[category test, AMS 11]
theorem nswSeq_one : nswSeq 1 = 1 := rfl

@[category test, AMS 11]
theorem nswSeq_two : nswSeq 2 = 3 := rfl

@[category test, AMS 11]
theorem nswSeq_three : nswSeq 3 = 7 := rfl

@[category test, AMS 11]
theorem nswSeq_four : nswSeq 4 = 17 := rfl

@[category test, AMS 11]
theorem nswSeq_five : nswSeq 5 = 41 := rfl

@[category test, AMS 11]
theorem nswSeq_six : nswSeq 6 = 99 := rfl

@[category test, AMS 11]
theorem nswSeq_seven : nswSeq 7 = 239 := rfl

/-- The closed form $S_n = \frac{(1 + \sqrt 2)^n + (1 - \sqrt 2)^n}{2}$. -/
@[category textbook, AMS 11]
theorem coe_nswSeq_eq (n : ℕ) : (nswSeq n : ℝ) = ((1 + √2) ^ n + (1 - √2) ^ n) / 2 := by
  -- The characteristic polynomial of the recursion is $x^2 = 2x + 1$, with roots
  -- $\alpha = 1 + \sqrt{2}$ and $\beta = 1 - \sqrt{2}$. The function $(\alpha^n + \beta^n) / 2$
  -- satisfies the same recursion and the same base cases as `nswSeq`.
  set α : ℝ := 1 + √2 with hα_def
  set β : ℝ := 1 - √2 with hβ_def
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hα_sq : α ^ 2 = 2 * α + 1 := by rw [hα_def]; ring_nf; linarith [hsq2]
  have hβ_sq : β ^ 2 = 2 * β + 1 := by rw [hβ_def]; ring_nf; linarith [hsq2]
  have hα_rec : ∀ n, α ^ (n + 2) = 2 * α ^ (n + 1) + α ^ n := by
    intro n
    have : α ^ (n + 2) = α ^ n * α ^ 2 := by ring
    rw [this, hα_sq]; ring
  have hβ_rec : ∀ n, β ^ (n + 2) = 2 * β ^ (n + 1) + β ^ n := by
    intro n
    have : β ^ (n + 2) = β ^ n * β ^ 2 := by ring
    rw [this, hβ_sq]; ring
  -- Joint induction on consecutive indices.
  suffices h : ∀ n,
      (nswSeq n : ℝ) = (α ^ n + β ^ n) / 2 ∧
      (nswSeq (n + 1) : ℝ) = (α ^ (n + 1) + β ^ (n + 1)) / 2 from (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [nswSeq]
    · simp only [nswSeq, pow_one, Nat.cast_one, zero_add]
      rw [hα_def, hβ_def]; ring
  | succ k ih =>
    obtain ⟨hk, hk1⟩ := ih
    refine ⟨hk1, ?_⟩
    have hrec : nswSeq (k + 1 + 1) = 2 * nswSeq (k + 1) + nswSeq k := rfl
    show (nswSeq (k + 1 + 1) : ℝ) = (α ^ (k + 1 + 1) + β ^ (k + 1 + 1)) / 2
    rw [hrec]
    push_cast
    rw [hk1, hk, hα_rec k, hβ_rec k]
    ring

/-- Every term of the sequence $S_n$ is positive. -/
@[category API, AMS 11]
theorem nswSeq_pos (n : ℕ) : 0 < nswSeq n := by
  induction n using nswSeq.induct with
  | case1 => decide
  | case2 => decide
  | case3 n _ _ => show 0 < 2 * nswSeq (n + 1) + nswSeq n; omega

/-- The sequence $S_n$ is strictly increasing from index $1$ onwards. -/
@[category API, AMS 11]
theorem nswSeq_lt_nswSeq_succ (n : ℕ) : nswSeq (n + 1) < nswSeq (n + 2) := by
  show nswSeq (n + 1) < 2 * nswSeq (n + 1) + nswSeq n
  have := nswSeq_pos (n + 1)
  omega

/-- The odd-index subsequence $m \mapsto S_{2m+1}$ is strictly increasing. -/
@[category API, AMS 11]
theorem strictMono_nswSeq_odd : StrictMono fun m => nswSeq (2 * m + 1) := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  calc nswSeq (2 * m + 1) < nswSeq (2 * m + 2) := nswSeq_lt_nswSeq_succ _
    _ < nswSeq (2 * m + 3) := nswSeq_lt_nswSeq_succ _
    _ = nswSeq (2 * (m + 1) + 1) := by ring_nf

/-- A natural number $p$ is a *Newman–Shanks–Williams prime* if it is prime and it is of the
form $S_{2m+1}$ for some $m$, where $S$ is the sequence `nswSeq`. Only odd indices are allowed:
for instance $S_2 = 3$ and $S_4 = 17$ are prime but are not NSW primes. -/
def IsNSWPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, p = nswSeq (2 * m + 1)

/-- $7 = S_3$ is a Newman–Shanks–Williams prime. -/
@[category test, AMS 11]
theorem isNSWPrime_seven : IsNSWPrime 7 :=
  ⟨by norm_num, 1, rfl⟩

/-- $41 = S_5$ is a Newman–Shanks–Williams prime. -/
@[category test, AMS 11]
theorem isNSWPrime_fortyOne : IsNSWPrime 41 :=
  ⟨by norm_num, 2, rfl⟩

/-- $239 = S_7$ is a Newman–Shanks–Williams prime. -/
@[category test, AMS 11]
theorem isNSWPrime_twoHundredThirtyNine : IsNSWPrime 239 :=
  ⟨by norm_num, 3, rfl⟩

/-- $S_2 = 3$ is prime but it is not a Newman–Shanks–Williams prime, since its index is even. -/
@[category test, AMS 11]
theorem not_isNSWPrime_three : ¬ IsNSWPrime 3 := by
  rintro ⟨-, m, hm⟩
  rcases m with _ | m
  · exact absurd hm (by decide)
  · have h7 : nswSeq (2 * 1 + 1) ≤ nswSeq (2 * (m + 1) + 1) :=
      strictMono_nswSeq_odd.monotone (by omega)
    rw [← hm] at h7
    exact absurd h7 (by decide)

/-- $S_4 = 17$ is prime but it is not a Newman–Shanks–Williams prime, since its index is
even. -/
@[category test, AMS 11]
theorem not_isNSWPrime_seventeen : ¬ IsNSWPrime 17 := by
  rintro ⟨-, m, hm⟩
  rcases m with _ | _ | m
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · have h41 : nswSeq (2 * 2 + 1) ≤ nswSeq (2 * (m + 1 + 1) + 1) :=
      strictMono_nswSeq_odd.monotone (by omega)
    rw [← hm] at h41
    exact absurd h41 (by decide)

/--
Are there infinitely many Newman–Shanks–Williams primes? That is, are there infinitely many
primes of the form
$$S_{2m+1} = \frac{(1 + \sqrt 2)^{2m+1} + (1 - \sqrt 2)^{2m+1}}{2},$$
where $S_0 = S_1 = 1$ and $S_n = 2 S_{n-1} + S_{n-2}$ for $n \geq 2$?
-/
@[category research open, AMS 11]
theorem newman_shanks_williams_prime :
    answer(sorry) ↔ {p : ℕ | IsNSWPrime p}.Infinite := by
  sorry

/--
Equivalent formulation in terms of indices: are there infinitely many $m$ such that
$S_{2m+1}$ is prime?
-/
@[category research open, AMS 11]
theorem newman_shanks_williams_prime.variant :
    answer(sorry) ↔ {m : ℕ | (nswSeq (2 * m + 1)).Prime}.Infinite := by
  sorry

/-- The set of Newman–Shanks–Williams primes is the image of the set of indices $m$ with
$S_{2m+1}$ prime under $m \mapsto S_{2m+1}$. -/
@[category API, AMS 11]
theorem setOf_isNSWPrime_eq_image :
    {p : ℕ | IsNSWPrime p} =
      (fun m => nswSeq (2 * m + 1)) '' {m : ℕ | (nswSeq (2 * m + 1)).Prime} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_image, IsNSWPrime]
  constructor
  · rintro ⟨hp, m, rfl⟩
    exact ⟨m, hp, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨hm, m, rfl⟩

/-- The two formulations of the question are equivalent, since $m \mapsto S_{2m+1}$ is
injective. -/
@[category test, AMS 11]
theorem isNSWPrime_infinite_iff :
    {p : ℕ | IsNSWPrime p}.Infinite ↔ {m : ℕ | (nswSeq (2 * m + 1)).Prime}.Infinite := by
  rw [setOf_isNSWPrime_eq_image, Set.infinite_image_iff strictMono_nswSeq_odd.injective.injOn]

end NewmanShanksWilliamsPrime
