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
# Lucas primes

The Lucas numbers are defined by $L_0 = 2$, $L_1 = 1$ and $L_{n+2} = L_{n+1} + L_n$.
A Lucas prime is a Lucas number that is prime. The first few Lucas primes are
$2, 3, 7, 11, 29, 47, 199, 521, 2207, 3571, \ldots$ and the corresponding indices are
$0, 2, 4, 5, 7, 8, 11, 13, 16, 17, \ldots$. It is not known whether there are infinitely many
Lucas primes.

*References:*
- [Wikipedia: Lucas number, § Lucas primes](https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [OEIS A005479](https://oeis.org/A005479): the Lucas primes
- [OEIS A001606](https://oeis.org/A001606): indices $n$ such that $L_n$ is prime
-/

namespace LucasPrime

/-- The Lucas numbers satisfy $L_{n+2} = L_{n+1} + L_n$. -/
@[category API, AMS 11]
theorem lucasNumber_add_two (n : ℕ) :
    lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := by
  simp [lucasNumber, LucasSequence.V]

/-- Every Lucas number $L_n$ (with $n \geq 0$) is a positive integer. -/
@[category API, AMS 11]
theorem lucasNumber_pos (n : ℕ) : 0 < lucasNumber n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h1 h2 => rw [lucasNumber_add_two]; omega

/-- The Lucas numbers are strictly increasing from index $1$ on: $1 = L_1 < L_2 < L_3 < \cdots$. -/
@[category API, AMS 11]
theorem lucasNumber_succ_strictMono : StrictMono (fun n => lucasNumber (n + 1)) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have := lucasNumber_pos n
  simp only [lucasNumber_add_two]
  omega

/--
**Lucas primes.** Are there infinitely many Lucas primes?

A Lucas prime is a Lucas number that is prime, where the Lucas numbers are given by
$L_0 = 2$, $L_1 = 1$ and $L_{n+2} = L_{n+1} + L_n$. The first few Lucas primes are
$2, 3, 7, 11, 29, 47, 199, 521, 2207, 3571, 9349, \ldots$
([OEIS A005479](https://oeis.org/A005479)); in particular $L_0 = 2$ is counted.
The question asks whether the set of prime numbers that occur as a Lucas number is infinite.
-/
@[category research open, AMS 11]
theorem lucas_prime :
    answer(sorry) ↔ {p : ℕ | p.Prime ∧ ∃ n, lucasNumber n = p}.Infinite := by
  sorry

/--
Are there infinitely many indices $n$ such that the $n$-th Lucas number $L_n$ is prime?
The known such indices are $0, 2, 4, 5, 7, 8, 11, 13, 16, 17, 19, 31, 37, 41, 47, \ldots$
([OEIS A001606](https://oeis.org/A001606)).
-/
@[category research open, AMS 11]
theorem lucas_prime.variants.index :
    answer(sorry) ↔ {n : ℕ | Prime (lucasNumber n)}.Infinite := by
  sorry

/-- $L_0 = 2$ is a Lucas prime. -/
@[category test, AMS 11]
theorem two_mem : 2 ∈ {p : ℕ | p.Prime ∧ ∃ n, lucasNumber n = p} :=
  ⟨by norm_num, 0, rfl⟩

/-- $L_4 = 7$ is a Lucas prime. -/
@[category test, AMS 11]
theorem seven_mem : 7 ∈ {p : ℕ | p.Prime ∧ ∃ n, lucasNumber n = p} :=
  ⟨by norm_num, 4, rfl⟩

/-- $L_1 = 1$ is not prime, so $1$ is not an index of a Lucas prime. -/
@[category test, AMS 11]
theorem one_notMem : 1 ∉ {n : ℕ | Prime (lucasNumber n)} := by
  decide

/-- $L_{16} = 2207$ is prime, so $16$ is an index of a Lucas prime. -/
@[category test, AMS 11]
theorem sixteen_mem : 16 ∈ {n : ℕ | Prime (lucasNumber n)} := by
  show Prime (lucasNumber 16)
  rw [show lucasNumber 16 = ((2207 : ℕ) : ℤ) from rfl]
  exact Nat.prime_iff_prime_int.mp (by norm_num)

/--
The two ways of phrasing the conjecture are equivalent: there are infinitely many Lucas primes
if and only if there are infinitely many indices $n$ with $L_n$ prime.
-/
@[category test, AMS 11]
theorem index_infinite_iff_lucas_prime_infinite :
    {n : ℕ | Prime (lucasNumber n)}.Infinite ↔
      {p : ℕ | p.Prime ∧ ∃ n, lucasNumber n = p}.Infinite := by
  have key : ∀ n, ((lucasNumber n).toNat : ℤ) = lucasNumber n :=
    fun n => Int.toNat_of_nonneg (lucasNumber_pos n).le
  constructor
  · intro h
    have hinj : Set.InjOn (fun n => (lucasNumber n).toNat)
        ({n : ℕ | Prime (lucasNumber n)} \ {0}) := by
      rintro (_ | a) ha (_ | b) hb hab
      · rfl
      · simp at ha
      · simp at hb
      · have := congrArg (fun m : ℕ => (m : ℤ)) hab
        simpa using lucasNumber_succ_strictMono.injective (by simpa only [key] using this)
    refine ((h.diff (Set.finite_singleton 0)).image hinj).mono ?_
    rintro _ ⟨n, ⟨hn, -⟩, rfl⟩
    exact ⟨Nat.prime_iff_prime_int.mpr (by simpa only [key] using hn), n, (key n).symm⟩
  · intro h
    refine fun hfin => h ((hfin.image (fun n => (lucasNumber n).toNat)).subset ?_)
    rintro p ⟨hp, n, hn⟩
    exact ⟨n, by simpa [hn] using Nat.prime_iff_prime_int.mp hp, by simp [hn]⟩

end LucasPrime
