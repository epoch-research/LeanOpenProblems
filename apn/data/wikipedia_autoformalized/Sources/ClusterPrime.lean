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
# Cluster primes

A cluster prime is a prime $p$ such that every even positive integer $k \le p - 3$ can be
written as the difference of two primes not exceeding $p$. By convention, $2$ is not a cluster
prime. The first $23$ odd primes (up to $89$) are all cluster primes; the first odd prime that
is not a cluster prime is $97$. Blecksmith, Erdős and Selfridge proved that the cluster primes
form a small set (the sum of their reciprocals converges), but it is not known whether there are
infinitely many of them.

The same question is Erdős Problem 17, see `FormalConjectures.ErdosProblems.«17»`. The
definition below follows the Wikipedia convention that $2$ is not a cluster prime.

*References:*
* [Wikipedia, Cluster prime](https://en.wikipedia.org/wiki/cluster_prime)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [OEIS A038134](https://oeis.org/A038134)
* R. Blecksmith, P. Erdős, J. L. Selfridge, *Cluster primes*,
  Amer. Math. Monthly 106 (1999), 43–48. [doi:10.2307/2589585](https://doi.org/10.2307/2589585)
-/

namespace ClusterPrime

/-- A prime $p$ is a *cluster prime* if every even positive integer $k \le p - 3$ can be
written as the difference $q_1 - q_2$ of two primes $q_1, q_2 \le p$. By convention, $2$ is
not a cluster prime (it would otherwise satisfy the condition vacuously). -/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ∀ k : ℕ, Even k → 0 < k → k ≤ p - 3 →
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧
        q₁ ≤ p ∧ q₂ ≤ p ∧ q₁ - q₂ = k

/-- Are there infinitely many cluster primes, i.e. primes $p \ne 2$ such that every even
positive integer $k \le p - 3$ is the difference of two primes not exceeding $p$? -/
@[category research open, AMS 11]
theorem cluster_prime : answer(sorry) ↔ {p : ℕ | IsClusterPrime p}.Infinite := by
  sorry

/-- By convention, $2$ is not a cluster prime. -/
@[category test, AMS 11]
theorem not_isClusterPrime_two : ¬ IsClusterPrime 2 := by
  simp [IsClusterPrime]

/-- The prime $3$ is a cluster prime: there is no even positive integer $k \le 3 - 3 = 0$. -/
@[category test, AMS 11]
theorem isClusterPrime_three : IsClusterPrime 3 := by
  refine ⟨by norm_num, by norm_num, fun k _ hk0 hk3 => ?_⟩
  omega

/-- The prime $5$ is a cluster prime: $2 = 5 - 3$. -/
@[category test, AMS 11]
theorem isClusterPrime_five : IsClusterPrime 5 := by
  refine ⟨by norm_num, by norm_num, fun k hk hk0 hk3 => ?_⟩
  obtain rfl : k = 2 := by rw [Nat.even_iff] at hk; omega
  exact ⟨5, 3, by norm_num, by norm_num, le_rfl, by norm_num, rfl⟩

/-- The prime $23$ is a cluster prime, as in the Wikipedia article: every even integer from
$2$ to $20$ is the difference of two primes not exceeding $23$. -/
@[category test, AMS 11]
theorem isClusterPrime_23 : IsClusterPrime 23 := by
  refine ⟨by norm_num, by norm_num, fun k hk hk0 hk3 => ?_⟩
  interval_cases k
  all_goals first
    | exact absurd hk (by decide)
    | exact ⟨5, 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨7, 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨11, 5, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨11, 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨13, 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨17, 5, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨17, 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨19, 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨23, 5, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
    | exact ⟨23, 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩

/-- The prime $97$ is not a cluster prime: $88 \le 94$ is not the difference of two primes
not exceeding $97$. It is the smallest odd prime that is not a cluster prime. -/
@[category test, AMS 11]
theorem not_isClusterPrime_97 : ¬ IsClusterPrime 97 := by
  rintro ⟨-, -, h⟩
  obtain ⟨q₁, q₂, hq₁, hq₂, hq₁p, -, hd⟩ :=
    h 88 (by decide) (by norm_num) (by norm_num)
  obtain rfl : q₁ = q₂ + 88 := by omega
  have : q₂ ≤ 9 := by omega
  interval_cases q₂ <;> revert hq₁ hq₂ <;> norm_num

end ClusterPrime
