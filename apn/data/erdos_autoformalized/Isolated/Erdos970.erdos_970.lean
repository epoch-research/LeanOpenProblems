import FormalConjecturesUtil

/-!
# Erdős Problem 970

*Reference:* [erdosproblems.com/970](https://www.erdosproblems.com/970)
-/

namespace Erdos970

/--
`IsJacobsthalBound k m` says that every interval of `m` consecutive integers contains an
integer coprime to every positive natural number having at most `k` distinct prime factors.
-/
def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

/--
Jacobsthal's function, uniformly parametrized by the maximum number of distinct prime factors.
-/
noncomputable def jacobsthalFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | IsJacobsthalBound k m}

/--
Let $h(k)$ be Jacobsthal's function, defined to as the minimal $m$ such that, if $n$ has at most $k$ prime factors, then in any set of $m$ consecutive integers there exists an integer coprime to $n$. Determine the order of magnitude of $h(k)$. In particular, is it true that\[h(k) \ll k^2?\]
-/
theorem erdos_970 :
    (∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 2) := by
  sorry

end Erdos970

theorem Erdos970.erdos_970.disproof : ¬ (type_of% @Erdos970.erdos_970) := sorry
