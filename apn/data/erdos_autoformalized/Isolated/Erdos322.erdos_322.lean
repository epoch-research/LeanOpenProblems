import FormalConjecturesUtil

/-!
# Erdős Problem 322

*Reference:* [erdosproblems.com/322](https://www.erdosproblems.com/322)
-/

namespace Erdos322

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of nonnegative integers. The bases can be restricted to the interval from `0` to `n`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

/--
Let $k\geq 3$ and $A\subset \mathbb{N}$ be the set of $k$th powers. What is the order of growth of $1_A^{(k)}(n)$, i.e. the number of representations of $n$ as the sum of $k$ many $k$th powers? Does there exist some $c>0$ and infinitely many $n$ such that\[1_A^{(k)}(n) >n^c?\]
-/
theorem erdos_322 :
    (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite) := by
  sorry

end Erdos322

theorem Erdos322.erdos_322.disproof : ¬ (type_of% @Erdos322.erdos_322) := sorry
