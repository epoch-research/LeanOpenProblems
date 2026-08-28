import FormalConjecturesUtil

/-!
# Erdős Problem 548

*Reference:* [erdosproblems.com/548](https://www.erdosproblems.com/548)
-/

open SimpleGraph

namespace Erdos548

/--
Let $n\geq k+1$. Every graph on $n$ vertices with at least $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices.
-/
theorem erdos_548 :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G := by
  sorry

end Erdos548

theorem Erdos548.erdos_548.disproof : ¬ (type_of% @Erdos548.erdos_548) := sorry
