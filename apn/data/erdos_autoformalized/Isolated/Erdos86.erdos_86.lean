import FormalConjecturesUtil

/-!
# Erdős Problem 86

*Reference:* [erdosproblems.com/86](https://www.erdosproblems.com/86)
-/

open Filter SimpleGraph

namespace Erdos86

/--
Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$ edges). Is it true that every subgraph of $Q_n$ with\[\geq \left(\frac{1}{2}+o(1)\right)n2^{n-1}\]many edges contains a $C_4$?
-/
theorem erdos_86 :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n → Bool),
      H ≤ hypercube n →
        (1 / 2 + ε) * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) →
          cycleGraph 4 ⊑ H) := by
  sorry

end Erdos86
