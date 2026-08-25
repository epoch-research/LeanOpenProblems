import FormalConjecturesUtil

/-!
# Erdős Problem 571

*References:*
- [erdosproblems.com/571](https://www.erdosproblems.com/571)
-/

open Filter SimpleGraph

namespace Erdos571

/--
Show that for any rational $\alpha \in [1,2)$ there exists a bipartite graph $G$ such that\[\mathrm{ex}(n;G)\asymp n^{\alpha}.\]
-/
theorem erdos_571 :
    ∀ α : ℚ, 1 ≤ α → α < 2 →
      ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
        Asymptotics.IsTheta atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (α : ℝ)) := by
  sorry

end Erdos571
