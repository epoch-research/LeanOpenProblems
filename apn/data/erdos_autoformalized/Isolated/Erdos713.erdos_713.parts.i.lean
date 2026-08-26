import FormalConjecturesUtil

/-!
# Erdős Problem 713

*References:*
- [erdosproblems.com/713](https://www.erdosproblems.com/713)
-/

open Filter SimpleGraph

namespace Erdos713

open scoped Classical in
/--
Is it true that, for every bipartite graph $G$, there exists some $\alpha\in [1,2)$ and $c>0$ such that\[\mathrm{ex}(n;G)\sim cn^\alpha?\]

The condition that $G$ have at least two edges excludes degenerate forbidden graphs whose
extremal number is eventually zero, for which the displayed asymptotic with $c>0$ is impossible.
-/
theorem erdos_713.parts.i :
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      ∃ α c : ℝ, α ∈ Set.Ico 1 2 ∧ 0 < c ∧
        Asymptotics.IsEquivalent atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ α) := by
  sorry

end Erdos713
