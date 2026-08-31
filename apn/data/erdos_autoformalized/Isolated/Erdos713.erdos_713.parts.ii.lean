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
Must $\alpha$ be rational?

The same nondegeneracy condition on $G$ is used as in part (i). Rationality means that the real
number $\alpha$ lies in the image of the canonical embedding $\mathbb{Q}\to\mathbb{R}$.
-/
theorem erdos_713.parts.ii :
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      ∀ α c : ℝ, α ∈ Set.Ico 1 2 → 0 < c →
        Asymptotics.IsEquivalent atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ α) →
        α ∈ Set.range ((↑) : ℚ → ℝ) := by
  sorry

end Erdos713

theorem Erdos713.erdos_713.parts.ii.disproof : ¬ (type_of% @Erdos713.erdos_713.parts.ii) := sorry
