import FormalConjecturesUtil

/-!
# Erdős Problem 714

*References:*
- [erdosproblems.com/714](https://www.erdosproblems.com/714)
-/

open Filter SimpleGraph

namespace Erdos714

/--
Is it true that\[\mathrm{ex}(n; K_{r,r}) \gg n^{2-1/r}?\]
-/
@[category research open, AMS 5]
theorem erdos_714 :
    (∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) := by
  sorry

end Erdos714
