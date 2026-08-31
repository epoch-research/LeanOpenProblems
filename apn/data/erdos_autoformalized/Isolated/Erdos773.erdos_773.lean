import FormalConjecturesUtil

/-!
# Erdős Problem 773

*Reference:* [erdosproblems.com/773](https://www.erdosproblems.com/773)
-/

namespace Erdos773

open Filter

/--
What is the size of the largest Sidon subset $A\subseteq\{1,2^2,\ldots,N^2\}$? Is it $N^{1-o(1)}$?
-/
theorem erdos_773 :
    (∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ)) := by
  sorry

end Erdos773

theorem Erdos773.erdos_773.disproof : ¬ (type_of% @Erdos773.erdos_773) := sorry
