import FormalConjecturesUtil

/-!
# Erdős Problem 1206

*Reference:* [erdosproblems.com/1206](https://www.erdosproblems.com/1206)
-/

namespace Erdos1206

/--
Does $\{1,2^3,\ldots,N^3\}$ contain a Sidon set of size $\gg N$?
-/
theorem erdos_1206.parts.i :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in Filter.atTop, ∃ S : Finset ℕ,
      S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ c * (N : ℝ) ≤ (S.card : ℝ) := by
  sorry

end Erdos1206
