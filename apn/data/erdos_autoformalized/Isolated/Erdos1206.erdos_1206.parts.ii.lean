import FormalConjecturesUtil

/-!
# Erdős Problem 1206

*Reference:* [erdosproblems.com/1206](https://www.erdosproblems.com/1206)
-/

namespace Erdos1206

/--
Is there an infinite set $A\subset \mathbb{N}$ of positive density such that $\{a^3 : a\in A\}$ is a Sidon set?
-/
theorem erdos_1206.parts.ii :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  sorry

end Erdos1206
