import FormalConjecturesUtil

/-!
# Erdős Problem 431

*Reference:* [erdosproblems.com/431](https://www.erdosproblems.com/431)
-/

open scoped Pointwise

namespace Erdos431

/--
Are there two infinite sets $A$ and $B$ such that $A+B$ agrees with the set of prime numbers up to finitely many exceptions?
-/
theorem erdos_431 :
    (∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (symmDiff (A + B) {p : ℕ | p.Prime}).Finite) := by
  sorry

end Erdos431
