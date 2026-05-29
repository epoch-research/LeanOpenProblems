import Mathlib

open Finset in
/-- Nicomachus's identity: the square of the sum of the first `n` naturals equals
the sum of their cubes. Requires induction plus algebraic manipulation. -/
theorem apn_sum_cubes (n : ℕ) :
    (∑ i ∈ range n, i) ^ 2 = ∑ i ∈ range n, i ^ 3 := by
  sorry
