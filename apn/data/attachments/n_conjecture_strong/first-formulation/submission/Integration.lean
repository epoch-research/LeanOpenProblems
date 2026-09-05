import Submission.Spec
import Submission.Coprimality
import Submission.PolynomialEstimates
import Submission.Sequence
import Submission.SubsumLemma
import Submission.RadicalEstimate
import Submission.PowerContradiction

/-! # An admissible family disproving the strong four-variable bound -/

namespace StrongFour

open NConjecture

/-- The four terms of the identity along the fixed-prime-support progression. -/
def tuple (n : ℕ) : Fin 4 → ℤ :=
  ![a (parameter n) ^ 5, -(b (parameter n) ^ 2),
    -(5 * (h (parameter n)) ^ 7), -g (parameter n)]

lemma tuple_admissible (n : ℕ) : tuple n ∈ strongAdmissibleSet 4 := by
  have hu := parameter_ge_three n
  have hbal : a (parameter n) ^ 5 = b (parameter n) ^ 2 +
      5 * (h (parameter n)) ^ 7 + g (parameter n) := by
    have := polynomial_identity (parameter n)
    linarith
  refine ⟨coprime_tuple (parameter n) (parameter_mod n), ?_, ?_⟩
  · exact sum_four hbal
  · exact no_vanishing_four (pow_pos (b_pos _ hu) 2)
      (mul_pos (by norm_num) (pow_pos (h_pos _ hu) 7)) (g_pos _ hu) hbal

lemma height_lower (n : ℕ) :
    (parameter n : ℝ) ^ 20 ≤ (maxAbs (tuple n) : ℝ) := by
  have hfirst : (tuple n 0).natAbs ≤ maxAbs (tuple n) :=
    Finset.le_sup (f := fun i : Fin 4 => (tuple n i).natAbs)
      (Finset.mem_univ (0 : Fin 4))
  have hcast : ((tuple n 0).natAbs : ℝ) ≤ (maxAbs (tuple n) : ℝ) := by
    exact_mod_cast hfirst
  exact (a_pow_five_natAbs_lower _ (parameter_ge_three n)).trans (by
    simpa only [tuple, Matrix.cons_val_zero] using hcast)

lemma radical_upper (n : ℕ) :
    (rad (tuple n) : ℝ) ≤ (98972845020 : ℝ) * (K : ℝ) * (parameter n : ℝ) ^ 19 := by
  have hu := parameter_ge_three n
  exact real_radical_estimate (a_pos _ hu) (b_pos _ hu) (g_pos _ hu) (h_pos _ hu)
    K_pos n (parameter_linear n) (a_natAbs_upper _ hu) (b_natAbs_upper _ hu)
    (g_natAbs_upper _ hu)

end StrongFour

theorem final_disproof_test : ¬ (type_of% @NConjecture.n_conjecture.variants.strong) := by
  intro hconj
  obtain ⟨C, hC⟩ := hconj 4 (by norm_num) (by norm_num) ((1 : ℝ) / 38) (by norm_num)
  let D : ℝ := 98972845020 * (StrongFour.K : ℝ)
  obtain ⟨n, hn⟩ := StrongFour.parameter_unbounded (max ((max C 0) ^ 38 * D ^ 39) 1)
  apply StrongFour.power_contradiction_of_large (C := max C 0) (D := D)
    (H := (NConjecture.maxAbs (StrongFour.tuple n) : ℝ))
    (R := (NConjecture.rad (StrongFour.tuple n) : ℝ))
    (le_max_right C 0) (by dsimp [D]; positivity) hn (StrongFour.height_lower n)
    (Nat.cast_nonneg _) (StrongFour.radical_upper n)
  exact (hC _ (StrongFour.tuple_admissible n)).trans_le
    (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

#print axioms final_disproof_test
