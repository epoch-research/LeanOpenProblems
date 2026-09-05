import Submission.Coprimality

/-! # A progression with fixed prime support in its linear factor -/

namespace StrongFour

/-- The fixed base whose prime divisors are allowed in the linear factor. -/
def K : ℕ := 2 * M.natAbs + 1

lemma K_pos : 0 < K := by
  unfold K
  omega

lemma K_cast : (K : ℤ) = 2 * M + 1 := by
  simp only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Int.natCast_natAbs, abs_of_pos M_pos]

/-- A division-free presentation of `(7 * K ^ n - 1) / 2`. -/
def parameter : ℕ → ℤ
  | 0 => 3
  | n + 1 => (2 * M + 1) * parameter n + M

lemma parameter_lower (n : ℕ) : (n : ℤ) + 3 ≤ parameter n := by
  induction n with
  | zero => norm_num [parameter]
  | succ n ih =>
    have hM : 1 ≤ M := M_pos
    have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    simp only [parameter, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma parameter_ge_three (n : ℕ) : 3 ≤ parameter n := by
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have := parameter_lower n
  omega

lemma parameter_mod (n : ℕ) : M ∣ parameter n - 3 := by
  induction n with
  | zero => simp [parameter]
  | succ n ih =>
    have heq : parameter (n + 1) - 3 =
        (2 * M + 1) * (parameter n - 3) + 7 * M := by
      simp only [parameter]
      ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_left M 7)

lemma parameter_linear (n : ℕ) : h (parameter n) = 7 * (K : ℤ) ^ n := by
  induction n with
  | zero => norm_num [parameter, h]
  | succ n ih =>
    have heq : h (parameter (n + 1)) = (2 * M + 1) * h (parameter n) := by
      simp only [parameter, h]
      ring
    rw [heq, ih, K_cast, pow_succ]
    ring

lemma parameter_unbounded (B : ℝ) : ∃ n : ℕ, B < (parameter n : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, hn.trans_le ?_⟩
  have hlow := parameter_lower n
  have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have hlow' : (n : ℤ) ≤ parameter n := by omega
  exact_mod_cast hlow'

end StrongFour
