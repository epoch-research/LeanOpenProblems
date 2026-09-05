import Submission.Coprimality

/-!
# Polynomial identity and growth bounds for the strong-four construction

For integer parameters `u ≥ 3`, all four base polynomials are positive.  The
height contribution `(a u)^5` has real lower bound `u^20`, while the base
polynomials `a`, `b`, and `g` have real upper bounds of degrees 4, 10, and 5.
-/

namespace StrongFour

/-- The exact identity underlying the four-term construction. -/
theorem polynomial_identity (u : ℤ) :
    a u ^ 5 - b u ^ 2 - 5 * (h u) ^ 7 - g u = 0 := by
  unfold a b h g
  ring

/- ## Positivity -/

theorem a_pos (u : ℤ) (hu : 3 ≤ u) : 0 < a u := by
  have hu0 : 0 ≤ u := by omega
  unfold a
  positivity

theorem b_pos (u : ℤ) (hu : 3 ≤ u) : 0 < b u := by
  have hu0 : 0 ≤ u := by omega
  have hp : 0 ≤ u^10 + 5*u^9 + 15*u^8 + 50*u^7 + 105*u^6 + 171*u^5 +
      305*u^4 + 270*u^3 + 195*u^2 := by positivity
  unfold b
  linarith

theorem h_pos (u : ℤ) (hu : 3 ≤ u) : 0 < h u := by
  unfold h
  omega

theorem g_pos (u : ℤ) (hu : 3 ≤ u) : 0 < g u := by
  have hu0 : 0 ≤ u := by omega
  have hp : 0 ≤ 1888*u^5 + 15760*u^4 + 22920*u^3 + 28380*u^2 := by
    positivity
  unfold g
  linarith

/- ## Integer degree bounds -/

/-- The leading monomial is a lower bound for `a`. -/
theorem a_lower (u : ℤ) (hu : 3 ≤ u) : u ^ 4 ≤ a u := by
  have hu0 : 0 ≤ u := by omega
  have hp : 0 ≤ 2*u^3 + 3*u^2 + 10*u + 1 := by positivity
  unfold a
  linarith only [hp]

/-- Bound every monomial of `a` by its degree-four counterpart. -/
theorem a_upper (u : ℤ) (hu : 3 ≤ u) : a u ≤ 17 * u ^ 4 := by
  have hu1 : 1 ≤ u := by omega
  calc
    a u = u^4 + 2*u^3 + 3*u^2 + 10*u^1 + u^0 := by simp [a]
    _ ≤ u^4 + 2*u^4 + 3*u^4 + 10*u^4 + u^4 := by
      gcongr <;> first | exact hu1 | norm_num
    _ = 17 * u^4 := by ring

/-- The positive coefficients of `b` sum to `1302`; discard its negative constant. -/
theorem b_upper (u : ℤ) (hu : 3 ≤ u) : b u ≤ 1302 * u ^ 10 := by
  have hu1 : 1 ≤ u := by omega
  calc
    b u ≤ u^10 + 5*u^9 + 15*u^8 + 50*u^7 + 105*u^6 + 171*u^5 +
        305*u^4 + 270*u^3 + 195*u^2 + 185*u^1 := by
      unfold b
      simp only [pow_one]
      omega
    _ ≤ u^10 + 5*u^10 + 15*u^10 + 50*u^10 + 105*u^10 + 171*u^10 +
        305*u^10 + 270*u^10 + 195*u^10 + 185*u^10 := by
      gcongr <;> first | exact hu1 | norm_num
    _ = 1302 * u^10 := by ring

/-- The positive coefficients of `g` sum to `127758`; discard its negative constant. -/
theorem g_upper (u : ℤ) (hu : 3 ≤ u) : g u ≤ 127758 * u ^ 5 := by
  have hu1 : 1 ≤ u := by omega
  calc
    g u ≤ 1888*u^5 + 15760*u^4 + 22920*u^3 + 28380*u^2 + 58810*u^1 := by
      unfold g
      simp only [pow_one]
      omega
    _ ≤ 1888*u^5 + 15760*u^5 + 22920*u^5 + 28380*u^5 + 58810*u^5 := by
      gcongr <;> first | exact hu1 | norm_num
    _ = 127758 * u^5 := by ring

/- ## Real bounds on natural absolute values -/

/-- The real degree-four lower bound, before taking the fifth power. -/
theorem a_natAbs_lower (u : ℤ) (hu : 3 ≤ u) :
    (u : ℝ) ^ 4 ≤ ((a u).natAbs : ℝ) := by
  rw [Nat.cast_natAbs, abs_of_pos (a_pos u hu)]
  exact_mod_cast a_lower u hu

/-- The first tuple entry has height at least `u^20`. -/
theorem a_pow_five_natAbs_lower (u : ℤ) (hu : 3 ≤ u) :
    (u : ℝ) ^ 20 ≤ ((a u ^ 5).natAbs : ℝ) := by
  calc
    (u : ℝ) ^ 20 = ((u : ℝ) ^ 4) ^ 5 := by rw [← pow_mul]
    _ ≤ ((a u).natAbs : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by positivity) (a_natAbs_lower u hu) 5
    _ = ((a u ^ 5).natAbs : ℝ) := by simp only [Int.natAbs_pow, Nat.cast_pow]

theorem a_natAbs_upper (u : ℤ) (hu : 3 ≤ u) :
    ((a u).natAbs : ℝ) ≤ 17 * (u : ℝ) ^ 4 := by
  rw [Nat.cast_natAbs, abs_of_pos (a_pos u hu)]
  exact_mod_cast a_upper u hu

theorem b_natAbs_upper (u : ℤ) (hu : 3 ≤ u) :
    ((b u).natAbs : ℝ) ≤ 1302 * (u : ℝ) ^ 10 := by
  rw [Nat.cast_natAbs, abs_of_pos (b_pos u hu)]
  exact_mod_cast b_upper u hu

theorem g_natAbs_upper (u : ℤ) (hu : 3 ≤ u) :
    ((g u).natAbs : ℝ) ≤ 127758 * (u : ℝ) ^ 5 := by
  rw [Nat.cast_natAbs, abs_of_pos (g_pos u hu)]
  exact_mod_cast g_upper u hu

end StrongFour
