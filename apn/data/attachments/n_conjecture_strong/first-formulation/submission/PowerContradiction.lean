import FormalConjecturesUtil

/-!
# The final power-growth contradiction for the strong four conjecture

This file contains only the real-variable estimate.  Raising the conjectured
bound to the 38th power gives exponents `20 * 38 = 760` and `19 * 39 = 741`;
canceling the positive factor `u ^ 741` contradicts the chosen size of `u`.
No limit or sequence argument is needed here.
-/

namespace StrongFour

/-- A height of degree 20 and a radical bound of degree 19 contradict the
exponent `1 + 1 / 38` once `u ^ 19` exceeds `C ^ 38 * D ^ 39`. -/
theorem power_contradiction {C D u H R : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hu : 1 ≤ u)
    (hlarge : C ^ 38 * D ^ 39 < u ^ 19)
    (hH : u ^ 20 ≤ H) (hR0 : 0 ≤ R) (hR : R ≤ D * u ^ 19)
    (hbound : H < C * R ^ (1 + (1 : ℝ) / 38)) : False := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hu_pos : 0 < u := zero_lt_one.trans_le hu
  have hrpow : (R ^ (1 + (1 : ℝ) / 38)) ^ (38 : ℕ) = R ^ (39 : ℕ) := by
    rw [← Real.rpow_mul_natCast hR0]
    norm_num
  have hpow : u ^ 760 < C ^ 38 * R ^ 39 := by
    have h := pow_lt_pow_left₀ (hH.trans_lt hbound) (pow_nonneg hu0 20)
      (by norm_num : (38 : ℕ) ≠ 0)
    simpa only [mul_pow, hrpow, ← pow_mul] using h
  have hRpow : R ^ 39 ≤ D ^ 39 * u ^ 741 := by
    calc
      R ^ 39 ≤ (D * u ^ 19) ^ 39 :=
        (pow_le_pow_iff_left₀ hR0 (mul_nonneg hD (pow_nonneg hu0 19))
          (by norm_num : (39 : ℕ) ≠ 0)).2 hR
      _ = D ^ 39 * u ^ 741 := by rw [mul_pow, ← pow_mul]
  have hmain : u ^ 19 * u ^ 741 < (C ^ 38 * D ^ 39) * u ^ 741 := by
    calc
      u ^ 19 * u ^ 741 = u ^ 760 := by rw [← pow_add]
      _ < C ^ 38 * R ^ 39 := hpow
      _ ≤ C ^ 38 * (D ^ 39 * u ^ 741) :=
        mul_le_mul_of_nonneg_left hRpow (pow_nonneg hC 38)
      _ = (C ^ 38 * D ^ 39) * u ^ 741 := (mul_assoc _ _ _).symm
  have hsmall : u ^ 19 < C ^ 38 * D ^ 39 :=
    (mul_lt_mul_iff_left₀ (pow_pos hu_pos 741)).mp hmain
  exact lt_asymm hlarge hsmall

/-- A convenient threshold for applying `power_contradiction` to an unbounded
family: it suffices to choose `u > max (C ^ 38 * D ^ 39) 1`. -/
theorem power_contradiction_of_large {C D u H R : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlarge : max (C ^ 38 * D ^ 39) 1 < u)
    (hH : u ^ 20 ≤ H) (hR0 : 0 ≤ R) (hR : R ≤ D * u ^ 19)
    (hbound : H < C * R ^ (1 + (1 : ℝ) / 38)) : False := by
  have hu : 1 ≤ u := (le_max_right _ _).trans hlarge.le
  have hlarge' : C ^ 38 * D ^ 39 < u ^ 19 :=
    ((le_max_left _ _).trans_lt hlarge).trans_le (le_self_pow₀ hu (by norm_num))
  exact power_contradiction hC hD hu hlarge' hH hR0 hR hbound

end StrongFour
