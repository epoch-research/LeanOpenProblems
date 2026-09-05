import FormalConjecturesUtil

/-!
# Radical estimates for a tuple of powers

The estimates below use divisibility of radicals, not coprimality.  In particular,
the exponent in `h = 7 * K ^ n` may be zero.
-/

namespace StrongFour

open scoped BigOperators
open UniqueFactorizationMonoid

/-- The radical of a natural-number power divides its base, even at exponent zero. -/
theorem nat_radical_power_dvd (x n : ℕ) : radical (x ^ n) ∣ x := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [radical_pow x hn]
    exact radical_dvd_self

/-- A product divisibility estimate; no positivity or coprimality is required. -/
theorem nat_radical_product_dvd (a b g K n : ℕ) :
    radical (a ^ 5 * b ^ 2 * (5 * (7 * K ^ n) ^ 7) * g) ∣
      35 * K * a * b * g := by
  have hK : radical (7 * K ^ n) ∣ 7 * K :=
    radical_mul_dvd.trans (mul_dvd_mul radical_dvd_self (nat_radical_power_dvd K n))
  have hh : radical ((7 * K ^ n) ^ 7) ∣ 7 * K := by
    rwa [radical_pow _ (by decide : (7 : ℕ) ≠ 0)]
  have hfive : radical (5 * (7 * K ^ n) ^ 7) ∣ 5 * (7 * K) :=
    radical_mul_dvd.trans (mul_dvd_mul radical_dvd_self hh)
  have hab : radical (a ^ 5 * b ^ 2) ∣ a * b :=
    radical_mul_dvd.trans
      (mul_dvd_mul (nat_radical_power_dvd a 5) (nat_radical_power_dvd b 2))
  have habh : radical (a ^ 5 * b ^ 2 * (5 * (7 * K ^ n) ^ 7)) ∣
      (a * b) * (5 * (7 * K)) :=
    radical_mul_dvd.trans (mul_dvd_mul hab hfive)
  have hall : radical (a ^ 5 * b ^ 2 * (5 * (7 * K ^ n) ^ 7) * g) ∣
      ((a * b) * (5 * (7 * K))) * g :=
    radical_mul_dvd.trans (mul_dvd_mul habh radical_dvd_self)
  convert hall using 1
  ring

/-- The divisibility estimate for the signed integer tuple, without sign assumptions. -/
theorem nat_radical_tuple_dvd {a b g h : ℤ} {K : ℕ} (n : ℕ)
    (he : h = (7 : ℤ) * (K : ℤ) ^ n) :
    radical (∏ i : Fin 4,
      ((![a ^ 5, -(b ^ 2), -(5 * h ^ 7), -g] : Fin 4 → ℤ) i).natAbs) ∣
        35 * K * a.natAbs * b.natAbs * g.natAbs := by
  simpa [Fin.prod_univ_succ, he, Int.natAbs_mul, Int.natAbs_pow, mul_assoc] using
    nat_radical_product_dvd a.natAbs b.natAbs g.natAbs K n

/-- The radical bound for a positive integer tuple with `h = 7 * K ^ n`.
The positivity hypothesis on `h` is retained for convenience, but is not needed. -/
theorem nat_radical_estimate {a b g h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) (_hh : 0 < h)
    {K : ℕ} (hK : 0 < K) (n : ℕ) (he : h = (7 : ℤ) * (K : ℤ) ^ n) :
    radical (∏ i : Fin 4,
      ((![a ^ 5, -(b ^ 2), -(5 * h ^ 7), -g] : Fin 4 → ℤ) i).natAbs) ≤
        35 * K * a.natAbs * b.natAbs * g.natAbs := by
  apply Nat.le_of_dvd
  · have ha' : 0 < a.natAbs := Int.natAbs_pos.mpr (ne_of_gt ha)
    have hb' : 0 < b.natAbs := Int.natAbs_pos.mpr (ne_of_gt hb)
    have hg' : 0 < g.natAbs := Int.natAbs_pos.mpr (ne_of_gt hg)
    positivity
  · exact nat_radical_tuple_dvd n he

/-- Combining the natural radical estimate with three real growth bounds gives degree 19. -/
theorem real_radical_estimate {a b g h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) (hh : 0 < h)
    {K : ℕ} (hK : 0 < K) (n : ℕ) (he : h = (7 : ℤ) * (K : ℤ) ^ n)
    {u : ℝ}
    (ha_growth : (a.natAbs : ℝ) ≤ 17 * u ^ 4)
    (hb_growth : (b.natAbs : ℝ) ≤ 1302 * u ^ 10)
    (hg_growth : (g.natAbs : ℝ) ≤ 127758 * u ^ 5) :
    ((radical (∏ i : Fin 4,
      ((![a ^ 5, -(b ^ 2), -(5 * h ^ 7), -g] : Fin 4 → ℤ) i).natAbs) : ℕ) : ℝ) ≤
        (98972845020 : ℝ) * (K : ℝ) * u ^ 19 := by
  calc
    ((radical (∏ i : Fin 4,
      ((![a ^ 5, -(b ^ 2), -(5 * h ^ 7), -g] : Fin 4 → ℤ) i).natAbs) : ℕ) : ℝ)
      ≤ (35 : ℝ) * (K : ℝ) * (a.natAbs : ℝ) * (b.natAbs : ℝ) *
          (g.natAbs : ℝ) := by
        exact_mod_cast nat_radical_estimate ha hb hg hh hK n he
    _ ≤ (35 : ℝ) * (K : ℝ) * (17 * u ^ 4) * (1302 * u ^ 10) *
        (127758 * u ^ 5) := by
      gcongr
    _ = (98972845020 : ℝ) * (K : ℝ) * u ^ 19 := by ring

end StrongFour
