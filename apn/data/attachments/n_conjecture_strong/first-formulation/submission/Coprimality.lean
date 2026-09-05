import FormalConjecturesUtil

/-!
# Coprimality of the explicit strong-four construction

The six integer-polynomial Bézout identities below, together with the seed `u = 3`,
prove pairwise coprimality on the arithmetic progression `M ∣ u - 3`.
This file does not import the conjectural specification.
-/

namespace StrongFour

def a (u : ℤ) : ℤ := u^4 + 2*u^3 + 3*u^2 + 10*u + 1

def b (u : ℤ) : ℤ :=
  u^10 + 5*u^9 + 15*u^8 + 50*u^7 + 105*u^6 + 171*u^5 +
    305*u^4 + 270*u^3 + 195*u^2 + 185*u - 159

def h (u : ℤ) : ℤ := 2*u + 1

def g (u : ℤ) : ℤ :=
  1888*u^5 + 15760*u^4 + 22920*u^3 + 28380*u^2 + 58810*u - 25285

/-- A positive multiple of 10 and of all six integer Bézout constants. -/
def M : ℤ :=
  10 * 44302336 * 55 * 25909670423005436759 * 226797 *
    4668301001649258879577091386750710258929233783901 * 1585088

theorem M_pos : 0 < M := by norm_num [M]

theorem M_ne_zero : M ≠ 0 := ne_of_gt M_pos

theorem two_dvd_M : (2 : ℤ) ∣ M := by norm_num [M]

theorem five_dvd_M : (5 : ℤ) ∣ M := by norm_num [M]

/-- Exact base values of the admissible seed. -/
theorem base_seed_values : a 3 = 193 ∧ b 3 = 517473 ∧ h 3 = 7 ∧ g 3 = 2760749 := by
  norm_num [a, b, h, g]

/-- All six base pairs are coprime at the seed. -/
theorem base_seed_coprimality :
    IsCoprime (a 3) (b 3) ∧ IsCoprime (a 3) (h 3) ∧ IsCoprime (a 3) (g 3) ∧
    IsCoprime (b 3) (h 3) ∧ IsCoprime (b 3) (g 3) ∧ IsCoprime (h 3) (g 3) := by
  norm_num [a, b, h, g]

/-- The coefficient 5 is coprime to every base value at the seed. -/
theorem seed_coprime_five :
    IsCoprime (a 3) (5 : ℤ) ∧ IsCoprime (b 3) (5 : ℤ) ∧
    IsCoprime (h 3) (5 : ℤ) ∧ IsCoprime (g 3) (5 : ℤ) := by
  norm_num [a, b, h, g]

/- ## Integer Bézout certificates

These are polynomial identities, proved by `ring`; no resultant algorithm is trusted.
-/

theorem bezout_ab (u : ℤ) :
    ((((((((((-106496) * u  - 479232) * u  - 1277952) * u  - 3727360) * u  - 6709248) * u  - 9105408) * u  - 12992512) * u  - 8626176) * u  - 4153344) * u  - 1970176) * a u +
    ((((106496) * u  + 159744) * u  + 159744) * u  + 266240) * b u = -44302336 := by
  unfold a b
  ring


theorem bezout_ah (u : ℤ) :
    (16) * a u +
    ((((-8) * u  - 12) * u  - 18) * u  - 71) * h u = -55 := by
  unfold a h
  ring


theorem bezout_ag (u : ℤ) :
    (((((-227834299828882432) * u  - 1778237434355735552) * u  - 1824472797576484928) * u  - 2215930789051075840) * u  - 4137133574859155744) * a u +
    ((((120674946943264) * u  + 175883935480752) * u  + 278945952679206) * u  + 861085103743179) * g u = -25909670423005436759 := by
  unfold a g
  ring


theorem bezout_bh (u : ℤ) :
    (1024) * b u +
    ((((((((((-512) * u  - 2304) * u  - 6528) * u  - 22336) * u  - 42592) * u  - 66256) * u  - 123032) * u  - 76724) * u  - 61478) * u  - 63981) * h u = -226797 := by
  unfold b h
  ring


theorem bezout_bg (u : ℤ) :
    (((((2925983761623782890206589682109247429400002560) * u  + 24978842913001479188865592094606968661809889280) * u  + 40671238544868839119071719486643049990703656960) * u  + 48683760062939682939703865109767787927725527040) * u  + 64774777683758193518623466876814890629126467584) * b u +
    ((((((((((-1549779534758359581677219111286677663877120) * u  - 8042498015534240801199982686056761560437760) * u  - 24991787008872744585564055099772982252219520) * u  - 79891114190240313622025020207834137668086080) * u  - 171159031139040693007126525503069822001090368) * u  - 285584337737578906702954134309081685629352800) * u  - 467479074255292741367825314098898691198259360) * u  - 464429322102562445193293012734143603683684240) * u  - 350175318602960334535377919707691096853316510) * u  - 222696802454747632583905076000113005778203463) * g u = -4668301001649258879577091386750710258929233783901 := by
  unfold b g
  ring


theorem bezout_hg (u : ℤ) :
    (((((-30208) * u  - 237056) * u  - 248192) * u  - 329984) * u  - 775968) * h u +
    (32) * g u = -1585088 := by
  unfold h g
  ring


/- ## Congruence and the seed argument -/

/-- Congruence transports coprimality if every common divisor divides a Bézout
constant that is itself a divisor of the modulus. -/
theorem isCoprime_of_bezout_modEq {x y x₀ y₀ c m U V : ℤ}
    (hbez : U * x + V * y = c) (hcm : c ∣ m)
    (hx : x ≡ x₀ [ZMOD m]) (hy : y ≡ y₀ [ZMOD m])
    (hseed : IsCoprime x₀ y₀) : IsCoprime x y := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  have hdx := Int.gcd_dvd_left x y
  have hdy := Int.gcd_dvd_right x y
  have hdc : (Int.gcd x y : ℤ) ∣ c := by
    rw [← hbez]
    exact dvd_add (dvd_mul_of_dvd_right hdx U) (dvd_mul_of_dvd_right hdy V)
  have hdm : (Int.gcd x y : ℤ) ∣ m := hdc.trans hcm
  have hdx₀ : (Int.gcd x y : ℤ) ∣ x₀ := (hx.of_dvd hdm).dvd_iff.mp hdx
  have hdy₀ : (Int.gcd x y : ℤ) ∣ y₀ := (hy.of_dvd hdm).dvd_iff.mp hdy
  have hdseed := Int.dvd_gcd hdx₀ hdy₀
  rw [Int.isCoprime_iff_gcd_eq_one.mp hseed] at hdseed
  exact Nat.dvd_one.mp hdseed

/-- The constant-polynomial instance of the seed argument. -/
theorem isCoprime_constant_of_modEq {x x₀ c m : ℤ}
    (hcm : c ∣ m) (hx : x ≡ x₀ [ZMOD m]) (hseed : IsCoprime x₀ c) :
    IsCoprime x c :=
  isCoprime_of_bezout_modEq (U := 0) (V := 1) (by ring) hcm hx
    Int.ModEq.rfl hseed

theorem a_modEq {m u v : ℤ} (hu : u ≡ v [ZMOD m]) :
    a u ≡ a v [ZMOD m] := by
  unfold a
  gcongr

theorem b_modEq {m u v : ℤ} (hu : u ≡ v [ZMOD m]) :
    b u ≡ b v [ZMOD m] := by
  unfold b
  gcongr

theorem h_modEq {m u v : ℤ} (hu : u ≡ v [ZMOD m]) :
    h u ≡ h v [ZMOD m] := by
  unfold h
  gcongr

theorem g_modEq {m u v : ℤ} (hu : u ≡ v [ZMOD m]) :
    g u ≡ g v [ZMOD m] := by
  unfold g
  gcongr

theorem modEq_seed (u : ℤ) (hu : M ∣ u - 3) : u ≡ 3 [ZMOD M] :=
  (Int.modEq_iff_dvd.mpr hu).symm

/- ## Coprimality of the base values -/

theorem coprime_ab (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (a u) (b u) :=
  isCoprime_of_bezout_modEq (m := M) (bezout_ab u) (by norm_num [M])
    (a_modEq (modEq_seed u hu)) (b_modEq (modEq_seed u hu))
    base_seed_coprimality.1

theorem coprime_ah (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (a u) (h u) :=
  isCoprime_of_bezout_modEq (m := M) (bezout_ah u) (by norm_num [M])
    (a_modEq (modEq_seed u hu)) (h_modEq (modEq_seed u hu))
    base_seed_coprimality.2.1

theorem coprime_ag (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (a u) (g u) :=
  isCoprime_of_bezout_modEq (m := M) (bezout_ag u) (by norm_num [M])
    (a_modEq (modEq_seed u hu)) (g_modEq (modEq_seed u hu))
    base_seed_coprimality.2.2.1

theorem coprime_bh (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (b u) (h u) :=
  isCoprime_of_bezout_modEq (m := M) (bezout_bh u) (by norm_num [M])
    (b_modEq (modEq_seed u hu)) (h_modEq (modEq_seed u hu))
    base_seed_coprimality.2.2.2.1

theorem coprime_bg (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (b u) (g u) :=
  isCoprime_of_bezout_modEq (m := M) (bezout_bg u) (by norm_num [M])
    (b_modEq (modEq_seed u hu)) (g_modEq (modEq_seed u hu))
    base_seed_coprimality.2.2.2.2.1

theorem coprime_hg (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (h u) (g u) :=
  isCoprime_of_bezout_modEq (m := M) (bezout_hg u) (by norm_num [M])
    (h_modEq (modEq_seed u hu)) (g_modEq (modEq_seed u hu))
    base_seed_coprimality.2.2.2.2.2

/-- Assemble six pairwise coprimality proofs into a four-vector. -/
theorem pairwise_coprime_four {x₀ x₁ x₂ x₃ : ℤ}
    (h01 : IsCoprime x₀ x₁) (h02 : IsCoprime x₀ x₂) (h03 : IsCoprime x₀ x₃)
    (h12 : IsCoprime x₁ x₂) (h13 : IsCoprime x₁ x₃) (h23 : IsCoprime x₂ x₃) :
    Pairwise fun i j : Fin 4 => IsCoprime (![x₀, x₁, x₂, x₃] i) (![x₀, x₁, x₂, x₃] j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals first
    | exact h01.symm
    | exact h02.symm
    | exact h03.symm
    | exact h12.symm
    | exact h13.symm
    | exact h23.symm

theorem coprime_base (u : ℤ) (hu : M ∣ u - 3) :
    Pairwise fun i j : Fin 4 =>
      IsCoprime (![a u, b u, h u, g u] i) (![a u, b u, h u, g u] j) :=
  pairwise_coprime_four (coprime_ab u hu) (coprime_ah u hu) (coprime_ag u hu)
    (coprime_bh u hu) (coprime_bg u hu) (coprime_hg u hu)

/- ## Coprimality with the coefficient 5 -/

theorem coprime_a_five (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (a u) (5 : ℤ) :=
  isCoprime_constant_of_modEq five_dvd_M (a_modEq (modEq_seed u hu))
    seed_coprime_five.1

theorem coprime_b_five (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (b u) (5 : ℤ) :=
  isCoprime_constant_of_modEq five_dvd_M (b_modEq (modEq_seed u hu))
    seed_coprime_five.2.1

theorem coprime_h_five (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (h u) (5 : ℤ) :=
  isCoprime_constant_of_modEq five_dvd_M (h_modEq (modEq_seed u hu))
    seed_coprime_five.2.2.1

theorem coprime_g_five (u : ℤ) (hu : M ∣ u - 3) : IsCoprime (g u) (5 : ℤ) :=
  isCoprime_constant_of_modEq five_dvd_M (g_modEq (modEq_seed u hu))
    seed_coprime_five.2.2.2

/- ## The requested four terms -/

/-- Every integer in the admissible progression gives pairwise-coprime terms. -/
theorem coprime_tuple (u : ℤ) (hu : M ∣ u - 3) :
    Pairwise fun i j : Fin 4 =>
      IsCoprime (![a u ^ 5, -(b u ^ 2), -(5 * (h u) ^ 7), -g u] i)
        (![a u ^ 5, -(b u ^ 2), -(5 * (h u) ^ 7), -g u] j) := by
  apply pairwise_coprime_four
  · exact (coprime_ab u hu).pow.neg_right
  · exact ((coprime_a_five u hu).pow_left.mul_right (coprime_ah u hu).pow).neg_right
  · exact (coprime_ag u hu).pow_left.neg_right
  · exact ((coprime_b_five u hu).pow_left.mul_right (coprime_bh u hu).pow).neg_neg
  · exact (coprime_bg u hu).pow_left.neg_neg
  · exact ((coprime_g_five u hu).symm.mul_left (coprime_hg u hu).pow_left).neg_neg

end StrongFour
