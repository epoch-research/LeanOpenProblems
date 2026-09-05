import FormalConjecturesUtil

/-!
# The $n$ conjecture

The $n$ conjecture of Browkin and Brzeziński (1994) is a generalization of the *abc* conjecture
to $n \geq 3$ integers. Given $n \geq 3$, one considers $n$-tuples of integers
$a_1, \dots, a_n$ such that
(i) $\gcd(a_1, \dots, a_n) = 1$,
(ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equals $0$.
The conjecture bounds $\max(|a_1|, \dots, |a_n|)$ by a power of the radical
$\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|)$; equivalently, it predicts the
limit superior of the qualities of such tuples.

The *strong* $n$ conjecture (attributed to Vojta (1998) by the Wikipedia article) replaces
setwise coprimality by pairwise coprimality and predicts the exponent $1 + \varepsilon$.
Hölzl, Kleine and Stephan (2025) refuted it for every $n \geq 5$; it remains open for $n = 3$
(the *abc* conjecture) and $n = 4$.

*References:*
- [Wikipedia, n conjecture](https://en.wikipedia.org/wiki/n_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J. Browkin, J. Brzeziński, *Some remarks on the abc-conjecture*, Math. Comp. 62 (1994),
  931–939. [doi:10.2307/2153551](https://doi.org/10.2307/2153551)
- P. Vojta, *A more general abc conjecture*, Int. Math. Res. Not. 1998 (1998), 1103–1116.
  [arXiv:math/9806171](https://arxiv.org/abs/math/9806171)
- R. Hölzl, S. Kleine, F. Stephan, *Improved lower bounds for strong n-conjectures*,
  J. Aust. Math. Soc. (2025). [arXiv:2409.13439](https://arxiv.org/abs/2409.13439)
-/

open Filter UniqueFactorizationMonoid

namespace NConjecture

/-- Condition (iii): no proper subsum of $a_1, \dots, a_n$ equals $0$, i.e.
$\sum_{i \in s} a_i \neq 0$ for every nonempty proper subset $s$ of the indices.
For $n \geq 2$ this forces every $a_i$ to be nonzero. -/
def HasNoVanishingProperSubsum {n : ℕ} (a : Fin n → ℤ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → s ≠ Finset.univ → ∑ i ∈ s, a i ≠ 0

/-- The set $A(n)$ of $n$-tuples of integers $(a_1, \dots, a_n)$ considered by the
$n$ conjecture: (i) $\gcd(a_1, \dots, a_n) = 1$, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equals $0$. -/
def admissibleSet (n : ℕ) : Set (Fin n → ℤ) :=
  {a | Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0 ∧ HasNoVanishingProperSubsum a}

/-- The set $R(n)$ of $n$-tuples of integers $(a_1, \dots, a_n)$ considered by the strong
$n$ conjecture: (i) $a_1, \dots, a_n$ are pairwise coprime, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equals $0$. -/
def strongAdmissibleSet (n : ℕ) : Set (Fin n → ℤ) :=
  {a | (Pairwise fun i j ↦ IsCoprime (a i) (a j)) ∧ ∑ i, a i = 0 ∧ HasNoVanishingProperSubsum a}

/-- The maximal absolute value $\max(|a_1|, \dots, |a_n|)$ of an $n$-tuple of integers. -/
def maxAbs {n : ℕ} (a : Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ (a i).natAbs

/-- The radical $\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|)$ of the product of
the absolute values of the entries of an $n$-tuple of integers, i.e. the product of the distinct
primes dividing $a_1 \cdot a_2 \cdot \ldots \cdot a_n$. -/
noncomputable def rad {n : ℕ} (a : Fin n → ℤ) : ℕ :=
  radical (∏ i, (a i).natAbs)

/-- The quality of an $n$-tuple of integers $(a_1, \dots, a_n)$:
$$q(a_1, \dots, a_n) = \frac{\log(\max(|a_1|, \dots, |a_n|))}
  {\log(\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|))}.$$
For $n \geq 3$ and every tuple in `admissibleSet n` or `strongAdmissibleSet n` the radical is
at least $2$, so the denominator is positive. -/
noncomputable def quality {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  Real.log (maxAbs a) / Real.log (rad a)

/-- The limit superior of the qualities $q(a_1, \dots, a_n)$ over a set $S$ of $n$-tuples of
integers, taken along the cofinite filter on $S$ (equivalently, for an infinite set $S$, along
any injective enumeration of $S$, or along $\max(|a_1|, \dots, |a_n|) \to \infty$ in $S$).
It is valued in `EReal` so that an unbounded set of qualities has limit superior $+\infty$. -/
noncomputable def limsupQuality {n : ℕ} (S : Set (Fin n → ℤ)) : EReal :=
  limsup (fun a : S ↦ (quality a.1 : EReal)) cofinite

/-- The **strong $n$ conjecture** (attributed to Vojta, 1998), first formulation. Let $n \geq 3$.
For every $\varepsilon > 0$ there is a constant $C_{n, \varepsilon}$ depending on $n$ and
$\varepsilon$ such that for all integers $a_1, \dots, a_n$ with
(i) $a_1, \dots, a_n$ pairwise coprime, (ii) $a_1 + \dots + a_n = 0$, and
(iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$, one has
$$\max(|a_1|, \dots, |a_n|)
  < C_{n, \varepsilon}
  \operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|)^{1 + \varepsilon}.$$

Hölzl, Kleine and Stephan (2025) showed that this statement is false for every $n \geq 5$
(see `NConjecture.n_conjecture.variants.strong_lower_bound_holzl_kleine_stephan`). It remains open
for $n = 3$ (where it is the *abc* conjecture) and for $n = 4$, so it is stated here only for
$n \in \{3, 4\}$. -/
theorem n_conjecture.variants.strong (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 4) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ a ∈ strongAdmissibleSet n,
      (maxAbs a : ℝ) < C * (rad a : ℝ) ^ (1 + ε) := by
  sorry

end NConjecture

/-
The disproof uses the degree-(20,20,7,5) identity from the Davenport–Zannier
pair of Beukers–Stewart (Tree O in Pakovich–Zvonkin, arXiv:1509.07973).
After an integral normalization it reads `a(u)^5 - b(u)^2 - 5*h(u)^7 - g(u) = 0`.
The seed `u = 3` and explicit Bézout certificates give pairwise coprimality
on a fixed progression.  On the subsequence `h(u) = 7*K^n`, the radical is
bounded by a fixed constant times `u^19`, while the height is at least `u^20`.
The fixed exponent `1 + 1/38` therefore cannot give the asserted uniform bound.
-/

/-
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

/-
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

/- # A progression with fixed prime support in its linear factor -/

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

/-
# Subsum lemmas for the strong-four construction

A tuple with one positive entry balancing three strictly negative entries has
zero total sum and no vanishing nonempty proper subsum.
-/

namespace StrongFour

/-- The balancing identity makes the total sum zero. -/
lemma sum_four {A B C D : ℤ} (hA : A = B + C + D) :
    (∑ i, (![A, -B, -C, -D] : Fin 4 → ℤ) i) = 0 := by
  simp [Fin.sum_univ_succ]
  omega

/-- Every nonempty proper subsum of a balanced tuple with three negative entries
is nonzero. -/
lemma no_vanishing_four {A B C D : ℤ}
    (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hA : A = B + C + D) :
    ∀ s : Finset (Fin 4), s.Nonempty → s ≠ Finset.univ →
      ∑ i ∈ s, (![A, -B, -C, -D] : Fin 4 → ℤ) i ≠ 0 := by
  intro s hs hproper
  fin_cases s <;> norm_num +decide at * <;> omega

end StrongFour

/-
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

/-
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

theorem NConjecture.n_conjecture.variants.strong.disproof : ¬ (type_of% @NConjecture.n_conjecture.variants.strong) := by
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
