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

/-- The **strong $n$ conjecture** (attributed to Vojta, 1998), second formulation. Let $n \geq 3$.
Over all integers $a_1, \dots, a_n$ with (i) $a_1, \dots, a_n$ pairwise coprime,
(ii) $a_1 + \dots + a_n = 0$, and (iii) no proper subsum of $a_1, \dots, a_n$ equal to $0$,
the limit superior of the qualities
$$q(a_1, \dots, a_n) = \frac{\log(\max(|a_1|, \dots, |a_n|))}
  {\log(\operatorname{rad}(|a_1| \cdot |a_2| \cdot \ldots \cdot |a_n|))}$$
equals $1$.

Hölzl, Kleine and Stephan (2025) showed that this statement is false for every $n \geq 5$
(see `NConjecture.n_conjecture.variants.strong_lower_bound_holzl_kleine_stephan`). It remains open
for $n = 3$ (where it is equivalent to the *abc* conjecture) and for $n = 4$, so it is stated
here only for $n \in \{3, 4\}$. -/
theorem n_conjecture.variants.strong_quality (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 4) :
    limsupQuality (strongAdmissibleSet n) = 1 := by
  sorry

end NConjecture

/-
## Counterexample for four integers

The proof below constructs a homogeneous equal-sums-of-fourth-powers curve with
pairwise coprime coordinate polynomials and a pairwise coprime integer seed. A
ramified degree-six substitution makes a sextic square divide one coordinate.
Along a suitable arithmetic progression, all evaluated coordinates remain
pairwise coprime. Their fourth powers have height of degree 1080, whereas the
radical is bounded by an integer polynomial of degree 1074. The resulting fixed
quality gap above one contradicts the asserted cofinite limsup for `n = 4`.

All polynomial identities and numerical Bézout certificates are checked in Lean.
The original conjectural theorem is not used by the counterexample.
-/

/-
# Coprime polynomial values on an arithmetic progression

Rationally coprime integer polynomials have a nonzero integer constant in the
ideal they generate. If their values at zero are coprime, every common divisor
of their values at a multiple of that constant must already divide both values
at zero. A finite product of such constants gives a common positive modulus for
any finite pairwise-coprime family.
-/

namespace CoprimeProgression

open Polynomial

/-- Clear denominators in a rational polynomial Bézout identity. -/
theorem exists_int_bezout_constant (p q : ℤ[X])
    (h : IsCoprime (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ))) :
    ∃ (c : ℤ) (a b : ℤ[X]), c ≠ 0 ∧ a * p + b * q = C c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨⟨c, hc⟩, hu⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) u
  obtain ⟨⟨d, hd⟩, hv⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) v
  rw [mem_nonZeroDivisors_iff_ne_zero] at hc hd
  rw [Algebra.smul_def, Polynomial.algebraMap_apply, Subtype.coe_mk] at hu hv
  refine ⟨c * d,
    C d * IsLocalization.integerNormalization (nonZeroDivisors ℤ) u,
    C c * IsLocalization.integerNormalization (nonZeroDivisors ℤ) v,
    mul_ne_zero hc hd, ?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  change (C (d : ℚ) * (IsLocalization.integerNormalization (nonZeroDivisors ℤ) u).map
      (algebraMap ℤ ℚ)) * p.map (Int.castRingHom ℚ) +
      (C (c : ℚ) * (IsLocalization.integerNormalization (nonZeroDivisors ℤ) v).map
      (algebraMap ℤ ℚ)) * q.map (Int.castRingHom ℚ) = C ((c * d : ℤ) : ℚ)
  rw [hu, hv, Int.cast_mul, C_mul]
  simp only [eq_intCast]
  calc
    _ = C (c : ℚ) * C (d : ℚ) *
        (u * p.map (Int.castRingHom ℚ) + v * q.map (Int.castRingHom ℚ)) := by ring
    _ = _ := by rw [huv, mul_one]

/-- An integer Bézout constant preserves coprimality at all multiples of it. -/
theorem isCoprime_eval_of_bezout_constant (p q a b : ℤ[X]) (c x : ℤ)
    (hbez : a * p + b * q = C c)
    (hseed : IsCoprime (p.eval 0) (q.eval 0)) (hcx : c ∣ x) :
    IsCoprime (p.eval x) (q.eval x) := by
  apply IsRelPrime.isCoprime
  intro d hdp hdq
  have hdc : d ∣ c := by
    have he := congrArg (Polynomial.eval x) hbez
    simp only [eval_add, eval_mul, eval_C] at he
    rw [← he]
    exact dvd_add (dvd_mul_of_dvd_right hdp _) (dvd_mul_of_dvd_right hdq _)
  have hdx : d ∣ x := hdc.trans hcx
  have hp : d ∣ p.eval x - p.eval 0 :=
    hdx.trans (by simpa only [sub_zero] using Polynomial.sub_dvd_eval_sub x 0 p)
  have hq : d ∣ q.eval x - q.eval 0 :=
    hdx.trans (by simpa only [sub_zero] using Polynomial.sub_dvd_eval_sub x 0 q)
  exact hseed.isUnit_of_dvd' ((dvd_sub_right hdp).mp hp)
    ((dvd_sub_right hdq).mp hq)

/-- A single rationally coprime pair with coprime values at zero has a positive
natural modulus on all of whose integer multiples its values are coprime. -/
theorem exists_pos_nat_coprime_eval_of_dvd (p q : ℤ[X])
    (hpoly : IsCoprime (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ)))
    (hseed : IsCoprime (p.eval 0) (q.eval 0)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : ℤ, (M : ℤ) ∣ x → IsCoprime (p.eval x) (q.eval x) := by
  obtain ⟨c, a, b, hc, hbez⟩ := exists_int_bezout_constant p q hpoly
  refine ⟨c.natAbs, Int.natAbs_pos.mpr hc, fun x hx => ?_⟩
  exact isCoprime_eval_of_bezout_constant p q a b c x hbez hseed
    (Int.dvd_natAbs_self.trans hx)

/-- A finite family of rationally pairwise-coprime integer polynomials with
pairwise-coprime values at zero stays pairwise coprime at every integer divisible
by a suitable positive natural modulus. -/
theorem exists_pos_nat_pairwise_coprime_eval_of_dvd {ι : Type*} [Finite ι]
    (p : ι → ℤ[X])
    (hpoly : Pairwise fun i j =>
      IsCoprime ((p i).map (Int.castRingHom ℚ)) ((p j).map (Int.castRingHom ℚ)))
    (hseed : Pairwise fun i j => IsCoprime ((p i).eval 0) ((p j).eval 0)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : ℤ, (M : ℤ) ∣ x →
      Pairwise fun i j => IsCoprime ((p i).eval x) ((p j).eval x) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let I := {ij : ι × ι // ij.1 ≠ ij.2}
  have hpair : ∀ ij : I, ∃ M : ℕ, 0 < M ∧ ∀ x : ℤ, (M : ℤ) ∣ x →
      IsCoprime ((p ij.val.1).eval x) ((p ij.val.2).eval x) := by
    intro ij
    exact exists_pos_nat_coprime_eval_of_dvd (p ij.val.1) (p ij.val.2)
      (hpoly ij.property) (hseed ij.property)
  choose m hmpos hm using hpair
  refine ⟨∏ ij, m ij, Finset.prod_pos (fun ij _ => hmpos ij), ?_⟩
  intro x hx i j hij
  apply hm ⟨(i, j), hij⟩ x
  apply dvd_trans _ hx
  exact Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem m (Finset.mem_univ _))

/-- A finite family of rationally pairwise-coprime integer polynomials with
pairwise-coprime values at zero is pairwise coprime along a common nonconstant
arithmetic progression through zero. In particular, this applies to `ι = Fin 4`. -/
theorem exists_pos_nat_pairwise_coprime_eval_mul {ι : Type*} [Finite ι]
    (p : ι → ℤ[X])
    (hpoly : Pairwise fun i j =>
      IsCoprime ((p i).map (Int.castRingHom ℚ)) ((p j).map (Int.castRingHom ℚ)))
    (hseed : Pairwise fun i j => IsCoprime ((p i).eval 0) ((p j).eval 0)) :
    ∃ M : ℕ, 0 < M ∧ ∀ k : ℤ,
      Pairwise fun i j =>
        IsCoprime ((p i).eval ((M : ℤ) * k)) ((p j).eval ((M : ℤ) * k)) := by
  obtain ⟨M, hMpos, hM⟩ := exists_pos_nat_pairwise_coprime_eval_of_dvd p hpoly hseed
  exact ⟨M, hMpos, fun k => hM ((M : ℤ) * k) (dvd_mul_right _ _)⟩

end CoprimeProgression

/-
# Strong admissibility of four pairwise coprime integers

These auxiliary lemmas use only the definitions in `Submission.Spec`.
-/

namespace NConjecture

/-- For four pairwise coprime integers of absolute value greater than one,
a zero total sum has no vanishing nonempty proper subsum. -/
theorem hasNoVanishingProperSubsum_four (a : Fin 4 → ℤ)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hsum : ∑ i, a i = 0) (habs : ∀ i, 1 < (a i).natAbs) :
    HasNoVanishingProperSubsum a := by
  classical
  have hne : ∀ i, a i ≠ 0 := by
    intro i hi
    have := habs i
    simp [hi] at this
  intro s hs hs' hz
  have hcpos : 0 < s.card := hs.card_pos
  have hclt : s.card < 4 := (Finset.card_lt_iff_ne_univ s).2 hs'
  have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with hc | hc | hc
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    exact hne i (by simpa using hz)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
    have hpair : a i + a j = 0 := by simpa [hij] using hz
    have heq : a j = -a i := by linarith
    have hcop' : IsCoprime (a i) (a j) := hcop hij
    rw [heq, IsCoprime.neg_right_iff, isCoprime_self,
      Int.isUnit_iff_natAbs_eq] at hcop'
    exact (ne_of_gt (habs i)) hcop'
  · have hccompl : sᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, hc]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hccompl
    have htotal := Finset.sum_add_sum_compl s a
    rw [hi, Finset.sum_singleton, hz, hsum, zero_add] at htotal
    exact hne i htotal

/-- A convenient criterion for membership in the strong admissible four-tuples. -/
theorem mem_strongAdmissibleSet_four (a : Fin 4 → ℤ)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hsum : ∑ i, a i = 0) (habs : ∀ i, 1 < (a i).natAbs) :
    a ∈ strongAdmissibleSet 4 :=
  ⟨hcop, hsum, hasNoVanishingProperSubsum_four a hcop hsum habs⟩

/-- Taking fourth powers and changing either sign preserves pairwise coprimality. -/
theorem pairwise_isCoprime_signed_fourthPowers (x : Fin 4 → ℤ)
    (hcop : Pairwise fun i j ↦ IsCoprime (x i) (x j)) :
    Pairwise fun i j ↦ IsCoprime
      (![x 0 ^ 4, x 1 ^ 4, -x 2 ^ 4, -x 3 ^ 4] i)
      (![x 0 ^ 4, x 1 ^ 4, -x 2 ^ 4, -x 3 ^ 4] j) := by
  intro i j hij
  have hpow : IsCoprime (x i ^ 4) (x j ^ 4) := (hcop hij).pow
  fin_cases i <;> fin_cases j <;>
    simpa [IsCoprime.neg_left_iff, IsCoprime.neg_right_iff] using hpow

/-- A pairwise coprime solution of the equal-sums-of-fourth-powers equation,
with all bases of absolute value greater than one, gives a strong admissible tuple. -/
theorem signed_fourthPowers_mem_strongAdmissibleSet_four (x : Fin 4 → ℤ)
    (hcop : Pairwise fun i j ↦ IsCoprime (x i) (x j))
    (hsum : x 0 ^ 4 + x 1 ^ 4 = x 2 ^ 4 + x 3 ^ 4)
    (habs : ∀ i, 1 < (x i).natAbs) :
    ![x 0 ^ 4, x 1 ^ 4, -x 2 ^ 4, -x 3 ^ 4] ∈ strongAdmissibleSet 4 := by
  refine mem_strongAdmissibleSet_four _
    (pairwise_isCoprime_signed_fourthPowers x hcop) ?_ ?_
  · simp [Fin.sum_univ_succ]
    linarith
  · intro i
    have hx : 1 < (x i).natAbs ^ 4 := one_lt_pow₀ (habs i) (by decide)
    fin_cases i <;> simpa [Int.natAbs_pow] using hx

end NConjecture

/-
# Eventual polynomial power bounds

A real polynomial of natural degree at most `d` is eventually bounded in absolute
value by a positive constant times `x ^ d`. A nonzero polynomial of natural
degree exactly `d` also has a matching positive lower bound.

The bounds are transported to arbitrary filters tending to positive infinity,
and to the real casts of `Int.natAbs` of integer polynomial values. In particular,
the arithmetic-progression lemmas bound evaluation at `a * k + b` by powers of
`k`; their upper bounds allow any slope and their lower bounds require only a
nonzero slope. No sign condition on the leading coefficient is needed.
-/

namespace PolynomialGrowth

open Filter Polynomial

/-- An eventual upper power bound, including for the zero polynomial. -/
theorem exists_pos_eventually_abs_eval_le (p : ℝ[X]) {d : ℕ}
    (hd : p.natDegree ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, |p.eval x| ≤ C * x ^ d := by
  obtain ⟨A, hA, hbound⟩ := p.isEquivalent_atTop_lead.isBigO.exists_pos
  refine ⟨A * |p.leadingCoeff| + 1, by positivity, ?_⟩
  filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℝ)] with x hb hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0] at hb
  calc
    |p.eval x| ≤ A * (|p.leadingCoeff| * x ^ p.natDegree) := hb
    _ ≤ (A * |p.leadingCoeff| + 1) * x ^ p.natDegree := by
      nlinarith only [pow_nonneg hx0 p.natDegree]
    _ ≤ (A * |p.leadingCoeff| + 1) * x ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hd) (by positivity)

/-- An eventual lower power bound. The nonzero hypothesis is essential when
`d = 0`, since `natDegree 0 = 0`. -/
theorem exists_pos_eventually_le_abs_eval (p : ℝ[X]) {d : ℕ}
    (hp : p ≠ 0) (hd : p.natDegree = d) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, c * x ^ d ≤ |p.eval x| := by
  obtain ⟨A, hA, hbound⟩ := p.isEquivalent_atTop_lead.isBigO_symm.exists_pos
  refine ⟨|p.leadingCoeff| / A,
    div_pos (abs_pos.mpr (leadingCoeff_ne_zero.mpr hp)) hA, ?_⟩
  filter_upwards [hbound.bound, eventually_ge_atTop (0 : ℝ)] with x hb hx
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx, hd] at hb
  rw [div_mul_eq_mul_div, div_le_iff₀ hA]
  simpa only [mul_comm] using hb

/-- Upper bounds along any real-valued parameter tending to positive infinity. -/
theorem exists_pos_eventually_abs_eval_le_along (p : ℝ[X]) {d : ℕ}
    (hd : p.natDegree ≤ d) {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : Tendsto x l atTop) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in l, |p.eval (x k)| ≤ C * x k ^ d := by
  obtain ⟨C, hC, h⟩ := exists_pos_eventually_abs_eval_le p hd
  exact ⟨C, hC, hx.eventually h⟩

/-- Lower bounds along any real-valued parameter tending to positive infinity. -/
theorem exists_pos_eventually_le_abs_eval_along (p : ℝ[X]) {d : ℕ}
    (hp : p ≠ 0) (hd : p.natDegree = d) {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : Tendsto x l atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in l, c * x k ^ d ≤ |p.eval (x k)| := by
  obtain ⟨c, hc, h⟩ := exists_pos_eventually_le_abs_eval p hp hd
  exact ⟨c, hc, hx.eventually h⟩

/-- Casting integer coefficients to the reals preserves natural degree. -/
theorem natDegree_map_intCast_real (p : ℤ[X]) :
    (p.map (Int.castRingHom ℝ)).natDegree = p.natDegree :=
  Polynomial.natDegree_map_eq_of_injective Int.cast_injective p

/-- Bridge between natural absolute values of integer evaluations and absolute
values of evaluations of the corresponding real polynomial. -/
theorem natAbs_eval_eq_abs_eval_map (p : ℤ[X]) (x : ℤ) :
    ((p.eval x).natAbs : ℝ) = |(p.map (Int.castRingHom ℝ)).eval (x : ℝ)| := by
  simp

/-- Upper growth bound for integer polynomial values along an arbitrary
integer-valued parameter whose real cast tends to positive infinity. -/
theorem exists_pos_eventually_natAbs_eval_le (p : ℤ[X]) {d : ℕ}
    (hd : p.natDegree ≤ d) {ι : Type*} {l : Filter ι} {x : ι → ℤ}
    (hx : Tendsto (fun k ↦ (x k : ℝ)) l atTop) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ k in l, ((p.eval (x k)).natAbs : ℝ) ≤ C * (x k : ℝ) ^ d := by
  obtain ⟨C, hC, h⟩ := exists_pos_eventually_abs_eval_le_along
    (p.map (Int.castRingHom ℝ)) (Polynomial.natDegree_map_le.trans hd) hx
  exact ⟨C, hC, by simpa only [natAbs_eval_eq_abs_eval_map] using h⟩

/-- Lower growth bound for nonzero integer polynomials along an arbitrary
integer-valued parameter whose real cast tends to positive infinity. -/
theorem exists_pos_eventually_le_natAbs_eval (p : ℤ[X]) {d : ℕ}
    (hp : p ≠ 0) (hd : p.natDegree = d) {ι : Type*} {l : Filter ι} {x : ι → ℤ}
    (hx : Tendsto (fun k ↦ (x k : ℝ)) l atTop) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in l, c * (x k : ℝ) ^ d ≤ ((p.eval (x k)).natAbs : ℝ) := by
  have hp' : p.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_eq_zero_iff Int.cast_injective).not.mpr hp
  obtain ⟨c, hc, h⟩ := exists_pos_eventually_le_abs_eval_along
    (p.map (Int.castRingHom ℝ)) hp' ((natDegree_map_intCast_real p).trans hd) hx
  exact ⟨c, hc, by simpa only [natAbs_eval_eq_abs_eval_map] using h⟩

/-- Upper growth bound at the natural numbers, with no progression. -/
theorem exists_pos_eventually_natAbs_eval_nat_le (p : ℤ[X]) {d : ℕ}
    (hd : p.natDegree ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ k : ℕ in atTop, ((p.eval (k : ℤ)).natAbs : ℝ) ≤ C * (k : ℝ) ^ d := by
  simpa only [Int.cast_natCast] using
    exists_pos_eventually_natAbs_eval_le p hd
      (x := fun k : ℕ ↦ (k : ℤ)) (by simpa using (tendsto_natCast_atTop_atTop
        : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop))

/-- Lower growth bound at the natural numbers, with no progression. -/
theorem exists_pos_eventually_le_natAbs_eval_nat (p : ℤ[X]) {d : ℕ}
    (hp : p ≠ 0) (hd : p.natDegree = d) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ d ≤ ((p.eval (k : ℤ)).natAbs : ℝ) := by
  simpa only [Int.cast_natCast] using
    exists_pos_eventually_le_natAbs_eval p hp hd
      (x := fun k : ℕ ↦ (k : ℤ)) (by simpa using (tendsto_natCast_atTop_atTop
        : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop))

/-- An upper bound by powers of the index on any integer arithmetic progression.
The slope may be positive, negative, or zero; the offset is arbitrary. -/
theorem exists_pos_eventually_natAbs_eval_affine_le (p : ℤ[X]) {d : ℕ}
    (hd : p.natDegree ≤ d) (a b : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ((p.eval (a * (k : ℤ) + b)).natAbs : ℝ) ≤ C * (k : ℝ) ^ d := by
  have hcomp : (p.comp (C a * X + C b)).natDegree ≤ d := by
    calc
      (p.comp (C a * X + C b)).natDegree ≤ p.natDegree * 1 :=
        Polynomial.natDegree_comp_le.trans
          (Nat.mul_le_mul_left _ Polynomial.natDegree_linear_le)
      _ ≤ d := by simpa using hd
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] using
    exists_pos_eventually_natAbs_eval_nat_le (p.comp (C a * X + C b)) hcomp

/-- A matching lower bound on a nonconstant arithmetic progression. A negative
slope is allowed because the conclusion uses absolute values. -/
theorem exists_pos_eventually_le_natAbs_eval_affine (p : ℤ[X]) {d : ℕ}
    (hp : p ≠ 0) (hd : p.natDegree = d) (a b : ℤ) (ha : a ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      c * (k : ℝ) ^ d ≤ ((p.eval (a * (k : ℤ) + b)).natAbs : ℝ) := by
  have hlin : (C a * X + C b : ℤ[X]).natDegree = 1 :=
    Polynomial.natDegree_linear ha
  have hcomp : (p.comp (C a * X + C b)).natDegree = d := by
    rw [Polynomial.natDegree_comp, hlin, mul_one, hd]
  have hne : p.comp (C a * X + C b) ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [Polynomial.leadingCoeff_comp (by rw [hlin]; decide),
      Polynomial.leadingCoeff_linear ha]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (pow_ne_zero _ ha)
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] using
    exists_pos_eventually_le_natAbs_eval_nat (p.comp (C a * X + C b)) hne hcomp

/-- Upper bound on the multiples of a natural modulus. -/
theorem exists_pos_eventually_natAbs_eval_mul_le (p : ℤ[X]) {d : ℕ}
    (hd : p.natDegree ≤ d) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ((p.eval ((M : ℤ) * (k : ℤ))).natAbs : ℝ) ≤ C * (k : ℝ) ^ d := by
  simpa only [add_zero] using exists_pos_eventually_natAbs_eval_affine_le p hd M 0

/-- Lower bound on the multiples of a positive natural modulus. -/
theorem exists_pos_eventually_le_natAbs_eval_mul (p : ℤ[X]) {d : ℕ}
    (hp : p ≠ 0) (hd : p.natDegree = d) (M : ℕ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      c * (k : ℝ) ^ d ≤ ((p.eval ((M : ℤ) * (k : ℤ))).natAbs : ℝ) := by
  simpa only [add_zero] using exists_pos_eventually_le_natAbs_eval_affine
    p hp hd M 0 (by exact_mod_cast hM.ne')

end PolynomialGrowth

/-
# Analytic criteria for a quality counterexample

These lemmas use only the definitions in `Submission.Spec`; they do not use either
of its conjectural theorems.  In particular, a family need not be injective:
a height tending to infinity makes it leave every finite set.
-/

open Filter

namespace NConjecture
namespace QualityContradiction

/-- A family whose natural-valued height tends to infinity leaves every finite set.
No injectivity or finiteness of the height sublevel sets is needed. -/
theorem tendsto_cofinite_of_height_tendsto
    {ι α : Type*} {l : Filter ι} (a : ι → α) (height : α → ℕ)
    (hheight : Tendsto (fun k ↦ height (a k)) l atTop) :
    Tendsto a l cofinite := by
  apply Filter.le_cofinite_iff_eventually_ne.mpr
  intro b
  change ∀ᶠ k in l, a k ≠ b
  filter_upwards [hheight.eventually_gt_atTop (height b)] with k hk
  intro h
  exact (ne_of_gt hk) (congrArg height h)

/-- An unbounded-height family of tuples tends to the cofinite filter on its set. -/
theorem tendsto_cofinite_of_maxAbs_tendsto
    {n : ℕ} {S : Set (Fin n → ℤ)} (a : ℕ → S)
    (hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop) :
    Tendsto a atTop cofinite :=
  tendsto_cofinite_of_height_tendsto a (fun b ↦ maxAbs b.1) hheight

/-- An eventual lower bound on the qualities along an unbounded-height family
is also a lower bound on the cofinite `EReal` limsup. -/
theorem le_limsupQuality_of_family
    {n : ℕ} {S : Set (Fin n → ℤ)} (a : ℕ → S) {c : ℝ}
    (hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop)
    (hquality : ∀ᶠ k in atTop, c ≤ quality (a k).1) :
    (c : EReal) ≤ limsupQuality S := by
  have hcof := tendsto_cofinite_of_maxAbs_tendsto a hheight
  apply Filter.le_limsup_of_frequently_le'
  apply hcof.frequently
  exact hquality.frequently.mono fun k hk ↦ EReal.coe_le_coe_iff.mpr hk

/-- A fixed quality gap above one along an unbounded-height family refutes a
limsup equal to one, with the stronger conclusion that the limsup exceeds one. -/
theorem one_lt_limsupQuality_of_family
    {n : ℕ} {S : Set (Fin n → ℤ)} (a : ℕ → S) {c : ℝ}
    (hc : 1 < c)
    (hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop)
    (hquality : ∀ᶠ k in atTop, c ≤ quality (a k).1) :
    (1 : EReal) < limsupQuality S := by
  have hc' : (1 : EReal) < (c : EReal) := by exact_mod_cast hc
  exact hc'.trans_le (le_limsupQuality_of_family a hheight hquality)

/-- The contradiction criterion with the quality gap packaged existentially. -/
theorem limsupQuality_ne_one_of_family
    {n : ℕ} {S : Set (Fin n → ℤ)} (a : ℕ → S)
    (hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop)
    (hquality : ∃ c : ℝ, 1 < c ∧ ∀ᶠ k in atTop, c ≤ quality (a k).1) :
    limsupQuality S ≠ 1 := by
  obtain ⟨c, hc, hquality⟩ := hquality
  exact (one_lt_limsupQuality_of_family a hc hheight hquality).ne'

/-- Specialized entry point for a proposed strong-four counterexample. -/
theorem strong4_limsupQuality_ne_one_of_family
    (a : ℕ → strongAdmissibleSet 4)
    (hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop)
    (hquality : ∃ c : ℝ, 1 < c ∧ ∀ᶠ k in atTop, c ≤ quality (a k).1) :
    limsupQuality (strongAdmissibleSet 4) ≠ 1 :=
  limsupQuality_ne_one_of_family a hheight hquality


/-- A nonzero integer tuple has height at most the product of the absolute values. -/
theorem maxAbs_le_prod_natAbs {n : ℕ} {b : Fin n → ℤ} (hb : ∀ i, b i ≠ 0) :
    maxAbs b ≤ ∏ i, (b i).natAbs := by
  apply Finset.sup_le
  intro i hi
  exact Finset.single_le_prod'
    (fun j _ ↦ Nat.succ_le_of_lt (Int.natAbs_pos.mpr (hb j))) hi

/-- Height greater than one gives a positive log-radical denominator for a nonzero tuple. -/
theorem one_lt_rad_of_one_lt_maxAbs {n : ℕ} {b : Fin n → ℤ}
    (hb : ∀ i, b i ≠ 0) (hh : 1 < maxAbs b) : 1 < rad b := by
  apply Nat.one_lt_radical_iff.mpr
  exact hh.trans_le (maxAbs_le_prod_natAbs hb)

/-- The no-vanishing-subsum condition makes every entry nonzero. -/
theorem entry_ne_zero_of_noVanishing {n : ℕ} (hn : 2 ≤ n) {b : Fin n → ℤ}
    (hb : HasNoVanishingProperSubsum b) (i : Fin n) : b i ≠ 0 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  simpa only [Finset.sum_singleton] using
    hb {i} (Finset.singleton_nonempty i) (Finset.singleton_ne_univ i)

/-- Along a growing family of strong-admissible tuples of length at least two,
the real logarithmic denominator is eventually positive. -/
theorem eventually_one_lt_rad_of_strongAdmissible
    {n : ℕ} (hn : 2 ≤ n) (a : ℕ → strongAdmissibleSet n)
    (hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop) :
    ∀ᶠ k in atTop, 1 < (rad (a k).1 : ℝ) := by
  filter_upwards [hheight.eventually_gt_atTop 1] with k hk
  have hrad := one_lt_rad_of_one_lt_maxAbs
    (entry_ne_zero_of_noVanishing hn (a k).property.2.2) hk
  exact_mod_cast hrad


/-- A positive power lower bound forces divergence to infinity. -/
theorem tendsto_atTop_of_power_lower_bound
    {ι : Type*} {l : Filter ι} {x H : ι → ℝ} {C : ℝ} {p : ℕ}
    (hx : Tendsto x l atTop) (hC : 0 < C) (hp : p ≠ 0)
    (hH : ∀ᶠ k in l, C * x k ^ p ≤ H k) :
    Tendsto H l atTop := by
  exact tendsto_atTop_mono' l hH ((tendsto_const_mul_pow_atTop hp hC).comp hx)

/-- Power bounds with a strict degree gap imply an eventual logarithmic quality
bound.  The assumption `1 < R` ensures that division by `log R` preserves order. -/
theorem eventually_lt_log_div_log_of_power_bounds
    {ι : Type*} {l : Filter ι} {x H R : ι → ℝ} {C D c : ℝ} {p q : ℕ}
    (hx : Tendsto x l atTop) (hC : 0 < C) (hD : 0 < D) (hc : 0 ≤ c)
    (hgap : c * (q : ℝ) < (p : ℝ))
    (hH : ∀ᶠ k in l, C * x k ^ p ≤ H k)
    (hR : ∀ᶠ k in l, 1 < R k)
    (hRbound : ∀ᶠ k in l, R k ≤ D * x k ^ q) :
    ∀ᶠ k in l, c < Real.log (H k) / Real.log (R k) := by
  have hlog : Tendsto (fun k ↦ Real.log (x k)) l atTop :=
    Real.tendsto_log_atTop.comp hx
  have hgrowth : Tendsto (fun k ↦ ((p : ℝ) - c * (q : ℝ)) * Real.log (x k))
      l atTop := hlog.const_mul_atTop (sub_pos.mpr hgap)
  filter_upwards [hx.eventually_gt_atTop 0, hH, hR, hRbound,
    hgrowth.eventually_gt_atTop (c * Real.log D - Real.log C)]
    with k hxk hHk hRk hRboundk hlarge
  have hlogH := Real.log_le_log (mul_pos hC (pow_pos hxk p)) hHk
  have hlogR := Real.log_le_log (lt_trans zero_lt_one hRk) hRboundk
  rw [Real.log_mul hC.ne' (pow_ne_zero _ hxk.ne'), Real.log_pow] at hlogH
  rw [Real.log_mul hD.ne' (pow_ne_zero _ hxk.ne'), Real.log_pow] at hlogR
  apply (lt_div_iff₀ (Real.log_pos hRk)).mpr
  have hmul := mul_le_mul_of_nonneg_left hlogR hc
  nlinarith only [hlogH, hmul, hlarge]

/-- Every strict degree gap gives a fixed eventual quality gap above one.
The explicit choice is `(p + 1) / (q + 1)`, which also works when `q = 0`. -/
theorem exists_eventually_one_lt_log_div_log_of_power_bounds
    {ι : Type*} {l : Filter ι} {x H R : ι → ℝ} {C D : ℝ} {p q : ℕ}
    (hx : Tendsto x l atTop) (hC : 0 < C) (hD : 0 < D) (hpq : q < p)
    (hH : ∀ᶠ k in l, C * x k ^ p ≤ H k)
    (hR : ∀ᶠ k in l, 1 < R k)
    (hRbound : ∀ᶠ k in l, R k ≤ D * x k ^ q) :
    ∃ c : ℝ, 1 < c ∧ ∀ᶠ k in l, c ≤ Real.log (H k) / Real.log (R k) := by
  let c : ℝ := ((p : ℝ) + 1) / ((q : ℝ) + 1)
  have hpq' : (q : ℝ) < (p : ℝ) := by exact_mod_cast hpq
  have hden : 0 < (q : ℝ) + 1 := by positivity
  have hc : 1 < c := by
    dsimp [c]
    apply (one_lt_div hden).mpr
    linarith
  have hgap : c * (q : ℝ) < (p : ℝ) := by
    dsimp [c]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith only [hpq']
  refine ⟨c, hc, ?_⟩
  exact (eventually_lt_log_div_log_of_power_bounds hx hC hD
    (le_of_lt (lt_trans zero_lt_one hc)) hgap hH hR hRbound).mono fun _ h ↦ h.le

/-- Concrete degree-1080 versus degree-1074 version, with rational quality
threshold `1001/1000`. -/
theorem eventually_quality_gap_1080_1074
    {H R : ℕ → ℝ} {C D : ℝ} (hC : 0 < C) (hD : 0 < D)
    (hH : ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 1080 ≤ H k)
    (hR : ∀ᶠ k in atTop, 1 < R k)
    (hRbound : ∀ᶠ k in atTop, R k ≤ D * (k : ℝ) ^ 1074) :
    ∀ᶠ k in atTop, (1001 / 1000 : ℝ) < Real.log (H k) / Real.log (R k) := by
  exact eventually_lt_log_div_log_of_power_bounds
    tendsto_natCast_atTop_atTop hC hD (by norm_num) (by norm_num) hH hR hRbound


/-- Combined analytic criterion for any set of integer tuples.  A strict degree
gap implies that its cofinite quality limsup is greater than one. -/
theorem one_lt_limsupQuality_of_power_bounds
    {n : ℕ} {S : Set (Fin n → ℤ)} (a : ℕ → S)
    {x : ℕ → ℝ} {C D : ℝ} {p q : ℕ}
    (hx : Tendsto x atTop atTop) (hC : 0 < C) (hD : 0 < D) (hpq : q < p)
    (hH : ∀ᶠ k in atTop, C * x k ^ p ≤ (maxAbs (a k).1 : ℝ))
    (hR : ∀ᶠ k in atTop, 1 < (rad (a k).1 : ℝ))
    (hRbound : ∀ᶠ k in atTop, (rad (a k).1 : ℝ) ≤ D * x k ^ q) :
    (1 : EReal) < limsupQuality S := by
  have hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_of_power_lower_bound hx hC (by omega) hH)
  obtain ⟨c, hc, hquality⟩ := exists_eventually_one_lt_log_div_log_of_power_bounds
    hx hC hD hpq hH hR hRbound
  exact one_lt_limsupQuality_of_family a hc hheight hquality

/-- For strong-admissible tuples the denominator hypothesis is automatic, so
only the power bounds and a strict degree gap are required. -/
theorem one_lt_strong_limsupQuality_of_power_bounds
    {n : ℕ} (hn : 2 ≤ n) (a : ℕ → strongAdmissibleSet n)
    {x : ℕ → ℝ} {C D : ℝ} {p q : ℕ}
    (hx : Tendsto x atTop atTop) (hC : 0 < C) (hD : 0 < D) (hpq : q < p)
    (hH : ∀ᶠ k in atTop, C * x k ^ p ≤ (maxAbs (a k).1 : ℝ))
    (hRbound : ∀ᶠ k in atTop, (rad (a k).1 : ℝ) ≤ D * x k ^ q) :
    (1 : EReal) < limsupQuality (strongAdmissibleSet n) := by
  have hheight : Tendsto (fun k ↦ maxAbs (a k).1) atTop atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_of_power_lower_bound hx hC (by omega) hH)
  exact one_lt_limsupQuality_of_power_bounds a hx hC hD hpq hH
    (eventually_one_lt_rad_of_strongAdmissible hn a hheight) hRbound

/-- Direct degree-1080 versus degree-1074 contradiction criterion for strong four.
The constants can be arbitrary positive reals, and all bounds need only hold eventually. -/
theorem strong4_limsupQuality_ne_one_of_bounds_1080_1074
    (a : ℕ → strongAdmissibleSet 4) {C D : ℝ} (hC : 0 < C) (hD : 0 < D)
    (hH : ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 1080 ≤ (maxAbs (a k).1 : ℝ))
    (hRbound : ∀ᶠ k : ℕ in atTop, (rad (a k).1 : ℝ) ≤ D * (k : ℝ) ^ 1074) :
    limsupQuality (strongAdmissibleSet 4) ≠ 1 := by
  exact (one_lt_strong_limsupQuality_of_power_bounds (by norm_num) a
    tendsto_natCast_atTop_atTop hC hD (by norm_num) hH hRbound).ne'

end QualityContradiction
end NConjecture

/-
# An explicit equal-sums-of-fourth-powers curve

The homogeneous coordinate forms and their integer polynomial specializations
are kept factored throughout. The quartic identity is proved over an arbitrary
commutative ring: a small preliminary identity cancels the even terms before
`ring` normalizes the remaining expression. All numerical seed certificates
are checked by `norm_num`.
-/

namespace StrongFourCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 8192

variable {R : Type*} [CommRing R]

/-- The first homogeneous sextic. -/
def P (x y : R) : R := x ^ 6 + x ^ 4 * y ^ 2 - 2 * x ^ 2 * y ^ 4 + y ^ 6

/-- The second homogeneous sextic. -/
def Q (x y : R) : R := x ^ 6 - 2 * x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + y ^ 6

/-- The auxiliary homogeneous sextic. -/
def L (x y : R) : R := x ^ 6 + 4 * x ^ 4 * y ^ 2 + 4 * x ^ 2 * y ^ 4 + y ^ 6

/-- An auxiliary homogeneous form of degree 38. -/
def E (x y : R) : R := 3 * L x y * (y ^ 8 * P x y ^ 4 - x ^ 8 * Q x y ^ 4)

/-- An auxiliary homogeneous form of degree 39. -/
def O (x y : R) : R := x ^ 3 * P x y * Q x y * (P x y ^ 2 - 9 * x ^ 2 * y ^ 10) ^ 2

/-- An auxiliary homogeneous form of degree 36. -/
def V (x y : R) : R := P x y * Q x y * (Q x y ^ 2 - 9 * x ^ 10 * y ^ 2) ^ 2

/-- The degree-45 homogeneous equal-sums-of-fourth-powers curve. -/
def FHom (x y : R) : Fin 4 → R :=
  ![(P x y + 3 * x * y ^ 5) * (y ^ 3 * V x y - x * E x y),
    (Q x y - 3 * x ^ 5 * y) * (y * E x y - O x y),
    -(P x y - 3 * x * y ^ 5) * (y ^ 3 * V x y + x * E x y),
    (Q x y + 3 * x ^ 5 * y) * (y * E x y + O x y)]

/-- A low-degree relation among the three auxiliary sextics. -/
theorem P_mul_L (x y : R) : P x y * L x y = Q x y ^ 2 + 9 * x ^ 10 * y ^ 2 := by
  unfold P Q L
  ring

/-- The symmetric low-degree relation among the auxiliary sextics. -/
theorem Q_mul_L (x y : R) : Q x y * L x y = P x y ^ 2 + 9 * x ^ 2 * y ^ 10 := by
  unfold P Q L
  ring

/-- Cancel the even terms before expanding the large coordinate forms. -/
private theorem quartic_step (a b c d u v w t : R)
    (h : (a * u - b * v) * (b * u - a * v) *
        ((a * u - b * v) ^ 2 + (b * u - a * v) ^ 2) =
      (c * w + d * t) * (c * t + d * w) *
        ((c * w + d * t) ^ 2 + (c * t + d * w) ^ 2)) :
    ((a + b) * (u - v)) ^ 4 + ((c - d) * (w - t)) ^ 4 =
      (-(a - b) * (u + v)) ^ 4 + ((c + d) * (w + t)) ^ 4 := by
  linear_combination 8 * h

/-- The defining equal-sums-of-fourth-powers identity, valid in every commutative ring. -/
theorem FHom_fourth_power_identity (x y : R) :
    FHom x y 0 ^ 4 + FHom x y 1 ^ 4 = FHom x y 2 ^ 4 + FHom x y 3 ^ 4 := by
  simp only [FHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  apply quartic_step
  unfold E O V L P Q
  ring

/-- Homogeneity of the first sextic. -/
theorem P_homogeneous (x y z : R) : P (x * z) (y * z) = z ^ 6 * P x y := by
  unfold P
  ring

/-- Homogeneity of the second sextic. -/
theorem Q_homogeneous (x y z : R) : Q (x * z) (y * z) = z ^ 6 * Q x y := by
  unfold Q
  ring

/-- Homogeneity of the auxiliary sextic. -/
theorem L_homogeneous (x y z : R) : L (x * z) (y * z) = z ^ 6 * L x y := by
  unfold L
  ring

/-- Homogeneity of the degree-38 auxiliary form. -/
theorem E_homogeneous (x y z : R) : E (x * z) (y * z) = z ^ 38 * E x y := by
  simp only [E, P_homogeneous, Q_homogeneous, L_homogeneous]
  ring

/-- Homogeneity of the degree-39 auxiliary form. -/
theorem O_homogeneous (x y z : R) : O (x * z) (y * z) = z ^ 39 * O x y := by
  simp only [O, P_homogeneous, Q_homogeneous]
  ring

/-- Homogeneity of the degree-36 auxiliary form. -/
theorem V_homogeneous (x y z : R) : V (x * z) (y * z) = z ^ 36 * V x y := by
  simp only [V, P_homogeneous, Q_homogeneous]
  ring

/-- Each coordinate of the curve is a homogeneous form of degree 45. -/
theorem FHom_homogeneous (x y z : R) (i : Fin 4) :
    FHom (x * z) (y * z) i = z ^ 45 * FHom x y i := by
  fin_cases i <;>
    simp [FHom, P_homogeneous, Q_homogeneous,
      E_homogeneous, O_homogeneous, V_homogeneous] <;> ring

/-- The curve commutes with all homomorphisms of commutative rings. -/
theorem map_FHom {S : Type*} [CommRing S] (f : R →+* S) (x y : R) (i : Fin 4) :
    f (FHom x y i) = FHom (f x) (f y) i := by
  fin_cases i <;> simp [FHom, E, O, V, L, P, Q, map_ofNat]

/-- The four coordinates at the point at infinity. -/
@[simp] theorem FHom_one_zero (i : Fin 4) :
    FHom (1 : R) 0 i = ![3, -1, 3, 1] i := by
  fin_cases i <;> norm_num [FHom, E, O, V, L, P, Q]

/-- The integer seed of the curve, obtained at `(2, 1)`. -/
def seed : Fin 4 → ℤ :=
  ![44162725988761, 47301468159703, 15168229732247, 54398746431911]

/-- Exact evaluation of the homogeneous curve at the seed. -/
@[simp] theorem FHom_two_one (i : Fin 4) : FHom (2 : ℤ) 1 i = seed i := by
  fin_cases i <;> norm_num [FHom, seed, E, O, V, L, P, Q]

/-- The four seed integers are pairwise coprime. -/
theorem pairwise_isCoprime_seed : Pairwise fun i j => IsCoprime (seed i) (seed j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [seed] at *

/-- The integer seed satisfies the same fourth-power identity. -/
theorem seed_fourth_power_identity :
    seed 0 ^ 4 + seed 1 ^ 4 = seed 2 ^ 4 + seed 3 ^ 4 := by
  simpa only [FHom_two_one] using FHom_fourth_power_identity (2 : ℤ) 1

open Polynomial

noncomputable section

/-- The four degree-45 univariate polynomials, in factored form. -/
def p (i : Fin 4) : ℤ[X] := FHom X 1 i

/-- The first degree-six substitution polynomial. -/
def A : ℤ[X] :=
  -156250 * X ^ 6 + 8750 * X ^ 5 - 3750 * X ^ 4 - 1400 * X ^ 3 +
    625 * X ^ 2 + 42 * X + 2

/-- The second degree-six substitution polynomial. -/
def B : ℤ[X] :=
  -21875 * X ^ 6 - 37500 * X ^ 5 + 875 * X ^ 4 - 1000 * X ^ 3 -
    210 * X ^ 2 + 124 * X + 1

/-- The substituted curve. Its large coefficients are deliberately not expanded. -/
def H (i : Fin 4) : ℤ[X] := FHom A B i

/-- The degree-six polynomial used for square divisibility of the first coordinate. -/
def g : ℤ[X] :=
  (5 * X) ^ 6 + (5 * X) ^ 4 - 2 * (5 * X) ^ 2 + 3 * (5 * X) + 1

/-- The univariate coordinates satisfy the fourth-power identity as polynomials. -/
theorem p_fourth_power_identity : p 0 ^ 4 + p 1 ^ 4 = p 2 ^ 4 + p 3 ^ 4 :=
  FHom_fourth_power_identity (X : ℤ[X]) 1

/-- The substituted coordinates satisfy the fourth-power identity as polynomials. -/
theorem H_fourth_power_identity : H 0 ^ 4 + H 1 ^ 4 = H 2 ^ 4 + H 3 ^ 4 :=
  FHom_fourth_power_identity A B

/-- Changing the coefficients of a univariate coordinate preserves its factored formula. -/
@[simp] theorem p_map (f : ℤ →+* R) (i : Fin 4) :
    (p i).map f = FHom (X : R[X]) 1 i := by
  simpa only [p, coe_mapRingHom, map_X, map_one] using
    map_FHom (mapRingHom f) (X : ℤ[X]) 1 i

/-- Changing coefficients commutes with the homogeneous substitution. -/
@[simp] theorem H_map (f : ℤ →+* R) (i : Fin 4) :
    (H i).map f = FHom (A.map f) (B.map f) i :=
  map_FHom (mapRingHom f) A B i

/-- Evaluation of a univariate coordinate in any commutative ring. -/
@[simp] theorem p_eval₂ (f : ℤ →+* R) (x : R) (i : Fin 4) :
    (p i).eval₂ f x = FHom x 1 i := by
  simpa only [p, coe_eval₂RingHom, eval₂_X, eval₂_one] using
    map_FHom (eval₂RingHom f x) (X : ℤ[X]) 1 i

/-- Integer evaluation of a univariate coordinate. -/
@[simp] theorem p_eval (x : ℤ) (i : Fin 4) : (p i).eval x = FHom x 1 i :=
  p_eval₂ (RingHom.id ℤ) x i

/-- Exact seed evaluation of each univariate polynomial. -/
@[simp] theorem p_eval_two (i : Fin 4) : (p i).eval 2 = seed i := by
  rw [p_eval, FHom_two_one]

/-- Seed evaluation after any change of coefficient ring. -/
theorem p_eval₂_two (f : ℤ →+* R) (i : Fin 4) :
    (p i).eval₂ f 2 = f (seed i) := by
  simpa only [map_ofNat, p_eval_two] using (eval₂_at_apply (p := p i) f 2)

/-- Evaluation of a substituted coordinate in any commutative ring. -/
@[simp] theorem H_eval₂ (f : ℤ →+* R) (x : R) (i : Fin 4) :
    (H i).eval₂ f x = FHom (A.eval₂ f x) (B.eval₂ f x) i :=
  map_FHom (eval₂RingHom f x) A B i

/-- Integer evaluation of a substituted coordinate. -/
@[simp] theorem H_eval (x : ℤ) (i : Fin 4) :
    (H i).eval x = FHom (A.eval x) (B.eval x) i :=
  H_eval₂ (RingHom.id ℤ) x i

@[simp] theorem A_eval_zero : A.eval 0 = 2 := by norm_num [A]

@[simp] theorem B_eval_zero : B.eval 0 = 1 := by norm_num [B]

@[simp] theorem g_eval_zero : g.eval 0 = 1 := by norm_num [g]

/-- Each substituted polynomial has the prescribed seed as its constant term. -/
@[simp] theorem H_eval_zero (i : Fin 4) : (H i).eval 0 = seed i := by
  rw [H_eval, A_eval_zero, B_eval_zero, FHom_two_one]

/-- The constant term certificate remains valid after changing coefficient rings. -/
theorem H_eval₂_zero (f : ℤ →+* R) (i : Fin 4) :
    (H i).eval₂ f 0 = f (seed i) := by
  simpa only [map_zero, H_eval_zero] using (eval₂_at_apply (p := H i) f 0)

/-- The fourth-power identity after evaluation in any commutative ring. -/
theorem H_eval₂_fourth_power_identity (f : ℤ →+* R) (x : R) :
    (H 0).eval₂ f x ^ 4 + (H 1).eval₂ f x ^ 4 =
      (H 2).eval₂ f x ^ 4 + (H 3).eval₂ f x ^ 4 := by
  simpa only [H_eval₂] using
    FHom_fourth_power_identity (A.eval₂ f x) (B.eval₂ f x)

/-- The fourth-power identity for the integer values of the substituted curve. -/
theorem H_eval_fourth_power_identity (x : ℤ) :
    (H 0).eval x ^ 4 + (H 1).eval x ^ 4 = (H 2).eval x ^ 4 + (H 3).eval x ^ 4 :=
  H_eval₂_fourth_power_identity (RingHom.id ℤ) x

/-- Pairwise coprimality of the univariate seed values. -/
theorem pairwise_isCoprime_p_eval_two :
    Pairwise fun i j => IsCoprime ((p i).eval 2) ((p j).eval 2) := by
  simpa only [p_eval_two] using pairwise_isCoprime_seed

/-- Pairwise coprimality of the substituted polynomials at zero. -/
theorem pairwise_isCoprime_H_eval_zero :
    Pairwise fun i j => IsCoprime ((H i).eval 0) ((H j).eval 0) := by
  simpa only [H_eval_zero] using pairwise_isCoprime_seed

end

end StrongFourCertificate

/-
# Exact Bézout certificates for the explicit curve

Each pair of coordinate polynomials has an integer linear combination equal to a
nonzero constant. The displayed coefficients are checked by ring normalization;
over the rationals these constants are units. The final certificate treats the
two degree-six substitution polynomials in the same way.
-/

namespace StrongFourCertificate

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 8192

private theorem coprime_of_constant (p q u v : ℚ[X]) (c : ℚ)
    (hc : c ≠ 0) (h : u * p + v * q = C c) : IsCoprime p q := by
  refine ⟨C c⁻¹ * u, C c⁻¹ * v, ?_⟩
  calc
    _ = C c⁻¹ * (u * p + v * q) := by ring
    _ = 1 := by rw [h, ← C_mul, inv_mul_cancel₀ hc, C_1]

private theorem p_coprime_01 : IsCoprime ((p 0).map (Int.castRingHom ℚ)) ((p 1).map (Int.castRingHom ℚ)) := by
  let u : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((68126602286569329 * X + 26597860198358300) * X - 533610080120043287) * X - 2043030529538290455) * X + 689397983069525675) * X + 3887973411408899279) * X + 1643666063796357630) * X + 10054384341759622450) * X - 7531699725439425343) * X - 39804203647226017353) * X + 12431125239963048190) * X + 29310637201125938398) * X - 5373052987032533841) * X + 61000813772791076220) * X + 25615834772837640144) * X - 104812489717737357243) * X - 10376700560187244230) * X - 21733100852480982606) * X - 124607828257717960002) * X + 188790900363535825244) * X + 241098492144662429032) * X - 129409922371699066659) * X - 75414303871655172001) * X - 141878299225724451454) * X - 323095697529848066616) * X + 316242843211431615021) * X + 544594184505971897340) * X - 227711065216013581113) * X - 360920245091240377599) * X - 2404554527965008558) * X + 12376520891917092843) * X + 89354147400139679788) * X + 125072373913248870590) * X - 50684324488204108593) * X - 63460676303569224818) * X + 4418014372853324143) * X - 6106928525959143447) * X + 9199370340623329334) * X + 11247597494231608240) * X - 5320704067618997424) * X - 557334757334220745) * X + 315499971735688166) * X - 169660723350547632) * X + 1019139030877645875) * X + 103789307806613148)
  let v : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((204379806859707987 * X + 79793580595074900) * X - 578931206061589926) * X - 143742298140811887) * X - 1302375034010195836) * X - 1692378094796161544) * X + 7117087732440965106) * X + 12099275321777581163) * X - 1895069479660796893) * X + 98650302229694538) * X - 29284915667883096113) * X - 74193967740948320146) * X + 60312223188359395512) * X + 121976932364815674349) * X - 18458759820585029006) * X + 34995343863118266435) * X - 139986556600413733725) * X - 368154816635978612652) * X + 302184450423025755597) * X + 542528870908207270164) * X - 220814301123562466298) * X - 309090198695824131843) * X - 33665748836029713343) * X - 76154696685912439988) * X + 216417352014390958212) * X + 244766205397347585050) * X - 144193648936073076478) * X - 139531775893665346734) * X - 51925983328587442035) * X - 4360221131785301580) * X + 122666579854344974544) * X + 41385503084168502921) * X - 41145462051961167606) * X - 24536045159279613930) * X - 40754860279814740997) * X + 13784553953359085219) * X + 40664065654373440758) * X + 1398214645511383078) * X - 4732317447682622981) * X - 2530363468001512011) * X - 4741912681595117143) * X + 760880690943246715) * X + 1247599664801746068) * X - 339713010292548625) * X + 304758200955753932)
  apply coprime_of_constant _ _ u v 1018063910673874944 (by norm_num)
  simp only [p_map, FHom, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [u, v, FHom, E, O, V, P, Q, L, Polynomial.C_ofNat]
  ring

private theorem p_coprime_02 : IsCoprime ((p 0).map (Int.castRingHom ℚ)) ((p 2).map (Int.castRingHom ℚ)) := by
  let u : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((1240899795385119 * X) * X - 4014026566077990) * X - 413633265128373) * X - 6462028869660816) * X + 7128874567156552) * X + 48519598546237050) * X - 59182340660032767) * X - 52500237705985029) * X + 12895257487123962) * X - 164640809694812253) * X + 373798503248613758) * X + 576016273176797784) * X - 706500486524033625) * X - 534747002389971498) * X - 25970029528840263) * X - 772227198877058709) * X + 1874456807875457880) * X + 2818887671560365345) * X - 3152419528664831544) * X - 3299138915871670650) * X + 2398491768504106287) * X + 1502896942222522257) * X - 414029902691465360) * X + 866945037607803084) * X - 872086472245302234) * X - 1524866960592226806) * X + 856238369359645542) * X + 446752950618427425) * X - 381943291775470368) * X + 535430699174311392) * X + 106062334539554259) * X - 459232346474196330) * X + 51168079408848642) * X - 35730471780624393) * X - 171171303489880963) * X + 210227541134166234) * X + 110924018656298034) * X - 102468220011555993) * X - 33921627714175581) * X + 10263348135890865) * X + 4730229660004909) * X + 3059545937412096) * X + 214787705019357) * X + 382443242176512)
  let v : ℚ[X] := (((((((((((((((((((((((((((((((((((((((((((((-1240899795385119) * X) * X + 4014026566077990) * X - 413633265128373) * X + 6462028869660816) * X + 7128874567156552) * X - 48519598546237050) * X - 59182340660032767) * X + 52500237705985029) * X + 12895257487123962) * X + 164640809694812253) * X + 373798503248613758) * X - 576016273176797784) * X - 706500486524033625) * X + 534747002389971498) * X - 25970029528840263) * X + 772227198877058709) * X + 1874456807875457880) * X - 2818887671560365345) * X - 3152419528664831544) * X + 3299138915871670650) * X + 2398491768504106287) * X - 1502896942222522257) * X - 414029902691465360) * X - 866945037607803084) * X - 872086472245302234) * X + 1524866960592226806) * X + 856238369359645542) * X - 446752950618427425) * X - 381943291775470368) * X - 535430699174311392) * X + 106062334539554259) * X + 459232346474196330) * X + 51168079408848642) * X + 35730471780624393) * X - 171171303489880963) * X - 210227541134166234) * X + 110924018656298034) * X + 102468220011555993) * X - 33921627714175581) * X - 10263348135890865) * X + 4730229660004909) * X - 3059545937412096) * X + 214787705019357) * X - 382443242176512)
  apply coprime_of_constant _ _ u v 764886484353024 (by norm_num)
  simp only [p_map, FHom, Matrix.cons_val_zero, Matrix.cons_val]
  norm_num [u, v, FHom, E, O, V, P, Q, L, Polynomial.C_ofNat]
  ring

private theorem p_coprime_03 : IsCoprime ((p 0).map (Int.castRingHom ℚ)) ((p 3).map (Int.castRingHom ℚ)) := by
  let u : ℚ[X] := (((((((((((((((((((((((((((((((((((((((((((((-3703651436825775) * X + 1783949912832839) * X + 29257292167029161) * X - 113555897678800038) * X - 30446608448368196) * X + 223768719072487294) * X - 95481303834336747) * X + 536053147147773820) * X + 350603020017317035) * X - 2249005015061006100) * X - 563177009682594235) * X + 1842186487067673104) * X + 394342516128451605) * X + 3174791475655648593) * X - 1875619483336331424) * X - 5915620850157593157) * X + 1001165386925874075) * X - 533819360548122504) * X + 7262052391027672968) * X + 9660182577810247310) * X - 14686897703968661020) * X - 7356262644739194573) * X + 5336566495149235456) * X - 6248715294813117857) * X + 18349103507422482558) * X + 15762692754964625259) * X - 32352776480228200275) * X - 12575799777826977759) * X + 22477275743250075228) * X + 1853188028426625141) * X - 1792047080669697471) * X + 2749977831639242077) * X - 7087615491301303658) * X - 1864787334292077117) * X + 4043112944728863665) * X + 359035934804638631) * X + 92379424206810900) * X + 182789557430568713) * X - 651082230455422918) * X - 217817141882431896) * X + 80811672199311991) * X + 33218536673401855) * X + 7710129706318314) * X + 50812855842830061) * X - 8232548772264405)
  let v : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((11110954310477325 * X - 5351849738498517) * X - 32217104948700858) * X + 17616329397845529) * X - 71472112407977807) * X - 24892808678308136) * X + 444180771524733270) * X + 320366739670788671) * X - 562237417823711140) * X + 161881847303809953) * X - 1724862544941914281) * X - 2565492214844537083) * X + 6255884895486053082) * X + 3211093611327230155) * X - 5122238244659741513) * X + 3191246350735321203) * X - 10148889309338450220) * X - 12328320305325918537) * X + 30384415067609637531) * X + 12946209590246251389) * X - 29936301897542807598) * X - 4895570731226532615) * X + 7275272018500810576) * X - 2992532818141956299) * X + 14513422727093049372) * X + 3257614525511940098) * X - 14594372043423669256) * X - 1387044972484468728) * X + 1054958398522320477) * X + 2092221476988010701) * X + 5960730785809413408) * X - 2339475707434432041) * X - 2613783429667355805) * X - 231428059549591440) * X - 1283290965518483581) * X + 2247606549231022436) * X + 1196022161405282973) * X - 1068111040200598748) * X - 227549170809101645) * X - 9449701824060510) * X - 185318784597171692) * X + 141354266044978246) * X + 32661777142713423) * X - 16937618614276687) * X + 19061761256952647)
  apply coprime_of_constant _ _ u v 48952734998593536 (by norm_num)
  simp only [p_map, FHom, Matrix.cons_val_zero, Matrix.cons_val]
  norm_num [u, v, FHom, E, O, V, P, Q, L, Polynomial.C_ofNat]
  ring

private theorem p_coprime_12 : IsCoprime ((p 1).map (Int.castRingHom ℚ)) ((p 2).map (Int.castRingHom ℚ)) := by
  let u : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((11110954310477325 * X + 5351849738498517) * X - 32217104948700858) * X - 17616329397845529) * X - 71472112407977807) * X + 24892808678308136) * X + 444180771524733270) * X - 320366739670788671) * X - 562237417823711140) * X - 161881847303809953) * X - 1724862544941914281) * X + 2565492214844537083) * X + 6255884895486053082) * X - 3211093611327230155) * X - 5122238244659741513) * X - 3191246350735321203) * X - 10148889309338450220) * X + 12328320305325918537) * X + 30384415067609637531) * X - 12946209590246251389) * X - 29936301897542807598) * X + 4895570731226532615) * X + 7275272018500810576) * X + 2992532818141956299) * X + 14513422727093049372) * X - 3257614525511940098) * X - 14594372043423669256) * X + 1387044972484468728) * X + 1054958398522320477) * X - 2092221476988010701) * X + 5960730785809413408) * X + 2339475707434432041) * X - 2613783429667355805) * X + 231428059549591440) * X - 1283290965518483581) * X - 2247606549231022436) * X + 1196022161405282973) * X + 1068111040200598748) * X - 227549170809101645) * X + 9449701824060510) * X - 185318784597171692) * X - 141354266044978246) * X + 32661777142713423) * X + 16937618614276687) * X + 19061761256952647)
  let v : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((3703651436825775 * X + 1783949912832839) * X - 29257292167029161) * X - 113555897678800038) * X + 30446608448368196) * X + 223768719072487294) * X + 95481303834336747) * X + 536053147147773820) * X - 350603020017317035) * X - 2249005015061006100) * X + 563177009682594235) * X + 1842186487067673104) * X - 394342516128451605) * X + 3174791475655648593) * X + 1875619483336331424) * X - 5915620850157593157) * X - 1001165386925874075) * X - 533819360548122504) * X - 7262052391027672968) * X + 9660182577810247310) * X + 14686897703968661020) * X - 7356262644739194573) * X - 5336566495149235456) * X - 6248715294813117857) * X - 18349103507422482558) * X + 15762692754964625259) * X + 32352776480228200275) * X - 12575799777826977759) * X - 22477275743250075228) * X + 1853188028426625141) * X + 1792047080669697471) * X + 2749977831639242077) * X + 7087615491301303658) * X - 1864787334292077117) * X - 4043112944728863665) * X + 359035934804638631) * X - 92379424206810900) * X + 182789557430568713) * X + 651082230455422918) * X - 217817141882431896) * X - 80811672199311991) * X + 33218536673401855) * X - 7710129706318314) * X + 50812855842830061) * X + 8232548772264405)
  apply coprime_of_constant _ _ u v 48952734998593536 (by norm_num)
  simp only [p_map, FHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  norm_num [u, v, FHom, E, O, V, P, Q, L, Polynomial.C_ofNat]
  ring

private theorem p_coprime_13 : IsCoprime ((p 1).map (Int.castRingHom ℚ)) ((p 3).map (Int.castRingHom ℚ)) := by
  let u : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((80098640013237 * X) * X - 612413050313211) * X + 2162663280357399) * X + 1542285055529035) * X - 3559172676312303) * X + 809052009511074) * X - 12153288763950858) * X - 13306471800843819) * X + 39317833503893889) * X + 27376792913643122) * X - 16627856390589798) * X - 8641419396669957) * X - 77964979876888416) * X + 506374507533024) * X + 109723979664436263) * X + 29828215069617846) * X + 55347006191174982) * X - 122793793295826186) * X - 256809452589296364) * X + 165799705573508592) * X + 171623825493193527) * X + 8958483390232567) * X + 190332744512769834) * X - 311357470157582712) * X - 445523860287861849) * X + 416286100433239704) * X + 351242467402009389) * X - 208977585538598223) * X - 37911209360916774) * X - 49371853798988241) * X - 102579830420058648) * X + 110496845223952782) * X + 70241065876578741) * X - 33309021781637974) * X - 7013897759092323) * X - 14644822246852551) * X - 12227446794324522) * X + 6616414516857096) * X + 4729070054718864) * X + 1685529810136627) * X + 767333664829302) * X + 382443242176512) * X - 680059202237799) * X + 127481080725504)
  let v : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((80098640013237 * X) * X - 612413050313211) * X - 2162663280357399) * X + 1542285055529035) * X + 3559172676312303) * X + 809052009511074) * X + 12153288763950858) * X - 13306471800843819) * X - 39317833503893889) * X + 27376792913643122) * X + 16627856390589798) * X - 8641419396669957) * X + 77964979876888416) * X + 506374507533024) * X - 109723979664436263) * X + 29828215069617846) * X - 55347006191174982) * X - 122793793295826186) * X + 256809452589296364) * X + 165799705573508592) * X - 171623825493193527) * X + 8958483390232567) * X - 190332744512769834) * X - 311357470157582712) * X + 445523860287861849) * X + 416286100433239704) * X - 351242467402009389) * X - 208977585538598223) * X + 37911209360916774) * X - 49371853798988241) * X + 102579830420058648) * X + 110496845223952782) * X - 70241065876578741) * X - 33309021781637974) * X + 7013897759092323) * X - 14644822246852551) * X + 12227446794324522) * X + 6616414516857096) * X - 4729070054718864) * X + 1685529810136627) * X - 767333664829302) * X + 382443242176512) * X + 680059202237799) * X + 127481080725504)
  apply coprime_of_constant _ _ u v 764886484353024 (by norm_num)
  simp only [p_map, FHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  norm_num [u, v, FHom, E, O, V, P, Q, L, Polynomial.C_ofNat]
  ring

private theorem p_coprime_23 : IsCoprime ((p 2).map (Int.castRingHom ℚ)) ((p 3).map (Int.castRingHom ℚ)) := by
  let u : ℚ[X] := (((((((((((((((((((((((((((((((((((((((((((((-68126602286569329) * X + 26597860198358300) * X + 533610080120043287) * X - 2043030529538290455) * X - 689397983069525675) * X + 3887973411408899279) * X - 1643666063796357630) * X + 10054384341759622450) * X + 7531699725439425343) * X - 39804203647226017353) * X - 12431125239963048190) * X + 29310637201125938398) * X + 5373052987032533841) * X + 61000813772791076220) * X - 25615834772837640144) * X - 104812489717737357243) * X + 10376700560187244230) * X - 21733100852480982606) * X + 124607828257717960002) * X + 188790900363535825244) * X - 241098492144662429032) * X - 129409922371699066659) * X + 75414303871655172001) * X - 141878299225724451454) * X + 323095697529848066616) * X + 316242843211431615021) * X - 544594184505971897340) * X - 227711065216013581113) * X + 360920245091240377599) * X - 2404554527965008558) * X - 12376520891917092843) * X + 89354147400139679788) * X - 125072373913248870590) * X - 50684324488204108593) * X + 63460676303569224818) * X + 4418014372853324143) * X + 6106928525959143447) * X + 9199370340623329334) * X - 11247597494231608240) * X - 5320704067618997424) * X + 557334757334220745) * X + 315499971735688166) * X + 169660723350547632) * X + 1019139030877645875) * X - 103789307806613148)
  let v : ℚ[X] := ((((((((((((((((((((((((((((((((((((((((((((204379806859707987 * X - 79793580595074900) * X - 578931206061589926) * X + 143742298140811887) * X - 1302375034010195836) * X + 1692378094796161544) * X + 7117087732440965106) * X - 12099275321777581163) * X - 1895069479660796893) * X - 98650302229694538) * X - 29284915667883096113) * X + 74193967740948320146) * X + 60312223188359395512) * X - 121976932364815674349) * X - 18458759820585029006) * X - 34995343863118266435) * X - 139986556600413733725) * X + 368154816635978612652) * X + 302184450423025755597) * X - 542528870908207270164) * X - 220814301123562466298) * X + 309090198695824131843) * X - 33665748836029713343) * X + 76154696685912439988) * X + 216417352014390958212) * X - 244766205397347585050) * X - 144193648936073076478) * X + 139531775893665346734) * X - 51925983328587442035) * X + 4360221131785301580) * X + 122666579854344974544) * X - 41385503084168502921) * X - 41145462051961167606) * X + 24536045159279613930) * X - 40754860279814740997) * X - 13784553953359085219) * X + 40664065654373440758) * X - 1398214645511383078) * X - 4732317447682622981) * X + 2530363468001512011) * X - 4741912681595117143) * X - 760880690943246715) * X + 1247599664801746068) * X + 339713010292548625) * X + 304758200955753932)
  apply coprime_of_constant _ _ u v 1018063910673874944 (by norm_num)
  simp only [p_map, FHom, Matrix.cons_val]
  norm_num [u, v, FHom, E, O, V, P, Q, L, Polynomial.C_ofNat]
  ring

private theorem A_B_coprime : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) := by
  let u : ℚ[X] := ((((((-1066835299051321800000) * X - 1645399750239682115625) * X + 316555120533545430750) * X - 116045005859911753875) * X + 14092325674924930520) * X + 2172342717551378362)
  let v : ℚ[X] := (((((7620252136080870000000 * X - 1737168136904290751250) * X + 546430753209619616250) * X - 48718607948912800050) * X - 14885664278107865200) * X - 843043396845966831)
  apply coprime_of_constant _ _ u v 3501642038256789893 (by norm_num)
  norm_num [u, v, A, B, Polynomial.C_ofNat]
  ring

theorem pairwise_isCoprime_p_map :
    Pairwise fun i j : Fin 4 =>
      IsCoprime ((p i).map (Int.castRingHom ℚ)) ((p j).map (Int.castRingHom ℚ)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact p_coprime_01 | exact p_coprime_02 | exact p_coprime_03 | exact p_coprime_12 | exact p_coprime_13 | exact p_coprime_23 | exact p_coprime_01.symm | exact p_coprime_02.symm | exact p_coprime_03.symm | exact p_coprime_12.symm | exact p_coprime_13.symm | exact p_coprime_23.symm

theorem isCoprime_A_B_map : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) :=
  A_B_coprime

end StrongFourCertificate

/-
# Coprimality transfer along the explicit homogeneous curve

This file only transfers coprimality: the finite certificates for the four
univariate coordinates and for the two substitution polynomials are hypotheses.
-/

namespace StrongFourCertificate

open Polynomial

/-- Dehomogenize a coordinate on the chart where the second argument is nonzero. -/
theorem FHom_dehomogenize {K : Type*} [Field K] (a b : K) (hb : b ≠ 0)
    (i : Fin 4) : FHom a b i = b ^ 45 * FHom (a / b) 1 i := by
  simpa only [div_mul_cancel₀ a hb, one_mul] using
    FHom_homogeneous (a / b) (1 : K) b i

/-- Every coordinate is nonzero at a nonzero point with second argument zero. -/
theorem FHom_zero_right_ne_zero {K : Type*} [Field K] [CharZero K]
    (a : K) (ha : a ≠ 0) (i : Fin 4) : FHom a 0 i ≠ 0 := by
  have hhom : FHom a 0 i = a ^ 45 * FHom (1 : K) 0 i := by
    simpa only [one_mul, zero_mul] using FHom_homogeneous (1 : K) 0 a i
  rw [hhom, FHom_one_zero]
  refine mul_ne_zero (pow_ne_zero _ ha) ?_
  fin_cases i <;> norm_num

/-- Coprimality of the univariate curve coordinates and of the substitution
polynomials implies pairwise coprimality of the substituted coordinates over ℚ. -/
theorem pairwise_isCoprime_H_map_of_coprime
    (hpoly : Pairwise fun i j : Fin 4 =>
      IsCoprime ((p i).map (Int.castRingHom ℚ)) ((p j).map (Int.castRingHom ℚ)))
    (hAB : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))) :
    Pairwise fun i j : Fin 4 =>
      IsCoprime ((H i).map (Int.castRingHom ℚ)) ((H j).map (Int.castRingHom ℚ)) := by
  intro i j hij
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ (AlgebraicClosure ℚ) _ _).2
  intro z
  let a : AlgebraicClosure ℚ := aeval z (A.map (Int.castRingHom ℚ))
  let b : AlgebraicClosure ℚ := aeval z (B.map (Int.castRingHom ℚ))
  have hab : a ≠ 0 ∨ b ≠ 0 := aeval_ne_zero_of_isCoprime hAB z
  have heval (k : Fin 4) :
      aeval z ((H k).map (Int.castRingHom ℚ)) = FHom a b k := by
    simp only [a, b, aeval_def, eval₂_map, H_eval₂]
  rw [heval, heval]
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hab.resolve_right (not_not_intro hb)
    left
    rw [hb]
    exact FHom_zero_right_ne_zero a ha i
  · have hp : FHom (a / b) 1 i ≠ 0 ∨ FHom (a / b) 1 j ≠ 0 := by
      simpa only [aeval_def, eval₂_map, p_eval₂] using
        aeval_ne_zero_of_isCoprime (hpoly hij) (a / b)
    rw [FHom_dehomogenize a b hb i, FHom_dehomogenize a b hb j]
    exact hp.imp (mul_ne_zero (pow_ne_zero _ hb)) (mul_ne_zero (pow_ne_zero _ hb))

end StrongFourCertificate

/-
# Degree and square-divisibility certificates for the explicit curve

The large coordinate polynomials remain factored. A degree bound together with
its top coefficient is propagated through the homogeneous formulas. Square
divisibility follows from a sextic Taylor identity; degree multiplicativity
then gives the degree of the quotient without expanding it.
-/

namespace StrongFourCertificate

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-- The first substitution has degree six. -/
theorem A_natDegree : A.natDegree = 6 := by
  unfold A
  compute_degree!

/-- The second substitution has degree six. -/
theorem B_natDegree : B.natDegree = 6 := by
  unfold B
  compute_degree!

/-- The square-divisibility polynomial has degree six. -/
theorem g_natDegree : g.natDegree = 6 := by
  unfold g
  compute_degree!

/-- The top coefficient of the first substitution. -/
theorem A_coeff_six : A.coeff 6 = -156250 := by
  unfold A
  compute_degree!

/-- The top coefficient of the second substitution. -/
theorem B_coeff_six : B.coeff 6 = -21875 := by
  unfold B
  compute_degree!

section TopCoefficients

variable {R : Type*} [CommRing R]

/-- A degree bound, with the coefficient at that bound (possibly zero). -/
private structure TopCoeff (p : R[X]) (n : ℕ) (c : R) : Prop where
  degree_le : p.natDegree ≤ n
  coeff_eq : p.coeff n = c

variable {p q : R[X]} {m n : ℕ} {a b : R}

private theorem TopCoeff.add (hp : TopCoeff p n a) (hq : TopCoeff q n b) :
    TopCoeff (p + q) n (a + b) :=
  ⟨by simpa only [max_self] using natDegree_add_le_of_le hp.degree_le hq.degree_le,
    by rw [coeff_add, hp.coeff_eq, hq.coeff_eq]⟩

private theorem TopCoeff.sub (hp : TopCoeff p n a) (hq : TopCoeff q n b) :
    TopCoeff (p - q) n (a - b) :=
  ⟨by simpa only [max_self] using natDegree_sub_le_of_le hp.degree_le hq.degree_le,
    by rw [coeff_sub, hp.coeff_eq, hq.coeff_eq]⟩

private theorem TopCoeff.neg (hp : TopCoeff p n a) : TopCoeff (-p) n (-a) :=
  ⟨by simpa only [natDegree_neg] using hp.degree_le,
    by rw [coeff_neg, hp.coeff_eq]⟩

private theorem TopCoeff.mul (hp : TopCoeff p m a) (hq : TopCoeff q n b) :
    TopCoeff (p * q) (m + n) (a * b) :=
  ⟨natDegree_mul_le_of_le hp.degree_le hq.degree_le,
    by rw [coeff_mul_add_eq_of_natDegree_le hp.degree_le hq.degree_le,
      hp.coeff_eq, hq.coeff_eq]⟩

private theorem TopCoeff.pow (hp : TopCoeff p n a) (k : ℕ) :
    TopCoeff (p ^ k) (k * n) (a ^ k) :=
  ⟨natDegree_pow_le_of_le k hp.degree_le,
    by rw [coeff_pow_of_natDegree_le hp.degree_le, hp.coeff_eq]⟩

private theorem TopCoeff.nat (k : ℕ) : TopCoeff (k : R[X]) 0 (k : R) :=
  ⟨by simp, by simp⟩

private theorem P_topCoeff (hp : TopCoeff p 6 a) (hq : TopCoeff q 6 b) :
    TopCoeff (P p q) 36 (P a b) := by
  unfold P
  exact (((hp.pow 6).add ((hp.pow 4).mul (hq.pow 2))).sub
    (((TopCoeff.nat 2).mul (hp.pow 2)).mul (hq.pow 4))).add (hq.pow 6)

private theorem Q_topCoeff (hp : TopCoeff p 6 a) (hq : TopCoeff q 6 b) :
    TopCoeff (Q p q) 36 (Q a b) := by
  unfold Q
  exact (((hp.pow 6).sub (((TopCoeff.nat 2).mul (hp.pow 4)).mul (hq.pow 2))).add
    ((hp.pow 2).mul (hq.pow 4))).add (hq.pow 6)

private theorem L_topCoeff (hp : TopCoeff p 6 a) (hq : TopCoeff q 6 b) :
    TopCoeff (L p q) 36 (L a b) := by
  unfold L
  exact (((hp.pow 6).add (((TopCoeff.nat 4).mul (hp.pow 4)).mul (hq.pow 2))).add
    (((TopCoeff.nat 4).mul (hp.pow 2)).mul (hq.pow 4))).add (hq.pow 6)

private theorem E_topCoeff (hp : TopCoeff p 6 a) (hq : TopCoeff q 6 b) :
    TopCoeff (E p q) 228 (E a b) := by
  unfold E
  exact ((TopCoeff.nat 3).mul (L_topCoeff hp hq)).mul
    (((hq.pow 8).mul ((P_topCoeff hp hq).pow 4)).sub
      ((hp.pow 8).mul ((Q_topCoeff hp hq).pow 4)))

private theorem O_topCoeff (hp : TopCoeff p 6 a) (hq : TopCoeff q 6 b) :
    TopCoeff (O p q) 234 (O a b) := by
  unfold O
  exact (((hp.pow 3).mul (P_topCoeff hp hq)).mul (Q_topCoeff hp hq)).mul
    ((((P_topCoeff hp hq).pow 2).sub
      (((TopCoeff.nat 9).mul (hp.pow 2)).mul (hq.pow 10))).pow 2)

private theorem V_topCoeff (hp : TopCoeff p 6 a) (hq : TopCoeff q 6 b) :
    TopCoeff (V p q) 216 (V a b) := by
  unfold V
  exact ((P_topCoeff hp hq).mul (Q_topCoeff hp hq)).mul
    ((((Q_topCoeff hp hq).pow 2).sub
      (((TopCoeff.nat 9).mul (hp.pow 10)).mul (hq.pow 2))).pow 2)

private theorem FHom_topCoeff (hp : TopCoeff p 6 a) (hq : TopCoeff q 6 b)
    (i : Fin 4) : TopCoeff (FHom p q i) 270 (FHom a b i) := by
  have hP := P_topCoeff hp hq
  have hQ := Q_topCoeff hp hq
  have hE := E_topCoeff hp hq
  have hO := O_topCoeff hp hq
  have hV := V_topCoeff hp hq
  have h3pq := ((TopCoeff.nat 3).mul hp).mul (hq.pow 5)
  have h3qp := ((TopCoeff.nat 3).mul (hp.pow 5)).mul hq
  fin_cases i
  · exact (hP.add h3pq).mul (((hq.pow 3).mul hV).sub (hp.mul hE))
  · exact (hQ.sub h3qp).mul ((hq.mul hE).sub hO)
  · exact (hP.sub h3pq).neg.mul (((hq.pow 3).mul hV).add (hp.mul hE))
  · exact (hQ.add h3qp).mul ((hq.mul hE).add hO)

end TopCoefficients

private theorem H_topCoeff (i : Fin 4) :
    TopCoeff (H i) 270 (FHom (-156250 : ℤ) (-21875) i) :=
  FHom_topCoeff ⟨A_natDegree.le, A_coeff_six⟩ ⟨B_natDegree.le, B_coeff_six⟩ i

/-- Homogeneity computes the top coefficient without expanding a coordinate. -/
theorem H_coeff_270 (i : Fin 4) :
    (H i).coeff 270 = FHom (-156250 : ℤ) (-21875) i :=
  (H_topCoeff i).coeff_eq

private theorem FHom_top_ne_zero (i : Fin 4) :
    FHom (-156250 : ℤ) (-21875) i ≠ 0 := by
  fin_cases i <;> norm_num [FHom, E, O, V, L, P, Q]

/-- Every substituted coordinate has exact degree 270. -/
theorem H_natDegree (i : Fin 4) : (H i).natDegree = 270 :=
  natDegree_eq_of_le_of_coeff_ne_zero (H_topCoeff i).degree_le
    (by rw [H_coeff_270]; exact FHom_top_ne_zero i)

/-- In particular no coordinate polynomial vanishes identically. -/
theorem H_ne_zero (i : Fin 4) : H i ≠ 0 :=
  ne_zero_of_natDegree_gt (show 0 < (H i).natDegree by rw [H_natDegree]; norm_num)

/-- The square-divisibility polynomial is nonzero. -/
theorem g_ne_zero : g ≠ 0 :=
  ne_zero_of_natDegree_gt (show 0 < g.natDegree by rw [g_natDegree]; norm_num)

section Taylor

variable {R : Type*} [CommRing R]

/-- The sextic Taylor remainder after dividing by the square of the increment. -/
private def sexticRemainder (x b z : R) : R :=
  (15 * x ^ 4 + 6 * x ^ 2 - 2) * b ^ 4 +
  (20 * x ^ 3 + 4 * x) * b ^ 3 * z +
  (15 * x ^ 2 + 1) * b ^ 2 * z ^ 2 + 6 * x * b * z ^ 3 + z ^ 4

private theorem sextic_taylor (x b z : R) :
    P (x * b + z) b + 3 * (x * b + z) * b ^ 5 =
      b ^ 6 * (x ^ 6 + x ^ 4 - 2 * x ^ 2 + 3 * x + 1) +
      z * b ^ 5 * (6 * x ^ 5 + 4 * x ^ 3 - 4 * x + 3) +
      z ^ 2 * sexticRemainder x b z := by
  unfold P sexticRemainder
  ring

end Taylor

/-- The substitution is a first-order correction of the point `5X`. -/
theorem A_taylor : A = (5 * X) * B + (7 * X + 2) * g := by
  unfold A B g
  ring

/-- The correction cancels the linear Taylor term modulo `g`. -/
theorem B_taylor :
    B + (7 * X + 2) * (6 * (5 * X) ^ 5 + 4 * (5 * X) ^ 3 - 4 * (5 * X) + 3) =
      7 * g := by
  unfold B g
  ring

/-- The square already divides the degree-36 first factor of coordinate zero. -/
theorem g_sq_dvd_first_factor : g ^ 2 ∣ P A B + 3 * A * B ^ 5 := by
  refine ⟨7 * B ^ 5 + (7 * X + 2) ^ 2 *
    sexticRemainder (5 * X) B ((7 * X + 2) * g), ?_⟩
  rw [A_taylor, sextic_taylor]
  change B ^ 6 * g + ((7 * X + 2) * g) * B ^ 5 *
    (6 * (5 * X) ^ 5 + 4 * (5 * X) ^ 3 - 4 * (5 * X) + 3) +
    ((7 * X + 2) * g) ^ 2 * sexticRemainder (5 * X) B ((7 * X + 2) * g) = _
  calc
    _ = g * B ^ 5 * (B + (7 * X + 2) *
        (6 * (5 * X) ^ 5 + 4 * (5 * X) ^ 3 - 4 * (5 * X) + 3)) +
        g ^ 2 * (7 * X + 2) ^ 2 * sexticRemainder (5 * X) B ((7 * X + 2) * g) := by ring
    _ = _ := by rw [B_taylor]; ring

/-- Square divisibility of the first curve coordinate, over the integers. -/
theorem g_sq_dvd_H_zero : g ^ 2 ∣ H 0 := by
  change g ^ 2 ∣ (P A B + 3 * A * B ^ 5) * (B ^ 3 * V A B - A * E A B)
  exact dvd_mul_of_dvd_left g_sq_dvd_first_factor _

/-- The integer quotient actually has exact degree 258. -/
theorem exists_H_zero_quotient_exact :
    ∃ K : ℤ[X], H 0 = g ^ 2 * K ∧ K.natDegree = 258 := by
  obtain ⟨K, hK⟩ := g_sq_dvd_H_zero
  have hK0 : K ≠ 0 := by
    intro h
    exact H_ne_zero 0 (by simpa only [h, mul_zero] using hK)
  have hdeg := H_natDegree 0
  rw [hK, natDegree_mul (pow_ne_zero 2 g_ne_zero) hK0, natDegree_pow, g_natDegree] at hdeg
  exact ⟨K, hK, by omega⟩

/-- A square factor of degree twelve leaves an integer quotient of degree at most 258. -/
theorem exists_H_zero_quotient :
    ∃ K : ℤ[X], H 0 = g ^ 2 * K ∧ K.natDegree ≤ 258 := by
  obtain ⟨K, hK, hdeg⟩ := exists_H_zero_quotient_exact
  exact ⟨K, hK, hdeg.le⟩

end StrongFourCertificate

/-
# A conditional counterexample from the explicit fourth-power curve

The only remaining hypothesis is pairwise coprimality of the four coordinate
polynomials over the rationals. Coprimality of their seed values then supplies
an arithmetic progression of pairwise coprime integer values. The degree-six
square factor saves six degrees in the radical, giving height growth of degree
1080 and a radical upper bound of degree 1074.

Only definitions, not the conjectural theorems, are used from `Submission.Spec`.
-/

namespace StrongFourCertificate

open Filter Polynomial UniqueFactorizationMonoid NConjecture

/-- The signed fourth powers associated to an equal-sums-of-fourth-powers solution. -/
def signedFourthPowers (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![x 0 ^ 4, x 1 ^ 4, -x 2 ^ 4, -x 3 ^ 4]

/-- Signs and fourth powers do not change the radical of the product of the bases. -/
theorem rad_signedFourthPowers (x : Fin 4 → ℤ) :
    rad (signedFourthPowers x) = radical ((x 0 * x 1 * x 2 * x 3).natAbs) := by
  have hprod : (∏ i, (signedFourthPowers x i).natAbs) =
      ((x 0 * x 1 * x 2 * x 3).natAbs) ^ 4 := by
    simp [signedFourthPowers, Fin.prod_univ_succ, Int.natAbs_pow,
      Int.natAbs_mul, mul_pow, mul_assoc]
  unfold rad
  rw [hprod, radical_pow _ (by decide)]

/-- A square factor in the first base can be counted only once in the radical.
No coprimality assumptions are needed for this estimate. -/
theorem rad_signedFourthPowers_le_of_sq_factor (x : Fin 4 → ℤ) (u v : ℤ)
    (hne : ∀ i, x i ≠ 0) (hfactor : x 0 = u ^ 2 * v) :
    rad (signedFourthPowers x) ≤ (u * v * x 1 * x 2 * x 3).natAbs := by
  have hu : u ≠ 0 := by
    intro h
    exact hne 0 (by simpa only [h, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] using hfactor)
  have hv : v ≠ 0 := by
    intro h
    exact hne 0 (by simpa only [h, mul_zero] using hfactor)
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hu hv) (hne 1)) (hne 2))
      (hne 3)))
  rw [rad_signedFourthPowers, hfactor]
  simp only [Int.natAbs_mul, Int.natAbs_pow, mul_assoc]
  refine radical_mul_dvd.trans (mul_dvd_mul ?_ radical_dvd_self)
  rw [radical_pow _ (by decide)]
  exact radical_dvd_self

/-- Every base on a positive arithmetic progression eventually has absolute value
larger than one, simultaneously for the four coordinates. -/
theorem eventually_one_lt_natAbs_H_eval_mul (M : ℕ) (hM : 0 < M) :
    ∀ᶠ k : ℕ in atTop, ∀ i : Fin 4,
      1 < ((H i).eval ((M : ℤ) * (k : ℤ))).natAbs := by
  apply eventually_all.mpr
  intro i
  obtain ⟨c, hc, hbound⟩ :=
    PolynomialGrowth.exists_pos_eventually_le_natAbs_eval_mul
      (H i) (H_ne_zero i) (H_natDegree i) M hM
  have ht : Tendsto
      (fun k : ℕ ↦ (((H i).eval ((M : ℤ) * (k : ℤ))).natAbs : ℝ)) atTop atTop :=
    QualityContradiction.tendsto_atTop_of_power_lower_bound
      tendsto_natCast_atTop_atTop hc (by decide) hbound
  filter_upwards [ht.eventually_gt_atTop 1] with k hk
  exact_mod_cast hk

/-- The seed gives an admissible fallback for all initial exceptional indices. -/
theorem signedFourthPowers_seed_mem :
    signedFourthPowers seed ∈ strongAdmissibleSet 4 := by
  apply signed_fourthPowers_mem_strongAdmissibleSet_four seed
    pairwise_isCoprime_seed seed_fourth_power_identity
  intro i
  fin_cases i <;> norm_num [seed]

/-- Rational pairwise coprimality of the explicit coordinate polynomials implies
that the strong-four quality limsup is not one. All remaining ingredients,
including radical and growth estimates, are unconditional. -/
theorem strong4_limsupQuality_ne_one_of_pairwise_isCoprime_H
    (hpoly : Pairwise fun i j ↦
      IsCoprime ((H i).map (Int.castRingHom ℚ))
        ((H j).map (Int.castRingHom ℚ))) :
    limsupQuality (strongAdmissibleSet 4) ≠ 1 := by
  classical
  obtain ⟨M, hM, hcop⟩ :=
    CoprimeProgression.exists_pos_nat_pairwise_coprime_eval_mul H hpoly
      pairwise_isCoprime_H_eval_zero
  let x : ℕ → Fin 4 → ℤ := fun k i ↦ (H i).eval ((M : ℤ) * (k : ℤ))
  let raw : ℕ → Fin 4 → ℤ := fun k ↦ signedFourthPowers (x k)
  have habs : ∀ᶠ k : ℕ in atTop, ∀ i : Fin 4, 1 < (x k i).natAbs :=
    eventually_one_lt_natAbs_H_eval_mul M hM
  have hmem : ∀ᶠ k : ℕ in atTop, raw k ∈ strongAdmissibleSet 4 := by
    filter_upwards [habs] with k hk
    exact signed_fourthPowers_mem_strongAdmissibleSet_four (x k)
      (hcop (k : ℤ)) (H_eval_fourth_power_identity ((M : ℤ) * (k : ℤ))) hk
  let a : ℕ → strongAdmissibleSet 4 := fun k ↦
    if hk : raw k ∈ strongAdmissibleSet 4 then ⟨raw k, hk⟩
    else ⟨signedFourthPowers seed, signedFourthPowers_seed_mem⟩
  have heq : ∀ᶠ k : ℕ in atTop, (a k).1 = raw k := by
    filter_upwards [hmem] with k hk
    simp only [a, dif_pos hk]
  obtain ⟨C, hC, hheight⟩ :=
    PolynomialGrowth.exists_pos_eventually_le_natAbs_eval_mul
      (H 0 ^ 4) (pow_ne_zero 4 (H_ne_zero 0))
      (show (H 0 ^ 4).natDegree = 1080 by rw [natDegree_pow, H_natDegree]) M hM
  have hH : ∀ᶠ k : ℕ in atTop,
      C * (k : ℝ) ^ 1080 ≤ (maxAbs (a k).1 : ℝ) := by
    filter_upwards [heq, hheight] with k hk hheightk
    rw [hk]
    have hcoord : (((H 0 ^ 4).eval ((M : ℤ) * (k : ℤ))).natAbs) ≤
        maxAbs (raw k) := by
      change (((H 0 ^ 4).eval ((M : ℤ) * (k : ℤ))).natAbs) ≤
        Finset.univ.sup (fun i ↦ (raw k i).natAbs)
      simpa only [raw, x, signedFourthPowers, Matrix.cons_val_zero, eval_pow] using
        (Finset.le_sup (f := fun i ↦ (raw k i).natAbs) (Finset.mem_univ (0 : Fin 4)))
    exact hheightk.trans (by exact_mod_cast hcoord)
  obtain ⟨K, hK, hKdeg⟩ := exists_H_zero_quotient
  let Rpoly : ℤ[X] := g * K * H 1 * H 2 * H 3
  have hRdeg : Rpoly.natDegree ≤ 1074 := by
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le
        (natDegree_mul_le_of_le
          (natDegree_mul_le_of_le g_natDegree.le hKdeg) (H_natDegree 1).le)
        (H_natDegree 2).le)
      (H_natDegree 3).le
  obtain ⟨D, hD, hradical⟩ :=
    PolynomialGrowth.exists_pos_eventually_natAbs_eval_mul_le Rpoly hRdeg M
  have hR : ∀ᶠ k : ℕ in atTop,
      (rad (a k).1 : ℝ) ≤ D * (k : ℝ) ^ 1074 := by
    filter_upwards [heq, habs, hradical] with k hk habsk hradicalk
    rw [hk]
    have hne : ∀ i : Fin 4, x k i ≠ 0 := by
      intro i hi
      have hiabs := habsk i
      simp only [hi, Int.natAbs_zero] at hiabs
      omega
    have hfactor : x k 0 = (g.eval ((M : ℤ) * (k : ℤ))) ^ 2 *
        K.eval ((M : ℤ) * (k : ℤ)) := by
      change (H 0).eval _ = _
      rw [hK, eval_mul, eval_pow]
    have hradbound : rad (raw k) ≤ (Rpoly.eval ((M : ℤ) * (k : ℤ))).natAbs := by
      simpa only [raw, Rpoly, x, eval_mul] using
        rad_signedFourthPowers_le_of_sq_factor (x k)
          (g.eval ((M : ℤ) * (k : ℤ))) (K.eval ((M : ℤ) * (k : ℤ))) hne hfactor
    exact (show (rad (raw k) : ℝ) ≤
      ((Rpoly.eval ((M : ℤ) * (k : ℤ))).natAbs : ℝ) by exact_mod_cast hradbound).trans
        hradicalk
  exact QualityContradiction.strong4_limsupQuality_ne_one_of_bounds_1080_1074
    a hC hD hH hR

end StrongFourCertificate

theorem NConjecture.n_conjecture.variants.strong_quality.disproof : ¬ (type_of% @NConjecture.n_conjecture.variants.strong_quality) := by
  intro h
  exact StrongFourCertificate.strong4_limsupQuality_ne_one_of_pairwise_isCoprime_H
    (StrongFourCertificate.pairwise_isCoprime_H_map_of_coprime
      StrongFourCertificate.pairwise_isCoprime_p_map
      StrongFourCertificate.isCoprime_A_B_map)
    (h 4 (by norm_num) (by norm_num))
