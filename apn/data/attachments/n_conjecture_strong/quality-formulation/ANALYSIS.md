# NConjecture.n_conjecture.variants.strong_quality

**Verdict:** C-possibly-new  (confidence: medium — high that the counterexample is mathematically legitimate for the stated conjecture; medium on novelty, see literature check)
**Claim:** disproof

Secondary flag: **bundled statement**. The theorem quantifies over n ∈ {3,4}; the agent refutes only the n = 4 instance
(`Spec.lean:1477`, `h 4 (by norm_num) (by norm_num)`). The n = 3 instance is the abc conjecture and is untouched.
The bundling is not a formalization *error* (the docstring states the conjecture for exactly these two open cases), but a
"disproof" score on this sample must not be read as saying anything about abc.

## Informal conjecture (Wikipedia / literature status)

The *strong n conjecture* (Wikipedia "n conjecture", "Stronger form", attributed to Vojta 1998; identical to
Ramaekers's 2009 "strong n-conjecture" = Conjecture 7 of Hölzl–Kleine–Stephan (HKS), arXiv:2409.13439, J. Aust. Math.
Soc. 2025): over n-tuples of integers that are (i) pairwise coprime, (ii) sum to 0, (iii) have no vanishing proper
subsum, the quality q = log max|a_i| / log rad(|a_1⋯a_n|) satisfies limsup q = 1 (second formulation; the first
formulation is max|a_i| < C_{n,ε} rad^{1+ε}). HKS proved limsup ≥ 5/3 (odd n ≥ 5) and ≥ 5/4 (even n ≥ 6), so the
conjecture is false for n ≥ 5. For n = 3 (abc) and n = 4 Wikipedia says HKS "did not find any nontrivial lower bounds";
HKS themselves write that examples in R(4) "exhibited a tendency of being of smaller quality than those in R(3), which
could make one suspect that disproving the claim Q_{R(4)} = 1 might be even harder than disproving the abc-conjecture",
and that they are "unaware of any known implications between the cases n = 3 and n = 4". Konyagin's bound for even
n (HKS Thm 6) is only the trivial Q_{B(4)} ≥ 1. So as of the 2025 literature, n = 4 was open with no bound > 1.

## What the formal statement actually says (Challenge.lean)

Hand-rolled definitions (all in `Challenge.lean`):
- `HasNoVanishingProperSubsum a` (l.39): ∀ nonempty proper s ⊆ Fin n, Σ_{i∈s} a_i ≠ 0. Faithful to (iii).
- `strongAdmissibleSet n` (l.51): {a : Fin n → ℤ | Pairwise IsCoprime (a i) (a j) ∧ Σ a_i = 0 ∧ no vanishing proper
  subsum}. `IsCoprime` over ℤ is gcd = 1. Faithful to (i)–(iii) (= Ramaekers's/HKS's set R(n)).
- `maxAbs a` (l.55) = sup_i |a_i| ∈ ℕ. Faithful.
- `rad a` (l.61) = `UniqueFactorizationMonoid.radical (∏ |a_i|)` = product of distinct primes dividing ∏ a_i. Faithful
  (junk value radical 0 = 1 is irrelevant: (iii) forces all a_i ≠ 0 for n ≥ 2).
- `quality a` (l.69) = Real.log(maxAbs) / Real.log(rad) ∈ ℝ. Faithful (rad ≥ 2 on admissible tuples, n ≥ 3, so no
  division-by-zero junk is reachable; the agent's family has enormous radicals anyway).
- `limsupQuality S` (l.76) = `limsup (fun a : S ↦ (quality a : EReal)) cofinite` on the subtype S. For infinite S this
  equals inf_N sup_{height>N} q (height sublevel sets are finite), i.e. the informal "limsup as the tuples go to
  infinity". Faithful.
- Theorem (l.91–93): ∀ n, 3 ≤ n → n ≤ 4 → limsupQuality (strongAdmissibleSet n) = 1.
- `.disproof` (l.97): ¬ (∀ n, 3 ≤ n → n ≤ 4 → limsupQuality (strongAdmissibleSet n) = 1).

Plain math: "the strong n-conjecture (limsup form) holds for n = 3 and for n = 4". Its negation is proved by exhibiting
limsup_{R(4)} q ≠ 1 (in fact > 1).

## What the agent proved and how

Top-level: `Spec.lean:1471–1477` proves `.disproof` by `intro h` and applying
`StrongFourCertificate.strong4_limsupQuality_ne_one_of_pairwise_isCoprime_H` (l.1397–1467) to `h 4 _ _` (l.1477).
Dependency chain, bottom-up:

1. **A rational curve on the Fermat quartic surface x⁴+y⁴ = z⁴+w⁴ with pairwise coprime coordinates.**
   Sextic forms P, Q, L (l.710–716), auxiliary forms E (deg 38), O (deg 39), V (deg 36) (l.719–725) and
   `FHom x y = ![(P+3xy⁵)(y³V − xE), (Q−3x⁵y)(yE − O), −(P−3xy⁵)(y³V + xE), (Q+3x⁵y)(yE + O)]` (l.728–732), four
   binary forms of degree 45 with `FHom_fourth_power_identity : F₀⁴ + F₁⁴ = F₂⁴ + F₃⁴` (l.755–760), proved over any
   commutative ring via `quartic_step` (l.745, the factorization (a+b)⁴(u−v)⁴ − (a−b)⁴(u+v)⁴ = 8(au−bv)(bu−av)(…))
   and `ring`. The first factors are exactly those of Euler's classical degree-7 parametrization
   a = x(P+3xy⁵), b = y(Q−3x⁵y), c = x(P−3xy⁵), d = y(Q+3x⁵y) (which gives 158⁴+59⁴ = 134⁴+133⁴ at (2,1)); Euler's
   curve is *not* pairwise coprime (a,c share x; b,d share y) — the agent replaces x, y by the degree-39 cofactors.
   `FHom_one_zero` (l.805): FHom(1,0) = (3,−1,3,1), so no coordinate vanishes at infinity.
   `seed := FHom 2 1 = (44162725988761, 47301468159703, 15168229732247, 54398746431911)` (l.810–814), pairwise coprime
   (l.818, `norm_num`).
2. **Univariate coordinates** `p i := FHom X 1 i ∈ ℤ[X]` (l.832), degree 45, proved pairwise coprime over ℚ by six
   explicit Bézout certificates u·p_i + v·p_j = c (degree-44 cofactors with ~21-digit coefficients, `norm_num`+`ring`,
   l.963–1010) — generated externally with Sage per the agent's notes, but fully kernel-checked.
3. **Ramified degree-6 base change forcing a square factor.** `A`, `B` ∈ ℤ[X] of degree 6 (l.835–842; A(0)=2,
   B(0)=1), `H i := FHom A B i` (l.845) of exact degree 270 (`H_natDegree`, l.1237, via top-coefficient bookkeeping),
   `g := (5X)⁶ + (5X)⁴ − 2(5X)² + 3(5X) + 1` (l.848) — note g(X) = P(5X,1) + 3·(5X), i.e. Euler's first factor at
   t = 5X. `A_taylor : A = 5X·B + (7X+2)·g` (l.1270) and `B_taylor` (l.1275) make the point (A:B) agree with (5X:1)
   to second order along g = 0, so `g_sq_dvd_first_factor : g² ∣ P A B + 3AB⁵` (l.1282) and `g_sq_dvd_H_zero`
   (l.1296); hence `H 0 = g² · K` with deg K = 258 (l.1301). A, B are coprime over ℚ (Bézout certificate l.1011).
   `pairwise_isCoprime_H_map_of_coprime` (l.1058–1083) transfers coprimality of the p_i and of (A,B) to the H_i over
   ℚ via common roots in `AlgebraicClosure ℚ` and dehomogenization (l.1042, 1048).
4. **Integer pairwise coprimality along an arithmetic progression** (`CoprimeProgression`, l.127–222): coprime over ℚ
   ⇒ ∃ c ≠ 0 with c ∈ (p,q)ℤ[X]; if p(0), q(0) are coprime then p(x), q(x) are coprime for every c ∣ x
   (l.155–174). Applied to the H_i with `H_eval_zero : (H i).eval 0 = seed i` (l.906) it gives M > 0 with
   H_i(Mk) pairwise coprime for all k (l.213).
5. **Admissibility** (l.236–297): for pairwise coprime x with |x_i| > 1 and x₀⁴+x₁⁴ = x₂⁴+x₃⁴, the tuple
   `signedFourthPowers x = ![x₀⁴, x₁⁴, −x₂⁴, −x₃⁴]` lies in `strongAdmissibleSet 4` (no vanishing proper subsum is
   checked by cases on |s| ∈ {1,2,3}, l.236–265).
6. **Radical bound** `rad_signedFourthPowers_le_of_sq_factor` (l.1351–1367): rad(∏|x_i⁴|) = rad(|x₀x₁x₂x₃|) ≤
   |u·v·x₁x₂x₃| when x₀ = u²v. With u = g(Mk), v = K(Mk): rad ≤ |(g·K·H₁·H₂·H₃)(Mk)|, a polynomial of degree
   6+258+3·270 = 1074 (l.1441–1447), while maxAbs ≥ |H₀(Mk)|⁴ has degree 1080 (l.1428–1440).
7. **Analytic wrap-up** (`QualityContradiction`, l.486–687): power bounds C·k¹⁰⁸⁰ ≤ maxAbs and rad ≤ D·k¹⁰⁷⁴ give
   an eventual quality gap (e.g. q > 1001/1000, l.637) along a family whose height → ∞, hence the family tends to the
   cofinite filter (l.486–503) and `le_limsupQuality_of_family` (l.506) yields limsupQuality > 1 (l.649–687).
   Exceptional early indices fall back to the seed tuple (l.1387, 1413–1418).

Loophole scan: no `native_decide`, no `axiom`, `sorry` only in the original theorem (l.93); `decide` only on tiny
literals (`2 ≠ 0`, `4 ≠ 0`); `maxHeartbeats 0` only for the big `ring`/`norm_num` certificates; `Classical` only for
`if … then … else` on membership in the fallback family — the witnesses are fully explicit. Kernel axioms:
propext, Classical.choice, Quot.sound.

### Independent checks (Python/sympy, not relying on Lean)
- Fourth-power identity holds at 29 integer points (incl. random 7-digit ones); as univariate polynomials
  p₀⁴+p₁⁴−p₂⁴−p₃⁴ = 0 and H₀⁴+H₁⁴−H₂⁴−H₃⁴ = 0 (degree 1080) exactly.
- FHom(2,1) = seed; seed⁴-identity holds; seed pairwise coprime; factorizations 79·41221·13561579,
  23²·59·1515538373, 67·226391488541, 7·19·83·17029·289381; the seed tuple (X = 0) is itself an R(4) element with
  quality 1.0391 (a single tuple proves nothing, but it is a concrete member of the family). Euler(2,1) = (158,−59,134,133).
- deg p_i = 45, deg H_i = 270, gcd(A,B) = 1, all six gcd(H_i,H_j) = 1 over ℚ, g² ∣ H₀ exactly with deg K = 258 and
  gcd(K,g) = 1; squarefree part of H₀H₁H₂H₃ has degree exactly 1074 (so the polynomial radical bound is sharp).
- Integer values H_i(k) are pairwise coprime for every even k ≤ 60 (odd k share a factor, consistent with an even
  modulus M); the provable quality lower bound 4·log|H₀(k)| / log|(gKH₁H₂H₃)(k)| is 1.00613 (k=2), 1.005624 (k=10),
  1.005595 (k=10³), 1.005588 (k=10²⁰), decreasing to 1080/1074 = 180/179 ≈ 1.0055866 from above.
- The X = 2 member has coordinates of ~315 digits (fourth powers ~1260 digits).

## Faithfulness assessment

- Definitions (coprimality, subsum condition, max, radical, quality, cofinite limsup) all match Wikipedia's and
  Ramaekers/HKS's R(n) formulation; no degenerate object, junk value, or quantifier slip is used. The counterexample
  family consists of honest, huge, pairwise coprime 4-tuples with zero sum and no vanishing subsums, and the quality
  lower bound is exactly the informal one. I also checked (informally, not in Lean) that the family satisfies HKS's
  stricter signed-subsum condition (any ±H_i⁴ ± H_j⁴ (± H_k⁴) = 0 would be a nontrivial solution of a Fermat quartic
  or force |H_i| = |H_j|), so it lies in HKS's most demanding set U(∅,4).
- The only formal/informal divergence is the bundling: the formal theorem is "n = 3 and n = 4", the disproof kills
  n = 4 only. For the *informal* conjecture as stated on Wikipedia ("for every n ≥ 3, limsup = 1") the family is a
  legitimate counterexample at n = 4.
- Caveat on attribution rather than faithfulness: Vojta's actual Conjecture 2.3 (IMRN 1998, arXiv math/9806171)
  is stated with an exceptional proper Zariski-closed subset Z; Vojta explicitly says the exponent 1+ε for
  a+b+c+d = 0 should hold "only generically" and that "working with Z is the hardest part". A single rational curve
  (the agent's degree-1080 curve in the plane x₀+x₁+x₂+x₃ = 0) is a proper closed subset, so Vojta's conjecture is
  NOT refuted. What is refuted is the exceptional-set-free formulation used by Wikipedia, Ramaekers (2009,
  Conj. 5.1) and HKS (Conj. 7, "Q_{R(4)} = 1"). The Challenge docstring correctly hedges ("attributed to Vojta
  (1998) by the Wikipedia article").

## Mathematical significance

- Claimed result (kernel-checked, modulo the faithful definitions above): **Q_{R(4)} ≥ 1080/1074 = 180/179 > 1**,
  i.e. Ramaekers's strong 4-conjecture / the Wikipedia strong n conjecture at n = 4 is false, and consequently
  Q_{B(4)} ≥ 180/179 (first bound above Konyagin's trivial 1 for even n = 4). HKS (2025) explicitly left this case
  open and speculated it might be harder than abc; Ramaekers (2009, §4.2.2, §4.4) wrote that the data "make it more
  plausible that indeed with the extra gcd demands limsup Q₄ = 1" and that the known polynomial identities (e.g.
  Granville's (x+1)⁵ − (x−1)⁵ = 10(x²+1)² − 8) fail pairwise coprimality. The agent's contribution is precisely a
  polynomial family with pairwise coprime terms (a pairwise-coprime rational curve on the Fermat quartic K3 surface,
  plus a ramified base change to create a square factor). I found no prior publication of this or any Q_{R(4)} > 1
  bound (searched arXiv/web; checked HKS 2025a, HKS 2025b "Strong n-conjectures over rings of integers"
  arXiv:2503.05296 — which treats n = 4 only over ℤ[i] and quaternions — Vojta 1998, Ramaekers 2009). Not checked:
  Browkin 2000 survey, Darmon–Granville 1995 p. 542 items (d)/(e), de Weger's unpublished 2020 notes.
- Conceptually it is unsurprising to experts of the Vojta/Granville school: Granville (reported via Pomerance 2008 in
  Ramaekers §4.4) expected counterexamples to limsup Q₄ = 1 to come from finitely many polynomial families for each
  ε, i.e. exactly Vojta's exceptional set. So this is a modest, explicit result, not a paradigm shift, and it says
  nothing about Vojta's conjecture proper.
- It says **nothing about abc** (n = 3): the proof never instantiates n = 3, Mason–Stothers forbids any polynomial
  family of quality > 1 for three terms, and HKS note no known implication between n = 3 and n = 4.
- Method ceiling (my back-of-envelope): the 45-degree curve has 180 distinct roots; a degree-d base change removes at
  most 2d−2 of 180d preimages, so this curve cannot beat 180/178 = 90/89 ≈ 1.0112; the agent used 6 of the 10
  available ramification points. Better curves or heavier ramification could improve the constant.
- The proof engineering is notable: 1477 lines, single file, Bézout certificates for degree-45 polynomials checked by
  `norm_num`/`ring`, degree-1080 identity by `ring` after a factorization trick, generic "coprime over ℚ ⇒ coprime
  values on a progression" lemma.

## Recommended fix to the formalization / follow-up

1. Split the bundled theorem into `strong_quality_three : limsupQuality (strongAdmissibleSet 3) = 1` (= abc, open)
   and `strong_quality_four : limsupQuality (strongAdmissibleSet 4) = 1`; record the latter as **refuted** (with
   this construction as the witness, limsup ≥ 180/179) so that future runs are scored against abc alone. More
   generally, avoid bundling several n in one statement when they have different status.
2. If the intended target is Vojta's conjecture rather than the Wikipedia/Ramaekers form, the formalization would
   need the exceptional-set quantifier ("∃ proper Zariski-closed Z, ∀ tuples outside Z …"), which would rule out
   rational-curve counterexamples of this type.
3. Follow-up for an expert (number theorist): confirm novelty against Browkin (2000), Darmon–Granville (1995,
   p. 542) and de Weger's notes; if new, the statement "Q_{U(∅,4)} ≥ Q_{R(4)} ≥ 180/179" is a publishable remark
   (an HKS-style short note), and the construction (pairwise-coprime rational curves on x⁴+y⁴ = z⁴+w⁴ + ramified base
   change) suggests systematic improvements.
