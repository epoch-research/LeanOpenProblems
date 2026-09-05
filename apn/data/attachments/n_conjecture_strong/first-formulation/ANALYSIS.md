# NConjecture.n_conjecture.variants.strong

**Verdict:** C-possibly-new (confidence: medium) — structurally also A-bundled: the refutation uses only the
n = 4 component of a theorem stated for n ∈ {3, 4}; the n = 3 component (the abc conjecture) is untouched.
Correctness of the counterexample: high confidence (kernel-checked, and independently re-verified here with
sympy/Python). Novelty: medium confidence (HKS 2025 and today's Wikipedia explicitly record no nontrivial lower
bound for n = 4; I found no 2025-2026 paper closing it; unpublished notes/folklore cannot be excluded).

**Claim:** disproof

## Informal conjecture (Wikipedia / literature status)

Wikipedia, "n conjecture", section "Stronger form", first formulation: for n ≥ 3 and every ε > 0 there is
C_{n,ε} such that for all integers a_1..a_n that are (i) pairwise coprime, (ii) sum to 0, (iii) have no
vanishing proper subsum, max|a_i| < C_{n,ε} · rad(|a_1|···|a_n|)^{1+ε}. Second formulation: limsup of the
quality q = log max / log rad equals 1. Wikipedia attributes it to Vojta (1998).

Status (all sources fetched 2026-09-05):
- n = 3 is the abc conjecture (open).
- Hölzl–Kleine–Stephan (HKS), arXiv:2409.13439 / J. Aust. Math. Soc. 2025, refute it for n ≥ 5
  (limsup ≥ 5/3 for odd n ≥ 5, ≥ 5/4 for n ≥ 6). In their notation the Wikipedia statement is exactly
  Ramaekers's Conjecture 7: Q_R(n) = 1, where R(n) = {sum 0, no vanishing proper subsum, pairwise coprime}.
- n = 4: HKS Theorem 6 (Konyagin, in Browkin 2000) gives only the trivial bound Q_B(4) ≥ 1. HKS write that
  Ramaekers's sporadic R(4) examples "could make one suspect that disproving the claim Q_R(4) = 1 might be even
  harder than disproving the abc-conjecture. We are however unaware of any known implications between the cases
  n = 3 and n = 4." Their 2025 follow-up (arXiv:2503.05296) proves n = 4 bounds only over Z[i]. Wikipedia
  today: "For the cases n=3 (abc-conjecture) and n=4, they did not find any nontrivial lower bounds."
- Vojta's actual Conjecture 2.3 (arXiv:math/9806171, §2) carries an exceptional proper Zariski-closed subset Z,
  and Vojta states "This subset is, in fact, essential." The Wikipedia statement drops Z; it is really the
  Browkin (2000) / Ramaekers (2009) strong n-conjecture.

## What the formal statement actually says (Challenge.lean)

Hand-rolled definitions (all faithful):
- `HasNoVanishingProperSubsum a` [39-40]: ∀ s : Finset (Fin n), s nonempty, s ≠ univ → Σ_{i∈s} a i ≠ 0.
  Exactly (iii); for n ≥ 2 it forces every entry nonzero.
- `strongAdmissibleSet n` [51-52]: Pairwise (IsCoprime (a i) (a j)) ∧ Σ a i = 0 ∧ HasNoVanishingProperSubsum a.
  Exactly (i)-(iii) (`Pairwise` = for all i ≠ j; `IsCoprime` over ℤ = gcd 1).
- `maxAbs a` [55-56]: sup_i |a_i| in ℕ. `rad a` [61-62]: Mathlib `UniqueFactorizationMonoid.radical` of
  ∏|a_i| in ℕ = product of distinct primes; the product is nonzero for admissible tuples, so no junk value.
- `quality`, `limsupQuality` [69-77] are defined but not used by the theorem.

Theorem [92-95]:
  ∀ n, 3 ≤ n → n ≤ 4 → ∀ ε > 0, ∃ C : ℝ, ∀ a ∈ strongAdmissibleSet n, (maxAbs a : ℝ) < C · (rad a : ℝ)^(1+ε).
This is Wikipedia's first formulation for each of n = 3 and n = 4, bundled into one ∀ n statement. C ranges over
all reals (harmless: C ≤ 0 can never satisfy the inequality). `.disproof` [100] is ¬ of this type; a
counterexample for either n refutes the bundled statement.

## What the agent proved and how (Spec.lean)

Top-level: `NConjecture.n_conjecture.variants.strong.disproof` [742-754]. Decisive lines:
  744: `obtain ⟨C, hC⟩ := hconj 4 (by norm_num) (by norm_num) ((1 : ℝ) / 38) (by norm_num)`
  — instantiates **n = 4, ε = 1/38**. It then picks an index n with `parameter n > max ((max C 0)^38 * D^39) 1`
  (D = 98972845020·K) and closes with `power_contradiction_of_large` [691-699] using `height_lower`,
  `radical_upper`, `tuple_admissible`.

The counterexample family (namespace `StrongFour`):
- Base polynomials [120-129]: a(u) = u⁴+2u³+3u²+10u+1, b(u) = u¹⁰+5u⁹+15u⁸+50u⁷+105u⁶+171u⁵+305u⁴+270u³
  +195u²+185u−159, h(u) = 2u+1, g(u) = 1888u⁵+15760u⁴+22920u³+28380u²+58810u−25285.
- `polynomial_identity` [357-360]: a(u)⁵ − b(u)² − 5·h(u)⁷ − g(u) = 0, proved by `ring`.
  Provenance (verified): this is the Beukers–Stewart (5,2) Davenport–Zannier pair, "Tree O" in
  Pakovich–Zvonkin arXiv:1509.07973 §9.5: P = (x⁴+6x²+64x−55)⁵, Q = (x¹⁰+…−226797)², P − Q = R =
  2²⁰(5x⁷+59x⁵+690x⁴−485x³+3820x²+20165x−49534). With x = 2u+1: P_base = 16·a(u), Q_base = 1024·b(u),
  R/2²⁰ = 5h⁷ + g. deg(a⁵−b²) = 7 is the DZ minimum 20(1−1/5−1/2)+1; because R has no x⁶ term, the degree-7
  remainder splits as 5·(linear)⁷ + (degree 5). Sympy check: identity exact; a, b, g irreducible; all six
  pairwise polynomial gcds are 1.
- `tuple n` [708-710] := ![a(u)⁵, −b(u)², −5h(u)⁷, −g(u)] at u = `parameter n`; degrees (20, 20, 7, 5).
- Pairwise coprimality: six integer Bézout certificates U·p + V·q = c [165-204] with c =
  −44302336, −55, −25909670423005436759, −226797, −4668301001649258879577091386750710258929233783901,
  −1585088 (these are exactly the resultants; checked with sympy). `M` [132-134] := 10 × product of the six
  constants (≈ 10⁹⁰). `isCoprime_of_bezout_modEq` [211-227]: for u ≡ 3 (mod M), any common divisor of p(u),
  q(u) divides c | M, hence divides p(3), q(3), which are coprime (seed values 193, 517473, 7, 2760749 [145]).
  Coprimality with the coefficient 5 uses 5 | M [142, 313-329]; `coprime_tuple` [332-342] lifts to the powers.
- The sequence: `K` := 2M+1 [470]; `parameter 0 = 3`, `parameter (n+1) = (2M+1)·parameter n + M` [481-483];
  `parameter_mod`: M | parameter n − 3 [499-507]; `parameter_linear`: h(parameter n) = 7·Kⁿ [510-518].
  So along the sequence the linear factor is (up to 7) a perfect power of the fixed base K and its radical is
  bounded by 7K.
- Subsum condition: `no_vanishing_four` [547-552]: A = B + C + D with B, C, D > 0 (positivity for u ≥ 3 at
  [364-386]); `fin_cases` over the 16 subsets.
- Height: `height_lower` [723-731]: u²⁰ ≤ a(u)⁵ ≤ maxAbs (via `a_lower` [390]).
- Radical: `nat_radical_product_dvd` [576-596]: radical(a⁵·b²·5(7Kⁿ)⁷·g) | 35·K·a·b·g, using only
  `radical_dvd_self`, `radical_mul_dvd`, `radical_pow`; with a ≤ 17u⁴, b ≤ 1302u¹⁰, g ≤ 127758u⁵ [397-431]
  this gives rad ≤ 98972845020·K·u¹⁹ (`real_radical_estimate` [622-641], `radical_upper` [733-738]).
- `power_contradiction` [658-689]: u²⁰ ≤ H < C·R^{1+1/38} and R ≤ D·u¹⁹ ⇒ u⁷⁶⁰ < C³⁸D³⁹u⁷⁴¹ ⇒ u¹⁹ < C³⁸D³⁹,
  contradicting the choice of u. Quality along the family → 20/19 ≈ 1.0526 > 1 + 1/38.

Loophole scan: axioms are only propext/Classical.choice/Quot.sound; no `native_decide`; `decide` only for
`(7:ℕ) ≠ 0` [582] and `norm_num +decide` on Fin 4 subsets [552]; the witness sequence is an explicit primitive
recursion (not a Classical.choice witness); all entries are nonzero and the base polynomials are positive for
u ≥ 3, so no Nat-subtraction/division/log junk is involved; no degenerate parameters.
Independent re-verification (Python/sympy): identity holds; for u = parameter(0..3) and u = 3 + kM the four
entries are pairwise coprime, sum to 0, and satisfy the subsum condition — including HKS's stronger signed
condition (S2) with coefficients in {−1,0,1}, so the tuples lie in HKS's smallest set U(∅,4); the provable
quality lower bound log(max)/log(35K·a·b·g) is 0.9977, 1.0243, 1.0336 for n = 1, 2, 3 and tends to 20/19.

## Faithfulness assessment

- The formal statement is a faithful rendering of the Wikipedia (Browkin/Ramaekers) strong n-conjecture, first
  formulation, for each n. The only structural issue is the **bundling** of n = 3 and n = 4 into one theorem:
  the theorem is refuted by the n = 4 case alone, and the eval's "C" tells us nothing about n = 3 / abc.
- The **counterexample is legitimate** for the informal n = 4 statement: infinitely many 4-tuples, pairwise
  coprime, zero sum, no vanishing proper subsum (even with signs), and max ≥ rad^{20/19 − o(1)}. It refutes both
  Wikipedia formulations for n = 4 and Ramaekers's conjecture Q_R(4) = 1, and gives Q_U(∅,4) ≥ Q_R(4) ≥
  Q_B(4) ≥ 20/19 (first formulation fails for every ε < 1/19; the Lean proof uses ε = 1/38).
- Divergence from **Vojta's** conjecture: Vojta's Conjecture 2.3 admits an exceptional proper Zariski-closed
  subset; this family lies on the rational curve (a⁵ : b² : 5h⁷ : g) ⊂ P³, so Vojta's own conjecture is not
  refuted. The Challenge docstring's attribution to Vojta (copied from Wikipedia) is therefore loose, but the
  formal statement matches what the docstring actually states.
- The family is purely asymptotic: M ≈ 10⁹⁰, and the first member whose quality is provably > 1 has
  u ≈ 10¹⁸¹ (entries with thousands of digits). This does not affect validity; a CRT progression modulo the
  radical of the resultants (≈ 10⁸¹) would already suffice, and smarter choices could shrink it further.

## Mathematical significance

- If not already in unpublished notes or folklore, this is a new (modest) result: the first nontrivial lower
  bound for the strong 4-conjecture over Z, Q_R(4) ≥ 20/19, refuting the n = 4 case that HKS (2025) and
  Wikipedia list as open and that HKS speculated might be harder than abc. The construction is elementary once
  the DZ pair is in hand: a 3-term DZ identity P⁵ − Q² = R with deg R = 7, split R = 5x⁷ + g, and run x through
  7·Kⁿ so the x⁷ term has bounded radical; the degree count 20 vs 4 + 10 + 5 = 19 gives 20/19. In general a
  DZ pair of total degree N with the right normalization and polynomial coprimality gives N/(N−1); other DZ
  pairs over Q might improve the bound (e.g. a suitable (3,2) pair of degree 12 would give 12/11).
- It says **nothing about abc**: (1) only n = 4 is instantiated; (2) HKS note there is no known implication
  between the strong n = 4 and n = 3 cases (unlike the weak n-conjecture, where abc false ⇒ n-conjecture false);
  (3) the trick is intrinsically ≥ 4-term: a 3-term identity P⁵ − Q² = c·L⁷ would violate Mason–Stothers
  (20 ≤ 4 + 10 + 1 − 1 is false), and splitting off a lower-degree g is what makes it a 4-tuple; (4) Vojta's
  formulation with an exceptional set is untouched.
- The agent's self-report (final_messages.md) is accurate: it names n = 4, the DZ/Tree O provenance, the
  progression, and ε = 1/38, and it ran its own axiom/statement-preservation checks.

## Recommended fix to the formalization / follow-up

- Un-bundle the statement: formalize n = 3 (abc) and n = 4 as separate declarations so that a disproof of one
  cannot resolve the other. Given this counterexample, the n = 4 statement should (after expert confirmation) be
  reclassified from "open" to "refuted", or restated positively as "limsup quality ≥ 20/19 for n = 4".
- If the benchmark intends Vojta's conjecture, it must include the exceptional Zariski-closed subset (a
  genuinely different and harder-to-formalize statement); otherwise attribute the statement to Browkin (2000) /
  Ramaekers (2009) rather than Vojta.
- Follow-up: have a number theorist (e.g. the HKS authors) check the construction; if confirmed new, it merits a
  short note and an update to the Wikipedia sentence about n = 4. Search Ramaekers's thesis §4.4 and de Weger's
  unpublished notes (cited by HKS) to rule out prior appearance.
