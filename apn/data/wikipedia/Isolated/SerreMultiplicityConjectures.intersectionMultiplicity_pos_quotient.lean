/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Serre's multiplicity conjectures

Let $R$ be a regular local ring and let $M$, $N$ be finitely generated $R$-modules such that
$M \otimes_R N$ has finite length. Serre defined the intersection multiplicity
$$\chi(M, N) = \sum_{i \ge 0} (-1)^i \ell_R(\operatorname{Tor}_i^R(M, N)).$$
He proved the dimension inequality $\dim M + \dim N \le \dim R$ for every regular local ring,
and conjectured the following three properties:

- **Non-negativity:** $\chi(M, N) \ge 0$.
- **Vanishing:** if $\dim M + \dim N < \dim R$, then $\chi(M, N) = 0$.
- **Positivity:** if $\dim M + \dim N = \dim R$, then $\chi(M, N) > 0$.

Serre proved all three when $R$ is of equal characteristic, or of mixed characteristic and
unramified. Vanishing was proved in general by Roberts and, independently, by Gillet and Soulé.
Non-negativity was proved in general by Gabber. Positivity is open in general. For Serre's two
special cases, this file states only positivity, since non-negativity and vanishing are now known
in general.

The intersection multiplicity is `Module.intersectionMultiplicity`, defined in
`FormalConjecturesForMathlib.RingTheory.IntersectionMultiplicity`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Serre%27s_multiplicity_conjectures)
- [Se00] J.-P. Serre, *Local algebra*, Springer Monographs in Mathematics, Springer, 2000,
  Chapter V, Part B.
- [Ro85] P. Roberts, *The vanishing of intersection multiplicities of perfect complexes*,
  Bull. Amer. Math. Soc. 13 (1985), 127–130.
- [GS87] H. Gillet, C. Soulé, *Intersection theory using Adams operations*,
  Invent. Math. 90 (1987), 243–277.
- [Ro98] P. Roberts, *Recent developments on Serre's multiplicity conjectures: Gabber's proof of
  the nonnegativity conjecture*, Enseign. Math. 44 (1998), 305–324.
- [Sk19] C. Skalit, *Positivity of intersection multiplicity over a two-dimensional base*,
  J. Pure Appl. Algebra 223 (2019), 1801–1816.
  [arXiv:1510.05146](https://arxiv.org/abs/1510.05146)
-/

open IsLocalRing Module TensorProduct

namespace SerreMultiplicityConjectures

universe u

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]
  (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N]

/--
**Positivity conjecture**, in the form stated on Wikipedia. Let $R$ be a regular local ring and
let $P$, $Q$ be prime ideals of $R$ such that $R/P \otimes_R R/Q$ has finite length. If
$\dim R/P + \dim R/Q = \dim R$, then $\chi(R/P, R/Q) > 0$.
-/
theorem intersectionMultiplicity_pos_quotient (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (h : IsFiniteLength R ((R ⧸ P) ⊗[R] (R ⧸ Q)))
    (hdim : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R) :
    0 < intersectionMultiplicity R (R ⧸ P) (R ⧸ Q) := by
  sorry

end SerreMultiplicityConjectures

theorem SerreMultiplicityConjectures.intersectionMultiplicity_pos_quotient.disproof : ¬ (type_of% @SerreMultiplicityConjectures.intersectionMultiplicity_pos_quotient) := sorry
