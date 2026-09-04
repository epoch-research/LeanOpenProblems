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
# Green's conjecture

Green's conjecture states that the Clifford index of a non-hyperelliptic curve over $\mathbb{C}$
is determined by the extent to which the curve, as a canonical curve, has linear syzygies.

A smooth projective curve $C$ over $\mathbb{C}$ is determined up to isomorphism by its function
field $F$, an algebraic function field of one variable over $\mathbb{C}$ (a finite extension of
$\mathbb{C}(t)$). Following Stichtenoth's textbook [St09], we model $C$ by $F$: the points of $C$
are the places of $F$ (valuation subrings $\mathbb{C} \subseteq \mathcal{O} \subsetneq F$),
divisors are finite formal $\mathbb{Z}$-linear combinations of places, $\mathcal{L}(D)$ is the
Riemann–Roch space of a divisor $D$ and $\ell(D)$ its dimension, the genus is
$g = \max_D (\deg D - \ell(D) + 1)$ (Riemann's theorem), and a canonical divisor is a divisor $K$
with $\deg K = 2g - 2$ and $\ell(K) \ge g$.

For a smooth projective non-hyperelliptic curve of genus $g \ge 4$, the *Clifford index* is
$$\operatorname{Cliff}(C) = \min\{\deg D - 2(\ell(D) - 1) : h^0(D) \ge 2,\ h^1(D) \ge 2\}.$$
The canonical curve $C \subseteq \mathbb{P}^{g-1}$ is projectively normal (Noether), so its
homogeneous coordinate ring is the canonical ring $\bigoplus_q H^0(C, qK)$, and its graded
Betti numbers are $\beta_{p, p+q} = \dim K_{p,q}(C, K_C)$, where the Koszul cohomology group
$K_{p,q}(C, K_C)$ is the middle cohomology of
$$\bigwedge^{p+1} V \otimes H^0(C, (q-1)K) \to \bigwedge^{p} V \otimes H^0(C, qK)
  \to \bigwedge^{p-1} V \otimes H^0(C, (q+1)K), \qquad V = H^0(C, K).$$
We realise this Koszul complex inside the exterior algebra
$\bigwedge_F (F \otimes_{\mathbb{C}} V)$, whose differential is the contraction against the
$F$-linear form $F \otimes_{\mathbb{C}} V \to F$, $f \otimes v \mapsto f v$.

Green's conjecture states $\operatorname{Cliff}(C) = \min\{p : K_{p,2}(C, K_C) \neq 0\}$,
i.e. $\beta_{p, p+2} = 0$ exactly for $p < \operatorname{Cliff}(C)$ (in the range $p \le g - 3$
where the Betti table is nontrivial). The inequality
$\min\{p : K_{p,2}(C, K_C) \ne 0\} \le \operatorname{Cliff}(C)$ is the Green–Lazarsfeld
nonvanishing theorem; the reverse inequality is open. Voisin proved the conjecture for generic
curves.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Green's conjecture](https://en.wikipedia.org/wiki/Green%27s_conjecture)
- [Gr84] M. Green, *Koszul cohomology and the geometry of projective varieties*,
  J. Differential Geom. 19 (1984), 125–171.
- [St09] H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Springer GTM 254, 2009.
-/

open scoped TensorProduct

namespace GreensConjecture

variable (F : Type*) [Field F] [Algebra ℂ F]

/-- A *place* of the function field `F` over `ℂ`, i.e. a closed point of the corresponding
smooth projective curve: a valuation subring `𝒪 ⊊ F` containing `ℂ` (see [St09, Section 1.1]).
Such a valuation ring is automatically a discrete valuation ring with residue field `ℂ`. -/
structure Place where
  /-- The valuation ring of the place. -/
  toValuationSubring : ValuationSubring F
  algebraMap_mem : ∀ c : ℂ, algebraMap ℂ F c ∈ toValuationSubring
  ne_top : toValuationSubring ≠ ⊤

namespace Place

variable {F}

/-- The valuation ring of a place, as a `ℂ`-subalgebra of `F`. -/
def toSubalgebra (P : Place F) : Subalgebra ℂ F where
  __ := P.toValuationSubring.toSubring
  algebraMap_mem' := P.algebraMap_mem

/-- `t : F` is a *uniformizer* (local parameter) at `P` if it generates the maximal ideal of
the valuation ring of `P`, i.e. `v_P(t) = 1`. -/
def IsUniformizer (P : Place F) (t : F) : Prop :=
  ∃ h : t ∈ P.toValuationSubring,
    Ideal.span {(⟨t, h⟩ : P.toValuationSubring)} = IsLocalRing.maximalIdeal P.toValuationSubring

end Place

/-- A *divisor* on the curve with function field `F`: a finite formal `ℤ`-linear combination of
places. -/
abbrev Divisor := Place F →₀ ℤ

namespace Divisor

variable {F}

/-- The degree of a divisor. Since `ℂ` is algebraically closed every place has degree one, so
the degree of `D` is the sum of its coefficients. -/
def deg (D : Divisor F) : ℤ := D.sum fun _ n => n

@[category test, AMS 14]
theorem deg_zero : (0 : Divisor F).deg = 0 := by
  simp [Divisor.deg]

@[category API, AMS 14]
theorem deg_add (D E : Divisor F) : (D + E).deg = D.deg + E.deg := by
  simp [Divisor.deg, Finsupp.sum_add_index']

@[category API, AMS 14]
theorem deg_neg (D : Divisor F) : (-D).deg = -D.deg := by
  simp [Divisor.deg, Finsupp.sum_neg_index]

@[category API, AMS 14]
theorem deg_single (P : Place F) (n : ℤ) : Divisor.deg (Finsupp.single P n) = n := by
  simp [Divisor.deg]

/-- The Riemann–Roch space `𝓛(D) = {f ∈ F | v_P(f) ≥ -D(P) for all places P}` of a divisor `D`,
as a `ℂ`-subspace of `F`. The condition `v_P(f) ≥ -D(P)` is expressed as `t ^ D(P) * f ∈ 𝒪_P` for
every uniformizer `t` at `P` (see [St09, Section 1.4]). -/
def riemannRochSpace (D : Divisor F) : Submodule ℂ F :=
  ⨅ (P : Place F) (t : F) (_ : P.IsUniformizer t),
    (Subalgebra.toSubmodule P.toSubalgebra).comap (LinearMap.mulLeft ℂ (t ^ D P))

@[category test, AMS 14]
theorem algebraMap_mem_riemannRochSpace_zero (c : ℂ) :
    algebraMap ℂ F c ∈ (0 : Divisor F).riemannRochSpace := by
  simp only [Divisor.riemannRochSpace, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mulLeft_apply, Finsupp.coe_zero, Pi.zero_apply, zpow_zero, one_mul,
    Subalgebra.mem_toSubmodule]
  intro P t _
  exact P.toSubalgebra.algebraMap_mem c

/-- `ℓ(D) = dim_ℂ 𝓛(D)`, the dimension of the Riemann–Roch space of `D`. -/
noncomputable def ell (D : Divisor F) : ℕ := Module.finrank ℂ D.riemannRochSpace

end Divisor

/-- The genus of the curve with function field `F`, defined via Riemann's theorem as
`g = max {deg D - ℓ(D) + 1 | D a divisor}` (see [St09, Section 1.4]). -/
noncomputable def genus : ℕ :=
  sSup {g : ℕ | ∃ D : Divisor F, (g : ℤ) = D.deg - D.ell + 1}

variable {F}

/-- The index of speciality `i(D) = ℓ(D) - deg D + g - 1` of a divisor `D`; by the Riemann–Roch
theorem this is `h^1(C, 𝒪(D)) = ℓ(K - D)` for a canonical divisor `K`
(see [St09, Sections 1.5, 1.6]). -/
noncomputable def indexOfSpeciality (D : Divisor F) : ℤ :=
  D.ell - D.deg + genus F - 1

/-- A divisor `K` is *canonical* if `deg K = 2g - 2` and `ℓ(K) ≥ g`; equivalently, `K` is the
divisor of a nonzero rational differential on the curve (see [St09, Section 1.6]). -/
def IsCanonical (K : Divisor F) : Prop :=
  K.deg = 2 * (genus F : ℤ) - 2 ∧ genus F ≤ K.ell

variable (F) in
/-- The curve is *hyperelliptic* if it has genus `g ≥ 2` and admits a divisor `D` with
`deg D = 2` and `ℓ(D) = 2`, i.e. a degree two map to `ℙ¹` (see [St09, Section 6.2]). -/
def IsHyperelliptic : Prop :=
  2 ≤ genus F ∧ ∃ D : Divisor F, D.deg = 2 ∧ D.ell = 2

variable (F) in
/-- The *Clifford index* of the curve with function field `F` (of genus `g ≥ 4`):
`Cliff(C) = min {deg D - 2 (ℓ(D) - 1) | h^0(D) ≥ 2 and h^1(D) ≥ 2}`, where `h^0(D) = ℓ(D)` and
`h^1(D) = i(D)` is the index of speciality. By Clifford's theorem each such
`deg D - 2 (ℓ(D) - 1)` is a nonnegative integer. -/
noncomputable def cliffordIndex : ℕ :=
  sInf {c : ℕ | ∃ D : Divisor F, 2 ≤ D.ell ∧ 2 ≤ indexOfSpeciality D ∧
    (c : ℤ) = D.deg - 2 * (D.ell - 1)}

/-- The exterior algebra `⋀_F (F ⊗_ℂ V)` with `V = 𝓛(K)`; the Koszul complex computing the Koszul
cohomology groups `K_{p,q}(C, K)` lives inside it. -/
abbrev KoszulSpace (K : Divisor F) :=
  ExteriorAlgebra F (F ⊗[ℂ] K.riemannRochSpace)

/-- The Koszul differential: contraction against the `F`-linear form
`F ⊗_ℂ 𝓛(K) → F`, `f ⊗ v ↦ f v`. On `w • (v₁ ∧ ⋯ ∧ vₙ)` it is
`∑ᵢ (-1)^(i+1) (vᵢ w) • (v₁ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ)`. -/
noncomputable def koszulDifferential (K : Divisor F) : KoszulSpace K →ₗ[ℂ] KoszulSpace K :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm F (F ⊗[ℂ] K.riemannRochSpace)))
    (K.riemannRochSpace.subtype.liftBaseChange F)).restrictScalars ℂ

@[category API, AMS 13 14]
theorem koszulDifferential_comp_self (K : Divisor F) :
    koszulDifferential K ∘ₗ koszulDifferential K = 0 := by
  ext x
  simp [koszulDifferential, CliffordAlgebra.contractLeft_contractLeft]

@[category test, AMS 13 14]
theorem koszulDifferential_smul_ιMulti_one (K : Divisor F) (w : F) (v : K.riemannRochSpace) :
    koszulDifferential K (w • ExteriorAlgebra.ιMulti F 1 (fun _ => (1 : F) ⊗ₜ[ℂ] v)) =
      algebraMap F _ (w * v) := by
  simp [koszulDifferential, ExteriorAlgebra.ιMulti_apply, Algebra.smul_def]
  rw [CliffordAlgebra.contractLeft_algebraMap_mul, CliffordAlgebra.contractLeft_ι]
  simp

@[category test, AMS 13 14]
theorem koszulDifferential_ιMulti_two (K : Divisor F) (v₁ v₂ : K.riemannRochSpace) :
    koszulDifferential K
      (ExteriorAlgebra.ιMulti F 2 ![(1 : F) ⊗ₜ[ℂ] v₁, (1 : F) ⊗ₜ[ℂ] v₂]) =
      (v₁ : F) • ExteriorAlgebra.ι F ((1 : F) ⊗ₜ[ℂ] v₂) -
        (v₂ : F) • ExteriorAlgebra.ι F ((1 : F) ⊗ₜ[ℂ] v₁) := by
  simp [koszulDifferential, ExteriorAlgebra.ιMulti_apply, CliffordAlgebra.contractLeft_ι_mul,
    CliffordAlgebra.contractLeft_ι, Algebra.smul_def, Algebra.commutes]

/-- The bigraded piece `⋀^p V ⊗_ℂ W` of the Koszul complex, for `V = 𝓛(K)` and a `ℂ`-subspace
`W ⊆ F`: the `ℂ`-span of the elements `w • (v₁ ∧ ⋯ ∧ vₚ)` with `w ∈ W` and `vᵢ ∈ V`. -/
def koszulPiece (K : Divisor F) (p : ℕ) (W : Submodule ℂ F) : Submodule ℂ (KoszulSpace K) :=
  Submodule.span ℂ {x | ∃ (w : F) (v : Fin p → K.riemannRochSpace), w ∈ W ∧
    x = w • ExteriorAlgebra.ιMulti F p (fun i => (1 : F) ⊗ₜ[ℂ] v i)}

/-- The Koszul cohomology group `K_{p,q}(C, K)` vanishes: the cycles in `⋀^p V ⊗ 𝓛(qK)` are
exactly the boundaries of `⋀^(p+1) V ⊗ 𝓛((q-1)K)`, where `V = 𝓛(K)`. When `K` is canonical
and the curve is non-hyperelliptic, `K_{p,q}(C, K) = 0` means that the graded Betti number
`β_{p,p+q}` of the canonical curve vanishes. -/
def KoszulCohomologyVanishes (K : Divisor F) (p q : ℕ) : Prop :=
  LinearMap.ker (koszulDifferential K) ⊓ koszulPiece K p ((q : ℤ) • K).riemannRochSpace =
    (koszulPiece K (p + 1) (((q : ℤ) - 1) • K).riemannRochSpace).map (koszulDifferential K)

variable (F) in
/-- **Green's conjecture.** Let $C$ be a smooth projective non-hyperelliptic curve over
$\mathbb{C}$ of genus $g \ge 4$, with function field $F$ and canonical divisor $K$. Then the
Clifford index of $C$ is determined by the linear syzygies of the canonical curve
$C \subseteq \mathbb{P}^{g-1}$:
$$\operatorname{Cliff}(C) = \min\{p : K_{p,2}(C, K_C) \neq 0\},$$
i.e. $K_{p,2}(C, K_C) = 0$ for all $p < \operatorname{Cliff}(C)$ and
$K_{\operatorname{Cliff}(C), 2}(C, K_C) \ne 0$. Equivalently, if $a(C)$ is the largest $i$ such that
the graded Betti numbers $\beta_{p,p+2}$ of the canonical curve vanish for all $p \le i$, then
$\operatorname{Cliff}(C) = a(C) + 1$. The inequality $a(C) + 1 \le \operatorname{Cliff}(C)$ is the
Green–Lazarsfeld nonvanishing theorem; the reverse inequality is the open part.

The hypothesis $g \ge 4$ excludes the degenerate cases: curves of genus $g \le 2$ are
hyperelliptic (or have no canonical embedding), and a non-hyperelliptic curve of genus $3$ is a
plane quartic, for which no divisor computes the Clifford index and $K_{p,2}(C, K_C) = 0$ for
all $p$. -/
@[category research open, AMS 13 14]
theorem greens_conjecture [Algebra (RatFunc ℂ) F] [IsScalarTower ℂ (RatFunc ℂ) F]
    [FunctionField ℂ F]
    (hg : 4 ≤ genus F) (hC : ¬ IsHyperelliptic F) (K : Divisor F) (hK : IsCanonical K) :
    IsLeast {p : ℕ | ¬ KoszulCohomologyVanishes K p 2} (cliffordIndex F) := by
  sorry

end GreensConjecture
