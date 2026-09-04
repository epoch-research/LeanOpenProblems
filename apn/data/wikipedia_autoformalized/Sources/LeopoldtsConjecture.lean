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
# Leopoldt's conjecture

Leopoldt's conjecture states that the $p$-adic regulator of a number field $K$ does not vanish.
The $p$-adic regulator is an analogue of the usual regulator, defined using $p$-adic logarithms
instead of the usual logarithms.

Precise formulation (following the Wikipedia article). Let $K$ be a number field and $p$ a
rational prime. For each prime $P$ of $K$ above $p$, let $U_{1,P}$ be the group of principal
units of the completion $K_P$, i.e. the local units $u$ with $u \equiv 1 \pmod P$, and set
$U_1 = \prod_{P \mid p} U_{1,P}$. Let $E_1$ be the group of global units $\varepsilon$ of $K$
whose image under the diagonal embedding $\varepsilon \mapsto (\varepsilon)_{P \mid p}$ lies in
$U_1$. Since $E_1$ has finite index in the unit group of $K$, it is an abelian group of rank
$r_1 + r_2 - 1$, where $r_1$ is the number of real embeddings of $K$ and $r_2$ the number of
pairs of complex embeddings. Leopoldt's conjecture states that the $\mathbb{Z}_p$-module rank of
the closure $\overline{E_1}$ of $E_1$ embedded diagonally in $U_1$ is also $r_1 + r_2 - 1$;
equivalently, the *Leopoldt defect*
$\delta_p(K) = (r_1 + r_2 - 1) - \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$ is zero.

The conjecture is known when $K$ is an abelian extension of $\mathbb{Q}$ or of an imaginary
quadratic field (Ax, Brumer).

*References:*
- [Wikipedia, Leopoldt's conjecture](https://en.wikipedia.org/wiki/Leopoldt%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- H.-W. Leopoldt, *Zur Arithmetik in abelschen Zahlkörpern*, J. Reine Angew. Math. 209 (1962),
  54–71.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer, 2008,
  Chapter X, §3.
- L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer, 1997, Chapter 5.
-/

open NumberField IsDedekindDomain HeightOneSpectrum

namespace LeopoldtsConjecture

/-- A topological group $G$ *has $\mathbb{Z}_p$-rank $r$* if it has an open subgroup which is
topologically isomorphic to $\mathbb{Z}_p^r$ (with $\mathbb{Z}_p$ written multiplicatively).

For a finitely generated $\mathbb{Z}_p$-module $M$ carrying its $p$-adic topology (for instance
any closed subgroup of the group $U_1$ of principal local units), this holds exactly when the
$\mathbb{Z}_p$-module rank of $M$ is $r$: if $M \cong \mathbb{Z}_p^r \times T$ with $T$ finite,
then $\mathbb{Z}_p^r \times \{0\}$ is an open subgroup topologically isomorphic to
$\mathbb{Z}_p^r$; conversely, a topological group isomorphism from $\mathbb{Z}_p^r$ onto an open
subgroup $H$ of $M$ is automatically $\mathbb{Z}_p$-linear, and $H$ has finite index in the
compact group $M$, so $M$ has rank $r$. -/
def HasZpRank (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [TopologicalSpace G] (r : ℕ) : Prop :=
  ∃ H : Subgroup G, IsOpen (H : Set G) ∧ Nonempty (H ≃ₜ* (Fin r → Multiplicative ℤ_[p]))

@[category test, AMS 11]
theorem hasZpRank_pi (p : ℕ) [Fact p.Prime] (r : ℕ) :
    HasZpRank p (Fin r → Multiplicative ℤ_[p]) r :=
  ⟨⊤, by simp,
    ⟨{ Subgroup.topEquiv with
        continuous_toFun := continuous_subtype_val
        continuous_invFun := continuous_id.subtype_mk _ }⟩⟩

variable (K : Type*) [Field K] [NumberField K] (p : ℕ)

/-- The primes $P$ of the number field $K$ lying above the rational prime $p$, i.e. the nonzero
prime ideals of the ring of integers $\mathcal{O}_K$ containing $p$. -/
abbrev PrimesAbove : Type _ := {P : HeightOneSpectrum (𝓞 K) // (p : 𝓞 K) ∈ P.asIdeal}

/-- The product $\prod_{P \mid p} K_P^\times$ of the multiplicative groups of the completions
$K_P$ of $K$ at the primes $P$ above $p$, with the product topology. It contains the group
$\prod_{P \mid p} U_P$ of local units and the group $U_1 = \prod_{P \mid p} U_{1,P}$ of principal
local units, and it is the target of the diagonal embedding of the global units. -/
abbrev AdicUnits : Type _ := (P : PrimesAbove K p) → (P.1.adicCompletion K)ˣ

/-- The diagonal embedding $\varepsilon \mapsto (\varepsilon)_{P \mid p}$ of the global units
$\mathcal{O}_K^\times$ of $K$ into $\prod_{P \mid p} K_P^\times$. -/
noncomputable def diagonalEmbedding : (𝓞 K)ˣ →* AdicUnits K p :=
  Pi.monoidHom fun P => Units.map (algebraMap (𝓞 K) (P.1.adicCompletion K)).toMonoidHom

/-- The group $U_1 = \prod_{P \mid p} U_{1,P}$ of principal local units, where
$U_{1,P} = \{u \in K_P^\times : v_P(u - 1) < 1\} = 1 + P\mathcal{O}_{K_P}$ is the group of
principal units of the completion $K_P$ (a subgroup of the local units
$U_P = \mathcal{O}_{K_P}^\times$). -/
def principalLocalUnits : Subgroup (AdicUnits K p) :=
  Subgroup.pi Set.univ fun P => (P.1.adicCompletionIntegers K).principalUnitGroup

/-- The group $E_1$ of global units of $K$ which map into $U_1$ under the diagonal embedding,
i.e. (see `LeopoldtsConjecture.mem_principalGlobalUnits_iff'`) the units $\varepsilon$ with
$\varepsilon \equiv 1 \pmod P$ for every prime $P$ of $K$ above $p$. It has finite index in
$\mathcal{O}_K^\times$, hence rank $r_1 + r_2 - 1$. -/
noncomputable def principalGlobalUnits : Subgroup (𝓞 K)ˣ :=
  (principalLocalUnits K p).comap (diagonalEmbedding K p)

/-- The closure $\overline{E_1}$ of the diagonal image of $E_1$ in $\prod_{P \mid p} K_P^\times$.
Since $U_1$ is closed in $\prod_{P \mid p} K_P^\times$ and contains the image of $E_1$, this is
the closure of $E_1$ embedded diagonally in $U_1$. -/
noncomputable def closurePrincipalGlobalUnits : Subgroup (AdicUnits K p) :=
  ((principalGlobalUnits K p).map (diagonalEmbedding K p)).topologicalClosure

/-- **Leopoldt's conjecture.** Let $K$ be a number field and $p$ a rational prime. Then the
$p$-adic regulator of $K$ does not vanish. Precisely, in the formulation of the Wikipedia
article: the $\mathbb{Z}_p$-module rank of the closure $\overline{E_1}$ of $E_1$ (the global
units congruent to $1$ modulo every prime of $K$ above $p$) embedded diagonally in
$U_1 = \prod_{P \mid p} U_{1,P}$ equals $r_1 + r_2 - 1$ (which is `Units.rank K`), the rank of
the unit group of $K$; that is, the Leopoldt defect $\delta_p(K)$ is $0$. The
$\mathbb{Z}_p$-rank condition is expressed by `HasZpRank`: $\overline{E_1}$ has an open subgroup
topologically isomorphic to $\mathbb{Z}_p^{r_1 + r_2 - 1}$. -/
@[category research open, AMS 11]
theorem leopoldts_conjecture [Fact p.Prime] :
    HasZpRank p (closurePrincipalGlobalUnits K p) (Units.rank K) := by
  sorry

variable {K p}

@[category API, AMS 11]
theorem mem_principalGlobalUnits_iff (ε : (𝓞 K)ˣ) :
    ε ∈ principalGlobalUnits K p ↔
      ∀ P : PrimesAbove K p, Valued.v (algebraMap (𝓞 K) (P.1.adicCompletion K) ε - 1) < 1 := by
  simp only [principalGlobalUnits, principalLocalUnits, Subgroup.mem_comap, Subgroup.mem_pi,
    Set.mem_univ, true_implies, ValuationSubring.mem_principalUnitGroup_iff]
  exact forall_congr' fun P =>
    (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.symm

/-- A global unit lies in $E_1$ if and only if it is congruent to $1$ modulo every prime of $K$
above $p$. -/
@[category API, AMS 11]
theorem mem_principalGlobalUnits_iff' (ε : (𝓞 K)ˣ) :
    ε ∈ principalGlobalUnits K p ↔ ∀ P : PrimesAbove K p, (ε : 𝓞 K) - 1 ∈ P.1.asIdeal := by
  rw [mem_principalGlobalUnits_iff]
  refine forall_congr' fun P => ?_
  rw [← valuation_lt_one_iff_mem (K := K), ← valuedAdicCompletion_eq_valuation (K := K)]
  simp only [Algebra.cast, map_sub, map_one]

end LeopoldtsConjecture
