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
# Hilbert–Arnold problem

The Hilbert–Arnold problem asks whether there is a uniform bound on the number of limit cycles
in generic finite-parameter families of vector fields on the two-sphere $S^2$. More precisely:
is it true that, for a generic family of smooth vector fields on $S^2$, smoothly parameterised
by a compact set $B$ in a finite-dimensional Euclidean space $\mathbb{R}^k$, the number of limit
cycles of the members of the family is bounded uniformly in the parameter (by a bound that may
depend on the family)? The problem was posed by Arnold and Ilyashenko in the 1980s in connection
with Hilbert's sixteenth problem.

In this file a vector field on $S^2 \subseteq \mathbb{R}^3$ is described in ambient coordinates,
as a map $w : \mathbb{R}^3 \to \mathbb{R}^3$ tangent to $S^2$ along $S^2$; only the values of
$w$ on the sphere matter. A limit cycle is a closed orbit (a periodic trajectory which is not an
equilibrium) that is isolated in the set of closed orbits. A smooth $k$-parameter family with
compact base $B \subseteq \mathbb{R}^k$ is a smooth map $B \times S^2 \to TS^2$, i.e. the
restriction to $B \times S^2$ of a smooth map $\mathbb{R}^k \times \mathbb{R}^3 \to \mathbb{R}^3$
tangent to $S^2$ for the parameters in $B$. The space of families carries the $C^\infty$
topology, and "generic" means: on a residual set (a set containing a dense $G_\delta$ set).

*References:*
- [Wikipedia, Hilbert–Arnold problem](https://en.wikipedia.org/wiki/Hilbert%E2%80%93Arnold_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- Yu. Ilyashenko, *Centennial history of Hilbert's 16th problem*, Bull. Amer. Math. Soc. 39
  (2002), 301–354.
-/

open Set
open scoped ContDiff EuclideanGeometry InnerProductSpace UniformConvergence

namespace HilbertArnoldProblem

/-- The unit sphere $S^2 \subseteq \mathbb{R}^3$. -/
local notation "𝕊²" => Metric.sphere (0 : ℝ^3) 1

/-- `γ : ℝ → ℝ³` is an integral curve on the sphere of the vector field `w`: it stays on the
sphere and solves $\gamma'(t) = w(\gamma(t))$ for all $t$. -/
def IsIntegralCurveOnSphere (w : ℝ^3 → ℝ^3) (γ : ℝ → ℝ^3) : Prop :=
  (∀ t, γ t ∈ 𝕊²) ∧ ∀ t, HasDerivAt γ (w (γ t)) t

/-- `C` is a closed orbit of `w` on the sphere: the trajectory of a periodic integral curve on the
sphere which is not an equilibrium point. -/
def IsClosedOrbit (w : ℝ^3 → ℝ^3) (C : Set (ℝ^3)) : Prop :=
  ∃ γ : ℝ → ℝ^3, IsIntegralCurveOnSphere w γ ∧ (∃ T, 0 < T ∧ Function.Periodic γ T) ∧
    range γ = C ∧ C.Nontrivial

/-- `C` is a limit cycle of `w` on the sphere: a closed orbit which is isolated in the set of
closed orbits, i.e. some neighbourhood of `C` contains no other closed orbit. -/
def IsLimitCycle (w : ℝ^3 → ℝ^3) (C : Set (ℝ^3)) : Prop :=
  IsClosedOrbit w C ∧ ∃ U, IsOpen U ∧ C ⊆ U ∧ ∀ C', IsClosedOrbit w C' → C' ⊆ U → C' = C

/-- The number of limit cycles of the vector field `w` on the sphere (possibly infinite). -/
noncomputable def numLimitCycles (w : ℝ^3 → ℝ^3) : ℕ∞ :=
  {C | IsLimitCycle w C}.encard

/-- Being an integral curve on the sphere only depends on the values of the vector field on the
sphere. -/
@[category API, AMS 34 37]
theorem isIntegralCurveOnSphere_congr {w w' : ℝ^3 → ℝ^3} (h : EqOn w w' 𝕊²) {γ : ℝ → ℝ^3} :
    IsIntegralCurveOnSphere w γ ↔ IsIntegralCurveOnSphere w' γ := by
  refine ⟨fun ⟨hγ, hd⟩ => ⟨hγ, fun t => ?_⟩, fun ⟨hγ, hd⟩ => ⟨hγ, fun t => ?_⟩⟩
  · rw [← h (hγ t)]
    exact hd t
  · rw [h (hγ t)]
    exact hd t

/-- Being a closed orbit only depends on the values of the vector field on the sphere. -/
@[category API, AMS 34 37]
theorem isClosedOrbit_congr {w w' : ℝ^3 → ℝ^3} (h : EqOn w w' 𝕊²) {C : Set (ℝ^3)} :
    IsClosedOrbit w C ↔ IsClosedOrbit w' C := by
  simp only [IsClosedOrbit, isIntegralCurveOnSphere_congr h]

/-- Being a limit cycle only depends on the values of the vector field on the sphere. -/
@[category API, AMS 34 37]
theorem isLimitCycle_congr {w w' : ℝ^3 → ℝ^3} (h : EqOn w w' 𝕊²) {C : Set (ℝ^3)} :
    IsLimitCycle w C ↔ IsLimitCycle w' C := by
  simp only [IsLimitCycle, isClosedOrbit_congr h]

/-- The number of limit cycles only depends on the values of the vector field on the sphere. -/
@[category API, AMS 34 37]
theorem numLimitCycles_congr {w w' : ℝ^3 → ℝ^3} (h : EqOn w w' 𝕊²) :
    numLimitCycles w = numLimitCycles w' := by
  simp only [numLimitCycles, isLimitCycle_congr h]

/-- The zero vector field has no closed orbits. -/
@[category test, AMS 34 37]
theorem not_isClosedOrbit_zero (C : Set (ℝ^3)) : ¬ IsClosedOrbit 0 C := by
  rintro ⟨γ, ⟨-, hd⟩, -, rfl, x, ⟨s, rfl⟩, y, ⟨t, rfl⟩, hxy⟩
  exact hxy <| is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

/-- The zero vector field has no limit cycles. -/
@[category test, AMS 34 37]
theorem numLimitCycles_zero : numLimitCycles 0 = 0 := by
  simp [numLimitCycles, IsLimitCycle, not_isClosedOrbit_zero]

section SmoothMap

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The type of smooth ($C^\infty$) maps from `E` to `F`, carrying the $C^\infty$ topology. -/
def SmoothMap : Type _ := {f : E → F // ContDiff ℝ ∞ f}

instance : FunLike (SmoothMap E F) E F where
  coe f := f.1
  coe_injective' := Subtype.val_injective

/-- The $C^\infty$ topology on smooth maps: the coarsest topology for which, for every `n`, the
`n`-th derivative `f ↦ D^n f` is continuous into the space of maps with the topology of uniform
convergence on compact sets. That is, `fᵢ → f` iff all derivatives of `fᵢ` converge uniformly on
compact sets to the corresponding derivatives of `f`. -/
instance : TopologicalSpace (SmoothMap E F) :=
  ⨅ n : ℕ, TopologicalSpace.induced
    (fun f : SmoothMap E F => UniformOnFun.ofFun {K : Set E | IsCompact K} (iteratedFDeriv ℝ n f))
    inferInstance

variable {E F}

/-- For every `n`, the `n`-th derivative is continuous from the $C^\infty$ topology into the
topology of uniform convergence on compact sets. -/
@[category API, AMS 46]
theorem continuous_iteratedFDeriv (n : ℕ) :
    Continuous fun f : SmoothMap E F =>
      UniformOnFun.ofFun {K : Set E | IsCompact K} (iteratedFDeriv ℝ n f) :=
  continuous_iInf_dom (i := n) continuous_induced_dom

/-- Evaluation at a point is continuous for the $C^\infty$ topology. -/
@[category API, AMS 46]
theorem continuous_eval (x : E) : Continuous fun f : SmoothMap E F => f x := by
  have h1 : Continuous fun g : E →ᵤ[{K : Set E | IsCompact K}] (E [×0]→L[ℝ] F) =>
      UniformOnFun.toFun _ g x :=
    (UniformOnFun.uniformContinuous_eval_of_mem _ _ (mem_singleton x)
      isCompact_singleton).continuous
  have h2 := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp
    (h1.comp (continuous_iteratedFDeriv (E := E) (F := F) 0))
  convert h2 using 2

end SmoothMap

variable (k : ℕ) (B : Set (ℝ^k))

/-- A representative of a `k`-parameter family of vector fields on the sphere with parameter
base `B ⊆ ℝ^k`: a smooth map `v : ℝ^k × ℝ³ → ℝ³` such that for every parameter `ε ∈ B`, the
vector field `x ↦ v (ε, x)` is tangent to the sphere along the sphere. It carries the
$C^\infty$ topology. -/
abbrev FamilyRep : Type :=
  {v : SmoothMap (ℝ^k × ℝ^3) (ℝ^3) // ∀ ε ∈ B, ∀ x ∈ 𝕊², ⟪v (ε, x), x⟫_ℝ = 0}

/-- Two representatives define the same family of vector fields on the sphere iff they agree
on `B × 𝕊²`. -/
instance familySetoid : Setoid (FamilyRep k B) where
  r v w := EqOn (⇑v.1) (⇑w.1) (B ×ˢ 𝕊²)
  iseqv := ⟨fun _ => eqOn_refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The space of smooth `k`-parameter families of vector fields on the sphere with parameter
base `B ⊆ ℝ^k`, i.e. smooth maps `B × 𝕊² → T𝕊²`, with the $C^\infty$ topology (the quotient
topology induced from the $C^\infty$ topology on the ambient representatives). -/
abbrev Family : Type := Quotient (familySetoid k B)

variable {k B}

/-- The vector field `x ↦ v (ε, x)` at the parameter `ε` of the family `v`. -/
def FamilyRep.field (v : FamilyRep k B) (ε : ℝ^k) : ℝ^3 → ℝ^3 :=
  fun x => v.1 (ε, x)

/-- Whether the members of a family have a common bound on their number of limit cycles does
not depend on the choice of representative. -/
@[category API, AMS 34 37]
theorem exists_forall_numLimitCycles_le_congr {v w : FamilyRep k B} (h : v ≈ w) :
    (∃ N : ℕ, ∀ ε ∈ B, numLimitCycles (v.field ε) ≤ N) ↔
      ∃ N : ℕ, ∀ ε ∈ B, numLimitCycles (w.field ε) ≤ N := by
  refine exists_congr fun N => forall₂_congr fun ε hε => ?_
  have : EqOn (v.field ε) (w.field ε) 𝕊² := fun x hx => h ⟨hε, hx⟩
  rw [numLimitCycles_congr this]

/-- A family of vector fields on the sphere has *uniformly bounded limit cycles* if there is
`N` such that every member of the family has at most `N` limit cycles. -/
def HasUniformlyBoundedLimitCycles (F : Family k B) : Prop :=
  Quotient.lift (fun v : FamilyRep k B => ∃ N : ℕ, ∀ ε ∈ B, numLimitCycles (v.field ε) ≤ N)
    (fun _ _ h => propext (exists_forall_numLimitCycles_le_congr h)) F

/-- Unfolding `HasUniformlyBoundedLimitCycles` on a representative. -/
@[category API, AMS 34 37]
theorem hasUniformlyBoundedLimitCycles_mk (v : FamilyRep k B) :
    HasUniformlyBoundedLimitCycles ⟦v⟧ ↔ ∃ N : ℕ, ∀ ε ∈ B, numLimitCycles (v.field ε) ≤ N :=
  Iff.rfl

/--
**Hilbert–Arnold problem.**
Is there a uniform bound on the number of limit cycles in generic finite-parameter families of
vector fields on the sphere? That is: is it true that for every $k$ and every compact set
$B \subseteq \mathbb{R}^k$, the set of smooth families of vector fields on $S^2$ with parameter
base $B$ whose members have a uniformly bounded number of limit cycles is residual (contains a
dense $G_\delta$ set) in the space of all such families with the $C^\infty$ topology?
-/
@[category research open, AMS 34 37]
theorem hilbert_arnold_problem :
    answer(sorry) ↔ ∀ (k : ℕ) (B : Set (ℝ^k)), IsCompact B →
      {F : Family k B | HasUniformlyBoundedLimitCycles F} ∈ residual (Family k B) := by
  sorry

end HilbertArnoldProblem
