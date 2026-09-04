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
# The spherical Bernstein's problem

The spherical Bernstein's problem, posed by Shiing-Shen Chern in 1969 (and again in his 1970 ICM
plenary address), asks:

> Are the equators in $\mathbb{S}^{n+1}$ the only smooth embedded minimal hypersurfaces which are
> topological $n$-dimensional spheres?

The answer depends on $n$. It is affirmative for $n = 2$ (Almgren–Calabi). It is negative for
$n \in \{3, 4, 5, 6, 7, 9, 11, 13\}$ (Hsiang, 1983) and for all odd $n \geq 3$ (Tomter, 1987):
in these dimensions there exist smooth embedded minimal hyperspheres in $\mathbb{S}^{n+1}$ that
are not equators. The problem remains open for all even $n \geq 8$.

Note that the Wikipedia article says that Hsiang and Tomter "proved it" in these dimensions; their
results are constructions of non-equatorial minimal hyperspheres, so the answer to the question is
negative there. The article also uses a second indexing convention (an $(n-1)$-sphere in
$\mathbb{S}^n$), in which all dimensions are shifted by one. This file uses the first convention:
the hypersurface has dimension $n$ and lives in $\mathbb{S}^{n+1} \subseteq \mathbb{R}^{n+2}$.

## Formalisation

A *smooth embedded hypersurface which is a topological $n$-sphere* is the image of a $C^\infty$
embedding $f : M \to \mathbb{S}^{n+1}$ of a smooth $n$-manifold $M$ homeomorphic to
$\mathbb{S}^n$. Mathlib has no notion of mean curvature, so *minimal* is expressed through the
first variation of area: $f$ is minimal if, for every smooth variation
$F : \mathbb{R} \times M \to \mathbb{S}^{n+1}$ with $F(0, \cdot) = f$, the derivative at $t = 0$
of the $n$-dimensional (Hausdorff) area of $F(t, M)$ vanishes. For a smooth compact embedded
hypersurface this is equivalent to the vanishing of the mean curvature.
An *equator* is the intersection of $\mathbb{S}^{n+1}$ with a hyperplane through the origin.

*References:*
- [Wikipedia, *Spherical Bernstein's problem*](https://en.wikipedia.org/wiki/spherical_Bernstein%27s_problem)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- S.-S. Chern, *Differential geometry, its past and its future*, Actes du Congrès International
  des Mathématiciens (Nice, 1970), Tome 1, 41–53.
- F. J. Almgren Jr., *Some interior regularity theorems for minimal surfaces and an extension of
  Bernstein's theorem*, Ann. of Math. (2) 84 (1966), 277–292.
- E. Calabi, *Minimal immersions of surfaces in Euclidean spheres*, J. Differential Geom. 1 (1967),
  111–125.
- W.-Y. Hsiang, *Minimal cones and the spherical Bernstein problem, I*, Ann. of Math. (2) 118
  (1983), 61–73; *II*, Invent. Math. 74 (1983), 351–369.
- P. Tomter, *The spherical Bernstein problem in even dimensions and related problems*,
  Acta Math. 158 (1987), 189–212.
-/

namespace SphericalBernsteinsProblem

open Set Manifold MeasureTheory
open scoped ContDiff EuclideanGeometry InnerProductSpace

/-- `𝕊ⁿ` is the unit sphere in `ℝ^(n + 1)`, with its standard smooth structure. -/
local macro:max "𝕊" noWs n:superscript(term) : term =>
  `(Metric.sphere (0 : EuclideanSpace ℝ (Fin ($(⟨n.raw[0]⟩) + 1))) 1)

variable {n : ℕ}

/-- A subset of `𝕊ⁿ⁺¹` is an *equator* if it is the intersection of `𝕊ⁿ⁺¹` with a hyperplane
through the origin, i.e. the set of unit vectors orthogonal to some nonzero vector `v`. -/
def IsEquator (s : Set 𝕊ⁿ⁺¹) : Prop :=
  ∃ v : ℝ^(n + 2), v ≠ 0 ∧ s = {x : 𝕊ⁿ⁺¹ | ⟪(x : ℝ^(n + 2)), v⟫_ℝ = 0}

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^n) M]

/-- A map `f : M → 𝕊ⁿ⁺¹` from an `n`-manifold `M` is *minimal* if it is a critical point of the
`n`-dimensional area functional: for every smooth variation `F : ℝ × M → 𝕊ⁿ⁺¹` of `f`
(i.e. `F (0, x) = f x` for all `x`), the derivative at `t = 0` of the `n`-dimensional Hausdorff
measure of the image of `F (t, ·)` vanishes.

For a smooth compact embedded hypersurface this is the first variation formula characterisation
of vanishing mean curvature. -/
def IsMinimal (f : M → 𝕊ⁿ⁺¹) : Prop :=
  ∀ F : ℝ × M → 𝕊ⁿ⁺¹, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ F → (∀ x, F (0, x) = f x) →
    HasDerivAt (fun t : ℝ => (μH[n] (range fun x => F (t, x))).toReal) 0 0

/-- The statement that the spherical Bernstein's problem has an affirmative answer in dimension
`n`: every smooth (`C^∞`) embedded minimal hypersurface of `𝕊ⁿ⁺¹` that is homeomorphic to `𝕊ⁿ`
is an equator. The hypersurface is given as the image of a smooth embedding `f : M → 𝕊ⁿ⁺¹`
of a smooth `n`-manifold `M` homeomorphic to `𝕊ⁿ`. The smooth structure of `M` is not required
to be the standard one, since the problem only asks for a topological sphere. -/
def ConjectureFor (n : ℕ) : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (ℝ^n) M] [IsManifold (𝓡 n) ∞ M],
    Nonempty (M ≃ₜ 𝕊ⁿ) → ∀ f : M → 𝕊ⁿ⁺¹,
      IsSmoothEmbedding (𝓡 n) (𝓡 (n + 1)) ∞ f → IsMinimal f → IsEquator (range f)

/-- **The Almgren–Calabi theorem.** The spherical Bernstein's problem has an affirmative answer for
$n = 2$: every smooth embedded minimal $2$-sphere in $\mathbb{S}^3$ is an equator. (In the
article's second formulation this is the case $n = 3$.) -/
theorem spherical_bernsteins_problem.variants.almgren_calabi : ConjectureFor 2 := by
  sorry

end SphericalBernsteinsProblem

theorem SphericalBernsteinsProblem.spherical_bernsteins_problem.variants.almgren_calabi.disproof : ¬ (type_of% @SphericalBernsteinsProblem.spherical_bernsteins_problem.variants.almgren_calabi) := sorry
