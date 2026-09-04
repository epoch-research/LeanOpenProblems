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
# Reinhardt's conjecture

Reinhardt's conjecture (1934), found independently by Mahler (1947), states that the
*smoothed octagon* has the lowest maximum packing density of all centrally symmetric convex
plane sets.

The smoothed octagon is obtained from a regular octagon by replacing each corner with an arc
of a hyperbola that is tangent to the two sides adjacent to the corner and asymptotic to the two
sides adjacent to these. Its maximum packing density is
$$\frac{8 - 4\sqrt 2 - \ln 2}{2\sqrt 2 - 1} \approx 0.902414,$$
which is slightly less than the maximum packing density $\pi/\sqrt{12} \approx 0.906899$ of the
circular disk.

Following [HV24], the maximum (or *greatest*) packing density $\delta(K)$ of a convex disk $K$
is the supremum of the densities of all packings of the plane by congruent copies of $K$.
By a theorem of L. Fejes Tóth [FT50], for a centrally symmetric convex disk it coincides with
the greatest *lattice* packing density $\delta_L(K)$, so the conjecture can equivalently be
stated for lattice packings, which is how Reinhardt originally formulated it.

*References:*
- [Wikipedia, Smoothed octagon](https://en.wikipedia.org/wiki/Reinhardt%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Re34] Reinhardt, K., *Über die dichteste gitterförmige Lagerung kongruenter Bereiche in der
  Ebene und eine besondere Art konvexer Kurven*, Abh. Math. Sem. Univ. Hamburg 10 (1934),
  216–230.
- [Ma47] Mahler, K., *On the minimum determinant and the circumscribed hexagons of a convex
  domain*, Indag. Math. 9 (1947), 326–337.
- [FT50] Fejes Tóth, L., *Some packing and covering theorems*, Acta Sci. Math. Szeged 12
  (1950), 62–67.
- [HV24] Hales, T., Vajjha, K., *Packings of Smoothed Polygons*,
  [arXiv:2405.04331](https://arxiv.org/abs/2405.04331), Section 2.2.
-/

namespace ReinhardtsConjecture

open MeasureTheory Filter Topology Real
open scoped EuclideanGeometry Pointwise

/-
## Centrally symmetric convex disks and packings
-/

/-- A set $K \subseteq \mathbb{R}^2$ is a **centrally symmetric convex disk** if it is compact,
convex, has nonempty interior, and is symmetric about some point $c$, i.e. $2c - v \in K$
whenever $v \in K$.

This is the class $\mathfrak{K}_{ccs}$ of [HV24], except that the centre of symmetry is not
required to be the origin; this makes no difference since packing densities are invariant under
translations. The nonempty interior condition excludes degenerate sets (such as segments), all
of whose packings have density $0$. -/
def IsCentrallySymmetricConvexDisk (K : Set ℝ²) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧ ∃ c : ℝ², ∀ v ∈ K, (2 : ℝ) • c - v ∈ K

/-- A family `P` of subsets of the plane is a **packing by congruent copies of `K`** if every
member of `P` is a congruent copy of `K`, i.e. the image `g '' K` of `K` under an isometry `g`
of the plane, and any two distinct members of `P` do not overlap, i.e. have disjoint
interiors. -/
def IsPacking (K : Set ℝ²) (P : Set (Set ℝ²)) : Prop :=
  (∀ K' ∈ P, ∃ g : ℝ² ≃ᵢ ℝ², K' = g '' K) ∧
    P.Pairwise fun K₁ K₂ => Disjoint (interior K₁) (interior K₂)

/-- The proportion of the disk $B_r$ of radius `r` about the origin that is covered by the
members of the family `P`, namely
$$\frac{1}{\operatorname{area}(B_r)} \sum_{K' \in P} \operatorname{area}(K' \cap B_r).$$ -/
noncomputable def coveredProportion (P : Set (Set ℝ²)) (r : ℝ) : ℝ :=
  (∑' K' : P, volume ((K' : Set ℝ²) ∩ Metric.ball 0 r)).toReal /
    (volume (Metric.ball (0 : ℝ²) r)).toReal

/-- A family `P` of subsets of the plane **has density `d`** if the proportion of the disk $B_r$
covered by `P` tends to `d` as $r \to \infty$. Equivalently, the upper and lower densities of
`P` (the $\limsup$ and $\liminf$ of these proportions) both exist and coincide, in which case
their common value is the density of `P` [HV24]. -/
def HasDensity (P : Set (Set ℝ²)) (d : ℝ) : Prop :=
  Tendsto (coveredProportion P) atTop (𝓝 d)

/-- The **greatest packing density** $\delta(K)$ of a set $K \subseteq \mathbb{R}^2$ is the
supremum of the densities of all packings of the plane by congruent copies of $K$ whose density
exists [HV24].

The empty family is a packing of density $0$, and every packing has density at most $1$, so for
a convex disk $K$ this is the supremum of a nonempty set bounded above. -/
noncomputable def packingDensity (K : Set ℝ²) : ℝ :=
  sSup {d | ∃ P, IsPacking K P ∧ HasDensity P d}

/-- The translates $K + l$, $l \in L$, of `K` by the vectors of the `ℤ`-submodule `L` form a
**lattice packing** if any two distinct translates have disjoint interiors. -/
def IsLatticePacking (K : Set ℝ²) (L : Submodule ℤ ℝ²) : Prop :=
  (L : Set ℝ²).Pairwise fun l l' => Disjoint (interior (l +ᵥ K)) (interior (l' +ᵥ K))

/-- The **greatest lattice packing density** $\delta_L(K)$ of a set $K \subseteq \mathbb{R}^2$
is the supremum of $\operatorname{area}(K) / \det(L)$ over all lattices `L` (discrete
`ℤ`-submodules of full rank) such that the translates of `K` by `L` form a packing [HV24].
Here $\det(L)$ is the covolume of `L`, i.e. the area of a fundamental domain. -/
noncomputable def latticePackingDensity (K : Set ℝ²) : ℝ :=
  sSup {d | ∃ (L : Submodule ℤ ℝ²) (_ : DiscreteTopology L), IsZLattice ℝ L ∧
    IsLatticePacking K L ∧ d = (volume K).toReal / ZLattice.covolume L}

/-
## The smoothed octagon

We follow the construction on Wikipedia, translated so that the octagon is centred at the
origin. Start with the regular octagon of circumradius $\sqrt 2$ centred at the origin, with
vertices $\sqrt 2 (\cos(k\pi/4), \sin(k\pi/4))$, $k = 0, \dots, 7$. The corner at the vertex
$(\sqrt 2, 0)$ is replaced by an arc of the hyperbola
$$\ell^2 (x - 2 - \sqrt 2)^2 - y^2 = m^2, \qquad \ell = \sqrt 2 - 1,\quad m = (1/2)^{1/4},$$
which is tangent to the two sides $y = \pm(\sqrt 2 + 1)(x - \sqrt 2)$ of the octagon at this
vertex and asymptotic to the lines $y = \pm(\sqrt 2 - 1)(x - 2 - \sqrt 2)$ containing the two
sides adjacent to these. The other seven corners are treated in the same way, by rotating this
arc about the origin through the angles $k\pi/4$.
-/

/-- The hyperbolic arc that replaces the corner at the vertex $(\sqrt 2, 0)$ of the regular
octagon of circumradius $\sqrt 2$ centred at the origin. With $\ell = \sqrt 2 - 1$ and
$m = (1/2)^{1/4}$, it is the portion $-\frac{\ln 2}{4} \le t \le \frac{\ln 2}{4}$ of the branch
$$t \mapsto \left(2 + \sqrt 2 - \frac{m}{\ell} \cosh t,\ m \sinh t\right)$$
of the hyperbola $\ell^2 (x - 2 - \sqrt 2)^2 - y^2 = m^2$. Its endpoints
$\left(\frac{4 + \sqrt 2}{4}, \pm\frac{2 - \sqrt 2}{4}\right)$ are the points where the
hyperbola touches the two sides of the octagon adjacent to the vertex $(\sqrt 2, 0)$.

We use the closed parameter interval so that the arc contains its two points of tangency. -/
noncomputable def smoothedOctagonArc : Set ℝ² :=
  (fun t : ℝ => !₂[2 + √2 - (1 / 2 : ℝ) ^ (1 / 4 : ℝ) / (√2 - 1) * cosh t,
    (1 / 2 : ℝ) ^ (1 / 4 : ℝ) * sinh t]) '' Set.Icc (-(log 2 / 4)) (log 2 / 4)

/-- The **smoothed octagon** of Reinhardt, centred at the origin: the convex hull of the eight
hyperbolic arcs obtained by rotating `smoothedOctagonArc` about the origin through the angles
$k\pi/4$, $k = 0, \dots, 7$.

Its boundary consists of these eight arcs together with the eight straight segments of the sides
of the regular octagon between the endpoints of consecutive arcs, so it is exactly the regular
octagon of circumradius $\sqrt 2$ with each corner clipped by a hyperbolic arc. -/
noncomputable def smoothedOctagon : Set ℝ² :=
  convexHull ℝ (⋃ k : Fin 8,
    EuclideanGeometry.o.rotation (((k : ℕ) : ℝ) * (π / 4) : ℝ) '' smoothedOctagonArc)

/-
## Sanity checks
-/

/-
## The conjecture
-/

/-- **Reinhardt's conjecture**, with the explicit value of the greatest packing density of the
smoothed octagon: every centrally symmetric convex disk $K$ in the plane satisfies
$$\delta(K) \ge \frac{8 - 4\sqrt 2 - \ln 2}{2\sqrt 2 - 1} \approx 0.902414.$$
By `packingDensity_smoothedOctagon` this is equivalent to `reinhardts_conjecture`. -/
theorem reinhardts_conjecture.variants.explicit_bound (K : Set ℝ²)
    (hK : IsCentrallySymmetricConvexDisk K) :
    (8 - 4 * √2 - log 2) / (2 * √2 - 1) ≤ packingDensity K := by
  sorry

end ReinhardtsConjecture

theorem ReinhardtsConjecture.reinhardts_conjecture.variants.explicit_bound.disproof : ¬ (type_of% @ReinhardtsConjecture.reinhardts_conjecture.variants.explicit_bound) := sorry
