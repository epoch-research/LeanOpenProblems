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
# Cartan–Hadamard conjecture

A *Cartan–Hadamard manifold* is a complete, simply connected Riemannian manifold with
nonpositive sectional curvature. The Cartan–Hadamard conjecture asks whether the classical
isoperimetric inequality of Euclidean space extends to these manifolds: for every bounded
domain $\Omega$ in a Cartan–Hadamard manifold $M$ of dimension $n \geq 2$,
$$\operatorname{per}(\Omega)^n \geq
  \frac{\operatorname{per}(\mathbf{B}^n)^n}{\operatorname{vol}(\mathbf{B}^n)^{n-1}}
  \operatorname{vol}(\Omega)^{n-1},$$
where $\mathbf{B}^n$ is the unit ball of $\mathbb{R}^n$. In words: the perimeter of $\Omega$ is
at least the perimeter of a Euclidean ball of the same volume. The conjecture is known for
$n = 2$ (Weil, 1926), $n = 3$ (Kleiner, 1992) and $n = 4$ (Croke, 1984), and open for $n \geq 5$.

## Formalisation notes

Mathlib has no sectional curvature, Riemannian volume or perimeter, so we use classical
equivalent metric formulations.

* Riemannian manifold: `M` is a `C^∞` manifold modelled on `ℝ^n` with a `C^∞` Riemannian
  metric, and `M` is a `MetricSpace` whose distance is the Riemannian distance
  (`IsRiemannianManifold`). Finiteness of the distance forces `M` to be connected.
* Nonpositive curvature: by the Cartan–Hadamard theorem and Alexandrov's characterisation of
  nonpositive sectional curvature ([BH1999], Theorems II.1A.6 and II.4.1), a complete connected
  Riemannian manifold is simply connected with nonpositive sectional curvature if and only if its
  distance makes it a `CAT(0)` space, and a geodesic metric space (such as a complete connected
  Riemannian manifold, by Hopf–Rinow) is `CAT(0)` if and only if it satisfies the `CN` inequality
  of Bruhat and Tits ([BH1999], Chapter II.1, Exercise 1.9). This is `SatisfiesCNInequality`
  below. The `CN` inequality already implies simple connectivity; `SimplyConnectedSpace M` is
  kept as an explicit hypothesis to match the usual definition.
* Volume and perimeter: $\operatorname{vol}(\Omega)$ is the $n$-dimensional Hausdorff measure
  of $\Omega$ and $\operatorname{per}(\Omega)$ is the $(n-1)$-dimensional Hausdorff measure of
  the topological boundary of $\Omega$, both for the Riemannian distance. Mathlib's Hausdorff
  measures differ from the Riemannian volume and from the area of hypersurfaces by constants
  depending only on the dimension. The same constants appear in the Euclidean quantities
  $\operatorname{per}(\mathbf{B}^n)$ and $\operatorname{vol}(\mathbf{B}^n)$, which are also
  computed as Hausdorff measures in `ℝ^n`, so they cancel and the inequality is unchanged.
* Domains: $\Omega$ ranges over all open subsets of $M$ with compact closure. For a domain with
  piecewise $C^1$ boundary the Hausdorff measure of the boundary is the perimeter; for a general
  open set it is at least the perimeter (De Giorgi–Federer), and the statement for smooth domains
  implies the one for sets of finite perimeter by approximation. Hence this formulation is
  equivalent to the one for bounded sets of finite perimeter in [GS2022], Problem 2. Domains with
  infinite boundary measure satisfy the inequality trivially.

*References:*
- [Wikipedia, Cartan–Hadamard conjecture](https://en.wikipedia.org/wiki/Cartan%E2%80%93Hadamard_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [GS2022] M. Ghomi, J. Spruck, *Total curvature and the isoperimetric inequality in
  Cartan–Hadamard manifolds*, J. Geom. Anal. 32 (2022),
  [arXiv:1908.09814](https://arxiv.org/abs/1908.09814).
- [KK2019] B. Kloeckner, G. Kuperberg, *The Cartan–Hadamard conjecture and the Little Prince*,
  Rev. Mat. Iberoam. 35 (2019), [arXiv:1303.3115](https://arxiv.org/abs/1303.3115).
- [BH1999] M. Bridson, A. Haefliger, *Metric spaces of non-positive curvature*, Springer, 1999.
-/

open Bundle Metric
open scoped ContDiff EuclideanGeometry Manifold MeasureTheory

namespace CartanHadamardConjecture

/--
A metric space `X` satisfies the **`CN` inequality** of Bruhat and Tits if for all points
`p q r : X` and every midpoint `m` of `q` and `r` (that is, `dist q m = dist m r = dist q r / 2`),
$$2\, d(p, m)^2 + \tfrac{1}{2}\, d(q, r)^2 \leq d(p, q)^2 + d(p, r)^2.$$
In a Euclidean space this holds with equality (Apollonius' theorem). A geodesic metric space
satisfies it if and only if it is `CAT(0)` ([BH1999], Chapter II.1, Exercise 1.9), and a complete
connected Riemannian manifold satisfies it if and only if it is simply connected with nonpositive
sectional curvature ([BH1999], Theorems II.1A.6 and II.4.1).
-/
def SatisfiesCNInequality (X : Type*) [MetricSpace X] : Prop :=
  ∀ p q r m : X, dist q m = dist q r / 2 → dist m r = dist q r / 2 →
    2 * dist p m ^ 2 + dist q r ^ 2 / 2 ≤ dist p q ^ 2 + dist p r ^ 2

/-- A real inner product space satisfies the `CN` inequality (with equality). -/
@[category test, AMS 51 53]
theorem satisfiesCNInequality_of_innerProductSpace (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : SatisfiesCNInequality V := by
  intro p q r m hqm hmr
  obtain rfl : m = midpoint ℝ q r := eq_midpoint_of_dist_eq_half hqm hmr
  rw [EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq]
  nlinarith

/--
**Cartan–Hadamard conjecture.** Can the classical isoperimetric inequality for subsets of
Euclidean space be extended to spaces of nonpositive curvature, known as Cartan–Hadamard
manifolds (complete simply connected Riemannian manifolds of nonpositive sectional curvature)?

Precisely: is it true that for every $n \geq 2$, every Cartan–Hadamard manifold $M$ of
dimension $n$ and every bounded domain $\Omega \subseteq M$ (an open set with compact closure),
$$\operatorname{per}(\Omega)^n \geq
  \frac{\operatorname{per}(\mathbf{B}^n)^n}{\operatorname{vol}(\mathbf{B}^n)^{n-1}}
  \operatorname{vol}(\Omega)^{n-1},$$
where $\mathbf{B}^n$ is the unit ball of $\mathbb{R}^n$, so that
$\operatorname{per}(\mathbf{B}^n) = \operatorname{vol}(\mathbf{S}^{n-1})$? Equivalently, is the
perimeter of $\Omega$ at least the perimeter of a Euclidean ball of the same volume?

Here `M` is a `C^∞` Riemannian `n`-manifold whose distance is the Riemannian distance,
nonpositive sectional curvature is expressed by `SatisfiesCNInequality M`, the volume is the
$n$-dimensional Hausdorff measure and the perimeter is the $(n-1)$-dimensional Hausdorff measure
of the topological boundary, all for the Riemannian distance of $M$; see the module docstring.
The inequality is written in cross-multiplied form, with all quantities in `ℝ≥0∞`.
The restriction $n \geq 2$ excludes the trivial one-dimensional case $M = \mathbb{R}$. The answer
is known to be positive for $n = 2, 3, 4$.
-/
@[category research open, AMS 49 53]
theorem cartan_hadamard_conjecture :
    answer(sorry) ↔ ∀ n : ℕ, 2 ≤ n →
      ∀ (M : Type*) [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (ℝ^n) M] [IsManifold (𝓡 n) ∞ M]
        [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]
        [IsContMDiffRiemannianBundle (𝓡 n) ∞ (ℝ^n) (fun x : M ↦ TangentSpace (𝓡 n) x)]
        [IsRiemannianManifold (𝓡 n) M] [CompleteSpace M] [SimplyConnectedSpace M],
        SatisfiesCNInequality M →
      ∀ Ω : Set M, IsOpen Ω → IsCompact (closure Ω) →
        μH[(n : ℝ) - 1] (sphere (0 : ℝ^n) 1) ^ n * μH[n] Ω ^ (n - 1) ≤
          μH[(n : ℝ) - 1] (frontier Ω) ^ n * μH[n] (ball (0 : ℝ^n) 1) ^ (n - 1) := by
  sorry

end CartanHadamardConjecture
