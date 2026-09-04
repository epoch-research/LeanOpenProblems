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
# Sphere packing

The sphere packing problem asks for the largest fraction $\Delta_n$ of $\mathbb{R}^n$ that can be
covered by non-overlapping congruent balls. The value of $\Delta_n$ is known only for
$n = 1, 2, 3, 8, 24$. Its value in the remaining dimensions and its asymptotic behaviour as
$n \to \infty$ are open.

A packing of unit balls is described by its set of centres $X \subseteq \mathbb{R}^n$, where
distinct centres are at distance at least $2$. Following [Vi17], its (upper) density is
$$\Delta_X = \limsup_{r \to \infty}
  \frac{\mathrm{vol}\big(\bigcup_{x \in X} B(x, 1) \cap B(0, r)\big)}{\mathrm{vol}(B(0, r))}.$$
The sphere packing constant $\Delta_n$ is the supremum of $\Delta_X$ over all packings, and the
lattice sphere packing constant $\Delta_n^{(L)}$ is the supremum over the packings whose centres
form a lattice. Since density is invariant under scaling, fixing the radius to be $1$ loses no
generality.

This file states the following conjectures.

- The Conway–Sloane conjecture that $\Delta_n = \Delta_n^{(L)}$ for all $n \le 9$ [CoSl95, Sl98].
- The conjecture that in some dimension the densest packing is irregular, i.e.
  $\Delta_n^{(L)} < \Delta_n$ for some $n$.
- The Torquato–Stillinger conjectural lower bound
  $\Delta_n \ge \phi_* \sim 3.276\ldots \cdot n^{1/6} \cdot 2^{-(3 - \log_2 e) n / 2}$, an
  exponential improvement on Minkowski's bound $2^{-n}$ [ToSt06].

*References:*
- [Wikipedia, Sphere packing](https://en.wikipedia.org/wiki/Sphere_packing)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Sl98] N. J. A. Sloane, *The Sphere-Packing Problem*, Documenta Mathematica, Extra Volume ICM
  1998, III, 387–396. [arXiv:math/0207256](https://arxiv.org/abs/math/0207256)
- [CoSl95] J. H. Conway and N. J. A. Sloane, *What are all the best sphere packings in low
  dimensions?*, Discrete Comput. Geom. 13 (1995), 383–403.
- [ToSt06] S. Torquato and F. H. Stillinger, *New conjectural lower bounds on the optimal density
  of sphere packings*, Experimental Mathematics 15 (2006), 307–331.
  [arXiv:math/0508381](https://arxiv.org/abs/math/0508381)
- [Vi17] M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185
  (2017), 991–1015. [arXiv:1603.04246](https://arxiv.org/abs/1603.04246)
-/

open MeasureTheory Metric Filter Real
open scoped EuclideanGeometry

namespace SpherePacking

variable {n : ℕ}

/--
A set `X` of points of $\mathbb{R}^n$ is the set of centres of a (unit) sphere packing if any two
distinct points of `X` are at distance at least `2`, i.e. the open unit balls centred at the points
of `X` are pairwise disjoint.
-/
def IsPacking (X : Set (ℝ^n)) : Prop :=
  X.Pairwise fun x y => 2 ≤ dist x y

/--
A set `X` of points of $\mathbb{R}^n$ is the set of centres of a lattice sphere packing if it is
the set of centres of a sphere packing and it is a (full rank) lattice in $\mathbb{R}^n$, i.e. a
discrete additive subgroup spanning $\mathbb{R}^n$.
-/
def IsLatticePacking (X : Set (ℝ^n)) : Prop :=
  IsPacking X ∧
    ∃ (L : Submodule ℤ (ℝ^n)) (_ : DiscreteTopology L),
      IsZLattice ℝ L ∧ (L : Set (ℝ^n)) = X

/--
The finite density of the packing with centres `X` at radius `r`: the fraction of the ball of
radius `r` around the origin that is covered by the open unit balls centred at the points of `X`.
-/
noncomputable def finiteDensity (X : Set (ℝ^n)) (r : ℝ) : ℝ :=
  (volume ((⋃ x ∈ X, ball x 1) ∩ ball 0 r)).toReal / (volume (ball (0 : ℝ^n) r)).toReal

/--
The density of the packing with centres `X`, defined as the limit superior of the finite densities
as the radius tends to infinity, as in [Vi17].
-/
noncomputable def density (X : Set (ℝ^n)) : ℝ :=
  limsup (finiteDensity X) atTop

/--
The sphere packing constant $\Delta_n$: the supremum of the densities of all sphere packings in
$\mathbb{R}^n$.
-/
noncomputable def packingConstant (n : ℕ) : ℝ :=
  sSup (density '' {X : Set (ℝ^n) | IsPacking X})

/--
The lattice sphere packing constant $\Delta_n^{(L)}$: the supremum of the densities of all lattice
sphere packings in $\mathbb{R}^n$.
-/
noncomputable def latticePackingConstant (n : ℕ) : ℝ :=
  sSup (density '' {X : Set (ℝ^n) | IsLatticePacking X})

/--
**Torquato–Stillinger conjectural lower bound** [ToSt06, Section 5]: for large $n$,
$$\Delta_n \ge \phi_* \sim \frac{3.276100896 \cdot n^{1/6}}{2^{0.7786524795\ldots n}},$$
where the exponent is exactly $(3 - \log_2 e)/2$. This would be an exponential improvement on
Minkowski's lower bound $\Delta_n \ge 2^{-n}$. The bound is conditional on the conjecture of
[ToSt06] characterising the pair correlation functions of disordered sphere packings in high
dimensions.

Since the leading constant is only determined numerically, we state the bound with an unspecified
positive constant $c$: there is $c > 0$ such that
$\Delta_n \ge c \cdot n^{1/6} \cdot 2^{-(3 - \log_2 e) n / 2}$ for all sufficiently large $n$.
-/
theorem sphere_packing.variants.torquato_stillinger_lower_bound :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 6) * 2 ^ (-((3 - logb 2 (exp 1)) * n / 2)) ≤
        packingConstant n := by
  sorry

end SpherePacking

theorem SpherePacking.sphere_packing.variants.torquato_stillinger_lower_bound.disproof : ¬ (type_of% @SpherePacking.sphere_packing.variants.torquato_stillinger_lower_bound) := sorry
