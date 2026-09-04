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

@[category API, AMS 52]
theorem finiteDensity_nonneg (X : Set (ℝ^n)) (r : ℝ) : 0 ≤ finiteDensity X r := by
  unfold finiteDensity
  positivity

@[category API, AMS 52]
theorem finiteDensity_le_one (X : Set (ℝ^n)) (r : ℝ) : finiteDensity X r ≤ 1 :=
  div_le_one_of_le₀
    (ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono Set.inter_subset_right))
    ENNReal.toReal_nonneg

@[category API, AMS 52]
theorem density_nonneg (X : Set (ℝ^n)) : 0 ≤ density X :=
  le_limsup_of_frequently_le (Frequently.of_forall (finiteDensity_nonneg X))
    (isBoundedUnder_of ⟨1, finiteDensity_le_one X⟩)

@[category API, AMS 52]
theorem density_le_one (X : Set (ℝ^n)) : density X ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le _ (finiteDensity_nonneg X))
    (Eventually.of_forall (finiteDensity_le_one X))

@[category test, AMS 52]
theorem isPacking_empty : IsPacking (∅ : Set (ℝ^n)) :=
  Set.pairwise_empty _

@[category test, AMS 52]
theorem density_empty : density (∅ : Set (ℝ^n)) = 0 := by
  have : finiteDensity (∅ : Set (ℝ^n)) = fun _ => 0 := by
    ext r
    simp [finiteDensity]
  rw [density, this, limsup_const]

@[category API, AMS 52]
theorem packingConstant_nonneg (n : ℕ) : 0 ≤ packingConstant n :=
  le_csSup_of_le ⟨1, by rintro _ ⟨X, -, rfl⟩; exact density_le_one X⟩
    ⟨∅, isPacking_empty, rfl⟩ (density_nonneg _)

@[category API, AMS 52]
theorem packingConstant_le_one (n : ℕ) : packingConstant n ≤ 1 :=
  csSup_le ⟨_, ∅, isPacking_empty, rfl⟩ (by rintro _ ⟨X, -, rfl⟩; exact density_le_one X)

/-- Every lattice packing is a packing, so $\Delta_n^{(L)} \le \Delta_n$. -/
@[category API, AMS 11 52]
theorem latticePackingConstant_le_packingConstant (n : ℕ) :
    latticePackingConstant n ≤ packingConstant n := by
  by_cases h : ∃ X : Set (ℝ^n), IsLatticePacking X
  · refine csSup_le_csSup ⟨1, ?_⟩ (h.elim fun X hX => ⟨_, X, hX, rfl⟩)
      (Set.image_mono fun X hX => hX.1)
    rintro _ ⟨X, -, rfl⟩
    exact density_le_one X
  · push_neg at h
    have : {X : Set (ℝ^n) | IsLatticePacking X} = ∅ := Set.eq_empty_of_forall_notMem h
    simp only [latticePackingConstant, this, Set.image_empty, Real.sSup_empty]
    exact packingConstant_nonneg n

/--
**Conway–Sloane conjecture** [CoSl95, Sl98]: for every dimension $1 \le n \le 9$ the densest
sphere packing in $\mathbb{R}^n$ is no denser than the densest lattice packing, i.e.
$\Delta_n = \Delta_n^{(L)}$.

The densest lattice packings are known for $n \le 8$ (the root lattices
$A_1, A_2, A_3, D_4, D_5, E_6, E_7, E_8$), while $\Delta_9^{(L)}$ is unknown. The optimal packing
among all packings is known only in dimensions $1, 2, 3, 8$ and $24$, where it is a lattice
packing, so the conjecture is known for $n = 1, 2, 3, 8$ and open for $n = 4, 5, 6, 7, 9$. In
the open cases $n = 4, 5, 6, 7$ the conjecture asserts that $\Delta_n$ equals the density of
$D_4, D_5, E_6, E_7$ respectively, namely $\pi^2/16$, $\pi^2/(15\sqrt{2})$,
$\pi^3/(48\sqrt{3})$, $\pi^3/105$.
-/
@[category research open, AMS 11 52]
theorem sphere_packing (n : ℕ) (hn : n ∈ Finset.Icc 1 9) :
    packingConstant n = latticePackingConstant n := by
  sorry

/--
It is possible that in some dimension the densest sphere packing is irregular (that is, not a
lattice packing): there is some $n$ with $\Delta_n^{(L)} < \Delta_n$.

Some support for this comes from dimension $10$, where the densest known packing, the
non-lattice packing $P_{10c}$ of Best, is denser than the densest known lattice packing [Sl98].
-/
@[category research open, AMS 11 52]
theorem sphere_packing.variants.irregular :
    ∃ n : ℕ, latticePackingConstant n < packingConstant n := by
  sorry

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
@[category research open, AMS 52]
theorem sphere_packing.variants.torquato_stillinger_lower_bound :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 6) * 2 ^ (-((3 - logb 2 (exp 1)) * n / 2)) ≤
        packingConstant n := by
  sorry

end SpherePacking
