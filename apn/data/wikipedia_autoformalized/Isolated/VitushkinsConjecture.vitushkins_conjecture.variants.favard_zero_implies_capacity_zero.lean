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
# Vitushkin's conjecture

Let $K \subset \mathbb{C}$ be compact. The *analytic capacity* of $K$ is
$$\gamma(K) = \sup\{|f'(\infty)| :\ f \in \mathcal{H}^\infty(\mathbb{C} \setminus K),\
\|f\|_\infty \le 1,\ f(\infty) = 0\},$$
where $\mathcal{H}^\infty(U)$ is the set of bounded analytic functions $U \to \mathbb{C}$,
$f(\infty) = \lim_{z \to \infty} f(z)$ and $f'(\infty) = \lim_{z \to \infty} z (f(z) - f(\infty))$.
The *Favard length* of $K$ is
$$\operatorname{Fav}(K) = \int_0^\pi \mathcal{H}^1(\operatorname{proj}_\theta(K))\,d\theta,$$
where $\operatorname{proj}_\theta(x, y) = x \cos\theta + y \sin\theta$ is the orthogonal
projection in direction $\theta$ and $\mathcal{H}^1$ is the one-dimensional Hausdorff measure.

Vitushkin conjectured that for every compact $K \subset \mathbb{C}$
$$\gamma(K) = 0 \iff \operatorname{Fav}(K) = 0.$$
Mattila [Ma86] showed that this is false in general, without identifying the failing direction.
Jones and Murai [JM88] then constructed a compact set with zero Favard length and positive
analytic capacity, disproving the direction $\operatorname{Fav}(K) = 0 \Rightarrow \gamma(K) = 0$.
The results of David [Da98] and Tolsa [To03] imply that the conjecture holds when $K$ is
$\mathcal{H}^1$-$\sigma$-finite. The remaining direction, $\gamma(K) = 0 \Rightarrow
\operatorname{Fav}(K) = 0$ (equivalently, positive Favard length implies positive analytic
capacity), is open; see Chang and Tolsa [CT20] for partial progress.

*References:*
- [Wikipedia, Analytic capacity](https://en.wikipedia.org/wiki/Analytic_capacity%23Vitushkin%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Ma86] Mattila, P., *Smooth maps, null-sets for integralgeometric measure and analytic
  capacity*, Ann. of Math. 123 (1986), 303–309.
- [JM88] Jones, P. W. and Murai, T., *Positive analytic capacity but zero Buffon needle
  probability*, Pacific J. Math. 133 (1988), 99–114.
- [Da98] David, G., *Unrectifiable 1-sets have vanishing analytic capacity*,
  Rev. Mat. Iberoamericana 14 (1998), 369–479.
- [To03] Tolsa, X., *Painlevé's problem and the semiadditivity of analytic capacity*,
  Acta Math. 190 (2003), 105–149.
- [CT20] Chang, A. and Tolsa, X., *Analytic capacity and projections*,
  J. Eur. Math. Soc. 22 (2020), 4121–4159. [arXiv:1712.00594](https://arxiv.org/abs/1712.00594)
-/

open Filter MeasureTheory Topology
open scoped ENNReal Real

namespace VitushkinsConjecture

/--
`IsAdmissible K f` says that `f` is a competitor in the definition of the analytic capacity of
`K`: it is holomorphic on $\mathbb{C} \setminus K$, bounded by $1$ there, and satisfies
$f(\infty) := \lim_{z \to \infty} f(z) = 0$. The values of `f` on `K` play no role.
-/
structure IsAdmissible (K : Set ℂ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f Kᶜ
  norm_le_one : ∀ z ∈ Kᶜ, ‖f z‖ ≤ 1
  tendsto_zero : Tendsto f (cocompact ℂ) (𝓝 0)

/--
The **analytic capacity** of a set $K \subset \mathbb{C}$:
$$\gamma(K) = \sup\{|f'(\infty)| : f \in \mathcal{H}^\infty(\mathbb{C} \setminus K),\
\|f\|_\infty \le 1,\ f(\infty) = 0\},$$
where $f'(\infty) := \lim_{z \to \infty} z (f(z) - f(\infty)) = \lim_{z \to \infty} z f(z)$.
The supremum is taken over the values $\|a\|$ for which some admissible `f` satisfies
$z f(z) \to a$ as $z \to \infty$. For compact `K` this limit exists for every admissible `f`,
and the set of such values is bounded, so `sSup` is the genuine supremum.
-/
noncomputable def analyticCapacity (K : Set ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (f : ℂ → ℂ) (a : ℂ), IsAdmissible K f ∧
    Tendsto (fun z => z * f z) (cocompact ℂ) (𝓝 a) ∧ r = ‖a‖}

/--
The orthogonal projection $\operatorname{proj}_\theta(x, y) = x \cos \theta + y \sin \theta$ of
the plane onto the line through the origin in direction $\theta$, identified with $\mathbb{R}$.
-/
noncomputable def proj (θ : ℝ) (z : ℂ) : ℝ := z.re * Real.cos θ + z.im * Real.sin θ

/--
The **Favard length** of a set $K \subset \mathbb{C}$:
$$\operatorname{Fav}(K) = \int_0^\pi \mathcal{H}^1(\operatorname{proj}_\theta(K))\,d\theta,$$
where $\mathcal{H}^1$ is the one-dimensional Hausdorff measure on $\mathbb{R}$.
-/
noncomputable def favardLength (K : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Icc 0 π, μH[1] (proj θ '' K)

/--
The refuted direction of Vitushkin's conjecture: it is **not** true that every compact
$K \subset \mathbb{C}$ with zero Favard length has zero analytic capacity. Jones and Murai [JM88]
constructed a compact set with
$$\int_0^\pi \mathcal{H}^1(\operatorname{proj}_\theta(K))\,d\theta = 0 \quad\text{and}\quad
\gamma(K) > 0.$$
By `vitushkins_conjecture.variants.sigma_finite`, such a set is not
$\mathcal{H}^1$-$\sigma$-finite.
-/
theorem vitushkins_conjecture.variants.favard_zero_implies_capacity_zero :
    ∃ K : Set ℂ, IsCompact K ∧ favardLength K = 0 ∧ 0 < analyticCapacity K := by
  sorry

end VitushkinsConjecture

theorem VitushkinsConjecture.vitushkins_conjecture.variants.favard_zero_implies_capacity_zero.disproof : ¬ (type_of% @VitushkinsConjecture.vitushkins_conjecture.variants.favard_zero_implies_capacity_zero) := sorry
