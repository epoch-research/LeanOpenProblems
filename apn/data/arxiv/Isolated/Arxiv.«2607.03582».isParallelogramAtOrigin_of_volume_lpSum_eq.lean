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
# Planar $L_p$-Rogers-Shephard, the equality case

*Reference:* [arxiv/2607.03582](https://arxiv.org/abs/2607.03582)
**$L_p$-Rogers-Shephard type inequalities for $L_p$-zonoids and symmetric bodies**
by *Matthieu Fradelizi, Auttawich Manui, Mark Meyer, Cheikh Saliou Ndiaye*

Corollary 29 bounds $|K \oplus_p -K|$ against $|K|$ for planar convex bodies with a centre of
symmetry containing the origin, and notes that parallelograms with a vertex at the origin
attain it. Conjecture 5 asks whether they are the only bodies that do.
-/

open MeasureTheory Real

open scoped EuclideanGeometry

namespace Arxiv.«2607.03582»

/-- The support function $h_K(u) = \sup_{x \in K} \langle x, u\rangle$. -/
noncomputable def supportFunction (K : Set ℝ²) (u : ℝ²) : ℝ := ⨆ x : K, inner ℝ (x : ℝ²) u

/-- The Firey $L_p$-sum $K \oplus_p L$, equation (4) of the source: the body whose support
function is $(h_K^p + h_L^p)^{1/p}$.

The source defines it by that support function, which needs both bodies to contain the origin.
Here it is the intersection of the halfspaces the support function cuts out, which agrees with
the source's set on the bodies the statements below quantify over and needs no separate
existence argument. -/
noncomputable def lpSum (p : ℝ) (K L : Set ℝ²) : Set ℝ² :=
  {x | ∀ u : ℝ², inner ℝ x u ≤ (supportFunction K u ^ p + supportFunction L u ^ p) ^ (1 / p)}

/-- $K$ has a centre of symmetry: some $c$ with $K$ invariant under reflection in $c$. -/
def HasCentreOfSymmetry (K : Set ℝ²) : Prop := ∃ c : ℝ², ∀ x, x ∈ K ↔ (2 • c - x) ∈ K

/-- The constant of Corollary 29, $\frac{2\Gamma(1+1/q)^2}{\Gamma(1+2/q)} + 2$. -/
noncomputable def rsConstant (q : ℝ) : ℝ :=
  2 * Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q) + 2

/-- $K$ is a parallelogram with a vertex at the origin: the convex hull of $0$, $a$, $b$ and
$a + b$ for linearly independent $a$, $b$. -/
def IsParallelogramAtOrigin (K : Set ℝ²) : Prop :=
  ∃ a b : ℝ², LinearIndependent ℝ ![a, b] ∧ K = convexHull ℝ {0, a, b, a + b}

/--
**Conjecture 5 (Fradelizi-Manui-Meyer-Ndiaye, 2026).** Among planar convex bodies with a
centre of symmetry containing the origin, for $p > 1$, equality in Corollary 29 holds only for
parallelograms with a vertex at the origin.
-/
theorem isParallelogramAtOrigin_of_volume_lpSum_eq :
    ∀ (K : Set ℝ²), Convex ℝ K → IsCompact K → (interior K).Nonempty →
      HasCentreOfSymmetry K → (0 : ℝ²) ∈ K → ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
        volume (lpSum p K (-K)) = ENNReal.ofReal (rsConstant q) * volume K →
          IsParallelogramAtOrigin K := by
  sorry

end Arxiv.«2607.03582»

theorem Arxiv.«2607.03582».isParallelogramAtOrigin_of_volume_lpSum_eq.disproof : ¬ (type_of% @Arxiv.«2607.03582».isParallelogramAtOrigin_of_volume_lpSum_eq) := sorry
