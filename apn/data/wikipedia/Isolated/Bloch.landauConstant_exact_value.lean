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
# Bloch and Landau constants

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Bloch%27s_theorem_(complex_analysis))
- [CP96] Chen, H., Gauthier, P. M. "On Bloch's constant." Journal d'Analyse Mathématique 69 (1996),
  275–291.
- [AG37] Ahlfors, L. V., Grunsky, H. "Über die Blochsche Konstante." Mathematische Zeitschrift 42
  (1937), 671–673.
- [Ya95] Yanagihara, H. "On the locally univalent Bloch constant." Journal d'Analyse Mathématique
  65 (1995), 1–17.
- [Ra43] Rademacher, H. "On the Bloch-Landau Constant."" American Journal of Mathematics 65 (1943),
  387–390.
- [OptimizationConstants](https://teorth.github.io/optimizationproblems/constants/57c.html)
- [Skin2009] Skinner, Brian. The univalent Bloch constant problem. Complex Variables and Elliptic
  Equations 54 (2009), no. 10, 951–955.
- [MathWorld](https://mathworld.wolfram.com/BlochConstant.html)
- [Bhowmik–Sen](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/improved-bloch-and-landau-constants-for-meromorphic-functions/FD465D1F2CEF7E8C62AFF16C3E89B7B4)
-/
open scoped Topology ENNReal
open Metric Set Filter
namespace Bloch

/-- The **Bloch radius** $B_f$ of a function $f$ is the supremum of radii of univalent disks in the
image of the unit disk under $f$. Takes values in `ℝ≥0∞` so that functions whose image contains
arbitrarily large univalent disks correctly get radius `⊤` rather than `0`. -/
noncomputable def blochRadius (f : ℂ → ℂ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {r : ℝ | ∃ S ⊆ ball (0 : ℂ) 1, ∃ x, ball x r ⊆ f '' S ∧ InjOn f S})

/-- The **Landau radius** $L_f$ of a function $f$ is the supremum of radii of disks contained in
the image of the unit disk under $f$. Takes values in `ℝ≥0∞` so that functions with unbounded
image correctly get radius `⊤`. -/
noncomputable def landauRadius (f : ℂ → ℂ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {r : ℝ | ∃ x, ball x r ⊆ f '' (ball (0 : ℂ) 1)})

/-- The **Bloch constant** $B$ is the largest radius such that every holomorphic function on the
unit disk with $f'(0) = 1$ has a schlicht (univalent) disk of that radius in its image. -/
noncomputable def blochConstant : ℝ :=
  sSup {B : ℝ | ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) → deriv f 0 = 1 →
    ∃ S ⊆ ball 0 1, ∃ x, ball x B ⊆ f '' S ∧ InjOn f S}

/-- The **Univalent Bloch constant** $B_u$ is the largest radius such that every univalent
holomorphic function on the unit disk with $f'(0) = 1$ has a schlicht disk of that radius in its
image. -/
noncomputable def univalentBlochConstant : ℝ :=
  sSup {B : ℝ | ∀ f : ℂ → ℂ, InjOn f (ball 0 1) → DifferentiableOn ℂ f (ball 0 1) →
    deriv f 0 = 1 → ∃ S ⊆ ball 0 1, ∃ x, ball x B ⊆ f '' S ∧ InjOn f S}

/-- The **Landau constant** $L$ is the largest radius such that every holomorphic function on the
unit disk with $f'(0) = 1$ has a disk of that radius contained in its image. -/
noncomputable def landauConstant : ℝ :=
  sSup {B : ℝ | ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) → deriv f 0 = 1 →
    ∃ x, ball x B ⊆ f '' (ball 0 1)}

/-- In [Ra43], Rademacher says that he strongly believed that this upper bound is the precise value
of the Landau constant. -/
theorem landauConstant_exact_value :
    landauConstant = Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
  sorry

end Bloch
