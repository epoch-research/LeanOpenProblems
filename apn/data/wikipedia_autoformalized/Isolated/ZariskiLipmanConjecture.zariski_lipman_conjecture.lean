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
# Zariski–Lipman conjecture

Let $V$ be a complex algebraic variety with coordinate ring $R$. The Zariski–Lipman conjecture
states that if the $R$-module $\operatorname{Der}_{\mathbb{C}}(R)$ of $\mathbb{C}$-linear
derivations of $R$ is free, then $V$ is smooth.

We model the affine variety $V$ by its coordinate ring $R$, a reduced finitely generated
$\mathbb{C}$-algebra, and "$V$ is smooth" by `Algebra.Smooth ℂ R`. Since $\mathbb{C}$ is a
perfect field, a finitely generated $\mathbb{C}$-algebra is smooth over $\mathbb{C}$ if and only
if all of its local rings are regular, i.e. if and only if $V$ is nonsingular.

The conjecture is often phrased locally: if $R$ is the local ring of a point on a complex
algebraic variety and $\operatorname{Der}_{\mathbb{C}}(R)$ is free, then $R$ is regular. The
local and the affine formulations are equivalent, since the formation of derivations commutes
with localization for finitely generated algebras.

*References:*
- [Wikipedia, Nakai conjecture](https://en.wikipedia.org/wiki/Zariski%E2%80%93Lipman_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J. Lipman, *Free derivation modules on algebraic varieties*, Amer. J. Math. 87 (1965), 874–898.
-/

namespace ZariskiLipmanConjecture

/--
The **Zariski–Lipman conjecture**: for a complex algebraic variety $V$ with coordinate ring $R$,
if the derivations of $R$ are a free module over $R$, then $V$ is smooth.

Here $V$ is an affine variety over $\mathbb{C}$, so its coordinate ring $R$ is a reduced
finitely generated $\mathbb{C}$-algebra; "derivations of $R$" means the $R$-module
$\operatorname{Der}_{\mathbb{C}}(R) = \operatorname{Der}_{\mathbb{C}}(R, R)$ of
$\mathbb{C}$-linear derivations $R \to R$; and "$V$ is smooth" means that $R$ is a smooth
$\mathbb{C}$-algebra.
-/
theorem zariski_lipman_conjecture (R : Type*) [CommRing R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] [IsReduced R] [Module.Free R (Derivation ℂ R R)] :
    Algebra.Smooth ℂ R := by
  sorry

end ZariskiLipmanConjecture

theorem ZariskiLipmanConjecture.zariski_lipman_conjecture.disproof : ¬ (type_of% @ZariskiLipmanConjecture.zariski_lipman_conjecture) := sorry
