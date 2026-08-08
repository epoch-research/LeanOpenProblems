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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 501

*References:*
- [erdosproblems.com/501](https://www.erdosproblems.com/501)
- [Er61] Erdős, Paul, Some unsolved problems. Magyar Tud. Akad. Mat. Kutató Int. Közl. 6
  (1961), 221-254.
- [ErHa71] Erdős, Paul and Hajnal, András, Unsolved problems in set theory. Axiomatic Set
  Theory, Proc. Sympos. Pure Math. XIII Part I (1971), 17-48.
- [ErHa60] Erdős, Paul and Hajnal, András. On some combinatorial problems involving
  complete graphs. Acta Math. Acad. Sci. Hungar. (1960), 395-424.
- [Gl62] Gladysz, S. Some topological properties of independent sets. Colloq. Math. (1962).
- [He72] Hechler, S. H. A dozen small uncountable cardinals. TOPO 72, Lecture Notes
  in Math. (1972), 207-218.
- [NPS87] Newelski, L., Pawlikowski, J., and Seredyński, F. Infinite independent sets in
  the closed case. Acta Math. Acad. Sci. Hungar. (1987).
-/

open Set MeasureTheory
open scoped Cardinal ENNReal

namespace Erdos501

/- ## Setup

For every `x : ℝ` we are given a set `A x ⊆ ℝ`. We say that `X ⊆ ℝ` is an
**independent set** for the family `A` if `x ∉ A y` for all distinct `x y ∈ X`.
This is exactly `X.Pairwise (fun x y => x ∉ A y)`; we inline this rather than
introducing a custom predicate so that all `Set.Pairwise` lemmas apply.

The problem concerns outer measure `< 1` on ℝ. For a set `s : Set ℝ` we use
`(MeasureTheory.volume.toOuterMeasure) s`, which equals the Lebesgue outer measure
of `s` (defined for all sets, whether measurable or not). The condition `< 1` is
stated in `ℝ≥0∞` (extended non-negative reals). -/

/- ## Main open problem -/

/--
For every $x \in \mathbb{R}$ let $A_x \subset \mathbb{R}$ be a bounded set with outer measure
$< 1$. Must there exist an infinite independent set, that is, some infinite $X \subseteq
\mathbb{R}$ such that $x \notin A_y$ for all $x \neq y \in X$?

If the sets $A_x$ are closed and have measure $< 1$, then must there exist an independent set
of size $3$?

Known results: Erdős–Hajnal [ErHa60] proved the existence of arbitrarily large finite
independent sets. Hechler [He72] showed the answer is **no** assuming the continuum
hypothesis. -/
theorem erdos_501 : 
    ∀ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) →
      (∀ x, volume.toOuterMeasure (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  sorry

/- ## Variants and partial results -/

/- ## Sanity checks and examples

The following `example` declarations exercise the proved variants and demonstrate that
the hypotheses of the main theorem are non-vacuous. All goals are fully closed: no `sorry`. -/

end Erdos501
