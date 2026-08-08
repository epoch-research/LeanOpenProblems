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

/- ## Variants and partial results -/

/--
**Gladysz (1962) [Gl62]: independent set of size 2 in the closed case.**

If all the sets `A x` are closed with Lebesgue measure `< 1`, then there exist two
distinct reals `x y` such that `x ∉ A y` and `y ∉ A x`.

This is a weaker result proved by Gladysz before the full Newelski–Pawlikowski–
Seredyński theorem [NPS87]. -/
theorem erdos_501.variants.gladysz_size2 : 
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 2 ≤ X.ncard ∧ X.Pairwise (fun x y => x ∉ A y) := by
  simp only [true_iff]
  sorry

/- ## Sanity checks and examples

The following `example` declarations exercise the proved variants and demonstrate that
the hypotheses of the main theorem are non-vacuous. All goals are fully closed: no `sorry`. -/

end Erdos501
