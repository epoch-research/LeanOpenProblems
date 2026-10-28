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
# Borsuk's conjecture

In 1933 Karol Borsuk [Bo33] asked whether every bounded subset of $\mathbb{R}^n$ can be
partitioned into $n + 1$ sets, each of strictly smaller diameter. The hypothesis that the
answer is positive became known as **Borsuk's conjecture**.

The conjecture is true for $n = 2$ [Bo33] and $n = 3$ [Pe47, Eg55]. It is false in general:
Kahn and Kalai [KK93] disproved it for $n = 1325$ and for all $n > 2014$. Bondarenko [Bo14]
gave a counterexample in dimension $65$, and Jenrich and Brouwer [JB14] one in dimension $64$,
the smallest refereed counterexample. In 2026 Grinsztajn [Gr26] posted a 321-point
counterexample in dimension $63$, obtained with AI assistance and verified by exact
computation; the same configuration was found independently by Konz and by Ji [Ji26]. In
September 2026 an internal OpenAI model gave a compact counterexample in dimension $9$
[OAI26]: the set of rank-one orthogonal projectors on $\mathbb{R}^4$, viewed in the
nine-dimensional affine space of trace-one symmetric $4 \times 4$ matrices with the Frobenius
metric, has diameter $\sqrt{2}$ and cannot be covered by $10$ sets of smaller diameter. The
paper extends this to every dimension $n \geq 9$ (Corollary 7.1); see
`borsuk_conjecture.not_of_nine_le`. The linked Lean proof establishes the case $n = 9$.
The cases $4 \leq n \leq 8$ are open. In dimension $4$, every bounded set can be
partitioned into $9$ parts of smaller diameter [La82], and a 2026 preprint reduces this to $8$
parts [TV26].

Erdős Problem 505 (`FormalConjectures.ErdosProblems.«505»`) points to this file.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Borsuk%27s_conjecture)
- [Bo33] Borsuk, K. (1933). *Drei Sätze über die n-dimensionale euklidische Sphäre*.
  Fundamenta Mathematicae 20, 177–190. https://doi.org/10.4064/fm-20-1-177-190
- [Pe47] Perkal, J. (1947). *Sur la subdivision des ensembles en parties de diamètre inférieur*.
  Colloquium Mathematicum 2, 45.
- [Eg55] Eggleston, H. G. (1955). *Covering a three-dimensional set with sets of smaller
  diameter*. Journal of the London Mathematical Society 30, 11–24.
  https://doi.org/10.1112/jlms/s1-30.1.11
- [La82] Lassak, M. (1982). *An estimate concerning Borsuk partition problem*.
  Bulletin of the Polish Academy of Sciences, Mathematics 30(9–10), 449–451.
- [KK93] Kahn, J., Kalai, G. (1993). *A counterexample to Borsuk's conjecture*.
  Bulletin of the American Mathematical Society 29(1), 60–62.
  https://arxiv.org/abs/math/9307229
- [Bo14] Bondarenko, A. (2014). *On Borsuk's conjecture for two-distance sets*.
  Discrete & Computational Geometry 51(3), 509–515. https://doi.org/10.1007/s00454-014-9579-4
- [JB14] Jenrich, T., Brouwer, A. E. (2014). *A 64-dimensional counterexample to Borsuk's
  conjecture*. Electronic Journal of Combinatorics 21(4), P4.29. https://doi.org/10.37236/4069
- [Gr26] Grinsztajn, M. (2026). *A 63-dimensional counterexample to Borsuk's conjecture*.
  Proof note and verification script, https://github.com/maaxgrin/borsuk-63-counterexample
- [Ji26] Ji, Y. (2026). *An AI generated counterexample to Borsuk problem in dimension 63*.
  https://arxiv.org/abs/2608.12561 (withdrawn as a duplicate of [Gr26])
- [TV26] Tolmachev, A., Voronov, V. (2026). *Reducing the upper bound for the Borsuk number
  in $\mathbb{R}^4$ to 8*. https://arxiv.org/abs/2605.19068
- [OAI26] OpenAI (2026). *A nine-dimensional counterexample to Borsuk's covering assertion*.
  OpenAI Math Release preprint.
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf
- [OP28a] Tao, T. et al., *Optimization problems*, constant 28a (smallest Borsuk
  counterexample dimension). https://teorth.github.io/optimizationproblems/constants/28a.html
- [Ka15] Kalai, G. (2015). *Some old and new problems in combinatorial geometry I: Around
  Borsuk's problem*. https://arxiv.org/abs/1505.04952
-/

open Metric Bornology

open scoped EuclideanGeometry

namespace Borsuk

variable {E : Type*} [PseudoEMetricSpace E]

/--
`HasBorsukCover k s` means that the set `s` can be covered by `k` sets, each of strictly
smaller extended diameter than `s`.

We use the extended diameter `Metric.ediam` rather than `Metric.diam`: the latter takes the
junk value `0` on unbounded sets, which would make `Set.univ` a covering set of "small"
diameter. With `Metric.ediam`, a set of diameter `0` has no Borsuk cover, and an unbounded
set has no finite Borsuk cover, matching Borsuk's formulation for bounded sets with at
least two points.
-/
def HasBorsukCover (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

/--
**Borsuk's conjecture** in dimension `n`: every bounded subset of $\mathbb{R}^n$ with at
least two points can be partitioned into $n + 1$ sets of strictly smaller diameter.
-/
def BorsukConjecture (n : ℕ) : Prop :=
  ∀ s : Set (ℝ^n), IsBounded s → s.Nontrivial → HasBorsukCover (n + 1) s

/-- **Borsuk's conjecture** in dimension $4$, the smallest open case. -/
theorem borsuk_conjecture.four : BorsukConjecture 4 := by
  sorry

end Borsuk

theorem Borsuk.borsuk_conjecture.four.disproof : ¬ (type_of% @Borsuk.borsuk_conjecture.four) := sorry
