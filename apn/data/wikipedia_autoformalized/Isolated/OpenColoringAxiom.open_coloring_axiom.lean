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
# Open coloring axiom

The open coloring axiom (OCA) is an axiom about colorings of the pairs of a set of reals.
Two versions were introduced, by Abraham, Rubin and Shelah [ARS85] and by Todorčević [To89].
The version spelled out in the Wikipedia article, and formalized here, is Todorčević's.

**Todorčević's open coloring axiom.** Let $X \subseteq \mathbb{R}$ and color each pair of
distinct elements of $X$ either white or black, so that the set of white pairs is open in
$X \times X$. Then either
- $X$ has an uncountable subset all of whose pairs are white, or
- $X$ is the union of countably many subsets, each of which has all of its pairs black.

Wikipedia's list of unsolved problems asks: *Is OCA (the open coloring axiom) consistent with
$2^{\aleph_0} > \aleph_2$?* Todorčević's OCA implies that the bounding number $\mathfrak{b}$
equals $\aleph_2$, hence $2^{\aleph_0} \geq \aleph_2$; it is open whether the continuum can be
strictly larger than $\aleph_2$ in a model of OCA. (For the Abraham–Rubin–Shelah version the
analogous question was answered positively by Gilton and Neeman [GN22].)

## Formalization notes

- **Colorings as graphs.** A black/white coloring of the pairs of $X$ is recorded as a
  `SimpleGraph X` whose edges are the white pairs. White-homogeneous sets are cliques
  (`SimpleGraph.IsClique`) and black-homogeneous sets are independent sets
  (`SimpleGraph.IsIndepSet`). The openness hypothesis is that the adjacency relation is an open
  subset of `X × X`, where `X` carries the subspace topology of `ℝ`. Since the diagonal is closed
  in `X × X`, this is the same as openness of the set of white pairs in the complete graph on `X`.
- **Countable partitions.** "A partition of $X$ into countably many black-homogeneous sets" is
  recorded as a cover of $X$ by an `ℕ`-indexed family of independent sets. This is equivalent:
  a subset of an independent set is independent, so any such cover can be refined to a partition,
  and a finite or countable family can be re-indexed by `ℕ` (repeating sets or using `∅`).
- **Consistency placeholder.** The question is a *relative consistency* question
  (does $\mathrm{ZFC} + \mathrm{OCA} + 2^{\aleph_0} > \aleph_2$ have a model?). Lean works inside
  one fixed model of its set theory and Mathlib has no syntactic first-order theory of ZFC, so
  this cannot be expressed directly. Following the convention used elsewhere in this repository
  (e.g. `Erdos1175.erdos_1175.variants.shelah_consistency`), the problem is recorded as an
  `answer(sorry)` placeholder equivalent to the conjunction `OCA ∧ ℵ₂ < 𝔠`; the intended
  mathematical content is the model-theoretic statement
  $\mathrm{Con}(\mathrm{ZFC}) \to
  \mathrm{Con}(\mathrm{ZFC} + \mathrm{OCA} + 2^{\aleph_0} > \aleph_2)$.

*References:*
- [Wikipedia, Open coloring axiom](https://en.wikipedia.org/wiki/open_coloring_axiom)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [ARS85] Abraham, U., Rubin, M., Shelah, S., *On the consistency of some partition theorems for
  continuous colorings, and the structure of ℵ₁-dense real order types*,
  Ann. Pure Appl. Logic 29 (1985), 123–206.
- [To89] Todorčević, S., [*Partition problems in topology*](https://archive.org/details/partitionproblem0000todo),
  Contemporary Mathematics 84, American Mathematical Society (1989).
- [Mo10] Moore, J. T., [*The proper forcing axiom*](https://www.math.cornell.edu/~justin/Ftp/ICM.pdf),
  Proceedings of the International Congress of Mathematicians (ICM 2010), Vol. II, 3–29.
- [GN22] Gilton, T., Neeman, I., *Abraham–Rubin–Shelah open colorings and a large continuum*,
  J. Math. Log. 22 (2022).
-/

open Cardinal
open scoped Cardinal

namespace OpenColoringAxiom

/--
**Todorčević's open coloring axiom** (OCA).

For every set of reals $X$ and every coloring of the pairs of distinct elements of $X$ in black
and white such that the set of white pairs is open in $X \times X$, either
- there is an uncountable $Y \subseteq X$ all of whose pairs are white, or
- $X$ is a countable union of sets all of whose pairs are black.

The coloring is recorded as a graph `G : SimpleGraph X` whose edges are the white pairs, so the
openness hypothesis says that `{p : X × X | G.Adj p.1 p.2}` is open in `X × X`,
white-homogeneous sets are cliques of `G`, and black-homogeneous sets are independent sets of `G`.
-/
def OCA : Prop :=
  ∀ (X : Set ℝ) (G : SimpleGraph X), IsOpen {p : X × X | G.Adj p.1 p.2} →
    (∃ Y : Set X, ¬ Y.Countable ∧ G.IsClique Y) ∨
    (∃ Y : ℕ → Set X, (∀ n, G.IsIndepSet (Y n)) ∧ ⋃ n, Y n = Set.univ)

/--
Is OCA (the open coloring axiom) consistent with $2^{\aleph_0} > \aleph_2$?

Here OCA is Todorčević's open coloring axiom `OCA`, and `𝔠 = 2 ^ ℵ₀` is the cardinality of
the continuum, so `ℵ_ 2 < 𝔠` is the statement $2^{\aleph_0} > \aleph_2$. OCA implies
$\mathfrak{b} = \aleph_2$, so $\mathfrak{c} \geq \aleph_2$ in every model of OCA; the question
is whether the continuum can be strictly larger.

**Formalization caveat (consistency placeholder).** The question is a relative consistency
statement: it asks whether $\mathrm{Con}(\mathrm{ZFC})$ implies
$\mathrm{Con}(\mathrm{ZFC} + \mathrm{OCA} + 2^{\aleph_0} > \aleph_2)$. Lean works inside a single
fixed model of its set theory and has no syntactic first-order theory ZFC available, so
consistency cannot be expressed directly. Following the repository convention for such questions
(see `Erdos1175.erdos_1175.variants.shelah_consistency`), the question is recorded as an
`answer(sorry)` placeholder for the proposition `OCA ∧ ℵ_ 2 < 𝔠` that a witnessing model must
satisfy: `answer(True)` corresponds to a positive answer ("yes, it is consistent") and
`answer(False)` to a negative one (OCA refutes $2^{\aleph_0} > \aleph_2$).
-/
theorem open_coloring_axiom : (OCA ∧ (ℵ_ 2 : Cardinal.{0}) < 𝔠) := by
  sorry

/- ## Sanity checks for `OCA` -/

end OpenColoringAxiom

theorem OpenColoringAxiom.open_coloring_axiom.disproof : ¬ (type_of% @OpenColoringAxiom.open_coloring_axiom) := sorry
