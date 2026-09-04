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
# Hadwiger conjecture (combinatorial geometry)

The Hadwiger conjecture (also called the Levi–Hadwiger conjecture or the Hadwiger–Levi covering
problem) states that every convex body in $\mathbb{R}^n$ can be covered by $2^n$ or fewer smaller
positively homothetic copies of itself, and that $2^n$ copies are needed if and only if the body
is a parallelepiped.

Here a convex body is a compact convex set with nonempty interior, as in the primary
literature. The Wikipedia article states the covering bound for all bounded convex sets; for
convex bodies this is equivalent to covering $K$ by $2^n$ translates of its interior.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Hadwiger conjecture (combinatorial geometry)](https://en.wikipedia.org/wiki/Hadwiger_conjecture_%28combinatorial_geometry%29)
- [Ha57] Hadwiger, H., _Ungelöste Probleme Nr. 20_. Elemente der Mathematik 12 (1957), 121.
- [HSTV22] Huang, H., Slomka, B. A., Tkocz, T., Vritsiou, B.-H., _Improved bounds for Hadwiger's
  covering problem via thin-shell estimates_. J. Eur. Math. Soc. 24 (2022).
  [arXiv:1811.12548](https://arxiv.org/abs/1811.12548)
- [CvHMT23] Campos, M., van Hintum, P., Morris, R., Tiba, M., _Towards Hadwiger's conjecture via
  Bourgain slicing_. Int. Math. Res. Not. IMRN (2023).
  [arXiv:2206.11227](https://arxiv.org/abs/2206.11227)
-/

open scoped EuclideanGeometry Pointwise

namespace HadwigerConjecture

/--
`CoveredBySmallerHomothets K m` says that `K ⊆ ℝⁿ` is covered by `m` smaller positively
homothetic copies of itself: there are scalars $s_1, \dots, s_m$ with $0 < s_i < 1$ and
translation vectors $v_1, \dots, v_m$ such that
$$K \subseteq \bigcup_{i=1}^{m} (s_i K + v_i).$$
Copies may coincide, so for nonempty `K` this also expresses coverability by at most `m` copies.
-/
def CoveredBySmallerHomothets {n : ℕ} (K : Set (ℝ^n)) (m : ℕ) : Prop :=
  ∃ (s : Fin m → ℝ) (v : Fin m → ℝ^n),
    (∀ i, s i ∈ Set.Ioo 0 1) ∧ K ⊆ ⋃ i, v i +ᵥ s i • K

/--
`IsParallelepiped K` says that `K ⊆ ℝⁿ` is an $n$-dimensional parallelepiped: a translate of
the closed parallelepiped $\{\sum_i t_i b_i \mid 0 \le t_i \le 1\}$ spanned by a basis
$b_1, \dots, b_n$ of $\mathbb{R}^n$, that is, the image of the unit cube $[0,1]^n$ under an
affine bijection.
-/
def IsParallelepiped {n : ℕ} (K : Set (ℝ^n)) : Prop :=
  ∃ (b : Module.Basis (Fin n) ℝ (ℝ^n)) (x : ℝ^n), K = x +ᵥ parallelepiped b

/-- The unit cube $[0,1]^n$ is a parallelepiped. -/
@[category test, AMS 52]
theorem isParallelepiped_unitCube (n : ℕ) :
    IsParallelepiped (parallelepiped (EuclideanSpace.basisFun (Fin n) ℝ)) :=
  ⟨(EuclideanSpace.basisFun (Fin n) ℝ).toBasis, 0, by simp⟩

/-- A single point is covered by one smaller homothetic copy of itself. -/
@[category test, AMS 52]
theorem coveredBySmallerHomothets_singleton {n : ℕ} (x : ℝ^n) :
    CoveredBySmallerHomothets {x} 1 :=
  ⟨fun _ => 1 / 2, fun _ => (1 / 2 : ℝ) • x, fun _ => by norm_num, by
    simp only [Set.smul_set_singleton, Set.vadd_set_singleton, Set.iUnion_const, vadd_eq_add,
      ← add_smul]
    norm_num⟩

/--
**Hadwiger conjecture.** Every convex body $K \subseteq \mathbb{R}^n$ (a compact convex set with
nonempty interior) can be covered by at most $2^n$ smaller homothetic copies of itself: there are
$2^n$ scalars $s_i$ with $0 < s_i < 1$ and $2^n$ translation vectors $v_i$ such that
$$K \subseteq \bigcup_{i=1}^{2^n} (s_i K + v_i).$$
-/
@[category research open, AMS 52]
theorem hadwiger_conjecture (n : ℕ) (K : Set (ℝ^n)) (hK : Convex ℝ K) (hKc : IsCompact K)
    (hKi : (interior K).Nonempty) :
    CoveredBySmallerHomothets K (2 ^ n) := by
  sorry

/--
**Hadwiger conjecture, equality case.** For a convex body $K \subseteq \mathbb{R}^n$ (a compact
convex set with nonempty interior), the upper bound $2^n$ is necessary if and only if $K$ is a
parallelepiped: the least number of smaller homothetic copies of $K$ needed to cover $K$ equals
$2^n$ exactly when $K$ is a parallelepiped.

The nonempty interior hypothesis excludes lower-dimensional bodies, for which fewer copies
suffice and "parallelepiped" would not mean an $n$-dimensional affine image of the cube.
-/
@[category research open, AMS 52]
theorem hadwiger_conjecture.variants.equality_case (n : ℕ) (K : Set (ℝ^n)) (hK : Convex ℝ K)
    (hKc : IsCompact K) (hKi : (interior K).Nonempty) :
    IsLeast {m | CoveredBySmallerHomothets K m} (2 ^ n) ↔ IsParallelepiped K := by
  sorry

end HadwigerConjecture
