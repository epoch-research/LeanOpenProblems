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
# Orchard-planting problem

The orchard-planting problem asks for the maximum number $t_3^{\text{orchard}}(n)$ of
$3$-point lines (lines containing exactly three of the points) attainable by a configuration
of $n$ points in the plane.

Burr, Grünbaum and Sloane [BGS74] constructed, for every $n \geq 3$, configurations of $n$
points with $\lfloor n(n-3)/6 \rfloor + 1$ three-point lines. Green and Tao [GT13] proved that
for all sufficiently large $n$ no configuration of $n$ points has more than this many
three-point lines, so $t_3^{\text{orchard}}(n) = \lfloor n(n-3)/6 \rfloor + 1$ for all
sufficiently large $n$. The exact value for every $n$ is not known: the formula fails for some
small $n$ (for example $t_3^{\text{orchard}}(7) = 6$), and the threshold in the Green–Tao
theorem is not explicit.

*References:*
- [Wikipedia, Orchard-planting problem](https://en.wikipedia.org/wiki/Orchard-planting_problem)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [BGS74] Burr, S. A., Grünbaum, B., Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata 2 (1974), 397–424.
- [GT13] Green, B., Tao, T., *On sets defining few ordinary lines*.
  Discrete Comput. Geom. 50 (2013), 409–468. [arXiv:1208.4714](https://arxiv.org/abs/1208.4714)
- [A003035](https://oeis.org/A003035)
-/

open EuclideanGeometry Filter

namespace OrchardPlantingProblem

/-- A line in the plane: an affine subspace whose direction is one-dimensional. -/
def IsLine (L : AffineSubspace ℝ ℝ²) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- The number of lines in the plane that contain exactly `k` points of the finite set `P`. -/
noncomputable def kPointLines (P : Finset ℝ²) (k : ℕ) : ℕ :=
  {L : AffineSubspace ℝ ℝ² | IsLine L ∧ ((P : Set ℝ²) ∩ L).ncard = k}.ncard

/--
$t_3^{\text{orchard}}(n)$: the maximum number of $3$-point lines attainable by a configuration
of $n$ points in the plane. Two distinct points lie on exactly one line, so this number is at
most $\binom{n}{2} / 3$ and the supremum is attained.
-/
noncomputable def orchardNumber (n : ℕ) : ℕ :=
  sSup {kPointLines P 3 | (P : Finset ℝ²) (_ : P.card = n)}

/-- The line through two distinct points is a line. -/
@[category API, AMS 51 52]
theorem isLine_affineSpan_pair {a b : ℝ²} (h : a ≠ b) : IsLine line[ℝ, a, b] := by
  rw [IsLine, direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr h)

/-- A line through two distinct points `a` and `b` is the line `line[ℝ, a, b]`. -/
@[category API, AMS 51 52]
theorem IsLine.eq_affineSpan_pair {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) {a b : ℝ²}
    (hab : a ≠ b) (ha : a ∈ L) (hb : b ∈ L) : L = line[ℝ, a, b] := by
  refine (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_
    ⟨a, left_mem_affineSpan_pair ..⟩ (affineSpan_pair_le_of_mem_of_mem ha hb)).symm
  exact Submodule.eq_of_le_of_finrank_eq
    (AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha hb))
    ((isLine_affineSpan_pair hab).trans hL.symm)

/-- A line containing three points of the three-point set `{a, b, c}` is the line
`line[ℝ, a, b]`. -/
@[category API, AMS 51 52]
theorem IsLine.eq_affineSpan_pair_of_ncard_inter {L : AffineSubspace ℝ ℝ²} (hL : IsLine L)
    {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ((({a, b, c} : Finset ℝ²) : Set ℝ²) ∩ L).ncard = 3) : L = line[ℝ, a, b] := by
  have hP : (({a, b, c} : Finset ℝ²) : Set ℝ²).ncard = 3 := by
    rw [Set.ncard_coe_finset, Finset.card_eq_three]
    exact ⟨a, b, c, hab, hac, hbc, rfl⟩
  have h := Set.inter_eq_left.mp (Set.eq_of_subset_of_ncard_le Set.inter_subset_left
    (hP.trans h.symm).le)
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
    Set.singleton_subset_iff, SetLike.mem_coe] at h
  exact hL.eq_affineSpan_pair hab h.1 h.2.1

/-- A set of fewer than `k` points determines no `k`-point line. -/
@[category API, AMS 51 52]
theorem kPointLines_eq_zero_of_card_lt {P : Finset ℝ²} {k : ℕ} (h : P.card < k) :
    kPointLines P k = 0 := by
  unfold kPointLines
  convert Set.ncard_empty (AffineSubspace ℝ ℝ²)
  ext L
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hL
  have := (Set.ncard_le_ncard (Set.inter_subset_left (s := (P : Set ℝ²)) (t := (L : Set ℝ²)))
    (Finset.finite_toSet P)).trans_lt (by simpa using h)
  omega

/-- Three distinct collinear points determine exactly one $3$-point line. -/
@[category test, AMS 51 52]
theorem kPointLines_three {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hc : c ∈ line[ℝ, a, b]) : kPointLines {a, b, c} 3 = 1 := by
  rw [kPointLines, Set.ncard_eq_one]
  refine ⟨line[ℝ, a, b], Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨isLine_affineSpan_pair hab, ?_⟩,
      fun L ⟨hL, hL3⟩ => hL.eq_affineSpan_pair_of_ncard_inter hab hac hbc hL3⟩⟩
  rw [Set.inter_eq_left.mpr, Set.ncard_coe_finset, Finset.card_eq_three]
  · exact ⟨a, b, c, hab, hac, hbc, rfl⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
    Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨left_mem_affineSpan_pair .., right_mem_affineSpan_pair .., hc⟩

/-- Three points determine at most one $3$-point line. -/
@[category API, AMS 51 52]
theorem kPointLines_le_one_of_card_eq_three {P : Finset ℝ²} (hP : P.card = 3) :
    kPointLines P 3 ≤ 1 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hP
  unfold kPointLines
  refine (Set.ncard_le_ncard (t := {line[ℝ, a, b]}) ?_).trans_eq (Set.ncard_singleton _)
  rintro L ⟨hL, hL3⟩
  exact hL.eq_affineSpan_pair_of_ncard_inter hab hac hbc hL3

/-- Fewer than three points determine no $3$-point line. -/
@[category test, AMS 51 52]
theorem orchardNumber_eq_zero_of_lt_three {n : ℕ} (hn : n < 3) : orchardNumber n = 0 := by
  unfold orchardNumber
  convert csSup_singleton 0
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact kPointLines_eq_zero_of_card_lt (hP ▸ hn)
  · rintro rfl
    have hcard : ((Finset.range n).image
        fun i : ℕ => (EuclideanSpace.single (0 : Fin 2) (i : ℝ) : ℝ²)).card = n := by
      rw [Finset.card_image_of_injective _ fun i j hij => ?_, Finset.card_range]
      simpa using congrArg (fun v : ℝ² => v 0) hij
    exact ⟨_, hcard, kPointLines_eq_zero_of_card_lt (hcard.trans_lt hn)⟩

/-- $t_3^{\text{orchard}}(3) = 1$, the first term of [A003035](https://oeis.org/A003035). -/
@[category test, AMS 51 52]
theorem orchardNumber_three : orchardNumber 3 = 1 := by
  set v : ℝ² := EuclideanSpace.single 0 1 with hv
  have h0v : (0 : ℝ²) ≠ v := fun h => by simpa [hv] using congrArg (fun w : ℝ² => w 0) h
  have h02 : (0 : ℝ²) ≠ (2 : ℝ) • v := fun h => by
    simpa [hv] using congrArg (fun w : ℝ² => w 0) h
  have hv2 : v ≠ (2 : ℝ) • v := fun h => by
    have := congrArg (fun w : ℝ² => w 0) h
    norm_num [hv] at this
  have hle : ∀ m ∈ {kPointLines P 3 | (P : Finset ℝ²) (_ : P.card = 3)}, m ≤ 1 := by
    rintro _ ⟨P, hP, rfl⟩
    exact kPointLines_le_one_of_card_eq_three hP
  have hcard : ({0, v, (2 : ℝ) • v} : Finset ℝ²).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, h0v, h02, hv2, rfl⟩
  refine le_antisymm (csSup_le ⟨_, _, hcard, rfl⟩ hle)
    (le_csSup ⟨1, hle⟩ ⟨_, hcard, ?_⟩)
  refine kPointLines_three h0v h02 hv2 ?_
  simpa using smul_vsub_vadd_mem_affineSpan_pair (2 : ℝ) (0 : ℝ²) v

/--
**Orchard-planting problem.** Determine, for every $n$, the maximum number
$t_3^{\text{orchard}}(n)$ of $3$-point lines attainable by a configuration of $n$ points in the
plane (OEIS [A003035](https://oeis.org/A003035)). A $3$-point line is a line containing exactly
three of the $n$ points. The unknown is the whole function $n \mapsto t_3^{\text{orchard}}(n)$.

The value $\lfloor n(n-3)/6 \rfloor + 1$ is known for all sufficiently large $n$ (Green–Tao),
but it is not the answer for every $n$: for example $t_3^{\text{orchard}}(7) = 6$, while the
formula gives $5$.
-/
@[category research open, AMS 51 52]
theorem orchard_planting_problem : orchardNumber = answer(sorry) := by
  sorry

/--
For all sufficiently large $n$, the maximum number of $3$-point lines attainable by a
configuration of $n$ points in the plane is exactly $\lfloor n(n-3)/6 \rfloor + 1$: Green and
Tao [GT13] proved that there is $n_0$ such that for $n \geq n_0$ every configuration of $n$
points in the plane has at most $\lfloor n(n-3)/6 \rfloor + 1$ three-point lines, and this
matches the lower bound given by the constructions of Burr, Grünbaum and Sloane [BGS74].
-/
@[category research solved, AMS 51 52]
theorem orchard_planting_problem.variants.eventually :
    ∀ᶠ n : ℕ in atTop, orchardNumber n = n * (n - 3) / 6 + 1 := by
  sorry

end OrchardPlantingProblem
