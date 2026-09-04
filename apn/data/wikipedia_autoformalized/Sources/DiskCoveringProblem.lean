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
# Disk covering problem

The disk covering problem asks for the smallest real number $r(n)$ such that $n$ disks of
radius $r(n)$ can be arranged in such a way as to cover the unit disk.

Disks are closed disks in the Euclidean plane. The set of radii $r$ for which $n$ closed disks
of radius $r$ can cover the closed unit disk is closed and bounded below, so the smallest such
radius exists and $r(n)$ is a minimum, which we express with `IsLeast`.

The values $r(1) = r(2) = 1$, $r(3) = \sqrt 3 / 2$ and $r(4) = \sqrt 2 / 2$ are elementary.
K. Bezdek (1983, 1984) determined $r(5)$, $r(6)$ and $r(7) = 1/2$, and G. Fejes Tóth (2005)
determined $r(8)$, $r(9)$ and $r(10)$. For $n = 11$ and $n = 12$ the values of $r(n)$ are not
known; the best coverings known have radii $0.380083\ldots$ and $0.361141\ldots$ respectively
(Wikipedia lists these radii truncated to six decimals).

*References:*
- [Wikipedia, Disk covering problem](https://en.wikipedia.org/wiki/disk_covering_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Erich Friedman, Circles Covering Circles](https://erich-friedman.github.io/packing/circovcir/)
- R. Kershner, [The number of circles covering a set](https://doi.org/10.2307/2371320),
  American Journal of Mathematics 61 (1939), 665–671.
- K. Bezdek, Über einige Kreisüberdeckungen, Beiträge zur Algebra und Geometrie 14 (1983).
- K. Bezdek, Über einige optimale Konfigurationen von Kreisen, Annales Universitatis
  Scientiarum Budapestinensis de Rolando Eötvös Nominatae, Sectio Mathematica 27 (1984).
- G. Fejes Tóth, Thinnest covering of a circle by eight, nine, or ten congruent circles,
  Combinatorial and Computational Geometry, MSRI Publications 52 (2005).
-/

open EuclideanGeometry Real

namespace DiskCoveringProblem

/--
`CanCoverUnitDisk n r` means that `n` closed disks of radius `r` can be arranged so as to cover
the closed unit disk in the Euclidean plane: there are centres `c 0, …, c (n - 1)` with
$\overline{B}(0, 1) \subseteq \bigcup_i \overline{B}(c_i, r)$. Coincident centres are allowed.
It fails for every `r` when `n = 0`, and it fails for every negative `r`.
-/
def CanCoverUnitDisk (n : ℕ) (r : ℝ) : Prop :=
  ∃ c : Fin n → ℝ², Metric.closedBall 0 1 ⊆ ⋃ i, Metric.closedBall (c i) r

/-- A single disk of radius `1` covers the unit disk. -/
@[category test, AMS 52]
theorem canCoverUnitDisk_one_one : CanCoverUnitDisk 1 1 :=
  ⟨fun _ => 0, fun _ hx => Set.mem_iUnion.2 ⟨0, hx⟩⟩

/-- No arrangement of `0` disks covers the unit disk. -/
@[category test, AMS 52]
theorem not_canCoverUnitDisk_zero (r : ℝ) : ¬ CanCoverUnitDisk 0 r := by
  rintro ⟨c, hc⟩
  simpa using hc (Metric.mem_closedBall_self zero_le_one)

/-- Covering by `n` disks is monotone in the radius. -/
@[category API, AMS 52]
theorem CanCoverUnitDisk.mono {n : ℕ} {r s : ℝ} (h : CanCoverUnitDisk n r) (hrs : r ≤ s) :
    CanCoverUnitDisk n s := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.trans <| Set.iUnion_mono fun i => Metric.closedBall_subset_closedBall hrs⟩

/--
The centres of the "central disk" layout of `k + 1` disks: one disk is centred at the origin
and the remaining `k` disks are placed symmetrically around it, at distance `d` from the origin
and at the equally spaced angles $2\pi j / k$, $j = 0, \dots, k - 1$.
-/
noncomputable def centralLayout (k : ℕ) (d : ℝ) : Fin (k + 1) → ℝ² :=
  Fin.cons 0 fun j => !₂[d * cos (2 * π * j / k), d * sin (2 * π * j / k)]

/-- The first disk of the central layout is centred at the origin. -/
@[category test, AMS 52]
theorem centralLayout_zero (k : ℕ) (d : ℝ) : centralLayout k d 0 = 0 := rfl

/-- The outer disks of the central layout are centred at distance `|d|` from the origin. -/
@[category API, AMS 52]
theorem norm_centralLayout_succ (k : ℕ) (d : ℝ) (j : Fin k) :
    ‖centralLayout k d j.succ‖ = |d| := by
  simp only [centralLayout, Fin.cons_succ, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_pow, mul_pow, ← mul_add, cos_sq_add_sin_sq, mul_one, Real.sqrt_sq_eq_abs]

/--
**Disk covering problem.** Find the smallest real number $r(n)$ such that $n$ disks of radius
$r(n)$ can be arranged in such a way as to cover the unit disk.

The value $r(n)$ is known for $n \le 10$. The first open cases are $n = 11$ and $n = 12$, where
the best coverings known to date have radii $0.380083\ldots$ and $0.361141\ldots$ respectively,
and it is open whether they are optimal.
-/
@[category research open, AMS 52]
theorem disk_covering_problem :
    let r := (answer(sorry) : ℕ → ℝ)
    ∀ n ∈ ({11, 12} : Finset ℕ), IsLeast {ρ | CanCoverUnitDisk n ρ} (r n) := by
  sorry

/--
The best covering of the unit disk by eleven equal disks known to date has radius
$0.380083\ldots$; in particular eleven disks of radius $0.380084$ cover the unit disk.
-/
@[category research solved, AMS 52]
theorem disk_covering_problem.variants.eleven_upper_bound : CanCoverUnitDisk 11 0.380084 := by
  sorry

/--
The best covering of the unit disk by eleven equal disks known to date, of radius
$0.380083\ldots$, is conjectured to be optimal. In particular, eleven disks of radius less than
$0.380083$ cannot cover the unit disk, i.e. $0.380083 \le r(11)$.
-/
@[category research open, AMS 52]
theorem disk_covering_problem.variants.eleven_lower_bound :
    0.380083 ∈ lowerBounds {r | CanCoverUnitDisk 11 r} := by
  sorry

/--
The best covering of the unit disk by twelve equal disks known to date has radius
$0.361141\ldots$; in particular twelve disks of radius $0.361142$ cover the unit disk.
-/
@[category research solved, AMS 52]
theorem disk_covering_problem.variants.twelve_upper_bound : CanCoverUnitDisk 12 0.361142 := by
  sorry

/--
The best covering of the unit disk by twelve equal disks known to date, of radius
$0.361141\ldots$, is conjectured to be optimal. In particular, twelve disks of radius less than
$0.361141$ cannot cover the unit disk, i.e. $0.361141 \le r(12)$.
-/
@[category research open, AMS 52]
theorem disk_covering_problem.variants.twelve_lower_bound :
    0.361141 ∈ lowerBounds {r | CanCoverUnitDisk 12 r} := by
  sorry

/--
**Central disk layouts.** Arrangements of six, seven, eight, and nine disks around a central
disk, all having the same radius, result in the best layout strategies for $r(7)$, $r(8)$,
$r(9)$ and $r(10)$ respectively. Precisely, for $k = 6, 7, 8, 9$ the optimal radius is
$$r(k + 1) = \frac{1}{1 + 2\cos(2\pi / k)},$$
so $r(7) = 1/2$, $r(8) = 0.445041867\ldots$, $r(9) = \sqrt 2 - 1$ and
$r(10) = 0.394930843\ldots$, and it is attained by a central layout: one disk at the origin and
$k$ disks at some common distance $d$ from the origin, at the angles $2\pi j / k$.

Optimality was proved by K. Bezdek (1983, 1984) for $n = 7$ and by G. Fejes Tóth (2005) for
$n = 8, 9, 10$.
-/
@[category research solved, AMS 52]
theorem disk_covering_problem.variants.central_disk_layouts (k : ℕ) (hk : k ∈ Finset.Icc 6 9) :
    IsLeast {r | CanCoverUnitDisk (k + 1) r} (1 / (1 + 2 * cos (2 * π / k))) ∧
      ∃ d : ℝ, Metric.closedBall 0 1 ⊆
        ⋃ i, Metric.closedBall (centralLayout k d i) (1 / (1 + 2 * cos (2 * π / k))) := by
  sorry

/-- $r(1) = 1$: the smallest disk covering the unit disk is the unit disk itself. -/
@[category textbook, AMS 52]
theorem disk_covering_problem.variants.one : IsLeast {r | CanCoverUnitDisk 1 r} 1 := by
  sorry

/-- $r(2) = 1$: two disks of radius less than $1$ cannot cover the unit disk. -/
@[category textbook, AMS 52]
theorem disk_covering_problem.variants.two : IsLeast {r | CanCoverUnitDisk 2 r} 1 := by
  sorry

/-- $r(3) = \sqrt 3 / 2$. -/
@[category textbook, AMS 52]
theorem disk_covering_problem.variants.three :
    IsLeast {r | CanCoverUnitDisk 3 r} (√3 / 2) := by
  sorry

/-- $r(4) = \sqrt 2 / 2$. -/
@[category textbook, AMS 52]
theorem disk_covering_problem.variants.four :
    IsLeast {r | CanCoverUnitDisk 4 r} (√2 / 2) := by
  sorry

end DiskCoveringProblem
