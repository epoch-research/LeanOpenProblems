/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 633

*Reference:*
* [erdosproblems.com/633](https://www.erdosproblems.com/633)
* [So09] Soifer, Alexander, How Does One Cut a Triangle? I
* [So09c] Soifer, Alexander, Is there anything beyond the solution?
-/

open Affine
open scoped Congruent EuclideanGeometry Similar

namespace Erdos633
variable {n : ℕ} {T : Triangle ℝ ℝ²}

variable (n T) in
/-- A triangle is `n`-cuttable if it can be decomposed into `n` congruent triangles. -/
def IsCuttable : Prop :=
  ∃ Ts : Fin n → Triangle ℝ ℝ²,
    (∀ i j, (Ts i).points ≅ (Ts j).points) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
      ⋃ i, (Ts i).closedInterior = T.closedInterior

/-- A triangle isn't cuttable into zero triangles. -/
lemma IsCuttable.ne_zero (hT : IsCuttable n T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨Ts, -, -, hT⟩ := hT
  exact T.closedInterior_nonempty.ne_empty <| by simpa using hT.symm

/-- Every triangle is cuttable into any non-zero square number of congruent triangles. -/
protected lemma IsCuttable.sq (hn : n ≠ 0) : IsCuttable (n ^ 2) T := sorry

/-- Every triangle is cuttable into any non-zero square number of congruent triangles. -/
lemma IsCuttable.of_isSquare (hn₀ : n ≠ 0) (hn : IsSquare n) : IsCuttable n T := by
  obtain ⟨n, rfl⟩ := hn; rw [← sq]; exact .sq <| by simpa using hn₀

/-- A triangle whose side lengths and angles are integrally independent is cuttable only into
a non-zero square number of congruent triangles. This is proved in [So09c]. -/
lemma isCuttable_iff_isSquare_of_linearIndependent
    (hTsides : LinearIndependent ℤ
      ![dist (T.points 0) (T.points 1),
        dist (T.points 1) (T.points 2),
        dist (T.points 2) (T.points 0)])
    (hTangles : LinearIndependent ℤ
      ![∠ (T.points 0) (T.points 1) (T.points 2),
        ∠ (T.points 1) (T.points 2) (T.points 0),
        ∠ (T.points 2) (T.points 0) (T.points 1)]) :
    IsCuttable n T ↔ n ≠ 0 ∧ IsSquare n := by
  exact ⟨fun hT ↦ ⟨hT.ne_zero, sorry⟩, fun hn ↦ .of_isSquare hn.1 hn.2⟩

variable (n T) in
/-- A triangle is `n`-simili-cuttable if it can be decomposed into `n` similar triangles. -/
def IsSimiliCuttable (n : ℕ) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ Ts : Fin n → Triangle ℝ ℝ²,
    (∀ i j, (Ts i).points ∼ (Ts j).points) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
      ⋃ i, (Ts i).closedInterior = T.closedInterior

end Erdos633
