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

variable (n T) in
/-- A triangle is `n`-simili-cuttable if it can be decomposed into `n` similar triangles. -/
def IsSimiliCuttable (n : ℕ) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ Ts : Fin n → Triangle ℝ ℝ²,
    (∀ i j, (Ts i).points ∼ (Ts j).points) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
      ⋃ i, (Ts i).closedInterior = T.closedInterior

/-- There exists a triangle which isn't simili-cuttable into 0, 2, 3, 5 parts.
This is proved in [So09]. -/
lemma exists_isSimiliCuttable_iff_ne_zero_two_three_five :
    ∃ T, ∀ n, IsSimiliCuttable n T ↔ n ≠ 0 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 5 := sorry

end Erdos633
