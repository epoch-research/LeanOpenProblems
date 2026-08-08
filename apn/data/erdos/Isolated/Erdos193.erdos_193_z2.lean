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
# Erdős Problem 193

References:
- [erdosproblems.com/193](https://www.erdosproblems.com/193)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [GeRa79] Gerver, Joseph L. and Ramsey, L. Thomas, "On certain sequences of lattice points."
  Pacific J. Math. (1979), 357-363.
-/

open Set

namespace Erdos193

/-- An $S$-walk is a sequence where every difference is in $S$. -/
def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop :=
  ∀ n, a (n + 1) - a n ∈ S

/-- True if set $A$ contains 3 distinct collinear points over $R$. -/
def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V] [Module R V] (A : Set V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear R ({x, y, z} : Set V)

/--
[GeRa79] showed that the answer is yes for $\mathbb{Z}^2$
-/
theorem erdos_193_z2 :
    ∀ S : Set (Fin 2 → ℤ), S.Finite →
      ∀ a : ℕ → Fin 2 → ℤ, IsSWalk S a → (range a).Infinite →
      HasCollinearTriple ℚ (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 2 → ℚ)) := by
  sorry

-- TODO(jeangud): For $\mathbb{Z}^3$ the largest number of collinear points can be bounded [GeRa79].

end Erdos193
