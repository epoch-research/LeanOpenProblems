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
# Erdős Problem 331

*Reference:* [erdosproblems.com/331](https://www.erdosproblems.com/331)
-/

open Nat Filter
open scoped Asymptotics Classical

namespace Erdos331

/--
Ruzsa suggests that a non-trivial variant of this problem arises if one imposes the stronger
condition that $|A \cap \{1,\dots,N\}| \sim c_A N^{1/2}$ for some constant $c_A>0$, and similarly
for $B$.
-/
theorem erdos_331.variants.ruzsa :
    
      ∀ A B : Set ℕ,
      (∃ c_A > 0, (fun (n : ℕ) ↦ (count A n : ℝ)) ~[atTop] (fun (n : ℕ) ↦ c_A * (n : ℝ) ^ (1 / 2 : ℝ))) →
      (∃ c_B > 0, (fun (n : ℕ) ↦ (count B n : ℝ)) ~[atTop] (fun (n : ℕ) ↦ c_B * (n : ℝ) ^ (1 / 2 : ℝ))) →
      { s : ℕ × ℕ × ℕ × ℕ | let ⟨a₁, a₂, b₁, b₂⟩ := s
        a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
        a₁ ≠ a₂ ∧ a₁ + b₂ = a₂ + b₁ }.Infinite := by
  sorry
end Erdos331

theorem Erdos331.erdos_331.variants.ruzsa.disproof : ¬ (type_of% @Erdos331.erdos_331.variants.ruzsa) := sorry
