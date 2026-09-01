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
# Fuglede's conjecture in dimensions 1 and 2

*References:*
- [Fuglede's conjecture](https://en.wikipedia.org/wiki/Fuglede%27s_conjecture)
-/

namespace Fuglede

open MeasureTheory

/--
**Fuglede's conjecture** in dimension `n`: A bounded subset of ℝ^n with positive Lebesgue measure is spectral iff it tiles ℝ^n by translation.
-/
def FugledeConjectureFor (n : ℕ) : Prop :=
  ∀ Ω : Set (Fin n → ℝ),
    Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
      (isSpectral Ω ↔ tilesByTranslation Ω)

/--
**Fuglede's conjecture** in two dimensions: A bounded subset of ℝ^2 with positive Lebesgue measure is spectral iff it tiles ℝ^2 by translation.
-/
theorem FugledeConjecture.variants.dim_2 :
    FugledeConjectureFor 2 := by
  sorry

end Fuglede

theorem Fuglede.FugledeConjecture.variants.dim_2.disproof : ¬ (type_of% @Fuglede.FugledeConjecture.variants.dim_2) := sorry
