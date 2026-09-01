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
# Spectral sets and weak tiling

This file formalizes Problems 7.1 and 7.2 from Kolountzakis, Lev, and Matolcsi.

*References:*
- [KLM2023] Mihail N. Kolountzakis, Nir Lev, and Máté Matolcsi,
  [Spectral sets and weak tiling](https://arxiv.org/abs/2209.04540).
- [GL16] Rachel Greenfeld and Nir Lev, Spectrality and tiling by cylindric domains,
  *Journal of Functional Analysis* 271 (2016), 2808–2821.
- [GL20] Rachel Greenfeld and Nir Lev, Spectrality of product domains and Fuglede's conjecture
  for convex polytopes, *Journal d'Analyse Mathématique* 140 (2020), 409–441.
-/

open MeasureTheory

namespace NowhereDenseSpectralSet

end NowhereDenseSpectralSet

namespace SpectralSetProduct

/-- The product $A \times B$, represented by consecutive coordinate blocks. -/
def productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {x | (fun i ↦ x (Fin.castAdd m i)) ∈ A ∧ (fun j ↦ x (Fin.natAdd n j)) ∈ B}

/-- Spectrality of a product with an `n`-dimensional convex body forces spectrality of its
bounded, measurable `m`-dimensional right factor. -/
def spectralProductImpliesRightSpectral (n m : ℕ) : Prop :=
  ∀ (A : ConvexBody (Fin n → ℝ)) (B : Set (Fin m → ℝ)),
    Bornology.IsBounded B → MeasurableSet B →
      isSpectral (productSet (A : Set (Fin n → ℝ)) B) → isSpectral B

/--
[KLM2023, Problem 7.2] For a three-dimensional convex body $A$ and a bounded,
measurable set $B$, must spectrality of $A \times B$ imply spectrality of $B$?
-/
theorem isSpectral_right_of_product_three_dimensional :
    
      ∀ (m : ℕ), 0 < m → spectralProductImpliesRightSpectral 3 m := by
  sorry

end SpectralSetProduct

theorem SpectralSetProduct.isSpectral_right_of_product_three_dimensional.disproof : ¬ (type_of% @SpectralSetProduct.isSpectral_right_of_product_three_dimensional) := sorry
