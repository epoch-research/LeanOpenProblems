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
# Whitehead conjecture

The Whitehead conjecture (also called the Whitehead asphericity conjecture) was formulated by
J. H. C. Whitehead in 1941. It states that every connected subcomplex of a two-dimensional
aspherical CW complex is aspherical.

A space $Y$ is *aspherical* if it is connected and all of its higher homotopy groups vanish, i.e.
$\pi_n(Y) = 0$ for all $n \ge 2$. For a CW complex this is equivalent to the universal cover
being contractible.

A CW complex is modelled as a closed subset `C` of a Hausdorff space `X` equipped with a CW
structure `Topology.CWComplex C`. It is two-dimensional if it has no cells of dimension
greater than $2$. A subcomplex is a `Topology.CWComplex.Subcomplex C`, i.e. a closed subset of
`C` that is a union of open cells of `C`; it is not assumed to be finite.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Whitehead_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- J. H. C. Whitehead, *On adding relations to homotopy groups*, Annals of Mathematics 42 (1941),
  409–428. [doi:10.2307/1968907](https://doi.org/10.2307/1968907)
-/

open Topology

namespace WhiteheadConjecture

/-- A topological space `Y` is *aspherical* if it is connected and all of its higher homotopy
groups vanish: $\pi_n(Y, y) = 0$ for every $n \ge 2$ and every base point $y \in Y$. -/
class AsphericalSpace (Y : Type*) [TopologicalSpace Y] : Prop extends ConnectedSpace Y where
  subsingleton_homotopyGroup : ∀ n : ℕ, 2 ≤ n → ∀ y : Y, Subsingleton (π_ n Y y)

/-- A one-point space is aspherical. -/
instance : AsphericalSpace Unit where
  subsingleton_homotopyGroup _ _ _ := Quot.Subsingleton

/--
**Whitehead conjecture.** Every connected subcomplex of a two-dimensional aspherical CW complex
is aspherical.

Here `C` is a CW complex (a closed subset of a Hausdorff space `X` with a CW structure) that is
two-dimensional (no cells of dimension $n > 2$) and aspherical, and `E` is a connected subcomplex
of `C`. The subcomplex `E` is not assumed to be finite.
-/
theorem whitehead_conjecture {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X)
    [CWComplex C] (hdim : ∀ n : ℕ, 2 < n → IsEmpty (RelCWComplex.cell C n)) [AsphericalSpace C]
    (E : CWComplex.Subcomplex C) (hE : IsConnected (E : Set X)) :
    AsphericalSpace (E : Set X) := by
  sorry

end WhiteheadConjecture

theorem WhiteheadConjecture.whitehead_conjecture.disproof : ¬ (type_of% @WhiteheadConjecture.whitehead_conjecture) := sorry
