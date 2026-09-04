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
# The Borel conjecture

The Borel conjecture asserts that closed aspherical manifolds are determined up to homeomorphism
by their fundamental groups. Its precise form states that every homotopy equivalence between
closed aspherical topological manifolds is homotopic to a homeomorphism.

A space is *aspherical* if it is path-connected and all of its higher homotopy groups $\pi_n$,
$n \ge 2$, vanish. For CW complexes, and in particular for manifolds, this is equivalent to the
universal cover being contractible.

A *closed manifold* is a compact topological manifold without boundary. We model a closed
$m$-manifold as a compact Hausdorff second countable space with a `ChartedSpace` structure over
$\mathbb{R}^m$, so that every point has a neighbourhood homeomorphic to an open subset of
$\mathbb{R}^m$.

The conjecture concerns topological manifolds and homeomorphisms. The analogous statement for
smooth manifolds and diffeomorphisms is false: counterexamples are obtained by taking a connected
sum with an exotic sphere.

*References:*
- [Wikipedia, Borel conjecture](https://en.wikipedia.org/wiki/Borel_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Aspherical space](https://en.wikipedia.org/wiki/Aspherical_space)
- [Borel1953] A. Borel, letter to J.-P. Serre, May 1953.
  [The birth of the Borel conjecture](http://www.maths.ed.ac.uk/~aar/surgery/borel.pdf)
- [Rosenberg1986] J. Rosenberg, *C\*-algebras, positive scalar curvature, and the Novikov
  conjecture. III*, Topology 25 (1986). https://doi.org/10.1016/0040-9383(86)90047-9
-/

namespace BorelConjecture

open scoped Topology ContinuousMap

/-- A topological space `X` is *aspherical* if it is path-connected and all of its higher homotopy
groups vanish, i.e. $\pi_n(X, x)$ is trivial for every $n \ge 2$ and every basepoint $x$.
For CW complexes, and in particular for manifolds, this is equivalent to `X` being connected with
contractible universal cover. -/
class AsphericalSpace (X : Type*) [TopologicalSpace X] : Prop extends PathConnectedSpace X where
  subsingleton_homotopyGroup : ∀ n, 2 ≤ n → ∀ x : X, Subsingleton (π_ n X x)

/-- A point is aspherical. -/
instance : AsphericalSpace Unit where
  subsingleton_homotopyGroup n _ x :=
    inferInstanceAs (Subsingleton (Quotient (GenLoop.Homotopic.setoid (Fin n) x)))

/-- **Borel conjecture** (precise formulation). Let $M$ and $N$ be closed (compact, Hausdorff,
without boundary) aspherical topological manifolds and let $f \colon M \to N$ be a homotopy
equivalence. Then $f$ is homotopic to a homeomorphism: there is a homeomorphism
$h \colon M \to N$ with $f \simeq h$.

This implies `borel_conjecture`, since aspherical manifolds with isomorphic fundamental groups
are homotopy equivalent. -/
theorem borel_conjecture.variants.homotopy_equivalence (m n : ℕ) (M N : Type*)
    [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [CompactSpace M] [CompactSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [AsphericalSpace M] [AsphericalSpace N] (f : M ≃ₕ N) :
    ∃ h : M ≃ₜ N, f.toFun.Homotopic h := by
  sorry

end BorelConjecture

theorem BorelConjecture.borel_conjecture.variants.homotopy_equivalence.disproof : ¬ (type_of% @BorelConjecture.borel_conjecture.variants.homotopy_equivalence) := sorry
