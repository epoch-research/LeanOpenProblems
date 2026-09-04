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
# Zariski's multiplicity conjecture

The Wikipedia list of unsolved problems in mathematics lists the "Zariski multiplicity conjecture
on the topological equisingularity and equimultiplicity of varieties at singular points".

Zariski's multiplicity conjecture is the question of whether the multiplicity of a complex
hypersurface singularity is an invariant of its embedded topological type (Zariski's Question A),
and whether topological equisingularity of a hypersurface along a nonsingular subvariety implies
equimultiplicity along it (Zariski's Question B, a weaker form implied by Question A). Both were
posed by Zariski in 1971 and remain open in general. Despite the word "varieties" in the list
entry, the conjecture concerns hypersurfaces. Solved special cases ($n = 2$, multiplicity one,
$C^1$ or bi-Lipschitz homeomorphisms) are not stated here.

Here a *hypersurface* $V \subset \mathbb{C}^n$ near a point $P$ is the zero set of a holomorphic
function $F$ which is *reduced* at $P$, i.e. whose germ at $P$ is square-free in the ring of
holomorphic germs. The *multiplicity* $m(V, P)$ of $V$ at $P$ is the order of $F$ at $P$, i.e. the
degree of the lowest-degree non-zero homogeneous term in the Taylor expansion of $F$ at $P$. The
reducedness hypothesis is essential: $f$ and $f^2$ define the same zero set.

*References:*
- [Wikipedia, Algebraic variety](https://en.wikipedia.org/wiki/algebraic_variety)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Za71] Zariski, O. *Some open questions in the theory of singularities*.
  Bull. Amer. Math. Soc. 77 (1971), 481–491.
- [Ey07] Eyral, C. *Zariski's multiplicity question — a survey*.
  New Zealand J. Math. 36 (2007), 253–276.
-/

open Topology Filter

namespace Varieties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The order of a function `f : E → ℂ` at a point `p`: the least `k` such that the `k`-th
derivative of `f` at `p` is non-zero. For a holomorphic `f` which does not vanish identically
near `p`, this is the degree of the lowest-degree non-zero homogeneous term of the Taylor
expansion of `f` at `p`, i.e. the multiplicity at `p` of the hypersurface defined by `f` when
`f` is reduced at `p`. It takes the junk value `0` if `f` vanishes identically near `p`. -/
noncomputable def orderAt (f : E → ℂ) (p : E) : ℕ :=
  sInf {k : ℕ | iteratedFDeriv ℂ k f p ≠ 0}

/-- A function `f : E → ℂ` is *reduced* at `p` if its germ at `p` is square-free in the ring
of germs of holomorphic functions at `p`, i.e. whenever `f` agrees near `p` with `g ^ 2 * h` for
holomorphic `g` and `h`, the factor `g` is a unit, that is `g p ≠ 0`. In particular `f` does not
vanish identically near `p`. This is meant to be applied to functions holomorphic at `p`. -/
def IsReducedAt (f : E → ℂ) (p : E) : Prop :=
  ∀ g h : E → ℂ, AnalyticAt ℂ g p → AnalyticAt ℂ h p →
    (f =ᶠ[𝓝 p] fun x => g x ^ 2 * h x) → g p ≠ 0

/-- A set `W ⊆ ℂⁿ` is a *nonsingular (complex-analytic) subvariety of dimension `d`* near a
point `P ∈ W` if there is a biholomorphic chart of a neighbourhood of `P` in `ℂⁿ` onto an open
subset of `ℂ^d × ℂ^(n - d)` which carries `W` onto the linear subspace `ℂ^d × {0}`. -/
def IsSmoothSubvarietyAt {n : ℕ} (W : Set (EuclideanSpace ℂ (Fin n))) (d : ℕ)
    (P : EuclideanSpace ℂ (Fin n)) : Prop :=
  ∃ ψ : OpenPartialHomeomorph (EuclideanSpace ℂ (Fin n))
      (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin (n - d))),
    P ∈ ψ.source ∧ AnalyticOnNhd ℂ ψ ψ.source ∧ AnalyticOnNhd ℂ ψ.symm ψ.target ∧
      ∀ x ∈ ψ.source, x ∈ W ↔ (ψ x).2 = 0

/-- The hypersurface `V = {F = 0} ⊆ ℂⁿ` is *topologically equisingular* along the
`d`-dimensional subvariety `W` at the point `P ∈ W` if the triple `(ℂⁿ, V, W)` is locally
topologically trivial along `W` at `P`: there is a homeomorphism `h` from a neighbourhood `U` of
`P` in `ℂⁿ` onto a product `U₁ × U₂` of open sets `U₁ ⊆ ℂ^d`, `U₂ ⊆ ℂ^(n - d)` such that
`h (W ∩ U) = U₁ × {0}` and `h (V ∩ U) = U₁ × S` for some set `S ⊆ ℂ^(n - d)` (so that `S ∩ U₂`
is homeomorphic to a transversal slice of `V`). Such an `h` yields, for every `Q ∈ W ∩ U`, a
homeomorphism between neighbourhoods of `Q` and `P` in `ℂⁿ` carrying `V` onto `V` and `Q` to `P`.
-/
def IsTopologicallyEquisingularAlong {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (W : Set (EuclideanSpace ℂ (Fin n))) (d : ℕ) (P : EuclideanSpace ℂ (Fin n)) : Prop :=
  ∃ (h : OpenPartialHomeomorph (EuclideanSpace ℂ (Fin n))
      (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin (n - d))))
    (U₁ : Set (EuclideanSpace ℂ (Fin d))) (U₂ S : Set (EuclideanSpace ℂ (Fin (n - d)))),
    P ∈ h.source ∧ h.target = U₁ ×ˢ U₂ ∧
      (∀ x ∈ h.source, x ∈ W ↔ (h x).2 = 0) ∧
      (∀ x ∈ h.source, F x = 0 ↔ (h x).2 ∈ S)

/-- **Topological equisingularity implies equimultiplicity** (Zariski's Question B, [Za71]),
a consequence of `Varieties.varieties`.

Let $V = \{F = 0\} \subset \mathbb{C}^n$ be a hypersurface with $F$ holomorphic and reduced at
$P \in V$, and let $W$ be a nonsingular subvariety of dimension $d$ through $P$. If $V$ is
topologically equisingular along $W$ at $P$, then $V$ is equimultiple along $W$ at $P$: the
multiplicity $m(V, Q)$ is constant for $Q \in W$ near $P$.

Topological equisingularity is taken in the sense of ambient local topological triviality of the
triple $(\mathbb{C}^n, V, W)$ along $W$ (see `IsTopologicallyEquisingularAlong`), which is
stronger than asking that the germs $(\mathbb{C}^n, V, Q)$ have the same embedded topological
type for all $Q \in W$ near $P$. Topological equisingularity along $W$ together with $P \in V$
forces $W \subset V$ near $P$, so $W$ is a nonsingular subvariety of $V$ as in Zariski's
formulation. The conclusion is stated for `Q` in a neighbourhood of `P` in `W`, on which `F` is
holomorphic and reduced, so that `orderAt F Q` is the multiplicity of `V` at `Q`. -/
theorem varieties.variants.equisingular_family {n d : ℕ} {F : EuclideanSpace ℂ (Fin n) → ℂ}
    {W : Set (EuclideanSpace ℂ (Fin n))} {P : EuclideanSpace ℂ (Fin n)}
    (hF : AnalyticAt ℂ F P) (hF₀ : F P = 0) (hF' : IsReducedAt F P)
    (hP : P ∈ W) (hW : IsSmoothSubvarietyAt W d P)
    (hV : IsTopologicallyEquisingularAlong F W d P) :
    ∀ᶠ Q in 𝓝[W] P, orderAt F Q = orderAt F P := by
  sorry

end Varieties

theorem Varieties.varieties.variants.equisingular_family.disproof : ¬ (type_of% @Varieties.varieties.variants.equisingular_family) := sorry
