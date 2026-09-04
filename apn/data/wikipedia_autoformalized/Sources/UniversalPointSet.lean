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
# Universal point set

In graph drawing, a *universal point set of order $n$* (or *$n$-universal point set*) is a set
$S$ of points in the Euclidean plane such that every $n$-vertex planar graph has a crossing-free
straight-line drawing with all vertices placed at (distinct) points of $S$.

Grids of size $O(n) \times O(n)$ are $n$-universal, so $n$-universal point sets of size $O(n^2)$
exist; the smallest known ones have size $n^2/4 - \Theta(n)$ [BCDE14]. The best known lower bound
is $1.293n - o(n)$ [SSS20]. Rectangular grids of subquadratic size are never universal, but this
does not rule out subquadratic universal point sets of other types. The problem from Wikipedia's
list of unsolved problems asks whether $n$-universal point sets of *subquadratic* size, that is of
size $o(n^2)$, exist.

Mathlib has no notion of planarity. Planarity is defined here through crossing-free drawings in
the plane with edges drawn as simple arcs. By Fáry's theorem (recorded below as a solved
statement) this is the same as having a crossing-free straight-line drawing.

*References:*
- [Wikipedia: Universal point set](https://en.wikipedia.org/wiki/Universal_point_set)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [BCDE14] M. J. Bannister, Z. Cheng, W. E. Devanny, D. Eppstein, *Superpatterns and universal
  point sets*, J. Graph Algorithms Appl. 18 (2014), 177–209.
  [arXiv:1308.0403](https://arxiv.org/abs/1308.0403)
- [SSS20] M. Scheucher, H. Schrezenmaier, R. Steiner, *A note on universal point sets for planar
  graphs*, J. Graph Algorithms Appl. 24 (2020), 247–267.
  [arXiv:1811.06482](https://arxiv.org/abs/1811.06482)
-/

open Filter Asymptotics
open scoped EuclideanGeometry

namespace UniversalPointSet

variable {V : Type*}

/--
A crossing-free drawing of the simple graph `G` in the plane. The map `f` places the vertices at
distinct points, and `A e` is the curve drawn for the edge `e`:
* the curve of the edge `{u, v}` is a simple arc (the image of an injective path) from `f u` to
  `f v`;
* the curve of an edge contains no vertex other than its two endpoints;
* the curves of two distinct edges meet only in the images of their common endpoints.
-/
structure IsPlaneDrawing (G : SimpleGraph V) (f : V → ℝ²) (A : Sym2 V → Set ℝ²) :
    Prop where
  injective : Function.Injective f
  isArc : ∀ u v, G.Adj u v →
    ∃ γ : Path (f u) (f v), Function.Injective γ ∧ Set.range γ = A s(u, v)
  mem_of_mem_arc : ∀ e ∈ G.edgeSet, ∀ w, f w ∈ A e → w ∈ e
  inter_subset : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁ ≠ e₂ →
    A e₁ ∩ A e₂ ⊆ f '' {w | w ∈ e₁ ∧ w ∈ e₂}

/-- A simple graph is *planar* if it has a crossing-free drawing in the plane. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ∃ f A, IsPlaneDrawing G f A

/--
`f` is a crossing-free straight-line drawing of the simple graph `G` in the plane: the vertices are
placed at distinct points, every edge `{u, v}` is drawn as the closed line segment from `f u` to
`f v`, no such segment contains a vertex other than its two endpoints, and the segments of two
distinct edges meet only in the images of their common endpoints.
-/
def IsStraightLineDrawing (G : SimpleGraph V) (f : V → ℝ²) : Prop :=
  Function.Injective f ∧
    (∀ u v w, G.Adj u v → f w ∈ segment ℝ (f u) (f v) → w = u ∨ w = v) ∧
    ∀ u v x y, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
      segment ℝ (f u) (f v) ∩ segment ℝ (f x) (f y) ⊆ f '' ({u, v} ∩ {x, y})

/--
A finite set `S` of points in the plane is *`n`-universal* if every planar graph on `n` vertices
has a crossing-free straight-line drawing with all vertices placed at (distinct) points of `S`.
-/
def IsUniversal (n : ℕ) (S : Finset ℝ²) : Prop :=
  ∀ G : SimpleGraph (Fin n), IsPlanar G →
    ∃ f : Fin n → ℝ², IsStraightLineDrawing G f ∧ ∀ v, f v ∈ S

/--
**Universal point sets of subquadratic size for planar graphs.**

Do there exist $n$-universal point sets $S_n \subseteq \mathbb{R}^2$, one for each $n$, whose
sizes are subquadratic, i.e. $|S_n| = o(n^2)$? The point set $S_n$ may depend on $n$ and need not
be a grid. Equivalently, is the minimum size $f(n)$ of an $n$-universal point set $o(n^2)$?

The known bounds are linear from below ($f(n) \ge 1.293n - o(n)$, [SSS20]) and quadratic from
above ($f(n) \le n^2/4 - \Theta(n)$, [BCDE14]).
-/
@[category research open, AMS 5 52 68]
theorem universal_point_set :
    answer(sorry) ↔ ∃ S : ℕ → Finset ℝ², (∀ n, IsUniversal n (S n)) ∧
      (fun n => ((S n).card : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) := by
  sorry

/--
**Fáry's theorem.** A finite simple graph is planar if and only if it has a crossing-free
straight-line drawing in the plane.
-/
@[category research solved, AMS 5 52]
theorem isPlanar_iff_exists_isStraightLineDrawing [Finite V] (G : SimpleGraph V) :
    IsPlanar G ↔ ∃ f : V → ℝ², IsStraightLineDrawing G f := by
  sorry

/-- A crossing-free straight-line drawing is a crossing-free drawing. -/
@[category API, AMS 5 52]
theorem IsStraightLineDrawing.isPlanar {G : SimpleGraph V} {f : V → ℝ²}
    (h : IsStraightLineDrawing G f) : IsPlanar G := by
  obtain ⟨hinj, hvert, hcross⟩ := h
  refine ⟨f, Sym2.lift ⟨fun u v => segment ℝ (f u) (f v), fun u v => segment_symm ℝ _ _⟩,
    hinj, ?_, ?_, ?_⟩
  · intro u v huv
    refine ⟨Path.segment (f u) (f v), ?_, by simp⟩
    exact (AffineMap.lineMap_injective ℝ (hinj.ne huv.ne)).comp Subtype.val_injective
  · intro e he w hw
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Sym2.lift_mk] at hw
      simpa using hvert u v w he hw
  · intro e₁ he₁ e₂ he₂ hne p hp
    induction e₁ using Sym2.ind with
    | _ u v =>
      induction e₂ using Sym2.ind with
      | _ x y =>
        simp only [Sym2.lift_mk] at hp
        obtain ⟨w, hw, rfl⟩ := hcross u v x y he₁ he₂ hne hp
        exact ⟨w, by simpa using hw, rfl⟩

/-- The graph with no edges is planar. -/
@[category API, AMS 5 52]
theorem isPlanar_bot (n : ℕ) : IsPlanar (⊥ : SimpleGraph (Fin n)) := by
  refine IsStraightLineDrawing.isPlanar (f := fun i => EuclideanSpace.single (0 : Fin 2) (i : ℝ))
    ⟨?_, fun _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩
  intro i j h
  have := congrArg (fun p : ℝ² => p 0) h
  exact Fin.ext (by simpa using this)

/-- An `n`-universal point set has at least `n` points. -/
@[category API, AMS 5 52]
theorem le_card_of_isUniversal {n : ℕ} {S : Finset ℝ²} (hS : IsUniversal n S) :
    n ≤ S.card := by
  obtain ⟨f, ⟨hinj, -, -⟩, hfS⟩ := hS ⊥ (isPlanar_bot n)
  simpa using Finset.card_le_card_of_injOn (s := Finset.univ) f (fun v _ => hfS v) hinj.injOn

/-- Every superset of an `n`-universal point set is `n`-universal. -/
@[category API, AMS 5 52]
theorem IsUniversal.mono {n : ℕ} {S T : Finset ℝ²} (hS : IsUniversal n S) (hST : S ⊆ T) :
    IsUniversal n T := by
  intro G hG
  obtain ⟨f, hf, hfS⟩ := hS G hG
  exact ⟨f, hf, fun v => hST (hfS v)⟩

/-- The empty set is `0`-universal. -/
@[category test, AMS 5 52]
theorem isUniversal_zero_empty : IsUniversal 0 ∅ := by
  intro G _
  exact ⟨Fin.elim0, ⟨fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩,
    fun v => v.elim0⟩

end UniversalPointSet
