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
# GNRS conjecture

The GNRS conjecture (Gupta, Newman, Rabinovich and Sinclair, 2004) states that every minor-closed
family of finite graphs, other than the family of all graphs, has $\ell_1$ embeddings with bounded
distortion: there is a constant $C$, depending only on the family, such that the shortest-path
(pseudo)metric of every graph in the family, with respect to every nonnegative edge-length
function, embeds into an $\ell_1$ space with distortion at most $C$.

Equivalently (Linial–London–Rabinovich, GNRS), the multi-commodity max-flow/min-cut gap of
graphs in such a family is uniformly bounded. Only the metric embedding formulation is stated
here. The exclusion of the family of all graphs is essential: bounded-degree expander graphs on
$n$ vertices require distortion $\Omega(\log n)$.

*References:*
* [Wikipedia, GNRS conjecture](https://en.wikipedia.org/wiki/GNRS_conjecture)
* [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [GNRS04] Gupta, A., Newman, I., Rabinovich, Y., Sinclair, A. (2004). "Cuts, trees and
  $\ell_1$-embeddings of graphs." *Combinatorica* 24 (2), pp. 233--269.
* [LS13] Lee, J. R., Sidiropoulos, A. (2013). "Pathwidth, trees, and random embeddings."
  *Combinatorica* 33 (3), pp. 349--374. [arXiv:0910.1409](https://arxiv.org/abs/0910.1409)
-/

open SimpleGraph

namespace GNRSConjecture

variable {V W X : Type*}

/-- `IsMinor H G` means that the graph `H` is a *minor* of the graph `G`, i.e. `H` can be
obtained from `G` by deleting vertices, deleting edges and contracting edges.

We use the standard equivalent description by *branch sets*: there is a family `A` of pairwise
disjoint vertex sets `A w ⊆ V(G)`, indexed by the vertices `w` of `H`, each inducing a connected
(in particular nonempty) subgraph of `G`, such that whenever `w` and `w'` are adjacent in `H`
there is an edge of `G` between `A w` and `A w'`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ A : W → Set V, (∀ w, (G.induce (A w)).Connected) ∧
    Pairwise (fun w w' => Disjoint (A w) (A w')) ∧
    ∀ ⦃w w'⦄, H.Adj w w' → ∃ u ∈ A w, ∃ v ∈ A w', G.Adj u v

/-- Every subgraph of `G` (on the same vertex set) is a minor of `G`. -/
@[category API, AMS 5]
theorem IsMinor.of_le {H G : SimpleGraph V} (h : H ≤ G) : IsMinor H G :=
  ⟨fun v => {v}, fun _ => Connected.of_subsingleton,
    fun _ _ hvw => Set.disjoint_singleton.mpr hvw,
    fun u v huv => ⟨u, rfl, v, rfl, h huv⟩⟩

/-- Every graph is a minor of itself. -/
@[category API, AMS 5]
theorem IsMinor.refl (G : SimpleGraph V) : IsMinor G G := .of_le le_rfl

/-- The graph with no vertices is a minor of every graph. -/
@[category test, AMS 5]
theorem isMinor_bot_empty (G : SimpleGraph V) : IsMinor (⊥ : SimpleGraph Empty) G :=
  ⟨Empty.elim, fun w => w.elim, fun w => w.elim, fun w => w.elim⟩

/-- The one-vertex graph is a minor of every connected graph. -/
@[category test, AMS 5]
theorem isMinor_bot_unit (G : SimpleGraph V) (hG : G.Connected) :
    IsMinor (⊥ : SimpleGraph Unit) G :=
  ⟨fun _ => Set.univ, fun _ => (induceUnivIso G).connected_iff.mpr hG,
    fun a b hab => absurd (Subsingleton.elim a b) hab,
    fun _ _ hab => absurd hab (by simp)⟩

/-- A family of finite graphs, given by the sets `F n` of its members with vertex set `Fin n`,
is *minor-closed* if it contains every minor of each of its members.

Every finite graph is isomorphic to a graph on some `Fin n`, and since isomorphic graphs are
minors of each other, a minor-closed family is in particular closed under isomorphism. -/
def IsMinorClosed (F : ∀ n : ℕ, Set (SimpleGraph (Fin n))) : Prop :=
  ∀ ⦃n m : ℕ⦄ ⦃G : SimpleGraph (Fin n)⦄ ⦃H : SimpleGraph (Fin m)⦄,
    G ∈ F n → IsMinor H G → H ∈ F m

/-- The family of all finite graphs is minor-closed. -/
@[category test, AMS 5]
theorem isMinorClosed_univ : IsMinorClosed fun _ => Set.univ :=
  fun _ _ _ _ _ _ => Set.mem_univ _

/-- The shortest-path distance between `u` and `v` in the graph `G` with respect to the
edge-length function `w : Sym2 V → ℝ` (only the values of `w` on edges of `G` matter): the
infimum, over all walks `p` from `u` to `v` in `G`, of the total length of the edges of `p`.

For nonnegative `w` and connected `G` this is the shortest-path pseudometric $d_w$ *supported
on* `G`; it is only a pseudometric since zero-length edges are allowed. (For vertices in different
components the set of walks is empty and the infimum takes the junk value `0`, so the conjecture
below is stated for connected graphs.) -/
noncomputable def shortestPathDist (G : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) : ℝ :=
  ⨅ p : G.Walk u v, (p.edges.map w).sum

/-- The shortest-path distance is nonnegative for nonnegative edge lengths. -/
@[category API, AMS 5]
theorem shortestPathDist_nonneg (G : SimpleGraph V) {w : Sym2 V → ℝ} (hw : ∀ e, 0 ≤ w e)
    (u v : V) : 0 ≤ shortestPathDist G w u v :=
  Real.iInf_nonneg fun p => List.sum_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    exact hw e

/-- The shortest-path distance from a vertex to itself is `0` for nonnegative edge lengths. -/
@[category API, AMS 5]
theorem shortestPathDist_self (G : SimpleGraph V) {w : Sym2 V → ℝ} (hw : ∀ e, 0 ≤ w e)
    (u : V) : shortestPathDist G w u u = 0 := by
  refine le_antisymm ?_ (shortestPathDist_nonneg G hw u u)
  have hbdd : BddBelow (Set.range fun p : G.Walk u u => (p.edges.map w).sum) := by
    refine ⟨0, ?_⟩
    rintro x ⟨p, rfl⟩
    exact List.sum_nonneg fun x hx => by
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
      exact hw e
  simpa using ciInf_le hbdd (Walk.nil : G.Walk u u)

/-- A pseudometric `d` on `X` *embeds into `ℓ₁` with distortion at most `C`* if there are
`n : ℕ` and a map `f : X → ℝⁿ` such that, measuring distances in `ℝⁿ` with the `ℓ₁` (sum) norm,
$$d(x, y) \le \|f(x) - f(y)\|_1 \le C \cdot d(x, y)$$
for all `x y : X`.

This is the usual non-contracting normalisation: an embedding with
`c * d x y ≤ ‖f x - f y‖₁ ≤ C' * d x y` and stretch factor `C' / c ≤ C` can be rescaled to one of
the above form. For finite `X`, embeddings into the sequence space `ℓ₁` (or into `L₁`) can be
replaced by embeddings into some finite-dimensional `ℓ₁ⁿ` without changing the distortion. -/
def EmbedsIntoL1WithDistortion (d : X → X → ℝ) (C : ℝ) : Prop :=
  ∃ (n : ℕ) (f : X → PiLp 1 (fun _ : Fin n => ℝ)),
    ∀ x y, d x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ C * d x y

/-- The real line embeds isometrically into `ℓ₁`. -/
@[category test, AMS 46]
theorem embedsIntoL1WithDistortion_real :
    EmbedsIntoL1WithDistortion (fun x y : ℝ => |x - y|) 1 := by
  refine ⟨1, fun x => WithLp.toLp 1 (fun _ => x), fun x y => ?_⟩
  simp [PiLp.dist_eq_sum, Real.dist_eq]

/--
**The GNRS conjecture** (Gupta, Newman, Rabinovich and Sinclair, 2004).

Let $\mathcal F$ be a minor-closed family of finite graphs other than the family of all graphs
(equivalently, $\mathcal F$ forbids some minor). Then there is a constant $C = C(\mathcal F)$ such
that for every (connected) graph $G \in \mathcal F$ and every nonnegative edge-length function
$w$ on $G$, the shortest-path pseudometric $d_w$ on the vertices of $G$ embeds into $\ell_1$ with
distortion at most $C$; that is, there is a map $f$ from the vertices of $G$ into an $\ell_1$ space
with $d_w(u, v) \le \|f(u) - f(v)\|_1 \le C \cdot d_w(u, v)$ for all vertices $u, v$.

The constant $C$ depends only on the family $\mathcal F$, not on the individual graph or on the
edge lengths. Here a family of finite graphs is given by the sets `F n` of its members with vertex
set `Fin n`. The conclusion is only asserted for connected members of the family, since the
shortest-path metric of a disconnected graph takes infinite values; this loses nothing, as the
connected components of members of a minor-closed family belong to the family.
-/
@[category research open, AMS 5 46 68]
theorem gnrs_conjecture (F : ∀ n : ℕ, Set (SimpleGraph (Fin n))) (hF : IsMinorClosed F)
    (hF' : ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G ∉ F n) :
    ∃ C : ℝ, ∀ (n : ℕ), ∀ G ∈ F n, G.Connected →
      ∀ w : Sym2 (Fin n) → ℝ, (∀ e, 0 ≤ w e) →
        EmbedsIntoL1WithDistortion (shortestPathDist G w) C := by
  sorry

end GNRSConjecture
