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
# Tutte's 5-flow conjecture

*References:*
* [Wikipedia, Nowhere-zero flow](https://en.wikipedia.org/wiki/nowhere-zero_flows)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Tu54] Tutte, W. T. (1954). "A contribution to the theory of chromatic polynomials."
  *Canadian Journal of Mathematics* 6, pp. 80--91.

Let $G = (V, E)$ be a finite graph. A *nowhere-zero $k$-flow* on $G$ is an orientation of $E$
together with a map $\varphi : E \to \mathbb{Z}$ with $0 < |\varphi(e)| < k$ for every edge $e$
that satisfies Kirchhoff's law at every vertex: the total flow into $v$ equals the total flow
out of $v$. Reversing an edge and negating its value preserves these conditions, so the
existence of such a flow does not depend on the chosen orientation.

Nowhere-zero flows are usually considered on multigraphs. Deleting loops and subdividing every
edge of a multigraph preserves bridgelessness and the existence of a nowhere-zero $k$-flow, so
it suffices to state the conjecture for finite simple graphs.

We encode an orientation together with a flow as a single skew-symmetric function
$f : V \times V \to \mathbb{Z}$: the edge $\{u, v\}$ is oriented from $u$ to $v$ exactly when
$f(u, v) > 0$, and $|f(u, v)|$ is the flow along it. Kirchhoff's law at $v$ then reads
$\sum_w f(v, w) = 0$.
-/

namespace NowhereZero5Flow

variable {V : Type*} [Fintype V]

/--
`f : V → V → ℤ` is a nowhere-zero `k`-flow on the finite simple graph `G` if
* it is skew-symmetric: `f u v = -f v u`;
* it vanishes on non-adjacent pairs, so it only carries values on edges of `G`;
* it is nonzero on every edge, with `|f u v| < k`;
* it satisfies Kirchhoff's law: the net flow out of every vertex is `0`.

The value `f u v` is the flow along the edge `{u, v}` in the direction from `u` to `v`.
-/
structure IsNowhereZeroFlow (G : SimpleGraph V) (k : ℕ) (f : V → V → ℤ) : Prop where
  skew : ∀ u v, f u v = -f v u
  eq_zero_of_not_adj : ∀ u v, ¬ G.Adj u v → f u v = 0
  ne_zero_of_adj : ∀ u v, G.Adj u v → f u v ≠ 0
  abs_lt_of_adj : ∀ u v, G.Adj u v → |f u v| < k
  sum_eq_zero : ∀ v, ∑ w, f v w = 0

/-- The finite simple graph `G` has a nowhere-zero `k`-flow. -/
def HasNowhereZeroFlow (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f, IsNowhereZeroFlow G k f

/--
**Tutte's 5-flow conjecture** (1954). Every bridgeless graph has a nowhere-zero $5$-flow.

That is, if $G$ is a finite graph in which no edge is a bridge, then some (equivalently, every)
orientation of $G$ admits an integer circulation $\varphi$, i.e. a map on the edges satisfying
Kirchhoff's law at every vertex, with $0 < |\varphi(e)| < 5$ for every edge $e$.

The graph need not be connected. An edgeless graph is bridgeless and admits the zero flow, so
the statement holds trivially for it.
-/
@[category research open, AMS 5]
theorem nowhere_zero_5_flow (G : SimpleGraph V) (hG : G.IsBridgeless) :
    HasNowhereZeroFlow G 5 := by
  sorry

/-- The edgeless graph has a nowhere-zero `k`-flow for every `k`, namely the zero flow. -/
@[category test, AMS 5]
theorem hasNowhereZeroFlow_bot (k : ℕ) : HasNowhereZeroFlow (⊥ : SimpleGraph V) k :=
  ⟨0, fun _ _ => by simp, fun _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ h => h.elim,
    fun _ => by simp⟩

/-- A single edge is a bridge, and indeed it has no nowhere-zero `k`-flow for any `k`. -/
@[category test, AMS 5]
theorem not_hasNowhereZeroFlow_top_fin_two (k : ℕ) :
    ¬ HasNowhereZeroFlow (⊤ : SimpleGraph (Fin 2)) k := by
  rintro ⟨f, hf⟩
  have h00 := hf.skew 0 0
  have h01 := hf.ne_zero_of_adj 0 1 (by decide)
  have hsum := hf.sum_eq_zero 0
  rw [Fin.sum_univ_two] at hsum
  omega

/-- The triangle has a nowhere-zero `2`-flow: send one unit of flow around the cycle. -/
@[category test, AMS 5]
theorem hasNowhereZeroFlow_top_fin_three : HasNowhereZeroFlow (⊤ : SimpleGraph (Fin 3)) 2 := by
  refine ⟨fun i j => if j = i + 1 then 1 else if i = j + 1 then -1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end NowhereZero5Flow
