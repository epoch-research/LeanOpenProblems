/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 61 -- Erdős–Hajnal Conjecture

*Reference:* [erdosproblems.com/61](https://www.erdosproblems.com/61)
-/

open Filter
open SimpleGraph
open Real

namespace Erdos61

/-
For a graph $H$, consider all graphs $G$ that do not contain $H$ as an induced subgraph.
We would like to find a lower bound $f(n)$ such that every such $G$ on $n$ vertices
has a clique or independent set of size $\ge f(n)$ for sufficiently large $n$.
-/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/--
Chudnovsky, Scott, Seymour, and Spirkl [CSSS23] proved the conjecture for $H = C_5$, the
cycle on five vertices: every graph with no induced five-cycle has a clique or independent
set of polynomial size.

[CSSS23] Chudnovsky, M., Scott, A., Seymour, P. and Spirkl, S., Erdős–Hajnal for graphs with
no 5-hole. Proc. Lond. Math. Soc. (3) 126 (2023), 997–1014.
-/
theorem erdos_61.variants.c5 :
    ∃ c > (0 : ℝ), IsErdosHajnalLowerBound (cycleGraph 5) (fun n : ℕ => (n : ℝ) ^ c) := by
  sorry

end Erdos61

theorem Erdos61.erdos_61.variants.c5.disproof : ¬ (type_of% @Erdos61.erdos_61.variants.c5) := sorry
