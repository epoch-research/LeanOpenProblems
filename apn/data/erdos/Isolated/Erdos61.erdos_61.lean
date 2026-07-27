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

import FormalConjectures.Util.ProblemImports

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
The Erdős–Hajnal Conjecture states that there is a constant $c(H) > 0$ for each
$H$ such that we can take $f(n) = n^{c(H)}$ in the above formulation.
-/
theorem erdos_61 :
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c) := by
  sorry

end Erdos61
