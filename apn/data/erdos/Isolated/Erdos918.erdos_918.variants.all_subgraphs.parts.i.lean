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
# Erdős Problem 918

*References:*
- [erdosproblems.com/918](https://www.erdosproblems.com/918)
- [ErHa68b] Erdős, P. and Hajnal, A., On chromatic number of infinite graphs. (1968), 83--98.
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
-/

universe u

open scoped Cardinal

namespace Erdos918

/-- Is there a graph with $\aleph_2$ vertices and chromatic number $\aleph_2$ such that every
subgraph on $\aleph_1$ vertices has chromatic number $\leq\aleph_0$? -/
-- Formalisation note: It is not clear whether this question for general subgraphs is open or not
theorem erdos_918.variants.all_subgraphs.parts.i :
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal ≤ ℵ₀ := by
  sorry

end Erdos918

theorem Erdos918.erdos_918.variants.all_subgraphs.parts.i.disproof : ¬ (type_of% @Erdos918.erdos_918.variants.all_subgraphs.parts.i) := sorry
