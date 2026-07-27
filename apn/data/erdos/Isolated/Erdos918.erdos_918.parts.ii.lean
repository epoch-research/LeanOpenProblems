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

/-- Is there a graph with $\aleph_{\omega+1}$ vertices and chromatic number $\aleph_1$ such that
every subgraph on $\aleph_\omega$ vertices has chromatic number $\leq\aleph_0$? -/
theorem erdos_918.parts.ii :
    ∀ (ω : Ordinal),
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

end Erdos918
