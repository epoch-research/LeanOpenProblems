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
# Erdős Problem 198

*References:*
- [erdosproblems.com/198](https://www.erdosproblems.com/198)
- [Ba75] Baumgartner, James E., Partitioning vector spaces. J. Combinatorial Theory Ser. A (1975),
  231-233.
-/

open Function Set Nat

namespace Erdos198

/--
The answer is no; Erdős and Graham report this was proved by Baumgartner, presumably referring to
the paper [Ba75], which does not state this exactly, but the following simple construction is
implicit in [Ba75].

Let $P_1,P_2,\ldots$ be an enumeration of all countably many infinite arithmetic progressions. We
choose $a_1$ to be the minimal element of $P_1\cap \mathbb{N}$, and in general choose $a_n$ to be an
element of $P_n\cap \mathbb{N}$ such that $a_n>2a_{n-1}$. By construction $A=\{a_1 < a_2 < \cdots\}$
contains at least one element from every infinite arithmetic progression, and is a lacunary set, so
is certainly Sidon.

This was formalized in Lean by Alexeev using Aristotle.
-/
theorem erdos_198 : (∀ A : Set ℕ, IsSidon A → (∃ Y, IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ)) := by
  sorry

end Erdos198
