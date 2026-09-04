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
# Property B

A collection $C$ of subsets of a finite set $X$ has *Property B* if $X$ can be partitioned into
two sets $Y$ and $Z$ such that every member of $C$ meets both $Y$ and $Z$; equivalently, the
hypergraph with edge set $C$ is $2$-colourable. In this repository this is `Finset.HasPropertyB`.

Let $m(n)$ denote the smallest number of sets in a collection of $n$-element sets that does not
have Property B. The values $m(1) = 1$, $m(2) = 3$, $m(3) = 7$ and $m(4) = 23$ are known, but
$m(n)$ is unknown for every $n \ge 5$ (currently $29 \le m(5) \le 51$). Asymptotically, Erdős
proved $2^{n-1} \le m(n) \le O(2^n n^2)$, and Radhakrishnan and Srinivasan improved the lower
bound to $m(n) = \Omega(2^n \sqrt{n / \log n})$. Erdős and Lovász conjectured that
$m(n) = \Theta(2^n \cdot n)$.

*References:*
- [Wikipedia, *Property B*](https://en.wikipedia.org/wiki/Property_B)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [P. Erdős, *On a combinatorial problem*, Nordisk Mat. Tidskr. **11** (1963), 5–10]
- [P. Erdős, *On a combinatorial problem. II*, Acta Math. Acad. Sci. Hungar. **15** (1964),
  445–447](https://doi.org/10.1007/BF01897152)
- [J. Radhakrishnan and A. Srinivasan, *Improved bounds and algorithms for hypergraph
  2-coloring*, Random Structures & Algorithms **16** (2000),
  4–32](https://doi.org/10.1002/(SICI)1098-2418(200001)16:1<4::AID-RSA2>3.0.CO;2-2)
-/

open Filter Asymptotics

namespace PropertyB

/-- `m n` is the smallest number of sets in a finite collection of `n`-element sets that does
not have Property B (in the sense of `Finset.HasPropertyB`), i.e. the minimum number of edges
of an `n`-uniform hypergraph that is not `2`-colourable.

The ground set is taken to be `ℕ`. This loses no generality: a finite collection of finite sets
lives on a finite ground set, which embeds into `ℕ`, and Property B is preserved by relabelling
the ground set injectively. For every `n` the set of achievable cardinalities is nonempty (all
`n`-subsets of a `(2n - 1)`-element set for `n ≥ 1`, and `{∅}` for `n = 0`), so the infimum is
attained. -/
noncomputable def m (n : ℕ) : ℕ :=
  sInf {k | ∃ F : Finset (Finset ℕ),
    F.card = k ∧ (∀ A ∈ F, A.card = n) ∧ ¬ F.HasPropertyB}

/--
**Erdős–Lovász conjecture on Property B.**

Let $m(n)$ be the size of the smallest collection of $n$-element sets without Property B.
Erdős and Lovász conjectured that
$$m(n) = \Theta(2^n \cdot n),$$
that is, there are constants $c, C > 0$ such that $c \cdot 2^n n \le m(n) \le C \cdot 2^n n$
for all sufficiently large $n$.

The best known bounds are $m(n) = \Omega(2^n \sqrt{n / \log n})$ (Radhakrishnan–Srinivasan,
2000) and $m(n) = O(2^n n^2)$ (Erdős, 1964).
-/
theorem property_b :
    (fun n => (m n : ℝ)) =Θ[atTop] fun n : ℕ => (n : ℝ) * 2 ^ n := by
  sorry

end PropertyB

theorem PropertyB.property_b.disproof : ¬ (type_of% @PropertyB.property_b) := sorry
