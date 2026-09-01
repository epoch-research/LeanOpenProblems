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
# Group structure via subgroup counts

*Reference:* [arXiv:2604.08040v1](https://arxiv.org/abs/2604.08040v1)
**Group Structure via Subgroup Counts**
by *Angsuman Das, Hiranya Kishore Dey, Khyati Sharma* (2026)

For a finite group $G$, let $\mathrm{cyc}(G)$ denote the number of cyclic subgroups of $G$,
and let $t = \pi(G)$ denote the number of distinct prime divisors of $|G|$.

The paper establishes several structural results of the form
"if $\mathrm{cyc}(G)$ or $\mathrm{sub}(G)$ is small relative to $2^t$, then $G$
has a strong structural property":

* $\mathrm{cyc}(G) < 5 \cdot 2^{t-2} \implies G$ is nilpotent (Theorem 3.1)
* $\mathrm{cyc}(G) < 2^{t+1} \implies G$ is supersolvable (Theorem 4.2)
* $\mathrm{sub}(G) < 59 \cdot 2^{t-3} \implies G$ is solvable (Theorem 5.3)

**Conjecture 5.5** proposes the analogue for solvability via cyclic subgroup count:
if $\mathrm{cyc}(G) < 2^{t+2}$, then $G$ is solvable.

* **In-Paper Location:** Conjecture 5.5, Section 5 "Solvability of a group from $\mathrm{sub}(G)$"
  ([PDF page 15](https://arxiv.org/pdf/2604.08040v1#page=15))
* **OpenConjecture ID:** 1512
-/

namespace Arxiv.«2604.08040»

variable (G : Type*) [Group G] [Fintype G]

/--
The number of cyclic subgroups of a finite group `G`.
-/
noncomputable def cyc : ℕ :=
  Nat.card {H : Subgroup G // IsCyclic H}

/--
The number of distinct prime divisors of the order of `G`.

This is $\pi(G)$ in the notation of the paper.
-/
noncomputable def numPrimeFactors : ℕ :=
  (Fintype.card G).primeFactors.card

/--
**Conjecture 5.5** (Das, Dey, Sharma 2026):
If a finite group `G` satisfies $\mathrm{cyc}(G) < 2^{t+2}$, where $t = \pi(G)$ is the
number of distinct prime divisors of $|G|$, then `G` is solvable.
-/
theorem solvable_of_cyc_lt :
    ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → IsSolvable G := by
  sorry

/- ## Sharpness & Test cases -/

end Arxiv.«2604.08040»

theorem Arxiv.«2604.08040».solvable_of_cyc_lt.disproof : ¬ (type_of% @Arxiv.«2604.08040».solvable_of_cyc_lt) := sorry
