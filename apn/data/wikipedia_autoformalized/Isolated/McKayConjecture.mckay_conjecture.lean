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
# McKay conjecture

Let $p$ be a prime, $G$ a finite group and $P \leq G$ a Sylow $p$-subgroup. Write
$$\mathrm{Irr}_{p'}(G) := \{\chi \in \mathrm{Irr}(G) : p \nmid \chi(1)\}$$
for the set of irreducible complex characters of $G$ whose degree is not divisible by $p$.
The McKay conjecture asserts that
$$|\mathrm{Irr}_{p'}(G)| = |\mathrm{Irr}_{p'}(N_G(P))|,$$
where $N_G(P)$ is the normalizer of $P$ in $G$.

The conjecture was stated by McKay in 1971 for $p = 2$ and simple groups, and generalised to all
primes by Alperin. A proof for all primes and all finite groups was announced by Cabanes and
Späth in 2023.

*References:*
- [Wikipedia, *McKay conjecture*](https://en.wikipedia.org/wiki/McKay_conjecture)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [M. Cabanes, B. Späth, *The McKay Conjecture on character degrees*](https://arxiv.org/abs/2410.20392)
-/

namespace McKayConjecture

open CategoryTheory

/-- The set $\mathrm{Irr}_{p'}(G)$ of irreducible complex characters of the group $G$ whose
degree is not divisible by $p$.

A character is the function `G → ℂ` sending `g` to the trace of `ρ g`, and irreducible
representations are the simple objects of `FDRep ℂ G`. The degree of a character is the
dimension of the underlying representation, i.e. $\chi(1)$ (see `FDRep.char_one`). Since
isomorphic representations have the same character, each isomorphism class of irreducible
representations is counted once. -/
def irrCharsPrimeToDeg (p : ℕ) (G : Type) [Group G] : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ ∧ ¬ p ∣ Module.finrank ℂ V}

/-- **McKay conjecture.** Let $G$ be a finite group, $p$ a prime and $P$ a Sylow $p$-subgroup
of $G$. Then the number of irreducible complex characters of $G$ of degree not divisible by $p$
equals the number of irreducible complex characters of the normalizer $N_G(P)$ of degree not
divisible by $p$:
$$|\mathrm{Irr}_{p'}(G)| = |\mathrm{Irr}_{p'}(N_G(P))|.$$

Here isomorphic representations are counted once. Since all Sylow $p$-subgroups are conjugate,
the right-hand side does not depend on the choice of $P$. -/
theorem mckay_conjecture (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    (irrCharsPrimeToDeg p G).ncard = (irrCharsPrimeToDeg p P.normalizer).ncard := by
  sorry

end McKayConjecture

theorem McKayConjecture.mckay_conjecture.disproof : ¬ (type_of% @McKayConjecture.mckay_conjecture) := sorry
