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
# Monomial conjecture

*References:*
- [Wikipedia, Monomial conjecture](https://en.wikipedia.org/wiki/Monomial_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- P. Roberts, *Local Cohomology and the Homological Conjectures in Commutative Algebra*,
  [pdf](https://www5a.biglobe.ne.jp/~tomari/hamana/roberts.pdf)

Hochster's monomial conjecture: if $A$ is a Noetherian local ring of Krull dimension $d$ and
$x_1, \dots, x_d$ is a system of parameters for $A$, then for every positive integer $t$,
$$x_1^t \cdots x_d^t \notin (x_1^{t+1}, \dots, x_d^{t+1}).$$

A system of parameters for a Noetherian local ring $(A, \mathfrak m)$ of Krull dimension $d$
is a sequence $x_1, \dots, x_d$ of $d$ elements of $\mathfrak m$ such that the quotient
$A/(x_1, \dots, x_d)$ is Artinian (equivalently, $(x_1, \dots, x_d)$ is an $\mathfrak m$-primary
ideal). Mathlib has no named predicate for this, so the statement below spells it out. The
condition $x_i \in \mathfrak m$ is part of the definition and cannot be dropped: if some $x_i$
were a unit, then $A/(x_1, \dots, x_d) = 0$ would still be Artinian but the conclusion would fail.
-/

namespace MonomialConjecture

open IsLocalRing

/--
**Monomial conjecture** (Hochster).
Let $A$ be a Noetherian local ring of Krull dimension $d$ and let $x_1, \dots, x_d$ be a system
of parameters for $A$, i.e. $d$ elements of the maximal ideal of $A$ such that
$A/(x_1, \dots, x_d)$ is an Artinian ring. Then for all positive integers $t$,
$$x_1^t \cdots x_d^t \notin (x_1^{t+1}, \dots, x_d^{t+1}).$$
-/
@[category research open, AMS 13]
theorem monomial_conjecture {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {d : ℕ} (hd : ringKrullDim A = d) (x : Fin d → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hArt : IsArtinianRing (A ⧸ Ideal.span (Set.range x))) (t : ℕ) (ht : 0 < t) :
    ∏ i, x i ^ t ∉ Ideal.span (Set.range fun i ↦ x i ^ (t + 1)) := by
  sorry

end MonomialConjecture
