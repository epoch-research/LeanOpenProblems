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
# Lander's conjecture

A $(v, k, λ)$-difference set is a subset $D$ of size $k$ of a group $G$ of order $v$ such that
every non-identity element of $G$ can be written as $d_1 d_2^{-1}$ with $d_1, d_2 ∈ D$ in exactly
$λ$ ways. Its *order* is $n = k - λ$.

Lander's conjecture (1983) asks: if an abelian group of order $v$ contains a difference set of
order $n$, and a prime $p$ divides both $v$ and $n$, must the Sylow $p$-subgroup be non-cyclic?
It implies Ryser's cyclic difference-set conjecture, and hence the circulant Hadamard conjecture.

The matrix form of the circulant Hadamard conjecture is stated in
`FormalConjectures.Arxiv.«2402.13202».CirculantHadamard`.

*References:*
* [Wikipedia, Difference set](https://en.wikipedia.org/wiki/Difference_set%23Ryser_and_Lander_conjectures)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* E. S. Lander, *Symmetric Designs: An Algebraic Approach*, Cambridge University Press, 1983.
* L. D. Baumert, D. M. Gordon, *On the existence of cyclic difference sets with small parameters*,
  [arXiv:math/0304502](https://arxiv.org/abs/math/0304502)
-/

namespace LandersConjecture

/--
A subset `D` of a group `G` is a **`(v, k, λ)`-difference set** if `G` has order `v`, `D` has
`k` elements, and every non-identity element `g` of `G` can be written as `g = d₁ * d₂⁻¹` with
`d₁, d₂ ∈ D` in exactly `λ` ways (counting ordered pairs `(d₁, d₂)`). The *order* of the
difference set is `n = k - λ`.

The empty set (a `(v, 0, 0)`-difference set) and the whole group (a `(v, v, v)`-difference set)
are always difference sets. They are *trivial*, and both have order `0`.
-/
def IsDifferenceSet {G : Type*} [Group G] (D : Set G) (v k l : ℕ) : Prop :=
  Nat.card G = v ∧ D.ncard = k ∧
    ∀ g : G, g ≠ 1 → {d ∈ D ×ˢ D | d.1 * d.2⁻¹ = g}.ncard = l

/--
**Ryser's cyclic difference-set conjecture.**

A nontrivial $(v, k, λ)$-difference set in a cyclic group of order $v$ satisfies
$\gcd(v, n) = 1$, where $n = k - λ$ is its order.

Nontriviality ($0 < k < v$) is needed: the trivial difference sets $D = ∅$ and $D = G$ have
order $0$ and $\gcd(v, 0) = v$.

Lander's conjecture implies this conjecture, since every Sylow subgroup of a cyclic group is
cyclic.
-/
theorem landers_conjecture.variants.ryser {G : Type*} [Group G] [IsCyclic G] [Finite G]
    {D : Set G} {v k l : ℕ} (hD : IsDifferenceSet D v k l) (hk : 0 < k) (hkv : k < v) :
    Nat.Coprime v (k - l) := by
  sorry

end LandersConjecture

theorem LandersConjecture.landers_conjecture.variants.ryser.disproof : ¬ (type_of% @LandersConjecture.landers_conjecture.variants.ryser) := sorry
