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

/-- The empty set is a trivial `(v, 0, 0)`-difference set. -/
@[category test, AMS 5 20]
theorem isDifferenceSet_empty {G : Type*} [Group G] :
    IsDifferenceSet (∅ : Set G) (Nat.card G) 0 0 := by
  refine ⟨rfl, Set.ncard_empty _, fun g _ => ?_⟩
  simp

/-- A singleton is a trivial `(v, 1, 0)`-difference set. -/
@[category test, AMS 5 20]
theorem isDifferenceSet_singleton {G : Type*} [Group G] (a : G) :
    IsDifferenceSet ({a} : Set G) (Nat.card G) 1 0 := by
  refine ⟨rfl, Set.ncard_singleton _, fun g hg => ?_⟩
  rw [Set.ncard_eq_zero]
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro ⟨rfl, rfl⟩ h
  exact hg (h.symm.trans (mul_inv_cancel _))

/-- The whole group is a trivial `(v, v, v)`-difference set. Its order `v - v = 0` is divisible
by every prime, which is why the conjectures below require `k < v`. -/
@[category test, AMS 5 20]
theorem isDifferenceSet_univ {G : Type*} [Group G] [Finite G] :
    IsDifferenceSet (Set.univ : Set G) (Nat.card G) (Nat.card G) (Nat.card G) := by
  refine ⟨rfl, Set.ncard_univ G, fun g _ => ?_⟩
  have : {d ∈ (Set.univ : Set G) ×ˢ Set.univ | d.1 * d.2⁻¹ = g} =
      Set.range (fun y : G => (g * y, y)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_range,
      Prod.mk.injEq, exists_eq_right]
    exact mul_inv_eq_iff_eq_mul.trans eq_comm
  rw [this, Set.ncard_range_of_injective]
  intro a b h
  simpa using congrArg Prod.snd h

/-- The set `{1, 2, 4}` is a `(7, 3, 1)`-difference set in the cyclic group of order `7`. -/
@[category test, AMS 5 20]
theorem isDifferenceSet_fano :
    IsDifferenceSet ({Multiplicative.ofAdd 1, Multiplicative.ofAdd 2, Multiplicative.ofAdd 4} :
      Set (Multiplicative (ZMod 7))) 7 3 1 := by
  refine ⟨by simp, ?_, fun g hg => ?_⟩
  · rw [Set.ncard_eq_toFinset_card']
    decide
  · rw [Set.ncard_eq_toFinset_card']
    revert g
    decide

/-- A singleton in the cyclic group of order `4` is a `(4, 1, 0)`-difference set. These are the
Menon–Hadamard parameters `(4u², 2u² - u, u² - u)` with `u = 1`, so the hypothesis `1 < u` in
`landers_conjecture.variants.circulant_hadamard` is necessary. -/
@[category test, AMS 5 15 20]
theorem isDifferenceSet_menon_hadamard_one :
    IsDifferenceSet ({1} : Set (Multiplicative (ZMod 4))) (4 * 1 ^ 2) (2 * 1 ^ 2 - 1)
      (1 ^ 2 - 1) := by
  simpa using isDifferenceSet_singleton (1 : Multiplicative (ZMod 4))

/--
**Lander's conjecture** (Lander, 1983).

If a finite abelian group $G$ of order $v$ contains a difference set of order $n$, and a
prime $p$ divides both $v$ and $n$, must the Sylow $p$-subgroup of $G$ be non-cyclic?

Here a difference set of order $n$ means a $(v, k, λ)$-difference set $D ⊆ G$ with
$n = k - λ$. The difference set is required to be nontrivial, i.e. $0 < k < v$: the trivial
difference sets $D = ∅$ and $D = G$ have order $0$, which is divisible by every prime.
(For a nontrivial difference set $λ < k$, so $k - λ$ is the honest order $n ≥ 1$.)
Since $G$ is abelian, it has a unique Sylow $p$-subgroup, so quantifying over all Sylow
$p$-subgroups is the same as speaking of *the* Sylow $p$-subgroup.

Lander and the Wikipedia article state the conjecture as the positive answer.
-/
@[category research open, AMS 5 20]
theorem landers_conjecture : answer(sorry) ↔
    ∀ (G : Type) [CommGroup G] [Finite G] (D : Set G) (v k l : ℕ),
      IsDifferenceSet D v k l → 0 < k → k < v →
      ∀ p : ℕ, p.Prime → p ∣ v → p ∣ k - l →
      ∀ P : Sylow p G, ¬ IsCyclic P := by
  sorry

/--
**Ryser's cyclic difference-set conjecture.**

A nontrivial $(v, k, λ)$-difference set in a cyclic group of order $v$ satisfies
$\gcd(v, n) = 1$, where $n = k - λ$ is its order.

Nontriviality ($0 < k < v$) is needed: the trivial difference sets $D = ∅$ and $D = G$ have
order $0$ and $\gcd(v, 0) = v$.

Lander's conjecture implies this conjecture, since every Sylow subgroup of a cyclic group is
cyclic.
-/
@[category research open, AMS 5 20]
theorem landers_conjecture.variants.ryser {G : Type*} [Group G] [IsCyclic G] [Finite G]
    {D : Set G} {v k l : ℕ} (hD : IsDifferenceSet D v k l) (hk : 0 < k) (hkv : k < v) :
    Nat.Coprime v (k - l) := by
  sorry

/--
**The circulant Hadamard conjecture**, in difference-set form.

There is no cyclic difference set with the Menon–Hadamard parameters
$(v, k, λ) = (4u^2, 2u^2 - u, u^2 - u)$ for $u > 1$. Such a difference set has order
$n = k - λ = u^2$, so $\gcd(v, n) = u^2 > 1$; this is therefore the special case of Ryser's
conjecture for these parameters. Equivalently, no circulant Hadamard matrix of order greater
than $4$ exists (see `CirculantHadamard.circulant_hadamard_conjecture`).

The case $u = 1$ is excluded since a single element of the cyclic group of order $4$ is a
$(4, 1, 0)$-difference set (the circulant Hadamard matrix of order $4$).
-/
@[category research open, AMS 5 15 20]
theorem landers_conjecture.variants.circulant_hadamard {G : Type*} [Group G] [IsCyclic G]
    [Finite G] {u : ℕ} (hu : 1 < u) (D : Set G) :
    ¬ IsDifferenceSet D (4 * u ^ 2) (2 * u ^ 2 - u) (u ^ 2 - u) := by
  sorry

end LandersConjecture
