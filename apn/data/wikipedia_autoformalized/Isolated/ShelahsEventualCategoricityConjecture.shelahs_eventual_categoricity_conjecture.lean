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
# Shelah's eventual categoricity conjecture

An *abstract elementary class* (AEC) is a class $K$ of structures in a first-order language
$L = L(K)$ together with a partial order $\prec_K$ ("strong substructure") on $K$, refining the
substructure relation, closed under isomorphisms, satisfying coherence, the Tarski–Vaught chain
axioms and a Löwenheim–Skolem axiom. The *Löwenheim–Skolem number* $\operatorname{LS}(K)$ is the
least cardinal $\mu \ge |L(K)| + \aleph_0$ such that every subset $A$ of a model $M \in K$ is
contained in some $N \prec_K M$ with $\|N\| \le |A| + \mu$.

$K$ is *categorical* in a cardinal $\kappa$ if it has exactly one model of cardinality $\kappa$
up to isomorphism.

Shelah's eventual categoricity conjecture: for every cardinal $\lambda$ there exists a cardinal
$\mu(\lambda)$ such that if an AEC $K$ with $\operatorname{LS}(K) \le \lambda$ is categorical in a
cardinal $\ge \mu(\lambda)$, then it is categorical in all cardinals $\ge \mu(\lambda)$.

Since Mathlib has no notion of abstract elementary class, this file defines one. Strong
substructures are encoded by a class of `L`-embeddings, the `K`-embeddings: an `L`-embedding
`f : M ↪[L] N` is a `K`-embedding exactly when `f[M] ≺_K N`. Unions of chains are encoded by
`FirstOrder.Language.DirectLimit`. The language, the models and all cardinals live in a single
universe `u`, which plays the role of the set-theoretic universe; the statement is
universe-polymorphic.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Abstract elementary class](https://en.wikipedia.org/wiki/Abstract_elementary_class)
- [S. Shelah, *Categoricity for abstract classes with amalgamation*](https://arxiv.org/abs/math/9809197)
- [W. Boney, *Tameness from large cardinal axioms*](https://arxiv.org/abs/1303.0550)
-/

namespace ShelahsEventualCategoricityConjecture

open FirstOrder FirstOrder.Language Cardinal

universe u

variable (L : FirstOrder.Language.{u, u})

/-- The data underlying an abstract elementary class: a class `K` of `L`-structures (with
universes in `Type u`) together with a class of `L`-embeddings between them, the `K`-embeddings.
An `L`-embedding `f : M ↪[L] N` is a `K`-embedding exactly when `f[M] ≺_K N`, where `≺_K` is the
strong substructure relation of `K`. In particular, for a substructure `N ≤ M`, `N ≺_K M` means
that the inclusion `N.subtype` is a `K`-embedding. -/
structure AbstractClass where
  /-- `IsModel M` means that the `L`-structure `M` belongs to the class `K`. -/
  IsModel : ∀ (M : Type u) [L.Structure M], Prop
  /-- `IsStrong f` means that the `L`-embedding `f : M ↪[L] N` is a `K`-embedding, i.e.
  `f[M] ≺_K N`. -/
  IsStrong : ∀ {M N : Type u} [L.Structure M] [L.Structure N], (M ↪[L] N) → Prop

variable {L}

namespace AbstractClass

/-- `K.IsLowenheimSkolemBound μ` means that `μ ≥ |L(K)| + ℵ₀` and that every subset `A` of a
model `M ∈ K` is contained in some `N ≺_K M` with `‖N‖ ≤ |A| + μ`. -/
def IsLowenheimSkolemBound (K : AbstractClass L) (μ : Cardinal.{u}) : Prop :=
  L.card + ℵ₀ ≤ μ ∧ ∀ (M : Type u) [L.Structure M], K.IsModel M → ∀ A : Set M,
    ∃ N : L.Substructure M, A ⊆ N ∧ #N ≤ #A + μ ∧ K.IsStrong N.subtype

/-- The Löwenheim–Skolem number `LS(K)` of `K`: the least cardinal `μ ≥ |L(K)| + ℵ₀` such that
every subset `A` of a model `M ∈ K` is contained in some `N ≺_K M` with `‖N‖ ≤ |A| + μ`. -/
noncomputable def lowenheimSkolemNumber (K : AbstractClass L) : Cardinal.{u} :=
  sInf {μ | K.IsLowenheimSkolemBound μ}

/-- `K.Categorical κ` means that `K` has exactly one model of cardinality `κ` up to
isomorphism. -/
def Categorical (K : AbstractClass L) (κ : Cardinal.{u}) : Prop :=
  (∃ (M : Type u) (_ : L.Structure M), K.IsModel M ∧ #M = κ) ∧
    ∀ (M N : Type u) [L.Structure M] [L.Structure N],
      K.IsModel M → K.IsModel N → #M = κ → #N = κ → Nonempty (M ≃[L] N)

end AbstractClass

variable (L) in
/-- An *abstract elementary class* (AEC) in the language `L`, with models in `Type u`.

It is given by a class `K` of `L`-structures together with the strong substructure relation
`≺_K`, encoded by the class of `K`-embeddings (`IsStrong`), subject to the following axioms.
* `≺_K` is a relation on `K`: a `K`-embedding goes between members of `K`.
* Isomorphisms: every isomorphism out of a member of `K` is a `K`-embedding (in particular `K` is
  closed under isomorphism and `≺_K` is reflexive on `K`), and `K`-embeddings are closed under
  composition (`≺_K` is transitive and respects isomorphisms).
* Coherence: if `M₁ ⊆ M₂ ≺_K M₃` and `M₁ ≺_K M₃`, then `M₁ ≺_K M₂`.
* Tarski–Vaught chain axioms: if `(Mᵢ)ᵢ` is a `≺_K`-chain indexed by a nonempty well-ordered
  type, then its union `⋃ᵢ Mᵢ` (the direct limit) is in `K`, `Mᵢ ≺_K ⋃ᵢ Mᵢ` for every `i`, and
  `⋃ᵢ Mᵢ ≺_K N` whenever `Mᵢ ≺_K N` for every `i`.
* Löwenheim–Skolem axiom: there is a cardinal `μ ≥ |L(K)| + ℵ₀` such that every subset `A` of a
  model `M ∈ K` is contained in some `N ≺_K M` with `‖N‖ ≤ |A| + μ`. -/
structure AbstractElementaryClass extends AbstractClass L where
  /-- `≺_K` is a relation on `K`. -/
  isModel_of_isStrong {M N : Type u} [L.Structure M] [L.Structure N] {f : M ↪[L] N} :
    IsStrong f → IsModel M ∧ IsModel N
  /-- Every isomorphism out of a member of `K` is a `K`-embedding. -/
  isStrong_equiv {M N : Type u} [L.Structure M] [L.Structure N] :
    IsModel M → ∀ e : M ≃[L] N, IsStrong e.toEmbedding
  /-- `K`-embeddings are closed under composition. -/
  isStrong_comp {M N P : Type u} [L.Structure M] [L.Structure N] [L.Structure P]
    {f : M ↪[L] N} {g : N ↪[L] P} : IsStrong f → IsStrong g → IsStrong (g.comp f)
  /-- Coherence: if `g` and `g ∘ f` are `K`-embeddings, then so is `f`. -/
  isStrong_of_comp {M N P : Type u} [L.Structure M] [L.Structure N] [L.Structure P]
    {f : M ↪[L] N} {g : N ↪[L] P} : IsStrong g → IsStrong (g.comp f) → IsStrong f
  /-- Chain axiom: the union of a `≺_K`-chain is in `K`. -/
  isModel_directLimit {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι]
    {G : ι → Type u} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h => f i j h] :
    (∀ i j h, IsStrong (f i j h)) → IsModel (Language.DirectLimit G f)
  /-- Chain axiom: every member of a `≺_K`-chain is a strong substructure of the union. -/
  isStrong_directLimit_of {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι]
    {G : ι → Type u} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h => f i j h] :
    (∀ i j h, IsStrong (f i j h)) → ∀ i, IsStrong (Language.DirectLimit.of L ι G f i)
  /-- Chain axiom: if every member of a `≺_K`-chain is a strong substructure of `N`, then so is
  the union. -/
  isStrong_directLimit_lift {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι]
    {G : ι → Type u} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h => f i j h] {N : Type u} [L.Structure N]
    (g : ∀ i, G i ↪[L] N) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    (∀ i j h, IsStrong (f i j h)) → (∀ i, IsStrong (g i)) →
      IsStrong (Language.DirectLimit.lift L ι G f g Hg)
  /-- Löwenheim–Skolem axiom. -/
  exists_isLowenheimSkolemBound : ∃ μ, toAbstractClass.IsLowenheimSkolemBound μ

namespace AbstractElementaryClass

variable (K : AbstractElementaryClass L) {M N : Type u} [L.Structure M] [L.Structure N]

variable (L) in
/-- The class of all `L`-structures, with all `L`-embeddings as `K`-embeddings, is an abstract
elementary class (with Löwenheim–Skolem number at most `|L| + ℵ₀`). -/
def univ : AbstractElementaryClass L where
  IsModel _ := True
  IsStrong _ := True
  isModel_of_isStrong _ := ⟨trivial, trivial⟩
  isStrong_equiv _ _ := trivial
  isStrong_comp _ _ := trivial
  isStrong_of_comp _ _ := trivial
  isModel_directLimit _ _ _ := trivial
  isStrong_directLimit_of _ _ _ _ := trivial
  isStrong_directLimit_lift _ _ _ _ _ _ _ _ := trivial
  exists_isLowenheimSkolemBound := by
    refine ⟨L.card + ℵ₀, le_rfl, fun M _ _ A => ⟨Substructure.closure L A,
      Substructure.subset_closure, ?_, trivial⟩⟩
    have h := Substructure.lift_card_closure_le (L := L) (s := A)
    simp only [lift_id] at h
    have hF : #(Σ i, L.Functions i) ≤ L.card := by
      rw [card, mk_sum, lift_id, lift_id]
      exact le_self_add
    refine h.trans (max_le ?_ ?_)
    · exact le_add_left le_add_self
    · exact add_le_add_right (hF.trans le_self_add) _

end AbstractElementaryClass

/-- **Shelah's eventual categoricity conjecture.**
For every cardinal $\lambda$ there exists a cardinal $\mu(\lambda)$ such that if an abstract
elementary class $K$ with $\operatorname{LS}(K) \le \lambda$ is categorical in some cardinal
$\kappa \ge \mu(\lambda)$, then it is categorical in every cardinal $\kappa \ge \mu(\lambda)$.

Here $\mu(\lambda)$ depends only on $\lambda$, not on $K$, and "categorical in $\kappa$" means
that $K$ has exactly one model of cardinality $\kappa$ up to isomorphism. -/
theorem shelahs_eventual_categoricity_conjecture :
    ∀ lam : Cardinal.{u}, ∃ μ : Cardinal.{u},
      ∀ (L : FirstOrder.Language.{u, u}) (K : AbstractElementaryClass L),
        K.lowenheimSkolemNumber ≤ lam → (∃ κ, μ ≤ κ ∧ K.Categorical κ) →
          ∀ κ, μ ≤ κ → K.Categorical κ := by
  sorry

end ShelahsEventualCategoricityConjecture

theorem ShelahsEventualCategoricityConjecture.shelahs_eventual_categoricity_conjecture.disproof : ¬ (type_of% @ShelahsEventualCategoricityConjecture.shelahs_eventual_categoricity_conjecture) := sorry
