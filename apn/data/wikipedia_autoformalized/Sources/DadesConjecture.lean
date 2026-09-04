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
# Dade's conjecture

Dade's conjecture relates the numbers of irreducible characters in the $p$-blocks of a finite
group $G$ to the numbers of irreducible characters in $p$-blocks of local subgroups, namely the
normalizers of chains of $p$-subgroups of $G$. This file states Dade's *ordinary conjecture*
(Dade 1992, Conjecture 6.3), the form referred to by the Wikipedia list entry.

We use the classical set-up of block theory (Isaacs, *Character theory of finite groups*, Ch. 15;
Navarro, *Characters and blocks of finite groups*, Ch. 3): fix a maximal ideal $M$ of the ring
$\mathbf{R}$ of algebraic integers in $\mathbb{C}$ with $p \in M$, so that $\mathbf{R}/M$ is an
algebraically closed field of characteristic $p$.

* For $\chi \in \operatorname{Irr}(G)$ the central character $\omega_\chi$ sends the class sum
  $K^+$ of a conjugacy class $K$ of $G$ to $\omega_\chi(K^+) = \sum_{x \in K} \chi(x)/\chi(1)
  = |K| \chi(g)/\chi(1) \in \mathbf{R}$ (for $g \in K$). Two irreducible characters of $G$ lie in
  the same $p$-block iff their central characters agree modulo $M$ on all class sums.
* For a subgroup $H \le G$, a $p$-block $b$ of $H$ and a $p$-block $B$ of $G$, the Brauer induced
  block $b^G$ is defined and equals $B$ iff
  $\omega_\chi(K^+) \equiv \omega_\psi((K \cap H)^+) \pmod M$ for all conjugacy classes $K$ of
  $G$, where $\psi \in b$, $\chi \in B$ and $(K \cap H)^+ = \sum_{h \in K \cap H} h$.
* The $p$-defect $d(\psi)$ of $\psi \in \operatorname{Irr}(H)$ is defined by
  $p^{d(\psi)} = |H|_p / \psi(1)_p$. The defect of a block is the maximum of the defects of its
  irreducible characters; in particular a block has positive defect iff it contains an
  irreducible character of positive defect.
* $O_p(H)$ denotes the largest normal $p$-subgroup of $H$.
* A *radical $p$-chain* of $G$ is a strictly increasing chain $C : P_0 < P_1 < \dots < P_n$ of
  $p$-subgroups of $G$ with $P_0 = O_p(G)$ and $P_i = O_p(N_G(P_0) \cap \dots \cap N_G(P_i))$ for
  all $i$. Its length is $|C| = n$ and its normalizer is
  $N_G(C) = N_G(P_0) \cap \dots \cap N_G(P_n)$. The group $G$ acts on the set $\mathcal{R}(G)$ of
  radical $p$-chains by conjugation.
* For $H \le G$, a block $B$ of $G$ and $d \ge 0$, $k(H, B, d)$ is the number of
  $\psi \in \operatorname{Irr}(H)$ with $d(\psi) = d$ whose block $b$ satisfies $b^G = B$.

**Dade's ordinary conjecture.** Let $G$ be a finite group and $p$ a prime with $O_p(G) = 1$. Then
for every $p$-block $B$ of $G$ of positive defect and every integer $d \ge 0$,
$$\sum_{C \in \mathcal{R}(G)/G} (-1)^{|C|} k(N_G(C), B, d) = 0,$$
where $C$ runs over a set of representatives of the $G$-conjugacy classes of radical $p$-chains.

*References:*
* [Wikipedia, Dade's conjecture](https://en.wikipedia.org/wiki/Dade%27s_conjecture)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* E. C. Dade, *Counting characters in blocks. I*, Invent. Math. 109 (1992), 187–210.
  [doi:10.1007/BF01232023](https://doi.org/10.1007/BF01232023)
* E. C. Dade, *Counting characters in blocks. II*, J. reine angew. Math. 448 (1994), 97–190.
  [doi:10.1515/crll.1994.448.97](https://doi.org/10.1515/crll.1994.448.97)
* E. C. Dade, *Counting characters in blocks. II.9*, in: Representation theory of finite groups
  (Columbus, OH, 1995), de Gruyter, Berlin, 1997, 45–59.
-/

namespace DadesConjecture

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `O_p(H)` for a subgroup `H` of `G`, regarded as a subgroup of `G`: the largest normal
`p`-subgroup of `H`, i.e. the join of all `p`-subgroups `P ≤ H` that are normalized by `H`. -/
def pCore (p : ℕ) (H : Subgroup G) : Subgroup G :=
  sSup {P : Subgroup G | P ≤ H ∧ H ≤ P.normalizer ∧ IsPGroup p P}

/-- The normalizer `N_G(C) = N_G(P₀) ∩ ⋯ ∩ N_G(Pₙ)` of a chain `C = [P₀, …, Pₙ]` of
subgroups. -/
def chainNormalizer (C : List (Subgroup G)) : Subgroup G :=
  ⨅ P ∈ C, P.normalizer

/-- A radical `p`-chain of `G` in the sense of Dade: a strictly increasing chain
`P₀ < P₁ < ⋯ < Pₙ` of `p`-subgroups of `G` such that `P₀ = O_p(G)` and
`Pᵢ = O_p(N_G(P₀) ∩ ⋯ ∩ N_G(Pᵢ))` for every `i`. The chain is recorded as the list
`[P₀, …, Pₙ]`. -/
structure RadicalPChain (p : ℕ) (G : Type*) [Group G] where
  /-- The subgroups `P₀, …, Pₙ` of the chain, in increasing order. -/
  toList : List (Subgroup G)
  /-- The chain is nonempty. -/
  ne_nil : toList ≠ []
  /-- The chain is strictly increasing. -/
  sorted : toList.Pairwise (· < ·)
  /-- Every member of the chain is a `p`-subgroup. -/
  isPGroup : ∀ P ∈ toList, IsPGroup p P
  /-- `P₀ = O_p(G)`. -/
  head_eq : toList.head ne_nil = pCore p ⊤
  /-- `Pᵢ = O_p(N_G(Cᵢ))` where `Cᵢ : P₀ < ⋯ < Pᵢ` is the initial subchain. -/
  radical : ∀ i (hi : i < toList.length),
    toList[i] = pCore p (chainNormalizer (toList.take (i + 1)))

namespace RadicalPChain

variable {p : ℕ}

/-- The length `|C| = n` of the radical `p`-chain `C : P₀ < ⋯ < Pₙ`. -/
def length (C : RadicalPChain p G) : ℕ := C.toList.length - 1

/-- The normalizer `N_G(C) = N_G(P₀) ∩ ⋯ ∩ N_G(Pₙ)` of the radical `p`-chain `C`. -/
def normalizer (C : RadicalPChain p G) : Subgroup G := chainNormalizer C.toList

/-- Two radical `p`-chains are conjugate if some `g ∈ G` maps the first onto the second by
conjugation, `Pᵢ ↦ g Pᵢ g⁻¹`. -/
def IsConj (C C' : RadicalPChain p G) : Prop :=
  ∃ g : G, C'.toList = C.toList.map (MulAut.conj g • ·)

/-- A finite set `S` of radical `p`-chains is a set of representatives of the `G`-conjugacy
classes of radical `p`-chains if every radical `p`-chain is conjugate to exactly one element of
`S`. -/
def IsConjClassRepresentatives (S : Finset (RadicalPChain p G)) : Prop :=
  ∀ C : RadicalPChain p G, ∃! C', C' ∈ S ∧ C.IsConj C'

end RadicalPChain

/-- `χ : G → ℂ` is the character of an irreducible complex representation of `G` of degree
`n`, that is, `χ(g)` is the trace of `ρ(g)` for an irreducible representation `ρ` of `G` on
`ℂⁿ`. -/
def IsIrrCharOfDegree (n : ℕ) (χ : G → ℂ) : Prop :=
  ∃ ρ : Representation ℂ G (Fin n → ℂ), ρ.IsIrreducible ∧
    ∀ g, χ g = LinearMap.trace ℂ (Fin n → ℂ) (ρ g)

/-- `χ : G → ℂ` is an irreducible complex character of `G` of `p`-defect `d`, i.e.
$p^d = |G|_p / \chi(1)_p$. -/
def IsIrrCharOfDefect (p d : ℕ) (χ : G → ℂ) : Prop :=
  ∃ n, IsIrrCharOfDegree n χ ∧ padicValNat p (Nat.card G) = padicValNat p n + d

/-- The value $\omega_\chi(K^+) = \sum_{x \in K} \chi(x)/\chi(1)$ of the central character of
`χ` on the class sum of the conjugacy class `K` of `g` in `G`. -/
noncomputable def centralChar (χ : G → ℂ) (g : G) : ℂ :=
  ∑ᶠ x ∈ {x : G | IsConj g x}, χ x / χ 1

/-- For a character `ψ` of a subgroup `H ≤ G` and `g ∈ G` with `G`-conjugacy class `K`, the
value $\omega_\psi((K \cap H)^+) = \sum_{h \in K \cap H} \psi(h)/\psi(1)$ of the central character
of `ψ` on the sum of the elements of `H` that are conjugate in `G` to `g`. -/
noncomputable def centralCharInter (H : Subgroup G) (ψ : H → ℂ) (g : G) : ℂ :=
  ∑ᶠ h ∈ {h : H | IsConj g (h : G)}, ψ h / ψ 1

/-- Brauer induction of blocks, with respect to the maximal ideal `M` of the algebraic integers:
the `p`-block `b` of `H ≤ G` containing the irreducible character `ψ` satisfies `b^G = B`, where
`B` is the `p`-block of `G` containing the irreducible character `χ`. This holds iff the central
characters satisfy $\omega_\chi(K^+) \equiv \omega_\psi((K \cap H)^+) \pmod M$ for every
conjugacy class `K` of `G`. -/
def BlockInducesTo (M : Ideal (integralClosure ℤ ℂ)) (H : Subgroup G) (ψ : H → ℂ)
    (χ : G → ℂ) : Prop :=
  ∀ g : G, ∃ r ∈ M, (r : ℂ) = centralChar χ g - centralCharInter H ψ g

/-- The number `k(H, B, d)` of irreducible characters `ψ` of the subgroup `H ≤ G` of `p`-defect
`d` whose `p`-block `b` satisfies `b^G = B`, where `B` is the `p`-block of `G` containing the
irreducible character `χ` of `G`. -/
noncomputable def numChars (p : ℕ) (M : Ideal (integralClosure ℤ ℂ)) (H : Subgroup G)
    (χ : G → ℂ) (d : ℕ) : ℕ :=
  {ψ : H → ℂ | IsIrrCharOfDefect p d ψ ∧ BlockInducesTo M H ψ χ}.ncard

/-- `O_p(H)` is contained in `H`. -/
@[category API, AMS 20]
theorem pCore_le (p : ℕ) (H : Subgroup G) : pCore p H ≤ H :=
  sSup_le fun _ hP => hP.1

/-- Every radical `p`-chain is conjugate to itself. -/
@[category API, AMS 20]
theorem RadicalPChain.isConj_self {p : ℕ} (C : RadicalPChain p G) : C.IsConj C :=
  ⟨1, by simp⟩

/-- If `O_p(G) = 1`, the chain `1` of length `0` is a radical `p`-chain of `G`. -/
def RadicalPChain.trivial {p : ℕ} (h : pCore p (⊤ : Subgroup G) = ⊥) : RadicalPChain p G where
  toList := [⊥]
  ne_nil := by simp
  sorted := List.pairwise_singleton _ _
  isPGroup := by simpa using IsPGroup.of_bot
  head_eq := by simpa using h.symm
  radical i hi := by
    obtain rfl : i = 0 := by simpa using hi
    simpa [chainNormalizer, Subgroup.normalizer_eq_top] using h.symm

/-- The chain `1` has length `0`. -/
@[category test, AMS 20]
theorem RadicalPChain.length_trivial {p : ℕ} (h : pCore p (⊤ : Subgroup G) = ⊥) :
    (RadicalPChain.trivial h).length = 0 := rfl

/-- The normalizer of the chain `1` is `G`. -/
@[category test, AMS 20]
theorem RadicalPChain.normalizer_trivial {p : ℕ} (h : pCore p (⊤ : Subgroup G) = ⊥) :
    (RadicalPChain.trivial h).normalizer = ⊤ := by
  simp [RadicalPChain.trivial, RadicalPChain.normalizer, chainNormalizer,
    Subgroup.normalizer_eq_top]

/-- An irreducible character of degree `n` takes the value `n` at the identity. -/
@[category API, AMS 20]
theorem IsIrrCharOfDegree.apply_one {n : ℕ} {χ : G → ℂ} (h : IsIrrCharOfDegree n χ) :
    χ 1 = n := by
  obtain ⟨ρ, -, hχ⟩ := h
  simp [hχ]

/-- The central character takes the value `1` on the class sum of the identity. -/
@[category API, AMS 20]
theorem centralChar_one {χ : G → ℂ} (hχ : χ 1 ≠ 0) : centralChar χ 1 = 1 := by
  simp [centralChar, hχ]

/--
**Dade's ordinary conjecture** (Dade 1992, Conjecture 6.3). Let $G$ be a finite group and $p$ a
prime such that $O_p(G) = 1$. Let $B$ be a $p$-block of $G$ of positive defect and let $d \ge 0$.
Then
$$\sum_{C \in \mathcal{R}(G)/G} (-1)^{|C|} k(N_G(C), B, d) = 0,$$
where $C$ runs over a set of representatives of the $G$-conjugacy classes of radical $p$-chains
of $G$, $N_G(C)$ is the normalizer of $C$, and $k(N_G(C), B, d)$ is the number of irreducible
characters of $N_G(C)$ of $p$-defect $d$ lying in blocks $b$ of $N_G(C)$ with $b^G = B$.

Here blocks are taken with respect to a maximal ideal $M$ of the algebraic integers containing
$p$. The block $B$ is specified by an irreducible character $\chi \in B$; since the defect of a
block is the maximum of the defects of its characters, the blocks of positive defect are exactly
the blocks of the irreducible characters $\chi$ of positive defect.
-/
@[category research open, AMS 20]
theorem dades_conjecture {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : pCore p (⊤ : Subgroup G) = ⊥)
    (M : Ideal (integralClosure ℤ ℂ)) [M.IsMaximal] (hpM : (p : integralClosure ℤ ℂ) ∈ M)
    {χ : G → ℂ} {e : ℕ} (hχ : IsIrrCharOfDefect p e χ) (he : 0 < e) (d : ℕ)
    {S : Finset (RadicalPChain p G)} (hS : RadicalPChain.IsConjClassRepresentatives S) :
    ∑ C ∈ S, (-1 : ℤ) ^ C.length * numChars p M C.normalizer χ d = 0 := by
  sorry

end DadesConjecture
