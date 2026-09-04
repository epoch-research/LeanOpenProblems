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
# Hilbert's 9th problem

Hilbert's ninth problem asks to find the most general reciprocity law for the norm residues of
$k$-th order in a general algebraic number field, where $k$ is a power of a prime. In Hilbert's
words (1900): "For any field of numbers the law of reciprocity is to be proved for the residues of
the $l$-th power, when $l$ denotes an odd prime, and further when $l$ is a power of $2$ or a power
of an odd prime."

The abelian case was solved by Artin's reciprocity law (Artin 1927), which together with the work
of Takagi and Hasse developed into class field theory. This file states that solved case: for a
finite abelian extension $L/K$ of number fields whose Galois group has exponent dividing a prime
power $k$, there is a nonzero ideal $\mathfrak m$ of $\mathcal O_K$ such that the Artin symbol
$((\alpha), L/K) = \prod_{\mathfrak p} \mathrm{Frob}_{\mathfrak p}^{v_{\mathfrak p}(\alpha)}$ is
trivial for every totally positive $\alpha \in \mathcal O_K$ with
$\alpha \equiv 1 \pmod{\mathfrak m}$.
When $K$ contains the $k$-th roots of unity, these extensions are exactly the Kummer extensions of
exponent $k$ of $K$, and the statement is equivalent to Hilbert's product formula
$\prod_v (a, b)_v = 1$ for the norm residue symbols of $k$-th order.

The general (non-abelian) case is open. The expected answer is Langlands' reciprocity conjecture
(every irreducible $n$-dimensional representation of $\mathrm{Gal}(L/K)$ has the same $L$-function
as some cuspidal automorphic representation of $\mathrm{GL}_n(\mathbb A_K)$). Its statement needs
cuspidal automorphic representations and their $L$-functions, which are not available in Mathlib,
so it is not stated here.

*References:*
- [Wikipedia, Hilbert's ninth problem](https://en.wikipedia.org/wiki/Hilbert%27s_ninth_problem)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Artin reciprocity](https://en.wikipedia.org/wiki/Artin_reciprocity)
- E. Artin, *Beweis des allgemeinen Reziprozitätsgesetzes*, Abh. Math. Sem. Univ. Hamburg 5 (1927),
  353–363.
- D. Hilbert, *Mathematical problems*, Bull. Amer. Math. Soc. 8 (1902), 437–479.
-/

namespace Hilberts9thProblem

open NumberField UniqueFactorizationMonoid

variable {K L : Type*} [Field K] [NumberField K] [Field L] [Algebra K L]

/-- The **Artin symbol** `(I, L/K)` of an ideal `I` of `𝓞 K`, for an abelian extension `L/K` and
a choice `frob` of elements of `Gal(L/K)` indexed by the ideals of `𝓞 K` (only the values at the
nonzero prime ideals matter): the product `∏_𝔭 (frob 𝔭) ^ v_𝔭(I)` of the `frob 𝔭` over the prime
ideal factors `𝔭` of `I`, counted with multiplicity. When `frob 𝔭` is the Frobenius element at `𝔭`
for every prime factor `𝔭` of `I`, this is the classical Artin symbol of `I`. -/
noncomputable def artinSymbol [IsAbelianGalois K L] (frob : Ideal (𝓞 K) → Gal(L/K))
    (I : Ideal (𝓞 K)) : Gal(L/K) :=
  ((normalizedFactors I).map frob).prod

variable [NumberField L]

/-- `σ ∈ Gal(L/K)` is a **Frobenius element** at the prime ideal `𝔭` of `𝓞 K`: there is a prime
ideal `𝔓` of `𝓞 L` lying over `𝔭` such that `σ x ≡ x ^ N𝔭 (mod 𝔓)` for all `x ∈ 𝓞 L`, where
`N𝔭 = #(𝓞 K ⧸ 𝔭)` is the absolute norm of `𝔭`. If `𝔭` is unramified in `L` and `L/K` is abelian,
there is exactly one such element. -/
def IsFrobeniusAt (𝔭 : Ideal (𝓞 K)) (σ : Gal(L/K)) : Prop :=
  ∃ 𝔓 ∈ 𝔭.primesOver (𝓞 L), (galRestrict (𝓞 K) K L (𝓞 L) σ).toAlgHom.IsArithFrobAt 𝔓

/-- **Hilbert's 9th problem, abelian case: the reciprocity law for norm residues of $k$-th order**
(Artin's reciprocity law for abelian extensions of exponent dividing $k$).

Let $k$ be a power of a prime, let $K$ be a number field and let $L/K$ be a finite abelian
extension whose Galois group has exponent dividing $k$ (i.e. $\sigma^k = 1$ for all
$\sigma \in \mathrm{Gal}(L/K)$; when $\zeta_k \in K$ these are exactly the Kummer extensions of
exponent $k$ of $K$). Then there is a nonzero ideal $\mathfrak m$ of $\mathcal O_K$ such that,
for every choice of Frobenius elements $\mathrm{Frob}_{\mathfrak p} \in \mathrm{Gal}(L/K)$ at the
nonzero prime ideals $\mathfrak p \nmid \mathfrak m$, and every totally positive
$\alpha \in \mathcal O_K$ with $\alpha \equiv 1 \pmod{\mathfrak m}$, the Artin symbol of the
principal ideal $(\alpha)$ is trivial:
$$((\alpha), L/K) = \prod_{\mathfrak p} \mathrm{Frob}_{\mathfrak p}^{v_{\mathfrak p}(\alpha)} = 1.$$

Since the Frobenius element at a prime ramified in $L$ is not unique, such an $\mathfrak m$ is
necessarily divisible by every prime of $K$ that ramifies in $L$ (for instance, the finite part of
the conductor of $L/K$ works), so that the Frobenius elements appearing in the product are the
usual ones. Equivalently, the Artin map $\mathfrak a \mapsto (\mathfrak a, L/K)$ on the ideals of
$K$ coprime to $\mathfrak m$ is trivial on the subgroup $P_{\mathfrak m, 1}$ of principal ideals
$(\alpha)$ with $\alpha \equiv 1 \pmod{\mathfrak m}$ and $\alpha$ positive at every real place.
For $\zeta_k \in K$, this is equivalent to Hilbert's product formula $\prod_v (a, b)_v = 1$ for the
norm residue symbols of $k$-th order. It was proved by Artin (1927), following Furtwängler and
Takagi. -/
theorem hilberts_9th_problem.variants.abelian (k : ℕ) (hk : IsPrimePow k)
    [IsAbelianGalois K L] (hL : ∀ σ : Gal(L/K), σ ^ k = 1) :
    ∃ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ 0 ∧
      ∀ frob : Ideal (𝓞 K) → Gal(L/K),
        (∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔭 ∣ 𝔪 → IsFrobeniusAt 𝔭 (frob 𝔭)) →
        ∀ α : 𝓞 K, α - 1 ∈ 𝔪 → (∀ φ : K →+* ℝ, 0 < φ α) →
          artinSymbol frob (Ideal.span {α}) = 1 := by
  sorry

end Hilberts9thProblem

theorem Hilberts9thProblem.hilberts_9th_problem.variants.abelian.disproof : ¬ (type_of% @Hilberts9thProblem.hilberts_9th_problem.variants.abelian) := sorry
