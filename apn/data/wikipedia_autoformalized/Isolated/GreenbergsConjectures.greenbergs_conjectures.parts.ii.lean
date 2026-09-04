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
# Greenberg's conjectures

Two open conjectures of Ralph Greenberg in algebraic number theory.

* **Greenberg's invariants conjecture** (1971/1976). For every totally real number field $k$ and
  every prime $\ell$, the Iwasawa invariants of the cyclotomic $\mathbb{Z}_\ell$-extension
  $k_\infty/k$ vanish: $\lambda_\ell(k) = \mu_\ell(k) = 0$. Equivalently (by Iwasawa's formula
  $e_n = \lambda n + \mu \ell^n + \nu$ for $n \gg 0$), the exact power $\ell^{e_n}$ of $\ell$
  dividing the class number of the $n$-th layer $k_n$ of $k_\infty/k$ is bounded as
  $n \to \infty$. This bounded-class-number form is the one stated here.
* **Greenberg's $p$-rationality conjecture** (2016). For every odd prime $p$ and every $t$,
  there is a $p$-rational number field $K$ with
  $\operatorname{Gal}(K/\mathbb{Q}) \cong (\mathbb{Z}/2\mathbb{Z})^t$.

*References:*
* [Wikipedia, Greenberg's conjectures](https://en.wikipedia.org/wiki/Greenberg%27s_conjectures)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* R. Greenberg, *On the Iwasawa invariants of totally real number fields*,
  Amer. J. Math. 98 (1976), 263–284.
* R. Greenberg, [*Galois representations with open image*](https://arxiv.org/abs/1408.6788),
  Ann. Math. Québec 40 (2016), 83–119, Conjecture 4.2.1.
* A. Movahhedi, T. Nguyen Quang Do, *Sur l'arithmétique des corps de nombres $p$-rationnels*,
  Séminaire de Théorie des Nombres, Paris 1987–88, Progr. Math. 81 (1990), 155–200.
-/

open NumberField NumberField.InfinitePlace

namespace GreenbergsConjectures

/--
A finite extension `L/K` of number fields is *unramified outside `p`* if every nonzero prime
ideal of `𝓞 L` not containing `p` (i.e. not lying above `p`) is unramified over `𝓞 K`. By
`Algebra.isUnramifiedAt_iff_of_isDedekindDomain` this says exactly that all such primes have
ramification index `1` over `𝓞 K`. Infinite places are not considered; for odd `p` a
`p`-extension is automatically unramified at the infinite places.
-/
def IsUnramifiedOutside (p : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ → (p : 𝓞 L) ∉ P → Algebra.IsUnramifiedAt (𝓞 K) P

/--
The maximal abelian pro-`p` extension of `K` unramified outside `p`, as a subfield of a fixed
algebraic closure of `K`: the compositum of all finite abelian extensions `L/K` of `p`-power
degree that are unramified outside `p`.
-/
noncomputable def maxAbelianPExtension (p : ℕ) (K : Type*) [Field K] :
    IntermediateField K (AlgebraicClosure K) :=
  ⨆ L ∈ {L : IntermediateField K (AlgebraicClosure K) | FiniteDimensional K L ∧ IsGalois K L ∧
    IsMulCommutative (L ≃ₐ[K] L) ∧ IsPGroup p (L ≃ₐ[K] L) ∧ IsUnramifiedOutside p K L}, L

/--
A number field `K` is *`p`-rational* if the Galois group of its maximal abelian pro-`p`
extension unramified outside `p` is isomorphic, as a topological group (Krull topology), to
$\mathbb{Z}_p^{r_2 + 1}$, where $r_2$ is the number of complex places of `K`.

This is the form of the definition used by Greenberg (2016). For odd `p` it is equivalent
(Movahhedi–Nguyen Quang Do) to the original definition: the Galois group of the maximal pro-`p`
extension of `K` unramified outside `p` is a free pro-`p` group. Since this Galois group is
$\mathbb{Z}_p^{r_2 + 1 + \delta} \oplus T$ with $\delta$ the Leopoldt defect and $T$ finite,
it is also equivalent to: Leopoldt's conjecture holds for `K` at `p` and $T$ is trivial.
The definition is only intended for odd `p`; for `p = 2` conventions about the infinite places
differ in the literature.
-/
def IsPRational (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] : Prop :=
  Nonempty ((maxAbelianPExtension p K ≃ₐ[K] maxAbelianPExtension p K) ≃ₜ*
    Multiplicative (Fin (nrComplexPlaces K + 1) → ℤ_[p]))

/--
**Greenberg's $p$-rationality conjecture** (Greenberg, 2016, Conjecture 4.2.1). For every odd
prime $p$ and every $t$, there exists a $p$-rational number field $K$, Galois over $\mathbb{Q}$,
with $\operatorname{Gal}(K/\mathbb{Q}) \cong (\mathbb{Z}/2\mathbb{Z})^t$.

The case $t = 0$ is included; it holds with $K = \mathbb{Q}$.
-/
theorem greenbergs_conjectures.parts.ii (p : ℕ) [Fact p.Prime] (hp : Odd p) (t : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsGalois ℚ K ∧
      Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (Fin t → ZMod 2)) ∧ IsPRational p K := by
  sorry

end GreenbergsConjectures

theorem GreenbergsConjectures.greenbergs_conjectures.parts.ii.disproof : ¬ (type_of% @GreenbergsConjectures.greenbergs_conjectures.parts.ii) := sorry
