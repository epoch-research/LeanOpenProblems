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
# Selberg's orthogonality conjecture

The Selberg class $\mathcal{S}$ is the set of Dirichlet series
$F(s) = \sum_{n \ge 1} a_n n^{-s}$ that satisfy Selberg's axioms:
absolute convergence for $\operatorname{Re}(s) > 1$ with $a_1 = 1$, a meromorphic continuation
such that $(s-1)^m F(s)$ is an entire function of finite order for some $m \in \mathbb{N}$,
a functional equation with gamma factors, an Euler product
$F(s) = \prod_p F_p(s)$ with $F_p(s) = \exp\left(\sum_{k \ge 1} b_{p^k} p^{-ks}\right)$ and
$b_{p^k} = O(p^{k\theta})$ for some $\theta < 1/2$, and the Ramanujan hypothesis
$a_n = O(n^\varepsilon)$ for every $\varepsilon > 0$.

Selberg's orthogonality conjecture is the pair of conjectures made by Selberg (1992):

* **Conjecture 1** (Murty's Conjecture A): for all $F \in \mathcal{S}$ there is an integer $n_F$
  with $\sum_{p \le x} |a_p|^2 / p = n_F \log \log x + O(1)$. This generalizes Mertens' second
  theorem $\sum_{p \le x} 1/p = \log \log x + O(1)$, which is the case $F = \zeta$.
* **Conjecture 2** (Murty's Conjecture B(ii)): for distinct primitive $F, F' \in \mathcal{S}$,
  $\sum_{p \le x} a_p(F) \overline{a_p(F')} / p = O(1)$.

Selberg's original formulation and Murty's Conjecture B(i) also assert that $n_F = 1$ for every
primitive $F$. This normalization is recorded as a variant. Wikipedia lists "$n_F = 1$ if and
only if $F$ is primitive" among the consequences of the conjecture.

We represent an element of the Selberg class by its sequence of Dirichlet coefficients, an
`ArithmeticFunction ℂ` (a function `ℕ → ℂ` vanishing at `0`). A Dirichlet series is determined by
its coefficients, so equality of elements of `ArithmeticFunction ℂ` is equality of Dirichlet series,
and multiplication of arithmetic functions (Dirichlet convolution) is multiplication of Dirichlet
series.

*References:*
- [Wikipedia: Selberg class, Conjectures](https://en.wikipedia.org/wiki/Selberg_class%23Conjectures)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- A. Selberg, *Old and new conjectures and results about a class of Dirichlet series*,
  Proceedings of the Amalfi Conference on Analytic Number Theory (Maiori, 1989), Univ. Salerno,
  1992, pp. 367–385.
- [M. Ram Murty, *Selberg's conjectures and Artin L-functions*, Bull. Amer. Math. Soc. 31 (1994),
  1–14](https://arxiv.org/abs/math/9407219)
-/

namespace SelbergsOrthogonalityConjecture

open Complex Filter Asymptotics ComplexConjugate

/-- A function `G : ℂ → ℂ` is an entire function of finite order if it is holomorphic on `ℂ` and
there are constants $A, B, \rho$ with $|G(z)| \le A e^{B |z|^\rho}$ for all $z \in \mathbb{C}$. -/
def IsEntireOfFiniteOrder (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ ∃ A B ρ : ℝ, ∀ z : ℂ, ‖G z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)

/-- The **Selberg class** $\mathcal{S}$, as a set of coefficient sequences
`a : ArithmeticFunction ℂ`.
The sequence `a` belongs to `selbergClass` if the Dirichlet series
$F(s) = \sum_{n \ge 1} a_n n^{-s}$ satisfies Selberg's axioms:

1. (Dirichlet series) $a_1 = 1$ and the series converges absolutely for $\operatorname{Re}(s) > 1$.
2. (Analytic continuation) $F$ extends to a meromorphic function on $\mathbb{C}$ such that
   $(s - 1)^m F(s)$ is an entire function of finite order for some integer $m \ge 0$.
3. (Functional equation) There are $Q > 0$, $\alpha_i > 0$, $\operatorname{Re}(r_i) \ge 0$
   ($1 \le i \le d$) and $w \in \mathbb{C}$ with $|w| = 1$ such that
   $\Phi(s) = Q^s \prod_{i=1}^d \Gamma(\alpha_i s + r_i) F(s)$ satisfies
   $\Phi(s) = w \overline{\Phi(1 - \overline{s})}$.
4. (Euler product) $F(s) = \prod_p F_p(s)$ for $\operatorname{Re}(s) > 1$, where
   $F_p(s) = \exp\left(\sum_{k \ge 1} b_{p^k} p^{-ks}\right)$ and $b_{p^k} = O(p^{k\theta})$
   for some $\theta < 1/2$.
5. (Ramanujan hypothesis) $a_n = O(n^\varepsilon)$ for every fixed $\varepsilon > 0$.

The continuation `F` is only used at points `s ≠ 1`, so its value at the possible pole `s = 1`
is irrelevant. The functional equation is required on the strip $0 < \operatorname{Re}(s) < 1$,
which is mapped to itself by $s \mapsto 1 - \overline{s}$ and contains no pole of $F$ or of the
gamma factors. Both sides are meromorphic on $\mathbb{C}$, so by the identity theorem this is
equivalent to the functional equation as an identity of meromorphic functions. -/
def selbergClass : Set (ArithmeticFunction ℂ) :=
  {a | a 1 = 1 ∧
    (∀ ε : ℝ, 0 < ε → (fun n : ℕ => a n) =O[atTop] fun n : ℕ => (n : ℝ) ^ ε) ∧
    ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → LSeriesHasSum a s (F s)) ∧
      (∃ (m : ℕ) (G : ℂ → ℂ), IsEntireOfFiniteOrder G ∧
        ∀ s : ℂ, s ≠ 1 → G s = (s - 1) ^ m * F s) ∧
      (∃ (Q : ℝ) (d : ℕ) (α : Fin d → ℝ) (r : Fin d → ℂ) (w : ℂ),
        0 < Q ∧ (∀ i, 0 < α i) ∧ (∀ i, 0 ≤ (r i).re) ∧ ‖w‖ = 1 ∧
        ∀ s : ℂ, 0 < s.re → s.re < 1 →
          (Q : ℂ) ^ s * (∏ i, Gamma (α i * s + r i)) * F s =
            w * conj ((Q : ℂ) ^ (1 - conj s) * (∏ i, Gamma (α i * (1 - conj s) + r i)) *
              F (1 - conj s))) ∧
      (∃ (b : ℕ → ℂ) (θ : ℝ), θ < 1 / 2 ∧
        (∃ C : ℝ, ∀ p k : ℕ, p.Prime → 0 < k → ‖b (p ^ k)‖ ≤ C * (p : ℝ) ^ (k * θ)) ∧
        ∀ s : ℂ, 1 < s.re →
          HasProd (fun p : Nat.Primes => exp (∑' k : ℕ, b (p ^ (k + 1)) / (p : ℂ) ^ ((k + 1) * s)))
            (F s))}

/-- An element $F \ne 1$ of the Selberg class is **primitive** if, whenever $F = F_1 F_2$ with
$F_1, F_2 \in \mathcal{S}$, then $F = F_1$ or $F = F_2$. Here `1 : ArithmeticFunction ℂ` is the
coefficient sequence of the constant Dirichlet series $F = 1$, and `F₁ * F₂` is the Dirichlet
convolution, i.e. the coefficient sequence of the product $F_1 F_2$. -/
def IsPrimitive (a : ArithmeticFunction ℂ) : Prop :=
  a ∈ selbergClass ∧ a ≠ 1 ∧
    ∀ a₁ ∈ selbergClass, ∀ a₂ ∈ selbergClass, a = a₁ * a₂ → a = a₁ ∨ a = a₂

/-- **Selberg's Conjecture 2** (Murty's Conjecture B(ii)). For distinct primitive
$F, F' \in \mathcal{S}$ with coefficients $a_p$ and $a'_p$,
$$\sum_{p \le x} \frac{a_p \overline{a'_p}}{p} = O(1).$$ -/
theorem selbergs_orthogonality_conjecture.parts.ii (a a' : ArithmeticFunction ℂ)
    (ha : IsPrimitive a) (ha' : IsPrimitive a') (hne : a ≠ a') :
    (fun x : ℝ => ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), a p * conj (a' p) / p)
      =O[atTop] (fun _ => (1 : ℝ)) := by
  sorry

end SelbergsOrthogonalityConjecture

theorem SelbergsOrthogonalityConjecture.selbergs_orthogonality_conjecture.parts.ii.disproof : ¬ (type_of% @SelbergsOrthogonalityConjecture.selbergs_orthogonality_conjecture.parts.ii) := sorry
