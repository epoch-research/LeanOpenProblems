/-
Copyright 2025 The Formal Conjectures Authors.

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
# Kronecker coefficient

The Kronecker coefficients $g^\lambda_{\mu\nu}$ are the multiplicities in the decomposition of a
tensor product of two irreducible representations of the symmetric group $S_n$ into irreducible
representations: $V_\mu \otimes V_\nu = \bigoplus_\lambda g^\lambda_{\mu\nu} V_\lambda$.
They can be computed from the irreducible characters $\chi^\lambda$ of $S_n$ by
$$g^\lambda_{\mu\nu} = \frac{1}{n!} \sum_{\sigma \in S_n}
  \chi^\lambda(\sigma) \chi^\mu(\sigma) \chi^\nu(\sigma).$$

The Wikipedia list of unsolved problems asks to "give a combinatorial interpretation of the
Kronecker coefficients" (a question of Murnaghan, 1938). The standard formal version of this
problem, conjectured in Mulmuley's GCT6 and recorded by Ikenmeyer–Mulmuley–Walter, is that the
Kronecker coefficients have a `#P`-formula: there are a polynomial $p$ and a polynomial-time
computable $0$-$1$ function $F$ with
$$g^\lambda_{\mu\nu} = \sum_{\sigma \in \{0,1\}^{p(\langle\lambda\rangle, \langle\mu\rangle,
  \langle\nu\rangle)}} F(\lambda, \mu, \nu, \sigma),$$
where $\langle\lambda\rangle$ is the total bit-length of the parts of $\lambda$ written in binary.
In other words, the map $(\lambda, \mu, \nu) \mapsto g^\lambda_{\mu\nu}$, with the partitions
given in binary, is in the counting class `#P`. The weaker form in which the partitions are given
in unary is stated as a variant.

Mathlib has no Specht modules and no parametrisation of the irreducible characters of $S_n$ by
partitions, so this file defines $\chi^\lambda$ through the Frobenius character formula: for
$\sigma \in S_n$ of cycle type $\rho$ (fixed points counted as $1$-cycles), $\chi^\lambda(\sigma)$
is the coefficient of $x_1^{\lambda_1 + n - 1} x_2^{\lambda_2 + n - 2} \cdots x_n^{\lambda_n}$ in
$$\prod_{1 \le i < j \le n} (x_i - x_j) \cdot \prod_k p_{\rho_k}(x_1, \dots, x_n),$$
where $p_k = x_1^k + \dots + x_n^k$ is the $k$-th power sum and $\lambda_i = 0$ for $i$ larger
than the number of parts of $\lambda$.

*References:*
- [Wikipedia, Kronecker coefficient](https://en.wikipedia.org/wiki/Kronecker_coefficient)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- C. Ikenmeyer, K. D. Mulmuley, M. Walter, *On vanishing of Kronecker coefficients*,
  Comput. Complexity 26 (2017), [arXiv:1507.02955](https://arxiv.org/abs/1507.02955),
  Section 1.3.
- K. D. Mulmuley, *Geometric Complexity Theory VI: the flip via positivity*,
  [arXiv:0704.0229](https://arxiv.org/abs/0704.0229).
- R. P. Stanley, *Positivity problems and conjectures in algebraic combinatorics*, Problem 10.
- W. Fulton, J. Harris, *Representation Theory: A First Course*, Formula 4.10
  (Frobenius formula).
-/

namespace KroneckerCoefficient

open MvPolynomial

variable {n : ℕ}

/-- The part `μ_{i+1}` of the partition `μ` at position `i` (positions are counted from `0`,
parts are listed in decreasing order), with value `0` beyond the last part. -/
def part (μ : n.Partition) (i : ℕ) : ℕ :=
  (μ.parts.sort (· ≥ ·)).getD i 0

/-- The Vandermonde product `∏_{i < j} (X i - X j)` in the variables `X 0, …, X (n - 1)`. -/
noncomputable def vandermonde (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (X i - X j)

/-- The product `p_{ρ_1} ⋯ p_{ρ_k}` of the power sums `p_k = ∑ i, (X i) ^ k` over the cycle type
`ρ` of the permutation `σ ∈ S_n` (the fixed points of `σ` are counted as `1`-cycles). -/
noncomputable def powerSumProd (σ : Equiv.Perm (Fin n)) : MvPolynomial (Fin n) ℤ :=
  (σ.partition.parts.map (psum (Fin n) ℤ)).prod

/-- The value `χ^μ(σ)` of the irreducible character of `S_n` indexed by the partition `μ` of `n`
at the permutation `σ`, defined by the Frobenius character formula: the coefficient of
`X 0 ^ (μ_1 + n - 1) * X 1 ^ (μ_2 + n - 2) * ⋯ * X (n - 1) ^ μ_n` in the product of the
Vandermonde product and the power sums of the cycle type of `σ`. -/
noncomputable def character (μ : n.Partition) (σ : Equiv.Perm (Fin n)) : ℤ :=
  coeff (Finsupp.equivFunOnFinite.symm fun i : Fin n => part μ i + (n - 1 - i))
    (vandermonde n * powerSumProd σ)

/-- The Kronecker coefficient
`g^κ_{μν} = (1 / n!) * ∑_{σ ∈ S_n} χ^κ(σ) * χ^μ(σ) * χ^ν(σ)`
of three partitions `κ`, `μ`, `ν` of `n`. It is the multiplicity of the Specht module `V_κ` in
`V_μ ⊗ V_ν`, and hence a natural number. -/
noncomputable def kroneckerCoefficient (κ μ ν : n.Partition) : ℚ :=
  (∑ σ : Equiv.Perm (Fin n), (character κ σ * character μ σ * character ν σ : ℤ)) / n.factorial

/-- The bit-length `⟨μ⟩` of a partition `μ`: the total number of binary digits of its parts. -/
def bitLength (μ : n.Partition) : ℕ :=
  (μ.parts.map Nat.size).sum

/-- A self-delimiting binary encoding of a natural number `m`: each binary digit `b` of `m`
(least significant digit first) is written as the pair `[true, b]`, followed by a terminating
`false`. Its length is `2 * ⟨m⟩ + 1`, where `⟨m⟩` is the number of binary digits of `m`. -/
def encodeNat (m : ℕ) : List Bool :=
  (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]

/-- A self-delimiting binary encoding of a partition `μ`: for each part `m` of `μ` (in decreasing
order) the list `true :: encodeNat m`, followed by a terminating `false`. Its length is between
`⟨μ⟩` and `4 * ⟨μ⟩ + 1`, where `⟨μ⟩ = bitLength μ`. -/
def encodePartition (μ : n.Partition) : List Bool :=
  (μ.parts.sort (· ≥ ·)).flatMap (fun m => true :: encodeNat m) ++ [false]

/-- The binary encoding of a triple `(κ, μ, ν)` of partitions of `n`: the concatenation of the
(self-delimiting) encodings of the three partitions. -/
def encodeTriple (κ μ ν : n.Partition) : List Bool :=
  encodePartition κ ++ encodePartition μ ++ encodePartition ν

/-- A self-delimiting unary encoding of a partition `μ`: each part `m` of `μ` (in decreasing
order) is written as `m` copies of `true` followed by `false`, and the whole partition is
terminated by another `false`. Its length is `n + ℓ + 1`, where `ℓ` is the number of parts. -/
def unaryEncodePartition (μ : n.Partition) : List Bool :=
  (μ.parts.sort (· ≥ ·)).flatMap (fun m => List.replicate m true ++ [false]) ++ [false]

/-- The unary encoding of a triple `(κ, μ, ν)` of partitions of `n`: the concatenation of the
unary encodings of the three partitions. -/
def unaryEncodeTriple (κ μ ν : n.Partition) : List Bool :=
  unaryEncodePartition κ ++ unaryEncodePartition μ ++ unaryEncodePartition ν

/-- **Combinatorial interpretation of the Kronecker coefficients**

Wikipedia: "Give a combinatorial interpretation of the Kronecker coefficients" (Murnaghan, 1938).

Formal version (Ikenmeyer–Mulmuley–Walter, Section 1.3; conjectured in GCT6): the Kronecker
coefficients have a `#P`-formula, i.e. there exist a polynomial $p$ and a polynomial-time
computable $0$-$1$ function $F$ such that for all $n$ and all partitions $\lambda, \mu, \nu$ of $n$
$$g^\lambda_{\mu\nu} = \sum_{\sigma \in \{0,1\}^{p(\langle\lambda\rangle, \langle\mu\rangle,
  \langle\nu\rangle)}} F(\lambda, \mu, \nu, \sigma),$$
where $\langle\lambda\rangle$ is the total bit-length of the parts of $\lambda$ written in binary.
This is the binary (strong) form of the problem. In Lean the partition $\lambda$ is called `κ`,
and polynomial-time computability of `F` is in the sense of Mathlib's
`Turing.TM2ComputableInPolyTime`, with input the pair `(encodeTriple κ μ ν, σ)`, where
`encodeTriple κ μ ν` is a binary encoding of `(κ, μ, ν)` of length linear in
$\langle\lambda\rangle + \langle\mu\rangle + \langle\nu\rangle$. -/
theorem kronecker_coefficient :
    ∃ (p : MvPolynomial (Fin 3) ℕ) (F : List Bool × List Bool → Bool),
      Nonempty (Turing.TM2ComputableInPolyTime finEncodingListBoolProdListBool
        Computability.finEncodingBoolBool F) ∧
      ∀ (n : ℕ) (κ μ ν : n.Partition),
        kroneckerCoefficient κ μ ν =
          ((∑ σ : Fin (eval ![bitLength κ, bitLength μ, bitLength ν] p) → Bool,
            (F (encodeTriple κ μ ν, List.ofFn σ)).toNat : ℕ) : ℚ) := by
  sorry

end KroneckerCoefficient

theorem KroneckerCoefficient.kronecker_coefficient.disproof : ¬ (type_of% @KroneckerCoefficient.kronecker_coefficient) := sorry
