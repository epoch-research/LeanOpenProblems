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
# Lehmer pairs

A *Lehmer pair* is a pair of consecutive zeros $\tfrac12 + i\gamma_n$, $\tfrac12 + i\gamma_{n+1}$
of the Riemann zeta function on the critical line that are unusually close to each other.
Writing $0 < \gamma_1 < \gamma_2 < \cdots$ for the positive ordinates of the zeros of $\zeta$ on
the critical line, the pair $(\gamma_n, \gamma_{n+1})$ is a Lehmer pair if
$$\frac{1}{(\gamma_n - \gamma_{n+1})^2} \geq
  C \sum_{m \notin \{n, n+1\}} \left(\frac{1}{(\gamma_m - \gamma_n)^2} +
  \frac{1}{(\gamma_m - \gamma_{n+1})^2}\right)$$
for a constant $C > 5/4$. The first example, found by D. H. Lehmer, is the pair of zeros
$\tfrac12 + i\,7005.06266\ldots$ and $\tfrac12 + i\,7005.10056\ldots$
(the 6709th and 6710th zeros).

It is an open problem whether there are infinitely many Lehmer pairs. Csordas, Smith and Varga
showed that a positive answer would imply that the de Bruijn–Newman constant $\Lambda$ is
non-negative; this was later proved unconditionally by Rodgers and Tao.

In this file the ordinates are handled as a set of real numbers rather than as an enumerated
sequence: two ordinates are consecutive if no ordinate lies strictly between them, and the sum
over $m \notin \{n, n+1\}$ runs over all positive ordinates other than the two of the pair.
Under the Riemann hypothesis with simple zeros, the setting in which Lehmer pairs are usually
discussed, this agrees with the indexed formulation above.

The phrase "for a constant $C > 5/4$" can be read with $C$ depending on the pair (the original
definition of Csordas, Smith and Varga, which is equivalent to the strict inequality with
$C = 5/4$) or with one fixed $C$ for the whole infinite family (the "$C$-Lehmer pairs" of Tao).
The first reading is `lehmer_pair`; the second is `lehmer_pair.variants.uniform_constant`.

*References:*
- [Wikipedia: Lehmer pair](https://en.wikipedia.org/wiki/Lehmer_pair)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- G. Csordas, W. Smith, R. S. Varga, *Lehmer pairs of zeros, the de Bruijn–Newman constant
  $\Lambda$, and the Riemann hypothesis*, Constr. Approx. **10** (1994), 107–129.
  [doi:10.1007/BF01205170](https://doi.org/10.1007/BF01205170)
- D. H. Lehmer, *On the roots of the Riemann zeta-function*, Acta Math. **95** (1956), 291–298.
  [doi:10.1007/BF02401102](https://doi.org/10.1007/BF02401102)
- T. Tao, [*Lehmer pairs and GUE*](https://terrytao.wordpress.com/2018/01/20/lehmer-pairs-and-gue/),
  blog post (2018).
- B. Rodgers, T. Tao, *The De Bruijn–Newman constant is non-negative*, Forum Math. Pi **8**
  (2020). [arXiv:1801.05914](https://arxiv.org/abs/1801.05914)
-/

open Complex

namespace LehmerPair

/-- The set of positive ordinates of the zeros of the Riemann zeta function on the critical
line, i.e. the real numbers $\gamma > 0$ with $\zeta(\tfrac12 + i\gamma) = 0$.

Under the Riemann hypothesis this is the set of imaginary parts of all nontrivial zeros of
$\zeta$ in the upper half-plane. Each zero contributes one point, whatever its multiplicity. -/
def zetaZeroOrdinates : Set ℝ := {γ : ℝ | 0 < γ ∧ riemannZeta (1 / 2 + γ * I) = 0}

/-- `IsConsecutiveOrdinates γ γ'` says that `γ < γ'` are elements of `zetaZeroOrdinates` with
no element of `zetaZeroOrdinates` strictly between them, i.e. $\gamma = \gamma_n$ and
$\gamma' = \gamma_{n+1}$ for some $n$ in the increasing enumeration $0 < \gamma_1 < \gamma_2
< \cdots$ of the positive ordinates of the critical line zeros of $\zeta$. -/
def IsConsecutiveOrdinates (γ γ' : ℝ) : Prop :=
  γ ∈ zetaZeroOrdinates ∧ γ' ∈ zetaZeroOrdinates ∧ γ < γ' ∧
    ∀ δ ∈ zetaZeroOrdinates, δ ∉ Set.Ioo γ γ'

/-- `IsLehmerPair C γ γ'` says that `γ = γₙ` and `γ' = γₙ₊₁` are consecutive positive ordinates
of critical line zeros of $\zeta$ satisfying
$$\frac{1}{(\gamma_n - \gamma_{n+1})^2} \geq
  C \sum_{m \notin \{n, n+1\}} \left(\frac{1}{(\gamma_m - \gamma_n)^2} +
  \frac{1}{(\gamma_m - \gamma_{n+1})^2}\right),$$
where the sum runs over all positive ordinates $\gamma_m$ of critical line zeros of $\zeta$
other than $\gamma_n$ and $\gamma_{n+1}$. The series has positive terms and converges, since
$\sum_m \gamma_m^{-2} < \infty$; the `HasSum` clause names its value `S`.

A *Lehmer pair* is a pair `(γ, γ')` with `IsLehmerPair C γ γ'` for some constant `C > 5 / 4`. -/
def IsLehmerPair (C γ γ' : ℝ) : Prop :=
  IsConsecutiveOrdinates γ γ' ∧
    ∃ S : ℝ, HasSum (fun δ : ↥(zetaZeroOrdinates \ {γ, γ'}) =>
      1 / ((δ : ℝ) - γ) ^ 2 + 1 / ((δ : ℝ) - γ') ^ 2) S ∧
      C * S ≤ 1 / (γ - γ') ^ 2

/-- Are there infinitely many Lehmer pairs? That is, are there infinitely many pairs
$(\gamma_n, \gamma_{n+1})$ of consecutive positive ordinates of critical line zeros of the
Riemann zeta function such that
$$\frac{1}{(\gamma_n - \gamma_{n+1})^2} \geq
  C \sum_{m \notin \{n, n+1\}} \left(\frac{1}{(\gamma_m - \gamma_n)^2} +
  \frac{1}{(\gamma_m - \gamma_{n+1})^2}\right)$$
for some constant $C > 5/4$? Here $C$ may depend on the pair, as in the original definition of
Csordas, Smith and Varga; equivalently, the inequality holds strictly with $C = 5/4$. -/
theorem lehmer_pair :
    {p : ℝ × ℝ | ∃ C > 5 / 4, IsLehmerPair C p.1 p.2}.Infinite := by
  sorry

end LehmerPair

theorem LehmerPair.lehmer_pair.disproof : ¬ (type_of% @LehmerPair.lehmer_pair) := sorry
