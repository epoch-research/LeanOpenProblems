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
# Central binomial sum $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$

The sequence is defined by
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k.$$

*References:*
- [A179537](https://oeis.org/A179537)
- Z.-W. Sun, "Open Conjectures on Congruences", arXiv preprint
  [arXiv:0911.5665](https://arxiv.org/abs/0911.5665) [math.NT], 2009-2011.-/

namespace OeisA179537

/-- The sequence $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) ^ 2 * ((n - k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k

/--
$\sum_{k=0}^{p-1} (42k + 37) (-1)^k a(k) \equiv p(21(p/7) + 16) \pmod{p^2}$ for any prime $p \ne 7$.
- _Zhi-Wei Sun_, Jul 17 2010
-/
theorem conjecture4 (p : ℕ) [Fact p.Prime] (_hp7 : p ≠ 7) :
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    (∑ k ∈ Finset.range p, ((42 * (k : ℤ) + 37) * (-1 : ℤ) ^ k * a k)) ≡
      (p : ℤ) * (21 * legendreSym 7 p + 16) [ZMOD (p : ℤ) ^ 2] := by
  sorry

end OeisA179537

theorem OeisA179537.conjecture4.disproof : ¬ (type_of% @OeisA179537.conjecture4) := sorry
