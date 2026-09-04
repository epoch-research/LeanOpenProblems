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
# Superpermutations

A *superpermutation* on $n$ symbols is a string over an alphabet of $n$ symbols that contains
each of the $n!$ permutations of the symbols as a contiguous substring. For instance, $121$ is a
superpermutation on $2$ symbols, since it contains both $12$ and $21$. The problem asks for the
smallest possible length $L(n)$ of such a string.

It is known that $L(n) = 1! + 2! + \dots + n!$ for $1 \le n \le 5$. The conjecture that this
formula holds for every $n$ is false: Houston (2014) found a superpermutation on $6$ symbols of
length $872 < 873$. For $n > 5$ the exact value of $L(n)$ is unknown; the best known general
bounds are
$$n! + (n-1)! + (n-2)! + n - 3 \le L(n) \le n! + (n-1)! + (n-2)! + (n-3)! + n - 3.$$

We model a string of $n$ digits as a word `w : List (Fin n)`, a permutation of the $n$ symbols
as the word `List.ofFn σ` for `σ : Equiv.Perm (Fin n)` (one-line notation), and "contains" as
`List.IsInfix` (contiguous substring).

*References:*
- [Wikipedia, Superpermutation](https://en.wikipedia.org/wiki/Superpermutation)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [OEIS A180632](https://oeis.org/A180632)
- N. Johnston, *Non-uniqueness of minimal superpermutations*, Discrete Mathematics 313 (2013),
  1553–1557. [arXiv:1303.4150](https://arxiv.org/abs/1303.4150)
- R. Houston, *Tackling the Minimal Superpermutation Problem*.
  [arXiv:1408.5108](https://arxiv.org/abs/1408.5108)
- Anonymous 4chan poster, R. Houston, J. Pantone, V. Vatter,
  *A lower bound on the length of the shortest superpattern* (2018).
  [OEIS A180632 attachment](https://oeis.org/A180632/a180632.pdf)
- G. Egan, [*Superpermutations*](http://www.gregegan.net/SCIENCE/Superpermutations/Superpermutations.html)
-/

open scoped Nat

namespace Superpermutation

/--
A word `w` over the alphabet `Fin n` is a *superpermutation* on `n` symbols if it contains every
permutation of the `n` symbols as a contiguous substring. The permutation `σ` is identified with
the word `List.ofFn σ = [σ 0, σ 1, …, σ (n - 1)]`.
-/
def IsSuperpermutation {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), List.ofFn σ <:+: w

instance {n : ℕ} (w : List (Fin n)) : Decidable (IsSuperpermutation w) :=
  inferInstanceAs (Decidable (∀ σ : Equiv.Perm (Fin n), List.ofFn σ <:+: w))

/-- The length $L(n)$ of a shortest superpermutation on `n` symbols. -/
noncomputable def minLength (n : ℕ) : ℕ :=
  sInf {k | ∃ w : List (Fin n), IsSuperpermutation w ∧ w.length = k}

/--
**Lower bound** (anonymous 4chan poster 2011; Houston, Pantone, Vatter 2018).
For $n \ge 2$, the smallest superpermutation on $n$ symbols has length at least
$n! + (n-1)! + (n-2)! + n - 3$.
-/
theorem superpermutation.variants.lower_bound :
    ∀ n : ℕ, 2 ≤ n → n ! + (n - 1)! + (n - 2)! + n - 3 ≤ minLength n := by
  sorry

end Superpermutation

theorem Superpermutation.superpermutation.variants.lower_bound.disproof : ¬ (type_of% @Superpermutation.superpermutation.variants.lower_bound) := sorry
