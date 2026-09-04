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

/-- Concatenating all permutations gives a superpermutation, so superpermutations exist. -/
@[category API, AMS 5]
theorem exists_isSuperpermutation (n : ℕ) : ∃ w : List (Fin n), IsSuperpermutation w :=
  ⟨(Finset.univ : Finset (Equiv.Perm (Fin n))).toList.flatMap fun σ : Equiv.Perm (Fin n) =>
      List.ofFn σ,
    fun σ => List.infix_of_mem_flatten <|
      List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ σ))⟩

@[category API, AMS 5]
theorem minLength_le {n : ℕ} {w : List (Fin n)} (hw : IsSuperpermutation w) :
    minLength n ≤ w.length :=
  Nat.sInf_le ⟨w, hw, rfl⟩

@[category API, AMS 5]
theorem le_minLength {n m : ℕ}
    (h : ∀ w : List (Fin n), IsSuperpermutation w → m ≤ w.length) : m ≤ minLength n :=
  le_csInf (let ⟨w, hw⟩ := exists_isSuperpermutation n; ⟨_, w, hw, rfl⟩)
    fun _ ⟨w, hw, hk⟩ => hk ▸ h w hw

/-- Some superpermutation on `n` symbols has length exactly `minLength n`. -/
@[category API, AMS 5]
theorem exists_isSuperpermutation_length_eq_minLength (n : ℕ) :
    ∃ w : List (Fin n), IsSuperpermutation w ∧ w.length = minLength n := by
  obtain ⟨w, hw⟩ := exists_isSuperpermutation n
  exact Nat.sInf_mem (s := {k | ∃ w : List (Fin n), IsSuperpermutation w ∧ w.length = k})
    ⟨w.length, w, hw, rfl⟩

/-- The word `121` is a superpermutation on `2` symbols. -/
@[category test, AMS 5]
theorem isSuperpermutation_two : IsSuperpermutation ([0, 1, 0] : List (Fin 2)) := by
  decide

/-- The word `12` is not a superpermutation on `2` symbols. -/
@[category test, AMS 5]
theorem not_isSuperpermutation_two : ¬ IsSuperpermutation ([0, 1] : List (Fin 2)) := by
  decide

/-- The word `123121321` is a superpermutation on `3` symbols. -/
@[category test, AMS 5]
theorem isSuperpermutation_three :
    IsSuperpermutation ([0, 1, 2, 0, 1, 0, 2, 1, 0] : List (Fin 3)) := by
  decide

/-- The word `12312132` is not a superpermutation on `3` symbols (it misses `321`). -/
@[category test, AMS 5]
theorem not_isSuperpermutation_three :
    ¬ IsSuperpermutation ([0, 1, 2, 0, 1, 0, 2, 1] : List (Fin 3)) := by
  decide

/-- The empty word is a superpermutation on `0` symbols, so $L(0) = 0 = \sum_{k=1}^0 k!$. -/
@[category test, AMS 5]
theorem minLength_zero : minLength 0 = 0 :=
  Nat.le_zero.1 (minLength_le (w := []) fun _ => by simp)

/-- $L(1) = 1$. -/
@[category test, AMS 5]
theorem minLength_one : minLength 1 = 1 := by
  refine le_antisymm (minLength_le (w := [0]) (by decide)) ?_
  exact le_minLength fun w hw => by simpa using (hw 1).length_le

/-- $L(2) = 3$. -/
@[category test, AMS 5]
theorem minLength_two : minLength 2 = 3 := by
  refine le_antisymm (minLength_le isSuperpermutation_two) ?_
  refine le_minLength fun w hw => ?_
  have h1 := hw 1
  have h2 := hw (Equiv.swap 0 1)
  by_contra h
  have e1 := h1.eq_of_length_le (by simpa using Nat.lt_succ_iff.1 (not_le.1 h))
  have e2 := h2.eq_of_length_le (by simpa using Nat.lt_succ_iff.1 (not_le.1 h))
  rw [← e1] at e2
  have := congrArg (·[0]?) e2
  simp at this

/--
**Superpermutations.** The problem asks for the smallest possible length $L(n)$ of a string of
$n$ digits that contains all possible permutations of the $n$ digits as contiguous substrings.

The pattern for $1 \le n \le 5$ suggested the answer $L(n) = 1! + 2! + \dots + n!$ for all
$n \ge 1$ (Ashlock–Tillotson 1993; Johnston 2013, Conjecture 1). This conjectured formula is
false: Houston (2014) found a superpermutation on $6$ symbols of length
$872 < 873 = 1! + 2! + \dots + 6!$.
-/
@[category research solved, AMS 5]
theorem superpermutation :
    ¬ ∀ n : ℕ, 1 ≤ n → minLength n = ∑ k ∈ Finset.Icc 1 n, k ! := by
  sorry

/--
The open problem itself: determine, for every $n$, the length $L(n)$ of the smallest possible
string over $n$ symbols that contains all permutations of the $n$ symbols as contiguous
substrings. The value is known only for $n \le 5$. (For $n = 0$ the empty word gives
$L(0) = 0$.)
-/
@[category research open, AMS 5]
theorem superpermutation.variants.minimal_length : minLength = answer(sorry) := by
  sorry

/--
For $1 \le n \le 5$, the smallest superpermutation on $n$ symbols has length
$1! + 2! + \dots + n!$, i.e. $L(1), \dots, L(5) = 1, 3, 9, 33, 153$.
-/
@[category research solved, AMS 5]
theorem superpermutation.variants.le_five :
    ∀ n : ℕ, 1 ≤ n → n ≤ 5 → minLength n = ∑ k ∈ Finset.Icc 1 n, k ! := by
  sorry

/--
**Lower bound** (anonymous 4chan poster 2011; Houston, Pantone, Vatter 2018).
For $n \ge 2$, the smallest superpermutation on $n$ symbols has length at least
$n! + (n-1)! + (n-2)! + n - 3$.
-/
@[category research solved, AMS 5]
theorem superpermutation.variants.lower_bound :
    ∀ n : ℕ, 2 ≤ n → n ! + (n - 1)! + (n - 2)! + n - 3 ≤ minLength n := by
  sorry

/--
**Upper bound** (Egan 2018, adapting a Hamiltonian-path construction of Williams).
Egan's algorithm produces a superpermutation on $n$ symbols of length
$n! + (n-1)! + (n-2)! + (n-3)! + n - 3$, so $L(n)$ is at most this value.
The hypothesis $n \ge 3$ only ensures that the term $(n-3)!$ is meaningful.
-/
@[category research solved, AMS 5]
theorem superpermutation.variants.upper_bound :
    ∀ n : ℕ, 3 ≤ n → minLength n ≤ n ! + (n - 1)! + (n - 2)! + (n - 3)! + n - 3 := by
  sorry

/--
Egan (2019) produced a superpermutation on $7$ symbols of length $5906$, beating the general
upper bound $7! + 6! + 5! + 4! + 7 - 3 = 5908$ and Coanda's record $5907$. Hence $L(7) \le 5906$.
-/
@[category research solved, AMS 5]
theorem superpermutation.variants.seven : minLength 7 ≤ 5906 := by
  sorry

/--
Do superpermutations shorter than Egan's general bound also exist for every $n > 7$? That is, is
$L(n) < n! + (n-1)! + (n-2)! + (n-3)! + n - 3$ for all $n > 7$? (For $n = 6$ and $n = 7$ such
shorter superpermutations are known: $872 < 873$ and $5906 < 5908$.)
-/
@[category research open, AMS 5]
theorem superpermutation.variants.beyond_seven :
    answer(sorry) ↔ ∀ n : ℕ, 7 < n →
      minLength n < n ! + (n - 1)! + (n - 2)! + (n - 3)! + n - 3 := by
  sorry

end Superpermutation
