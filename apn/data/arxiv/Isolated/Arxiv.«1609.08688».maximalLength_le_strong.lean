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
# The length of an $s$-increasing sequence of $r$-tuples

This file contains the formalisation of [GoLo21] up to and
including Conjecture 1.8.

*References:*
- [arxiv/1609.08688](https://arxiv.org/abs/1609.08688)
  **The length of an $s$-increasing sequence of $r$-tuples** by *W. T. Gowers, J. Long*
- [GoLo21](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/length-of-an-sincreasing-sequence-of-rtuples/7301418D47DB1ECD6BE71C20E8A98D0A)
  **The length of an $s$-increasing sequence of $r$-tuples**
  by *W. T. Gowers, J. Long*, Combinatorics, Probability and Computing (2021), 686-721
-/

namespace Arxiv.«1609.08688»

/--
Let $a = (a_1, a_2, a_3)$ and $b = (b_1, b_2, b_3)$ be two triples of integers.
Say that $a$ is $2$-less than $b$, or $a <_2 b$, if $a_i < b_i$ for at least
two coordinates $i$.
-/
def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

/--
Since the $2$-less relation is not transitive, we make a further definition to
specify transivity.
-/
def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

/--
Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with each coordinate
belong to $[n]$ ($= \{1, 2, ..., n\}$).
-/
noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

/-- Two triples $t_1$ and $t_2$ are $2$-comparable if one of them is $2$-less
than the other. -/
def IsComparable₂ {α : Type*} [LT α] (t₁ t₂ : Fin 3 → α) : Prop :=
  t₁ <₂ t₂ ∨ t₂ <₂ t₁

/-- A set of triples is $2$-comparable if any two of them are $2$-comparable. -/
def IsComparableSet₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop :=
  ∃ t₁ t₂, t₁ ≠ t₂ ∧ t₁ ∈ s ∧ t₂ ∈ s ∧ IsComparable₂ t₁ t₂

/-- We define the product of two triples $(a, b, c)$ and $(d, e, f)$ by
$((a, d), (b, e), (c, f))$, where the pairs are arranged in lexicographical order. -/
def tripleProduct {α : Type*} (a b : Fin 3 → α) : Πₗ (_ : Fin 3), α × α := toLex (Pi.prod a b)

/-- We define the product $\otimes$ of two sequences $(a_i, b_i, c_i)$ and
$(d_i, e_i, f_i)$ by the sequence $((a_i, d_j), (b_i, e_j), (c_i, f_j))$, where
the indices $(i, j)$ are arranged lexicographically, and the pairs are also
ordered lexicographically. -/
def sequenceProduct {α : Type*} (s t : List (Fin 3 → α)) : Lex (List (Πₗ (_ : Fin 3), α × α)) :=
  toLex (s.flatMap (fun a => List.map (tripleProduct a) t))

local infix:100 " ⊗₂ " => sequenceProduct

/-- $F(n) \leq n^{3/2}$. -/
theorem maximalLength_le_strong (n : ℕ) : F n ≤ Real.sqrt n ^ 3 := by
  sorry

end Arxiv.«1609.08688»

theorem Arxiv.«1609.08688».maximalLength_le_strong.disproof : ¬ (type_of% @Arxiv.«1609.08688».maximalLength_le_strong) := sorry
