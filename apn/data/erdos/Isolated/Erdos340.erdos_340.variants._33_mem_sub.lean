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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 340

*Reference:* [erdosproblems.com/340](https://www.erdosproblems.com/340)
-/

open Filter Finset
open scoped Real Pointwise

namespace Erdos340

/-- Given a finite Sidon set `A` and a lower bound `m`, `go` finds the smallest number `m' ≥ m`
such that `A ∪ {m'}` is Sidon. If `A` is empty then this returns the value `m`. Note that
the lower bound is required to avoid `0` being a contender in some cases. -/
private def greedySidon.go (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ)} :=
  if h : A.Nonempty then
    haveI : ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
      simpa [and_assoc] using hA.exists_insert_ge h m
    ⟨Nat.find this, Nat.find_spec this⟩
  else ⟨m, by simp_all [IsSidon]⟩

/-- Main search loop for generating the greedy Sidon sequence. The return value for step `n` is the
finite set of numbers generated so far, a proof that it is Sidon, and the greatest element of
the finite set at that point. This is initialised at `{1}`, then `greedySidon.go` is
called iteratively using the lower bound `max + 1` to find the next smallest Sidon preserving
number. -/
private def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon (A : Set ℕ)} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A ∪ {s'.1}, s'.2.2.2⟩, s')

/-- `greedySidon` is the sequence obtained by the initial set $\{1\}$ and iteratively obtaining
then next smallest integer that preserves the Sidon property of the set. This gives the
sequence `1, 2, 4, 8, 13, 21, 31, ...`. -/
def greedySidon (n : ℕ) : ℕ := greedySidon.aux n |>.2

/--
The smallest integer which is unknown to be in $A - A$ is $33$.
 -/
theorem erdos_340.variants._33_mem_sub : 
    33 ∈ Set.range greedySidon - Set.range greedySidon := by
  sorry

end Erdos340

theorem Erdos340.erdos_340.variants._33_mem_sub.disproof : ¬ (type_of% @Erdos340.erdos_340.variants._33_mem_sub) := sorry
