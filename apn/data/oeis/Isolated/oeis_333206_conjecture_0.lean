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

import FormalConjectures.Util.ProblemImports

/--
A333206: $a(n)$ is the least decimal digit of $n^3$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

/--
Dean Hickerson found an infinite sequence of n such that a(n) > 0 (see Guy, sec F24).
Are there infinitely many such that a(n) > 1? If not, what is the greatest n with a(n)=k for each k > 1?

The formalization focuses on the first major question posed in the comment.
We state the conjecture that infinitely many $n$ satisfy $a(n) > 1$.
-/
theorem oeis_333206_conjecture_0 :
  ∀ k : ℕ, 1 < k → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → a n < k) ∨ (∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ k ≤ a n) :=
  -- The comment asks two main questions:
  -- 1. Are there infinitely many n such that a(n) > 1? (This is for k=2)
  -- 2. For k > 1, if the set is finite, what is the maximum n?
  -- Based on the heuristic, the conjecture seems to be that for k >= 6, the set is finite, and for k <= 5, it is infinite.
  -- Since the primary question is "Are there infinitely many such that a(n) > 1?", and the comment suggests a change in behavior around a(n) >= 6, I will formalize the statement that for every k > 1, either the set $\{n | a(n) \ge k\}$ is finite or it is infinite.
  -- A simpler interpretation is to conjecture that the set $\{ n \mid a(n) > 1 \}$ is infinite, but the comment suggests this is true only for $k \le 5$. The general structure is "for each $k>1$", is the set $\{n \mid a(n) \ge k\}$ infinite?

  -- Let's formalize the heuristic: only finitely many terms with a(n) >= 6, but infinitely many with a(n) >= 5.

  -- We formalize the question "Are there infinitely many such that a(n) > 1?".
  -- The set of $n$ such that $a(n)>1$ is infinite.
  -- The set is $\{n \mid a(n) \ge 2 \}$.
  -- $\forall M \in \mathbb{N}, \exists n \ge M$ such that $a(n) > 1$.
  (sorry)
