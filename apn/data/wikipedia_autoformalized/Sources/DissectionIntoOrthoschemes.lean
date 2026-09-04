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
# Dissection into orthoschemes

A *simplex* in $d$-dimensional Euclidean space is the convex hull of $d + 1$ points that do not
all lie in a common hyperplane. An *orthoscheme* (or *path simplex*) is a simplex whose vertices
can be ordered as $v_0, v_1, \dots, v_d$ so that the edges $v_0v_1, v_1v_2, \dots, v_{d-1}v_d$
of this path are pairwise orthogonal. A *dissection* of a simplex is a representation of it as a
finite union of simplices with pairwise disjoint interiors.

Hadwiger (1956) conjectured that there is a function $f : \mathbb{N} \to \mathbb{N}$ such that
every $d$-dimensional simplex can be dissected into at most $f(d)$ orthoschemes. This is known
for $d \le 5$ and open for all $d \ge 6$.

*References:*
* [Wikipedia, Dissection into orthoschemes](https://en.wikipedia.org/wiki/Dissection_into_orthoschemes)
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Ha56] Hadwiger, Hugo, *Ungelöste Probleme*, Elemente der Mathematik 11 (1956), 109–110.
-/

open Affine
open scoped EuclideanGeometry

namespace DissectionIntoOrthoschemes

variable {d n : ℕ}

/-- A simplex `S` in Euclidean space is an *orthoscheme* (or *path simplex*) if its vertices can
be ordered as $v_0, v_1, \dots, v_n$ so that the edges $v_0v_1, v_1v_2, \dots, v_{n-1}v_n$ of
this path are pairwise orthogonal. -/
def IsOrthoscheme (S : Simplex ℝ (ℝ^d) n) : Prop :=
  ∃ σ : Equiv.Perm (Fin (n + 1)), Pairwise fun i j : Fin n ↦
    inner ℝ (S.points (σ i.succ) -ᵥ S.points (σ i.castSucc))
      (S.points (σ j.succ) -ᵥ S.points (σ j.castSucc)) = 0

/-- A `d`-simplex `S` in `ℝ^d` *can be dissected into `n` orthoschemes* if it is the union of
`n` orthoschemes (each a `d`-simplex in `ℝ^d`) whose interiors are pairwise disjoint. -/
def IsDissectableIntoOrthoschemes (n : ℕ) (S : Simplex ℝ (ℝ^d) d) : Prop :=
  ∃ Ts : Fin n → Simplex ℝ (ℝ^d) d,
    (∀ i, IsOrthoscheme (Ts i)) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
      ⋃ i, (Ts i).closedInterior = S.closedInterior

/-- A simplex cannot be dissected into zero orthoschemes. -/
@[category API, AMS 51 52]
lemma IsDissectableIntoOrthoschemes.ne_zero {S : Simplex ℝ (ℝ^d) d}
    (hS : IsDissectableIntoOrthoschemes n S) : n ≠ 0 := by
  rintro rfl
  obtain ⟨Ts, -, -, hS⟩ := hS
  exact S.closedInterior_nonempty.ne_empty <| by simpa using hS.symm

/-- An orthoscheme can be dissected into one orthoscheme, namely itself. -/
@[category API, AMS 51 52]
lemma IsOrthoscheme.isDissectableIntoOrthoschemes_one {S : Simplex ℝ (ℝ^d) d}
    (hS : IsOrthoscheme S) : IsDissectableIntoOrthoschemes 1 S :=
  ⟨fun _ ↦ S, fun _ ↦ hS, Subsingleton.pairwise, Set.iUnion_const _⟩

/--
**Hadwiger's conjecture on dissection into orthoschemes** (list entry: "Dissection into
orthoschemes – is it possible for simplices of every dimension?").

Is there a function $f : \mathbb{N} \to \mathbb{N}$ such that, for every dimension $d$, every
$d$-dimensional simplex in $\mathbb{R}^d$ can be dissected into at most $f(d)$ orthoschemes,
i.e. written as a union of at most $f(d)$ orthoschemes with pairwise disjoint interiors?

The bound $f(d)$ depends only on the dimension $d$, not on the simplex.
-/
@[category research open, AMS 51 52]
theorem dissection_into_orthoschemes :
    answer(sorry) ↔ ∃ f : ℕ → ℕ, ∀ (d : ℕ) (S : Simplex ℝ (ℝ^d) d),
      ∃ n ≤ f d, IsDissectableIntoOrthoschemes n S := by
  sorry

/--
The literal reading of the list entry, without a uniform bound (Hadwiger's original
"finitely many" phrasing): for every dimension $d$, can every $d$-dimensional simplex in
$\mathbb{R}^d$ be dissected into finitely many orthoschemes?

This is implied by `dissection_into_orthoschemes` and is also open for $d \ge 6$.
-/
@[category research open, AMS 51 52]
theorem dissection_into_orthoschemes.variants.finite :
    answer(sorry) ↔ ∀ (d : ℕ) (S : Simplex ℝ (ℝ^d) d),
      ∃ n, IsDissectableIntoOrthoschemes n S := by
  sorry

end DissectionIntoOrthoschemes
