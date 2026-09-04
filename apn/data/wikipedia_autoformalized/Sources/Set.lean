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
# Set: the maximum number of Sets among $n$ cards

The card game Set is played with a deck of $81$ cards. Each card has $4$ features
(number, shape, shading, colour), each taking one of $3$ values, so a card is a point of
$\mathbb{F}_3^4$. Three cards form a *Set* if, for each feature, the three cards are either
all the same or all different; equivalently, the three points form an affine line in
$\mathbb{F}_3^4$.

Stevens and Wilson proved that the maximum number of Sets among $12$ cards is $14$ (and more
generally determined the maximum for $3 \le n \le 12$ cards). Determining the maximum number of
Sets among $n$ cards for $n > 12$ is open. For the $3$-feature variant of the game (points of
$\mathbb{F}_3^3$) the maximum is known for every $n \le 27$ by exhaustive computer search, and
Stevens and Wilson conjecture that for $13 \le n \le 27$ the maximum for the standard
$4$-feature game is the same as for the $3$-feature game.

*References:*
- [Wikipedia: Set (card game)](https://en.wikipedia.org/wiki/Set_%28card_game%29)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [SW25] J. Stevens, D. Wilson, *The Maximum Number of Sets for 12 Cards is 14*,
  [arXiv:2501.12565](https://arxiv.org/abs/2501.12565)
-/

namespace Set

/-- A card of the game Set with `d` features: each feature takes one of `3` values, so a card
is a point of $\mathbb{F}_3^d$. The standard game has `d = 4` features and `81` cards. -/
abbrev Card (d : ℕ) := Fin d → ZMod 3

/-- A finite set of cards `s` is a *Set* if it consists of exactly `3` cards and, for every
feature `i`, the three cards are either all the same in feature `i` (the feature takes `1`
value on `s`) or all different in feature `i` (the feature takes `3` values on `s`).
Equivalently, `s` is a `3`-point affine line in $\mathbb{F}_3^d$. -/
def IsSet {d : ℕ} (s : Finset (Card d)) : Prop :=
  s.card = 3 ∧ ∀ i : Fin d, (s.image (· i)).card = 1 ∨ (s.image (· i)).card = 3

instance {d : ℕ} (s : Finset (Card d)) : Decidable (IsSet s) := by
  unfold IsSet
  infer_instance

/-- The number of Sets contained in a board `S` of cards, i.e. the number of `3`-card
subsets of `S` that are Sets. -/
def numSets {d : ℕ} (S : Finset (Card d)) : ℕ :=
  ((S.powersetCard 3).filter IsSet).card

/-- The maximum number of Sets contained in a board of `n` distinct cards of the game with
`d` features. (For `n > 3 ^ d` there is no such board and the value is `0`.) -/
def maxSets (d n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Card d)).powersetCard n).sup numSets

/-- Three cards that agree in the first three features and differ in the last one form
a Set. -/
@[category test, AMS 5 51]
theorem isSet_example₁ : IsSet {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2]} := by
  decide

/-- Three cards that agree in the first feature and differ in the other three form a Set. -/
@[category test, AMS 5 51]
theorem isSet_example₂ : IsSet {![0, 0, 0, 0], ![0, 1, 1, 1], ![0, 2, 2, 2]} := by
  decide

/-- Three cards with exactly two different values in some feature do not form a Set. -/
@[category test, AMS 5 51]
theorem not_isSet_example : ¬ IsSet {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]} := by
  decide

/-- The `5`-card board from [SW25] realising the maximum of `2` Sets for `5` cards. -/
@[category test, AMS 5 51]
theorem numSets_example :
    numSets {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2], ![0, 0, 1, 0], ![0, 0, 2, 0]} = 2 := by
  decide

/-- The `9` cards of an affine plane ("magic square") contain `12` Sets. -/
@[category test, AMS 5 51]
theorem numSets_plane :
    numSets {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2], ![0, 0, 1, 0], ![0, 0, 1, 1],
      ![0, 0, 1, 2], ![0, 0, 2, 0], ![0, 0, 2, 1], ![0, 0, 2, 2]} = 12 := by
  decide

/-- With one feature there are only three cards, and they form a single Set. -/
@[category test, AMS 5 51]
theorem maxSets_one_three : maxSets 1 3 = 1 := by
  decide

/-- With two features, four cards contain at most one Set. -/
@[category test, AMS 5 51]
theorem maxSets_two_four : maxSets 2 4 = 1 := by
  decide +kernel

/-- With two features, the nine cards of the whole deck contain twelve Sets, namely the
lines of the affine plane $\mathbb{F}_3^2$. -/
@[category test, AMS 5 51]
theorem maxSets_two_nine : maxSets 2 9 = 12 := by
  decide +kernel

/-- When a board of `n` cards exists (`n ≤ 3 ^ d`), `maxSets d n` is the greatest number of Sets
contained in a board of `n` cards. -/
@[category API, AMS 5 51]
theorem isGreatest_maxSets {d n : ℕ} (hn : n ≤ 3 ^ d) :
    IsGreatest {k | ∃ S : Finset (Card d), S.card = n ∧ numSets S = k} (maxSets d n) := by
  have hne : ((Finset.univ : Finset (Card d)).powersetCard n).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simpa [Fintype.card_fun, ZMod.card] using hn)
  constructor
  · obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup _ hne numSets
    exact ⟨S, (Finset.mem_powersetCard.1 hS).2, hmax.symm⟩
  · rintro k ⟨S, hS, rfl⟩
    exact Finset.le_sup (f := numSets) (Finset.mem_powersetCard.2 ⟨S.subset_univ, hS⟩)

/--
**The maximum number of Sets among $n$ cards** (Stevens–Wilson conjecture, [SW25, Section 6]).

For a board of $n$ distinct cards of the standard $4$-feature game of Set (points of
$\mathbb{F}_3^4$), the maximum possible number of Sets is known for $n \le 12$; in particular the
maximum number of Sets for $12$ cards is $14$. For $13 \le n \le 27$, Stevens and Wilson
conjecture that the maximum equals the corresponding (computer-verified) maximum for the
$3$-feature game, that is, the maximum number of Sets among $n$ cards is
$$16, 19, 23, 26, 30, 36, 41, 47, 54, 62, 71, 81, 92, 104, 117$$
for $n = 13, 14, \dots, 27$ respectively.
-/
@[category research open, AMS 5 51]
theorem set : ∀ n k : ℕ,
    (n, k) ∈ [(13, 16), (14, 19), (15, 23), (16, 26), (17, 30), (18, 36), (19, 41), (20, 47),
      (21, 54), (22, 62), (23, 71), (24, 81), (25, 92), (26, 104), (27, 117)] →
    maxSets 4 n = k := by
  sorry

/--
The Stevens–Wilson conjecture as phrased in [SW25]: for $13 \le n \le 27$, the maximum number of
Sets among $n$ cards with $4$ features is the same as the maximum number of Sets among $n$ cards
with $3$ features.
-/
@[category research open, AMS 5 51]
theorem set.variants.eq_three_features (n : ℕ) (h₁ : 13 ≤ n) (h₂ : n ≤ 27) :
    maxSets 4 n = maxSets 3 n := by
  sorry

/--
The maximum number of Sets among $n$ cards of the $3$-feature game (points of $\mathbb{F}_3^3$),
for every $3 \le n \le 27$, as determined by exhaustive computer search in [SW25, Table 3].
-/
@[category research solved, AMS 5 51]
theorem set.variants.three_features : ∀ n k : ℕ, (n, k) ∈ [(3, 1), (4, 1), (5, 2), (6, 3),
      (7, 5), (8, 8), (9, 12), (10, 12), (11, 13), (12, 14), (13, 16), (14, 19), (15, 23), (16, 26),
      (17, 30), (18, 36), (19, 41), (20, 47), (21, 54), (22, 62), (23, 71), (24, 81), (25, 92),
      (26, 104), (27, 117)] →
    maxSets 3 n = k := by
  sorry

end Set
