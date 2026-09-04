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

/--
The maximum number of Sets among $n$ cards of the $3$-feature game (points of $\mathbb{F}_3^3$),
for every $3 \le n \le 27$, as determined by exhaustive computer search in [SW25, Table 3].
-/
theorem set.variants.three_features : ∀ n k : ℕ, (n, k) ∈ [(3, 1), (4, 1), (5, 2), (6, 3),
      (7, 5), (8, 8), (9, 12), (10, 12), (11, 13), (12, 14), (13, 16), (14, 19), (15, 23), (16, 26),
      (17, 30), (18, 36), (19, 41), (20, 47), (21, 54), (22, 62), (23, 71), (24, 81), (25, 92),
      (26, 104), (27, 117)] →
    maxSets 3 n = k := by
  sorry

end Set

theorem Set.set.variants.three_features.disproof : ¬ (type_of% @Set.set.variants.three_features) := sorry
