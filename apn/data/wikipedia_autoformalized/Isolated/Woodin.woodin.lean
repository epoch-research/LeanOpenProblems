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
# Woodin's question: GCH below a strongly compact cardinal

Woodin asked whether the generalized continuum hypothesis (GCH) below a strongly compact
cardinal implies GCH everywhere. That is, if $\kappa$ is strongly compact and
$2^\lambda = \lambda^+$ for every infinite cardinal $\lambda < \kappa$, must
$2^\lambda = \lambda^+$ hold for every infinite cardinal $\lambda$?

An uncountable cardinal $\kappa$ is *strongly compact* if every $\kappa$-complete filter
(on any set) can be extended to a $\kappa$-complete ultrafilter. Mathlib does not define
strongly compact cardinals, so this file defines them in terms of `CardinalInterFilter`.

*References:*
- [Wikipedia, W. Hugh Woodin](https://en.wikipedia.org/wiki/W._Hugh_Woodin)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Strongly compact cardinal](https://en.wikipedia.org/wiki/Strongly_compact_cardinal)
- A. Kanamori, *The Higher Infinite*, Chapter 1, §4 (strongly compact cardinals)
- T. Jech, *Set Theory*, 3rd millennium edition, Chapter 20 (strongly compact cardinals)
-/

universe u

namespace Woodin

open Cardinal

/--
A cardinal `κ` is *strongly compact* if it is uncountable and, for every type `S` (in the
same universe as `κ`), every proper `κ`-complete filter on `S` extends to a `κ`-complete
ultrafilter on `S`. Here a filter is `κ`-complete if it is closed under intersections of
fewer than `κ` of its members, see `CardinalInterFilter`.

The uncountability requirement is part of the standard definition: every proper filter
extends to an ultrafilter, so `ℵ₀` would otherwise satisfy the extension property trivially.
Since Mathlib's `Filter` includes the improper filter `⊥`, the filter to be extended is
required to be `NeBot`.
-/
def IsStronglyCompact (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ ∀ (S : Type u) (F : Filter S), F.NeBot → CardinalInterFilter F κ →
    ∃ U : Ultrafilter S, (U : Filter S) ≤ F ∧ CardinalInterFilter (U : Filter S) κ

/--
**Woodin's question.** Does the generalized continuum hypothesis below a strongly compact
cardinal imply the generalized continuum hypothesis everywhere?

That is, for every strongly compact cardinal $\kappa$: if $2^\lambda = \lambda^+$ for every
infinite cardinal $\lambda < \kappa$, then $2^\lambda = \lambda^+$ for every infinite
cardinal $\lambda$. All cardinals are taken in a single universe `u`.
-/
theorem woodin : 
    ∀ κ : Cardinal.{u}, IsStronglyCompact κ →
      (∀ μ < κ, ℵ₀ ≤ μ → 2 ^ μ = Order.succ μ) →
      ∀ μ : Cardinal.{u}, ℵ₀ ≤ μ → 2 ^ μ = Order.succ μ := by
  sorry

end Woodin

theorem Woodin.woodin.disproof : ¬ (type_of% @Woodin.woodin) := sorry
