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
# Singular cardinals hypothesis

If $\aleph_\omega$ is a strong limit cardinal, is $2^{\aleph_\omega} < \aleph_{\omega_1}$?
The best known bound, $2^{\aleph_\omega} < \aleph_{\omega_4}$, was obtained by Shelah using
his PCF theory.

Here $\aleph_{\omega_1}$ is the aleph indexed by the first uncountable ordinal $\omega_1$
(Mathlib's `ℵ_ ω₁`, that is `ℵ_ (ω_ 1)`), not $\aleph_{\omega + 1}$, and $\aleph_{\omega_4}$ is
the aleph indexed by the fourth uncountable initial ordinal $\omega_4$ (Mathlib's `ℵ_ (ω_ 4)`),
not $\aleph_{\omega \cdot 4}$.

The full singular cardinals hypothesis ($2^\kappa = \kappa^+$ for every singular strong limit
cardinal $\kappa$) is independent of ZFC and is not stated here. The question above only asks
whether the weaker bound $\aleph_{\omega_1}$ holds. The strong limit hypothesis is kept as an
antecedent since it is not a theorem of ZFC.

*References:*
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, Singular cardinals hypothesis](https://en.wikipedia.org/wiki/Singular_cardinals_hypothesis)
- S. Shelah, *Cardinal Arithmetic*, Oxford Logic Guides 29, Oxford University Press, 1994.
-/

namespace SingularCardinalsHypothesis

open Cardinal Ordinal

universe u

/--
If $\aleph_\omega$ is a strong limit cardinal, is $2^{\aleph_\omega} < \aleph_{\omega_1}$?

Here `ℵ_ ω₁` is $\aleph_{\omega_1}$, the aleph indexed by the first uncountable ordinal
(not $\aleph_{\omega + 1}$).
-/
@[category research open, AMS 3]
theorem singular_cardinals_hypothesis :
    answer(sorry) ↔
      (IsStrongLimit (ℵ_ ω : Cardinal.{u}) → 2 ^ (ℵ_ ω : Cardinal.{u}) < ℵ_ ω₁) := by
  sorry

/--
**Shelah's bound.** If $\aleph_\omega$ is a strong limit cardinal, then
$2^{\aleph_\omega} < \aleph_{\omega_4}$. This is the best known upper bound; it was obtained
by Shelah using his PCF theory.

Here `ℵ_ (ω_ 4)` is $\aleph_{\omega_4}$, the aleph indexed by the fourth uncountable initial
ordinal (not $\aleph_{\omega \cdot 4}$).
-/
@[category research solved, AMS 3]
theorem singular_cardinals_hypothesis.variants.shelah_bound
    (h : IsStrongLimit (ℵ_ ω : Cardinal.{u})) : 2 ^ (ℵ_ ω : Cardinal.{u}) < ℵ_ (ω_ 4) := by
  sorry

end SingularCardinalsHypothesis
