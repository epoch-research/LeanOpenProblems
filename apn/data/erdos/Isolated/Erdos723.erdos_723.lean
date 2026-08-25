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
# Erdős Problem 723: The prime power conjecture.

*Reference:* [erdosproblems.com/723](https://www.erdosproblems.com/723)
-/

open Configuration

namespace Erdos723

/--
If there is a finite projective plane of order $n$ then must $n$ be a prime power?
-/
theorem erdos_723 :
    ∀ {P L : Type} (_: Membership P L) (_ : Fintype P) (_ : Fintype L),
      ∀ pp : ProjectivePlane P L, IsPrimePow pp.order := by
  sorry

end Erdos723
