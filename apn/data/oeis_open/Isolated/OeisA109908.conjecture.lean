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
# Conjectures associated with A109908

$a(n)$ = greatest prime of the form $k(n-k)-1$, or $0$ if no such prime exists.

*References:*
- [A109908](https://oeis.org/A109908)
-/

namespace OeisA109908

/--
$a(n)$ = greatest prime of the form $k(n-k)-1$, or $0$ if no such prime exists.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2))
  |>.image (fun k => k * (n - k) - 1)
  |>.filter Nat.Prime
  |>.sup id

/--
Conjecture: $a(n) > 0$ for $n > 3$.
-/
theorem conjecture : ∀ n > 3, a n > 0 := by
  sorry

end OeisA109908
