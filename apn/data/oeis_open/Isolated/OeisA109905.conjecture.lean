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
# Conjectures associated with A109905

$a(n)$ is the greatest prime of the form $k(n-k)+1$, where $k$ can take values from
$1$ to $\lfloor n/2 \rfloor$. $a(n)=0$ if no such prime exists.

*References:*
- [A109905](https://oeis.org/A109905)
-/

namespace OeisA109905

/--
$a(n)$ is the greatest prime of the form $k(n-k)+1$, where $k$ can take values
from $1$ to $\lfloor n/2 \rfloor$.
$a(n) = 0$ if no such prime exists.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2))
  |>.image (fun k => k * (n - k) + 1)
  |>.filter Nat.Prime
  |>.sup id

/--
$a(n) = 0$ for $n = 1$, $6$, $30$ and $54$. Are there any others?
-/
theorem conjecture : {n : ℕ | n > 0 ∧ a n = 0} = {1, 6, 30, 54} := by
  sorry

end OeisA109905
