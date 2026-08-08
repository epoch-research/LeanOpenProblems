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
# Erdős Problem 6

*References:*
- [erdosproblems.com/6](https://www.erdosproblems.com/6)
- [BFT15] Banks, William D. and Freiberg, Tristan and Turnage-Butterbaugh, Caroline L., Consecutive primes in tuples. Acta Arith. (2015), 261-266.
- [Ma15] Maynard, James, Small gaps between primes. Ann. of Math. (2) (2015), 383-413.
-/

namespace Erdos6

/--
There are infinitely many $n$ such that $d_n < d_{n+1} < d_{n+2}$, where $d$
denotes the prime gap function.
-/
theorem erdos_6 :
    {n | primeGap n < primeGap (n + 1) ∧ primeGap (n + 1) < primeGap (n + 2)}.Infinite := by
  sorry

end Erdos6
