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
# Converse of Wolstenholme's theorem

Wolstenholme's theorem states that every prime $p \geq 5$ satisfies
$$\binom{2p-1}{p-1} \equiv 1 \pmod{p^3}.$$
It is conjectured that the converse holds: if a natural number $n \geq 2$ satisfies
$\binom{2n-1}{n-1} \equiv 1 \pmod{n^3}$, then $n$ is prime.

*References:*
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Wikipedia, *Wolstenholme's theorem: The converse as a conjecture*](https://en.wikipedia.org/wiki/Wolstenholme%27s_theorem%23The_converse_as_a_conjecture)
- [R. J. McIntosh, *On the converse of Wolstenholme's theorem*, Acta Arith. 71 (1995), 381–389](https://doi.org/10.4064/aa-71-4-381-389)
-/

namespace ConverseOfWolstenholmesTheorem

/--
Does the converse of Wolstenholme's theorem hold for all natural numbers?
That is, is every natural number $n \geq 2$ with
$$\binom{2n-1}{n-1} \equiv 1 \pmod{n^3}$$
a prime number?

The restriction $n \geq 2$ excludes the degenerate cases $n = 0$ and $n = 1$, which satisfy the
congruence trivially (modulo $0$ and modulo $1$) without being prime.
-/
@[category research open, AMS 11]
theorem converse_of_wolstenholmes_theorem :
    answer(sorry) ↔
      ∀ n : ℕ, 2 ≤ n → (2 * n - 1).choose (n - 1) ≡ 1 [MOD n ^ 3] → n.Prime := by
  sorry

end ConverseOfWolstenholmesTheorem
