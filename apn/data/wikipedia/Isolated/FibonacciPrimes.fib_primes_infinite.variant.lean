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
# Fibonacci Primes

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Fibonacci_prime)
-/

namespace FibonacciPrimes

/--
There are infinitely many indices $i$, such that the $i$-th Fibonacci is prime.
-/
theorem fib_primes_infinite.variant : {n : ℕ | n.fib.Prime}.Infinite := by
  sorry

end FibonacciPrimes
