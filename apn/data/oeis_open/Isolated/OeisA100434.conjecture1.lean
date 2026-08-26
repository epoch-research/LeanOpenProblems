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
# Expansion of g.f. $(1+x)(3+x)/(1+6x^2+x^4)$

This sequence is defined by the linear recurrence relation
$a(n) = -6 a(n-2) - a(n-4)$ for $n \ge 4$,
with initial values $a(0)=3$, $a(1)=4$, $a(2)=-17$, $a(3)=-24$.

*References:*
- [A100434](https://oeis.org/A100434)
-/

namespace OeisA100434

/-- The primary defining sequence `a`, which is the expansion of the generating function
$(1+x)(3+x)/(1+6x^2+x^4)$. It satisfies the recurrence $a(n) = -6 a(n-2) - a(n-4)$
for $n \ge 4$. -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 4
  | 2 => -17
  | 3 => -24
  | n + 4 => -6 * a (n + 2) - a n

/-- $c(n)$ starts with $(1, -3, -7, 17)$ and satisfies the same recurrence as `a` -/
def c : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => -7
  | 3 => 17
  | n + 4 => -6 * c (n + 2) - c n

/-- $d(n)$ starts with $(2, 4, -10, -24)$ and satisfies the same recurrence as `a` -/
def d : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => -10
  | 3 => -24
  | n + 4 => -6 * d (n + 2) - d n

/-- $b(2n) = c(2n+1)$, $b(2n+1) = c(2n)$ -/
def b (n : ℕ) : ℤ :=
  if n % 2 = 0 then c (n + 1)
  else c (n - 1)

/-- $e(2n) = d(2n)/2$, $e(2n+1) = - d(2n)/2$ -/
def e (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    d n / 2
  else
    -- n is positive, so n-1 is safe in ℕ
    - (d (n - 1) / 2)

/-- $f(2n) = f(2n+1) = d(2n+1)/2$ -/
def f (n : ℕ) : ℤ :=
  let m := n / 2
  d (2 * m + 1) / 2

/-- $g(2n) = 0, g(2n+1) = c(2n+1)$ -/
def g (n : ℕ) : ℤ :=
  if n % 2 = 0 then 0
  else c n

/--
**Conjecture from Creighton Dement (A100434)**:
Let the auxiliary sequences c, d, e, f, g, b be defined as specified.
Then for all $n \ge 0$, $c(n) + d(n) = b(n)$.
-/
theorem conjecture1 (n : ℕ) : c n + d n = b n := by
  sorry

end OeisA100434
