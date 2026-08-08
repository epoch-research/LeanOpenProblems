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
# Erdős Problem 125

*Reference:* [erdosproblems.com/125](https://www.erdosproblems.com/125)

There are four possibilities for the density of $A+B$:
1. $A+B$ has zero upper and lower density (and hence also zero density).
2. $A+B$ has zero lower density, but positive upper density (and hence no density).
3. $A+B$ has positive upper and lower density that are equal (and hence positive density).
4. $A+B$ has positive upper and lower density that are unequal (and hence no density).
-/

open Nat Pointwise

namespace Erdos125

set_option quotPrecheck false

/--
Let $A$ be the set of integers which have only the digits $0, 1$ when written base 3,
-/
local notation "A" => { x : ℕ | (digits 3 x).toFinset ⊆ {0, 1} }
/--
and $B$ be the set of integers which have only the digits $0, 1$ when written base 4.
-/
local notation "B" => { x : ℕ | (digits 4 x).toFinset ⊆ {0, 1} }

/-
There are four possibilities for the density of $A+B$:
1. $A+B$ has zero upper and lower density (and hence also zero density).
2. $A+B$ has zero lower density, but positive upper density (and hence no density).
3. $A+B$ has positive upper and lower density that are equal (and hence positive density).
4. $A+B$ has positive upper and lower density that are unequal (and hence no density).
-/

/--
Case 3:
Does $A + B$ have positive upper and lower density that are equal?
This is the literal interpretation of "positive density" which was falsified.
-/

theorem erdos_125 :
    (A + B).HasPosDensity := by
  sorry

end Erdos125
