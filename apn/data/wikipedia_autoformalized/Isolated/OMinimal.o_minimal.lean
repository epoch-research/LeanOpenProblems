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
# O-minimal theories with a trans-exponential function

Wikipedia's list of unsolved problems asks:
"Does there exist an o-minimal first order theory with a trans-exponential (rapid growth)
function?"

A totally ordered structure $(M, <, \dots)$ is *o-minimal* if every subset of $M$ definable
with parameters is a finite union of points and open intervals (with endpoints in
$M \cup \{\pm\infty\}$).
A theory is o-minimal if all of its models are o-minimal; the complete theory of an o-minimal
structure is o-minimal (Knight, Pillay, Steinhorn). The question therefore asks for an o-minimal
*structure* in which a trans-exponential function is definable.

"Trans-exponential" only makes sense relative to an exponential function, so, as is standard, we
work with expansions of the real ordered field $(\mathbb{R}, <, +, \cdot)$. A function
$f : \mathbb{R} \to \mathbb{R}$ is trans-exponential if it eventually dominates every finite iterate
$\exp \circ \dots \circ \exp$ of the exponential function. Wilkie's theorem says that
$(\mathbb{R}, <, +, \cdot, \exp)$ is o-minimal, so the question is whether o-minimality is
compatible with definable functions growing faster than every iterate of $\exp$.

*References:*
- [Wikipedia: O-minimal theory](https://en.wikipedia.org/wiki/o-minimal)
- [Wikipedia: List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998.
- A. J. Wilkie, [*Model completeness results for expansions of the ordered field of real numbers
  by restricted Pfaffian functions and the exponential
  function*](https://doi.org/10.1090/S0894-0347-96-00216-0), J. Amer. Math. Soc. 9 (1996),
  1051--1094.
-/

open FirstOrder FirstOrder.Language Filter

universe u v

namespace OMinimal

/-- A set $X \subseteq \mathbb{R}$ is a finite union of points and open intervals: there are a
finite set $X_0 \subseteq \mathbb{R}$ and finitely many open intervals $I_1, \dots, I_r$ with
endpoints in $\mathbb{R} \cup \{\pm\infty\}$ such that $X = X_0 \cup I_1 \cup \dots \cup I_r$. -/
def IsFiniteUnionOfIntervalsAndPoints (X : Set ℝ) : Prop :=
  ∃ (X₀ : Finset ℝ) (I : Finset (EReal × EReal)),
    X = ↑X₀ ∪ ⋃ ab ∈ I, {x : ℝ | ab.1 < x ∧ x < ab.2}

/-- A first-order structure on the real line (in a language `L`) is *o-minimal* if every subset
of $\mathbb{R}$ that is definable with parameters from $\mathbb{R}$ is a finite union of points and
open intervals. -/
def IsOMinimal (L : FirstOrder.Language.{u, v}) [L.Structure ℝ] : Prop :=
  ∀ X : Set ℝ, (Set.univ : Set ℝ).Definable₁ L X → IsFiniteUnionOfIntervalsAndPoints X

/-- The standard interpretation of the language of ordered rings (the language of rings together
with the relation symbol `≤`) in the ordered field of real numbers. -/
noncomputable scoped instance realOrderedRingStructure :
    (Language.ring.sum Language.order).Structure ℝ :=
  letI := Ring.compatibleRingOfRing ℝ
  letI := orderStructure ℝ
  inferInstance

/-- A function $f : \mathbb{R} \to \mathbb{R}$ is *trans-exponential* if it eventually dominates
every finite iterate of the exponential function: for every $n$, $f(x) > \exp^{(n)}(x)$ for all
sufficiently large $x$, where $\exp^{(n)} = \exp \circ \dots \circ \exp$ ($n$ times). -/
def IsTransExponential (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ᶠ x in atTop, Real.exp^[n] x < f x

/--
Does there exist an o-minimal first order theory with a trans-exponential (rapid growth)
function?

Formally: is there an expansion of the real ordered field $(\mathbb{R}, <, +, \cdot)$, i.e. a
language `L` with an `L`-structure on `ℝ` extending the standard interpretation of the language of
ordered rings, that is o-minimal and in which some trans-exponential function
$f : \mathbb{R} \to \mathbb{R}$ is definable (with parameters)?
-/
theorem o_minimal :
    
      ∃ (L : FirstOrder.Language.{u, v}) (_ : L.Structure ℝ)
        (φ : Language.ring.sum Language.order →ᴸ L),
        φ.IsExpansionOn ℝ ∧ IsOMinimal L ∧
          ∃ f : ℝ → ℝ,
            (Set.univ : Set ℝ).Definable₂ L {p : ℝ × ℝ | p.2 = f p.1} ∧
              IsTransExponential f := by
  sorry

end OMinimal

theorem OMinimal.o_minimal.disproof : ¬ (type_of% @OMinimal.o_minimal) := sorry
