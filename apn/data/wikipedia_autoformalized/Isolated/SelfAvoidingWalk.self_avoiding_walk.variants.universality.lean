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
# Self-avoiding walk

An $n$-step self-avoiding walk (SAW) on a lattice is a nearest-neighbour path
$\omega = (\omega_0, \omega_1, \ldots, \omega_n)$ that visits no vertex more than once. Let $c_n$
be the number of $n$-step self-avoiding walks starting at a fixed vertex (the origin). Since
$c_{n+m} \le c_n c_m$, Fekete's lemma shows that the *connective constant*
$$\mu = \lim_{n \to \infty} c_n^{1/n}$$
exists. Its value is not known for the square lattice $\mathbb{Z}^2$ ($\mu \approx 2.638$); for
the honeycomb lattice, Duminil-Copin and Smirnov proved that $\mu = \sqrt{2 + \sqrt 2}$.

No formula for $c_n$ is known. The Wikipedia list of unsolved problems asks for
"a function to model $n$-step self-avoiding walks"; the conjectured model (Nienhuis) is
$$c_n \approx \mu^n n^{11/32} \qquad (n \to \infty),$$
where $11/32 = \gamma - 1$ with the critical exponent $\gamma = 43/32$. The constant $\mu$
depends on the lattice, but the power-law correction $n^{11/32}$ is believed to be *universal*,
i.e. the same for every two-dimensional lattice.

The symbol $\approx$ is not made precise in the Wikipedia article. The main statements below use
the strong form $c_n \sim A \mu^n n^{11/32}$ for some constant $A > 0$, as in [Ni82], [MS93] and
[LSW04]. The `weak` variants use the weaker reading $c_n = \mu^n n^{11/32 + o(1)}$, which
[DCS12] mention as a possible hedge. The universality clause is instantiated on the honeycomb
lattice (where $\mu$ is known) and on the triangular lattice.

*References:*
- [Wikipedia, Self-avoiding walk](https://en.wikipedia.org/wiki/self-avoiding_walk)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [DCS12] Duminil-Copin, H. and Smirnov, S., *The connective constant of the honeycomb lattice
  equals $\sqrt{2+\sqrt 2}$*, Ann. of Math. 175 (2012), 1653–1665.
  [arXiv:1007.0575](https://arxiv.org/abs/1007.0575)
- [LSW04] Lawler, G. F., Schramm, O. and Werner, W., *On the scaling limit of planar
  self-avoiding walk*, Proc. Sympos. Pure Math. 72, Part 2 (2004), 339–364.
  [arXiv:math/0204277](https://arxiv.org/abs/math/0204277)
- [MS93] Madras, N. and Slade, G., *The Self-Avoiding Walk*, Birkhäuser, 1993.
- [Ni82] Nienhuis, B., *Exact critical point and critical exponents of $O(n)$ models in two
  dimensions*, Phys. Rev. Lett. 49 (1982), 1062–1065.
-/

open Asymptotics Filter Topology SimpleGraph

namespace SelfAvoidingWalk

variable {V : Type*}

/-- The number $c_n$ of `n`-step self-avoiding walks in the graph `G` starting at the vertex `v`,
i.e. the number of walks of length `n` in `G` starting at `v` (with any endpoint) that visit no
vertex more than once. -/
noncomputable def numSelfAvoidingWalks (G : SimpleGraph V) (v : V) (n : ℕ) : ℕ :=
  Nat.card {p : Σ w, G.Walk v w // p.2.IsPath ∧ p.2.length = n}

/-- The square lattice $\mathbb{Z}^2$: two points are adjacent iff they differ by one of the four
unit vectors $\pm(1, 0)$, $\pm(0, 1)$. -/
def squareLattice : SimpleGraph (ℤ × ℤ) := circulantGraph {(1, 0), (0, 1)}

/-- The triangular lattice in oblique coordinates: two points of $\mathbb{Z}^2$ are adjacent iff
they differ by one of the six vectors $\pm(1, 0)$, $\pm(0, 1)$, $\pm(1, -1)$. Every vertex has
degree `6`. -/
def triangularLattice : SimpleGraph (ℤ × ℤ) := circulantGraph {(1, 0), (0, 1), (1, -1)}

/-- The honeycomb (hexagonal) lattice in *brick-wall* coordinates: the vertices are the points of
$\mathbb{Z}^2$, all horizontal edges $(x, y) - (x + 1, y)$ are present, and the vertical edge
$(x, y) - (x, y + 1)$ is present iff $x + y$ is even. Every vertex has degree `3` and every face
is a hexagon, so this graph is isomorphic to the honeycomb lattice. -/
def honeycombLattice : SimpleGraph (ℤ × ℤ) :=
  fromRel fun p q => q = (p.1 + 1, p.2) ∨ (Even (p.1 + p.2) ∧ q = (p.1, p.2 + 1))

variable (G : SimpleGraph V) (v : V)

/-- **Universality of the exponent $11/32$: the honeycomb lattice** ([Ni82]; [DCS12, Section 4]).
The law $c_n \approx \mu^n n^{11/32}$ is believed to hold on every two-dimensional lattice: the
connective constant $\mu$ depends on the lattice, but the power-law correction $n^{11/32}$ does
not. On the honeycomb lattice the connective constant is known to be $\mu = \sqrt{2 + \sqrt 2}$,
so the conjecture becomes fully explicit: if $c_n$ is the number of $n$-step self-avoiding walks
on the honeycomb lattice starting at a fixed vertex, then there is a constant $A > 0$ with
$$c_n \sim A \, \sqrt{2 + \sqrt 2}^{\,n} \, n^{11/32} \qquad (n \to \infty).$$
See `SelfAvoidingWalk.self_avoiding_walk.variants.universality_weak` for the weaker reading. -/
theorem self_avoiding_walk.variants.universality :
    ∃ A : ℝ, 0 < A ∧
      (fun n : ℕ => (numSelfAvoidingWalks honeycombLattice 0 n : ℝ)) ~[atTop]
        fun n : ℕ => A * √(2 + √2) ^ n * (n : ℝ) ^ (11 / 32 : ℝ) := by
  sorry

end SelfAvoidingWalk

theorem SelfAvoidingWalk.self_avoiding_walk.variants.universality.disproof : ¬ (type_of% @SelfAvoidingWalk.self_avoiding_walk.variants.universality) := sorry
