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

/-- There is exactly one `0`-step self-avoiding walk starting at `v`, namely the trivial walk. -/
@[category API, AMS 5]
theorem numSelfAvoidingWalks_zero : numSelfAvoidingWalks G v 0 = 1 := by
  rw [numSelfAvoidingWalks, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun ⟨⟨w, p⟩, hp⟩ ⟨⟨w', p'⟩, hp'⟩ => ?_⟩, ⟨⟨⟨v, .nil⟩, .nil, rfl⟩⟩⟩
  obtain ⟨-, hp⟩ := hp
  obtain ⟨-, hp'⟩ := hp'
  simp only at hp hp'
  cases p with
  | nil =>
    cases p' with
    | nil => rfl
    | cons _ _ => simp at hp'
  | cons _ _ => simp at hp

/-- The `1`-step self-avoiding walks starting at `v` correspond to the neighbours of `v`. -/
@[category API, AMS 5]
theorem numSelfAvoidingWalks_one : numSelfAvoidingWalks G v 1 = Nat.card (G.neighborSet v) := by
  refine Nat.card_congr
    { toFun := fun p => ⟨p.1.1, Walk.adj_of_length_eq_one p.2.2⟩
      invFun := fun w => ⟨⟨w.1, .cons w.2 .nil⟩, by simp [w.2.ne], rfl⟩
      left_inv := ?_
      right_inv := fun w => rfl }
  rintro ⟨⟨w, p⟩, hp, hl⟩
  cases p with
  | nil => simp at hl
  | cons h q =>
    cases q with
    | nil => rfl
    | cons h' q' => simp at hl

/-- The neighbours of the origin in the square lattice. -/
@[category test, AMS 5]
theorem squareLattice_neighborSet_zero :
    squareLattice.neighborSet 0 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  ext ⟨a, b⟩
  simp [squareLattice, Prod.ext_iff]
  omega

/-- On the square lattice, $c_1 = 4$. -/
@[category test, AMS 5]
theorem numSelfAvoidingWalks_squareLattice_one : numSelfAvoidingWalks squareLattice 0 1 = 4 := by
  rw [numSelfAvoidingWalks_one, squareLattice_neighborSet_zero, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card']
  decide

/-- On the square lattice, $c_0, \ldots, c_4 = 1, 4, 12, 36, 100$
(OEIS [A001411](https://oeis.org/A001411)). -/
@[category test, AMS 5]
theorem numSelfAvoidingWalks_squareLattice_small :
    (List.range 5).map (numSelfAvoidingWalks squareLattice 0) = [1, 4, 12, 36, 100] := by
  sorry

/-- The neighbours of the origin in the triangular lattice. -/
@[category test, AMS 5]
theorem triangularLattice_neighborSet_zero :
    triangularLattice.neighborSet 0 = {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)} := by
  ext ⟨a, b⟩
  simp [triangularLattice, Prod.ext_iff]
  omega

/-- On the triangular lattice, $c_1 = 6$. -/
@[category test, AMS 5]
theorem numSelfAvoidingWalks_triangularLattice_one :
    numSelfAvoidingWalks triangularLattice 0 1 = 6 := by
  rw [numSelfAvoidingWalks_one, triangularLattice_neighborSet_zero, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card']
  decide

/-- The neighbours of the origin in the honeycomb lattice. -/
@[category test, AMS 5]
theorem honeycombLattice_neighborSet_zero :
    honeycombLattice.neighborSet 0 = {(1, 0), (-1, 0), (0, 1)} := by
  ext ⟨a, b⟩
  simp [honeycombLattice, Int.even_iff, Prod.ext_iff]
  omega

/-- The neighbours of the point `(1, 0)` in the honeycomb lattice: its vertical edge goes down. -/
@[category test, AMS 5]
theorem honeycombLattice_neighborSet_one_zero :
    honeycombLattice.neighborSet (1, 0) = {(0, 0), (2, 0), (1, -1)} := by
  ext ⟨a, b⟩
  simp [honeycombLattice, Int.even_iff, Prod.ext_iff]
  omega

/-- On the honeycomb lattice, $c_1 = 3$. -/
@[category test, AMS 5]
theorem numSelfAvoidingWalks_honeycombLattice_one :
    numSelfAvoidingWalks honeycombLattice 0 1 = 3 := by
  rw [numSelfAvoidingWalks_one, honeycombLattice_neighborSet_zero, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card']
  decide

/-- On the honeycomb lattice, $c_0, \ldots, c_6 = 1, 3, 6, 12, 24, 48, 90$
(OEIS [A001668](https://oeis.org/A001668)). -/
@[category test, AMS 5]
theorem numSelfAvoidingWalks_honeycombLattice_small :
    (List.range 7).map (numSelfAvoidingWalks honeycombLattice 0) = [1, 3, 6, 12, 24, 48, 90] := by
  sorry

/-- **Nienhuis's conjecture for the square lattice** ([Ni82]; see [MS93], [LSW04]).
Let $c_n$ be the number of $n$-step self-avoiding walks on the square lattice $\mathbb{Z}^2$
starting at the origin, and let $\mu = \lim_{n \to \infty} c_n^{1/n}$ be the connective constant
of $\mathbb{Z}^2$ (the limit exists by Fekete's lemma, but its value is not known). Then
$$c_n \approx \mu^n n^{11/32} \qquad (n \to \infty),$$
in the sense that there is a constant $A > 0$ with $c_n \sim A \mu^n n^{11/32}$.
Here $11/32 = \gamma - 1$ with the critical exponent $\gamma = 43/32$. See
`SelfAvoidingWalk.self_avoiding_walk.variants.weak` for the weaker reading of $\approx$. -/
@[category research open, AMS 5 60 82]
theorem self_avoiding_walk :
    ∃ μ : ℝ,
      Tendsto (fun n : ℕ => (numSelfAvoidingWalks squareLattice 0 n : ℝ) ^ (1 / n : ℝ))
        atTop (𝓝 μ) ∧
      ∃ A : ℝ, 0 < A ∧
        (fun n : ℕ => (numSelfAvoidingWalks squareLattice 0 n : ℝ)) ~[atTop]
          fun n : ℕ => A * μ ^ n * (n : ℝ) ^ (11 / 32 : ℝ) := by
  sorry

/-- **Nienhuis's conjecture for the square lattice, weak form.**
Let $c_n$ be the number of $n$-step self-avoiding walks on the square lattice $\mathbb{Z}^2$
starting at the origin, and let $\mu = \lim_{n \to \infty} c_n^{1/n}$ be the connective constant
of $\mathbb{Z}^2$. Then
$$c_n = \mu^n n^{11/32 + o(1)} \qquad (n \to \infty),$$
i.e. the ratio $c_n / (\mu^n n^{11/32})$ is $n^{o(1)}$. This is the reading of
$c_n \approx \mu^n n^{11/32}$ used as a hedge in [DCS12, Section 4]; it is implied by
`SelfAvoidingWalk.self_avoiding_walk`. -/
@[category research open, AMS 5 60 82]
theorem self_avoiding_walk.variants.weak :
    ∃ μ : ℝ,
      Tendsto (fun n : ℕ => (numSelfAvoidingWalks squareLattice 0 n : ℝ) ^ (1 / n : ℝ))
        atTop (𝓝 μ) ∧
      ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop,
          (numSelfAvoidingWalks squareLattice 0 n : ℝ) = μ ^ n * (n : ℝ) ^ (11 / 32 + o n) := by
  sorry

/-- **Theorem** (Duminil-Copin–Smirnov [DCS12]). The connective constant of the honeycomb
lattice is $\mu = \lim_{n \to \infty} c_n^{1/n} = \sqrt{2 + \sqrt 2}$, as predicted by Nienhuis. -/
@[category research solved, AMS 5 60 82]
theorem honeycombLattice_connective_constant :
    Tendsto (fun n : ℕ => (numSelfAvoidingWalks honeycombLattice 0 n : ℝ) ^ (1 / n : ℝ))
      atTop (𝓝 √(2 + √2)) := by
  sorry

/-- **Universality of the exponent $11/32$: the honeycomb lattice** ([Ni82]; [DCS12, Section 4]).
The law $c_n \approx \mu^n n^{11/32}$ is believed to hold on every two-dimensional lattice: the
connective constant $\mu$ depends on the lattice, but the power-law correction $n^{11/32}$ does
not. On the honeycomb lattice the connective constant is known to be $\mu = \sqrt{2 + \sqrt 2}$,
so the conjecture becomes fully explicit: if $c_n$ is the number of $n$-step self-avoiding walks
on the honeycomb lattice starting at a fixed vertex, then there is a constant $A > 0$ with
$$c_n \sim A \, \sqrt{2 + \sqrt 2}^{\,n} \, n^{11/32} \qquad (n \to \infty).$$
See `SelfAvoidingWalk.self_avoiding_walk.variants.universality_weak` for the weaker reading. -/
@[category research open, AMS 5 60 82]
theorem self_avoiding_walk.variants.universality :
    ∃ A : ℝ, 0 < A ∧
      (fun n : ℕ => (numSelfAvoidingWalks honeycombLattice 0 n : ℝ)) ~[atTop]
        fun n : ℕ => A * √(2 + √2) ^ n * (n : ℝ) ^ (11 / 32 : ℝ) := by
  sorry

/-- **Universality of the exponent $11/32$: the honeycomb lattice, weak form.**
If $c_n$ is the number of $n$-step self-avoiding walks on the honeycomb lattice starting at a
fixed vertex, then
$$c_n = \sqrt{2 + \sqrt 2}^{\,n} \, n^{11/32 + o(1)} \qquad (n \to \infty),$$
i.e. the ratio $c_n / (\sqrt{2 + \sqrt 2}^{\,n} n^{11/32})$ is $n^{o(1)}$ [DCS12, Section 4]. -/
@[category research open, AMS 5 60 82]
theorem self_avoiding_walk.variants.universality_weak :
    ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (numSelfAvoidingWalks honeycombLattice 0 n : ℝ) =
          √(2 + √2) ^ n * (n : ℝ) ^ (11 / 32 + o n) := by
  sorry

/-- **Universality of the exponent $11/32$: the triangular lattice.**
Let $c_n$ be the number of $n$-step self-avoiding walks on the triangular lattice starting at a
fixed vertex, and let $\mu = \lim_{n \to \infty} c_n^{1/n}$ be its connective constant (whose
value is not known, $\mu \approx 4.15$). Then there is a constant $A > 0$ with
$$c_n \sim A \, \mu^n \, n^{11/32} \qquad (n \to \infty),$$
with the same exponent $11/32$ as on the square and honeycomb lattices. -/
@[category research open, AMS 5 60 82]
theorem self_avoiding_walk.variants.universality_triangular :
    ∃ μ : ℝ,
      Tendsto (fun n : ℕ => (numSelfAvoidingWalks triangularLattice 0 n : ℝ) ^ (1 / n : ℝ))
        atTop (𝓝 μ) ∧
      ∃ A : ℝ, 0 < A ∧
        (fun n : ℕ => (numSelfAvoidingWalks triangularLattice 0 n : ℝ)) ~[atTop]
          fun n : ℕ => A * μ ^ n * (n : ℝ) ^ (11 / 32 : ℝ) := by
  sorry

end SelfAvoidingWalk
