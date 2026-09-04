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
# Regularity of solutions of the Vlasov–Maxwell equations

The relativistic Vlasov–Maxwell system describes a collisionless plasma made of finitely many
species $\alpha$ of charged particles with masses $m_\alpha > 0$ and charges $q_\alpha$. Each
species has a distribution function $f_\alpha(\mathbf r, \mathbf p, t) \ge 0$ on phase space
(position $\mathbf r \in \mathbb R^3$, momentum $\mathbf p \in \mathbb R^3$), and the particles
interact only through the self-consistent electromagnetic field $(\mathbf E, \mathbf B)$:
$$\frac{\partial f_\alpha}{\partial t} + \mathbf v_\alpha \cdot \nabla_{\mathbf r} f_\alpha
  + q_\alpha \left(\mathbf E + \mathbf v_\alpha \times \mathbf B\right) \cdot
    \frac{\partial f_\alpha}{\partial \mathbf p} = 0,
  \qquad
  \mathbf v_\alpha = \frac{\mathbf p / m_\alpha}{\sqrt{1 + |\mathbf p|^2 / (m_\alpha c)^2}},$$
$$\nabla \times \mathbf B = \mu_0 \mathbf j
    + \mu_0 \varepsilon_0 \frac{\partial \mathbf E}{\partial t},
  \quad \nabla \cdot \mathbf B = 0, \quad
  \nabla \times \mathbf E = -\frac{\partial \mathbf B}{\partial t}, \quad
  \nabla \cdot \mathbf E = \frac{\rho}{\varepsilon_0},$$
$$\rho = \sum_\alpha q_\alpha \int f_\alpha \, d^3\mathbf p, \qquad
  \mathbf j = \sum_\alpha q_\alpha \int f_\alpha \mathbf v_\alpha \, d^3\mathbf p.$$
Here $c$ is the speed of light and $\varepsilon_0$, $\mu_0$ are the vacuum permittivity and
permeability, related by $\varepsilon_0 \mu_0 c^2 = 1$.

The problem listed on Wikipedia as *"Regularity of solutions of Vlasov–Maxwell equations"* is
the global regularity question of Glassey and Strauss for this system in three space dimensions:
does every smooth ($C^\infty$), compactly supported initial datum
$(f_\alpha(\cdot, \cdot, 0), \mathbf E_0, \mathbf B_0)$ satisfying the constraint equations
$\nabla \cdot \mathbf B_0 = 0$ and $\nabla \cdot \mathbf E_0 = \rho_0 / \varepsilon_0$ launch a
global-in-time classical solution, i.e. can regularity never be lost in finite time? Glassey and
Strauss proved that a singularity can only form if the momentum support of some $f_\alpha$ becomes
unbounded in finite time. The answer is expected to be affirmative, but is only known for small
or nearly neutral data, in lower dimensions, or under an a priori bound on the momentum support.

## Conventions

* Following the Wikipedia article, a distribution function is written `f α r p t`
  (species, position, momentum, time) and a field is written `E r t` (position, time).
* Solutions live on the closed time half-line $t \ge 0$; the time derivative is encoded with
  `derivWithin` relative to `Set.Ici 0` and smoothness with `ContDiffOn`, as in
  `FormalConjectures.Millenium.NavierStokes`.
* Spatial and momentum derivatives use `fderiv`; the dot products
  $\mathbf a \cdot \nabla_{\mathbf r} f$ and $\mathbf a \cdot \partial_{\mathbf p} f$ are written
  as directional derivatives. `divergence` and `curl` take junk values at points of
  non-differentiability, which does not matter since every function involved is smooth.
* Since $\nabla \cdot \mathbf E_0 = \rho_0 / \varepsilon_0$, a compactly supported $\mathbf E_0$
  forces the total charge $\int \rho_0$ to vanish. The main statement
  `vlasov_maxwell_equations` assumes compactly supported initial fields; the variant
  `vlasov_maxwell_equations.variants.fields_not_compactly_supported` only assumes that the
  initial fields are smooth, which allows a nonzero total charge.

## References

* [Wikipedia, *Vlasov equation*](https://en.wikipedia.org/wiki/Vlasov%E2%80%93Maxwell_equations)
* [Wikipedia, *List of unsolved problems in
  mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* R. Glassey, W. Strauss, *Singularity formation in a collisionless plasma could occur only at
  high velocities*, Arch. Rational Mech. Anal. 92 (1986), 59–90.
  [doi:10.1007/BF00250732](https://doi.org/10.1007/BF00250732)
* R. Glassey, *The Cauchy Problem in Kinetic Theory*, SIAM, Philadelphia, 1996.
-/

open ContDiff Set MeasureTheory EuclideanGeometry
open scoped Matrix

namespace VlasovMaxwellEquations

/-- The cross product $a \times b$ of two vectors of $\mathbb R^3$, transported from Mathlib's
`crossProduct` on `Fin 3 → ℝ`. -/
noncomputable def cross (a b : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (WithLp.ofLp a ⨯₃ WithLp.ofLp b)

/-- The partial derivative $\partial_j F_i(x)$ of the $i$-th component of a vector field
$F : \mathbb R^3 \to \mathbb R^3$ in the $j$-th coordinate direction. If `F` is not
differentiable at `x`, then `fderiv` is the zero map, so this has the junk value $0$. -/
noncomputable def partialDeriv (F : ℝ³ → ℝ³) (x : ℝ³) (j i : Fin 3) : ℝ :=
  fderiv ℝ F x (EuclideanSpace.single j 1) i

/-- The divergence $\nabla \cdot F = \sum_i \partial_i F_i$ of a vector field
$F : \mathbb R^3 \to \mathbb R^3$ at `x`. -/
noncomputable def divergence (F : ℝ³ → ℝ³) (x : ℝ³) : ℝ :=
  ∑ i, partialDeriv F x i i

/-- The curl
$\nabla \times F = (\partial_1 F_2 - \partial_2 F_1,\ \partial_2 F_0 - \partial_0 F_2,\
\partial_0 F_1 - \partial_1 F_0)$ of a vector field $F : \mathbb R^3 \to \mathbb R^3$ at `x`,
with coordinates indexed by `0, 1, 2`. -/
noncomputable def curl (F : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 ![partialDeriv F x 1 2 - partialDeriv F x 2 1,
    partialDeriv F x 2 0 - partialDeriv F x 0 2,
    partialDeriv F x 0 1 - partialDeriv F x 1 0]

/-- The relativistic velocity
$\mathbf v = \dfrac{\mathbf p / m}{\sqrt{1 + |\mathbf p|^2 / (m c)^2}}$ of a particle of mass
`m` with momentum `p`, where `c` is the speed of light. -/
noncomputable def velocity (c m : ℝ) (p : ℝ³) : ℝ³ :=
  (1 / (m * √(1 + ‖p‖ ^ 2 / (m * c) ^ 2))) • p

variable {ι : Type*} [Fintype ι]

/-- The charge density
$\rho(\mathbf r) = \sum_\alpha q_\alpha \int f_\alpha(\mathbf r, \mathbf p) \, d^3\mathbf p$
of a family of distribution functions `f α r p` (position, momentum) at a fixed time, where
`q α` is the charge of species `α`. -/
noncomputable def chargeDensity (q : ι → ℝ) (f : ι → ℝ³ → ℝ³ → ℝ) (r : ℝ³) : ℝ :=
  ∑ α, q α * ∫ p, f α r p

/-- The current density
$\mathbf j(\mathbf r) = \sum_\alpha q_\alpha \int f_\alpha(\mathbf r, \mathbf p) \,
\mathbf v_\alpha(\mathbf p) \, d^3\mathbf p$ of a family of distribution functions `f α r p`
(position, momentum) at a fixed time, where `m α` and `q α` are the mass and charge of species
`α` and `c` is the speed of light. -/
noncomputable def currentDensity (c : ℝ) (m q : ι → ℝ) (f : ι → ℝ³ → ℝ³ → ℝ) (r : ℝ³) :
    ℝ³ :=
  ∑ α, q α • ∫ p, f α r p • velocity c (m α) p

/-- Admissible initial data `(f₀, E₀, B₀)` for the Vlasov–Maxwell Cauchy problem with vacuum
permittivity `ε₀` and charges `q`:

* each initial distribution function `f₀ α` is nonnegative, smooth ($C^\infty$) and compactly
  supported on phase space $\mathbb R^3 \times \mathbb R^3$;
* the initial fields `E₀`, `B₀` are smooth ($C^\infty$);
* the constraint equations $\nabla \cdot \mathbf B_0 = 0$ and
  $\nabla \cdot \mathbf E_0 = \rho_0 / \varepsilon_0$ hold, where $\rho_0$ is the charge
  density of `f₀`.

Compact support of the initial fields is not part of this structure, since
$\nabla \cdot \mathbf E_0 = \rho_0 / \varepsilon_0$ forces a compactly supported `E₀` to have
zero total charge; it is added as a separate hypothesis where wanted. -/
structure IsAdmissibleInitialData (ε₀ : ℝ) (q : ι → ℝ) (f₀ : ι → ℝ³ → ℝ³ → ℝ)
    (E₀ B₀ : ℝ³ → ℝ³) : Prop where
  /-- Each initial distribution function is nonnegative. -/
  nonneg_f₀ : ∀ α r p, 0 ≤ f₀ α r p
  /-- Each initial distribution function is smooth ($C^\infty$) on phase space. -/
  smooth_f₀ : ∀ α, ContDiff ℝ ∞ ↿(f₀ α)
  /-- Each initial distribution function has compact support in phase space. -/
  compactSupport_f₀ : ∀ α, HasCompactSupport ↿(f₀ α)
  /-- The initial electric field is smooth ($C^\infty$). -/
  smooth_E₀ : ContDiff ℝ ∞ E₀
  /-- The initial magnetic field is smooth ($C^\infty$). -/
  smooth_B₀ : ContDiff ℝ ∞ B₀
  /-- The constraint $\nabla \cdot \mathbf B_0 = 0$. -/
  div_B₀ : ∀ r, divergence B₀ r = 0
  /-- The constraint $\nabla \cdot \mathbf E_0 = \rho_0 / \varepsilon_0$. -/
  div_E₀ : ∀ r, divergence E₀ r = chargeDensity q f₀ r / ε₀

/-- `(f, E, B)` is a global classical (smooth) solution of the relativistic Vlasov–Maxwell system
on $\mathbb R^3 \times \mathbb R^3 \times [0, \infty)$ with initial data `(f₀, E₀, B₀)`, speed of
light `c`, vacuum permittivity `ε₀`, vacuum permeability `μ₀`, masses `m` and charges `q`.

The distribution functions `f α r p t` and the fields `E r t`, `B r t` are $C^\infty$ up to
$t = 0$, take the prescribed values at $t = 0$, and satisfy the Vlasov equation for every species
together with the four Maxwell equations, with charge and current densities computed from `f`.
Time derivatives are taken relative to `Set.Ici 0`, so they are one-sided at $t = 0$.

Each `f α` is also required to have compact support in phase space at every time $t \ge 0$. This
holds for every classical solution launched by compactly supported data (particles move slower
than light and the fields are bounded on compact sets), and it guarantees that the integrals
defining $\rho$ and $\mathbf j$ are integrals of compactly supported continuous functions. -/
structure IsGlobalClassicalSolution (c ε₀ μ₀ : ℝ) (m q : ι → ℝ) (f₀ : ι → ℝ³ → ℝ³ → ℝ)
    (E₀ B₀ : ℝ³ → ℝ³) (f : ι → ℝ³ → ℝ³ → ℝ → ℝ) (E B : ℝ³ → ℝ → ℝ³) : Prop where
  /-- Each distribution function is smooth ($C^\infty$) on
  $\mathbb R^3 \times \mathbb R^3 \times [0, \infty)$. -/
  smooth_f : ∀ α, ContDiffOn ℝ ∞ ↿(f α) (univ ×ˢ univ ×ˢ Ici 0)
  /-- The electric field is smooth ($C^\infty$) on $\mathbb R^3 \times [0, \infty)$. -/
  smooth_E : ContDiffOn ℝ ∞ ↿E (univ ×ˢ Ici 0)
  /-- The magnetic field is smooth ($C^\infty$) on $\mathbb R^3 \times [0, \infty)$. -/
  smooth_B : ContDiffOn ℝ ∞ ↿B (univ ×ˢ Ici 0)
  /-- At each time $t \ge 0$, each distribution function has compact support in phase space. -/
  compactSupport_f : ∀ α, ∀ t ≥ 0, HasCompactSupport fun rp : ℝ³ × ℝ³ => f α rp.1 rp.2 t
  /-- Initial condition
  $f_\alpha(\mathbf r, \mathbf p, 0) = f_{\alpha, 0}(\mathbf r, \mathbf p)$. -/
  initial_f : ∀ α r p, f α r p 0 = f₀ α r p
  /-- Initial condition $\mathbf E(\mathbf r, 0) = \mathbf E_0(\mathbf r)$. -/
  initial_E : ∀ r, E r 0 = E₀ r
  /-- Initial condition $\mathbf B(\mathbf r, 0) = \mathbf B_0(\mathbf r)$. -/
  initial_B : ∀ r, B r 0 = B₀ r
  /-- The Vlasov equation
  $\partial_t f_\alpha + \mathbf v_\alpha \cdot \nabla_{\mathbf r} f_\alpha
    + q_\alpha (\mathbf E + \mathbf v_\alpha \times \mathbf B) \cdot
    \partial_{\mathbf p} f_\alpha = 0$
  for every species, where $\mathbf a \cdot \nabla_{\mathbf r} f$ is the derivative of $f$ in
  $\mathbf r$ in the direction $\mathbf a$, and similarly in $\mathbf p$. -/
  vlasov : ∀ α r p, ∀ t ≥ 0,
    derivWithin (f α r p) (Ici 0) t
      + fderiv ℝ (f α · p t) r (velocity c (m α) p)
      + fderiv ℝ (f α r · t) p (q α • (E r t + cross (velocity c (m α) p) (B r t))) = 0
  /-- The Ampère–Maxwell law
  $\nabla \times \mathbf B = \mu_0 \mathbf j + \mu_0 \varepsilon_0 \, \partial_t \mathbf E$. -/
  ampere : ∀ r, ∀ t ≥ 0,
    curl (B · t) r =
      μ₀ • currentDensity c m q (fun α r p => f α r p t) r
        + (μ₀ * ε₀) • derivWithin (E r) (Ici 0) t
  /-- Gauss's law for magnetism $\nabla \cdot \mathbf B = 0$. -/
  div_B : ∀ r, ∀ t ≥ 0, divergence (B · t) r = 0
  /-- Faraday's law $\nabla \times \mathbf E = -\partial_t \mathbf B$. -/
  faraday : ∀ r, ∀ t ≥ 0, curl (E · t) r = -derivWithin (B r) (Ici 0) t
  /-- Gauss's law $\nabla \cdot \mathbf E = \rho / \varepsilon_0$. -/
  div_E : ∀ r, ∀ t ≥ 0,
    divergence (E · t) r = chargeDensity q (fun α r p => f α r p t) r / ε₀

/-- **Regularity of solutions of the Vlasov–Maxwell equations** (the Glassey–Strauss global
regularity problem).

Consider the relativistic Vlasov–Maxwell system in three space dimensions with speed of light
$c > 0$, vacuum permittivity $\varepsilon_0 > 0$ and permeability $\mu_0 > 0$ related by
$\varepsilon_0 \mu_0 c^2 = 1$, and finitely many species with masses $m_\alpha > 0$ and charges
$q_\alpha$. Does every smooth ($C^\infty$), compactly supported initial datum
$(f_\alpha(\cdot, \cdot, 0), \mathbf E_0, \mathbf B_0)$ with $f_\alpha(\cdot, \cdot, 0) \ge 0$
satisfying the constraint equations $\nabla \cdot \mathbf B_0 = 0$ and
$\nabla \cdot \mathbf E_0 = \rho_0 / \varepsilon_0$ launch a global-in-time classical (smooth)
solution, so that no loss of regularity occurs in finite time?

The answer is expected to be affirmative. -/
@[category research open, AMS 35 82]
theorem vlasov_maxwell_equations :
    answer(sorry) ↔
      ∀ (ι : Type) [Fintype ι] (c ε₀ μ₀ : ℝ) (m q : ι → ℝ),
        0 < c → 0 < ε₀ → 0 < μ₀ → ε₀ * μ₀ * c ^ 2 = 1 → (∀ α, 0 < m α) →
        ∀ (f₀ : ι → ℝ³ → ℝ³ → ℝ) (E₀ B₀ : ℝ³ → ℝ³), IsAdmissibleInitialData ε₀ q f₀ E₀ B₀ →
          HasCompactSupport E₀ → HasCompactSupport B₀ →
          ∃ (f : ι → ℝ³ → ℝ³ → ℝ → ℝ) (E B : ℝ³ → ℝ → ℝ³),
            IsGlobalClassicalSolution c ε₀ μ₀ m q f₀ E₀ B₀ f E B := by
  sorry

/-- The variant of `vlasov_maxwell_equations` in which only the initial distribution functions
are required to be compactly supported, while the initial fields $\mathbf E_0$, $\mathbf B_0$
are merely smooth and satisfy the constraint equations. This allows a nonzero total charge
$\int \rho_0$ (for instance a single species), which compactly supported initial fields exclude
by Gauss's law. -/
@[category research open, AMS 35 82]
theorem vlasov_maxwell_equations.variants.fields_not_compactly_supported :
    answer(sorry) ↔
      ∀ (ι : Type) [Fintype ι] (c ε₀ μ₀ : ℝ) (m q : ι → ℝ),
        0 < c → 0 < ε₀ → 0 < μ₀ → ε₀ * μ₀ * c ^ 2 = 1 → (∀ α, 0 < m α) →
        ∀ (f₀ : ι → ℝ³ → ℝ³ → ℝ) (E₀ B₀ : ℝ³ → ℝ³), IsAdmissibleInitialData ε₀ q f₀ E₀ B₀ →
          ∃ (f : ι → ℝ³ → ℝ³ → ℝ → ℝ) (E B : ℝ³ → ℝ → ℝ³),
            IsGlobalClassicalSolution c ε₀ μ₀ m q f₀ E₀ B₀ f E B := by
  sorry

/- ### Basic API and sanity checks for the bespoke definitions -/

/-- The cross product in coordinates. -/
@[category API, AMS 15]
theorem cross_apply (a b : ℝ³) :
    cross a b =
      WithLp.toLp 2 ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] :=
  rfl

/-- The cross product of a vector with itself vanishes. -/
@[category API, AMS 15]
theorem cross_self (a : ℝ³) : cross a a = 0 := by
  simp [cross]

/-- The partial derivatives of a continuous linear map are its matrix entries. -/
@[category API, AMS 35]
theorem partialDeriv_clm (L : ℝ³ →L[ℝ] ℝ³) (x : ℝ³) (j i : Fin 3) :
    partialDeriv L x j i = L (EuclideanSpace.single j 1) i := by
  simp [partialDeriv]

/-- The divergence of a constant vector field vanishes. -/
@[category API, AMS 35]
theorem divergence_const (v x : ℝ³) : divergence (fun _ => v) x = 0 := by
  simp [divergence, partialDeriv]

/-- The divergence of the identity vector field on $\mathbb R^3$ is $3$. -/
@[category test, AMS 35]
theorem divergence_id (x : ℝ³) : divergence id x = 3 := by
  simp [divergence, partialDeriv]

/-- The curl of a constant vector field vanishes. -/
@[category API, AMS 35]
theorem curl_const (v x : ℝ³) : curl (fun _ => v) x = 0 := by
  simp [curl, partialDeriv]

/-- The rotation field $(y_0, y_1, y_2) \mapsto (-y_1, y_0, 0)$ has curl $(0, 0, 2)$. This checks
the orientation convention of `curl`. -/
@[category test, AMS 35]
theorem curl_rotation (x : ℝ³) :
    curl (LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ))) x =
      WithLp.toLp 2 ![0, 0, 2] := by
  simp only [curl, partialDeriv_clm]
  ext i
  fin_cases i <;> simp [Matrix.toEuclideanLin_apply]; norm_num

/-- A particle at rest has zero velocity. -/
@[category API, AMS 35]
theorem velocity_zero (c m : ℝ) : velocity c m 0 = 0 := by
  simp [velocity]

/-- The charge density of the vacuum (no particles) vanishes. -/
@[category API, AMS 35]
theorem chargeDensity_zero (q : ι → ℝ) (r : ℝ³) : chargeDensity q 0 r = 0 := by
  simp [chargeDensity]

/-- The current density of the vacuum (no particles) vanishes. -/
@[category API, AMS 35]
theorem currentDensity_zero (c : ℝ) (m q : ι → ℝ) (r : ℝ³) : currentDensity c m q 0 r = 0 := by
  simp [currentDensity]

/-- The vacuum (no particles, no fields) is an admissible initial datum with compactly supported
fields, so the hypotheses of `vlasov_maxwell_equations` can be satisfied. -/
@[category test, AMS 35]
theorem isAdmissibleInitialData_zero (ε₀ : ℝ) (q : ι → ℝ) :
    IsAdmissibleInitialData ε₀ q 0 0 0 ∧ HasCompactSupport (0 : ℝ³ → ℝ³) where
  left :=
    { nonneg_f₀ := by simp
      smooth_f₀ α := by simpa [Function.HasUncurry.uncurry] using contDiff_const (c := (0 : ℝ))
      compactSupport_f₀ α := by
        simpa [Function.HasUncurry.uncurry] using HasCompactSupport.zero (α := ℝ³ × ℝ³) (β := ℝ)
      smooth_E₀ := contDiff_const
      smooth_B₀ := contDiff_const
      div_B₀ r := by simp [divergence, partialDeriv]
      div_E₀ r := by simp [divergence, partialDeriv, chargeDensity] }
  right := HasCompactSupport.zero

/-- The vacuum is a global classical solution with vacuum initial data. -/
@[category test, AMS 35]
theorem isGlobalClassicalSolution_zero (c ε₀ μ₀ : ℝ) (m q : ι → ℝ) :
    IsGlobalClassicalSolution c ε₀ μ₀ m q 0 0 0 (fun _ _ _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) where
  smooth_f α := by simpa [Function.HasUncurry.uncurry] using contDiffOn_const (c := (0 : ℝ))
  smooth_E := by simpa [Function.HasUncurry.uncurry] using contDiffOn_const (c := (0 : ℝ³))
  smooth_B := by simpa [Function.HasUncurry.uncurry] using contDiffOn_const (c := (0 : ℝ³))
  compactSupport_f α t _ := by simpa using HasCompactSupport.zero (α := ℝ³ × ℝ³) (β := ℝ)
  initial_f α r p := rfl
  initial_E r := rfl
  initial_B r := rfl
  vlasov α r p t _ := by simp
  ampere r t _ := by simp [curl, partialDeriv, currentDensity]
  div_B r t _ := by simp [divergence, partialDeriv]
  faraday r t _ := by simp [curl, partialDeriv]
  div_E r t _ := by simp [divergence, partialDeriv, chargeDensity]

end VlasovMaxwellEquations
