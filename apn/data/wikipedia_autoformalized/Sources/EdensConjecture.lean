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
# Eden's conjecture

Eden's conjecture states that the supremum of the local Lyapunov dimensions on the global
attractor of a smooth dynamical system is achieved on a stationary point or an unstable periodic
orbit embedded into the attractor. It was proposed by Alp Eden in 1987.

We follow the finite-dimensional setting of Kuznetsov (2016). A smooth dynamical system is a
semiflow $\{\varphi^t\}_{t \ge 0}$ on a finite-dimensional real inner product space $E$ of
dimension $n$ whose time-$t$ maps are continuously differentiable. For $u \in E$ and $t \ge 0$,
let $\sigma_1(t, u) \ge \dots \ge \sigma_n(t, u) \ge 0$ be the singular values of
$D\varphi^t(u)$ and, for $d \in [0, n]$, let
$$\omega_d(D\varphi^t(u)) = \sigma_1(t, u) \cdots \sigma_{\lfloor d \rfloor}(t, u)\,
  \sigma_{\lfloor d \rfloor + 1}(t, u)^{d - \lfloor d \rfloor}$$
be the singular value function. The (infinite-time) local Lyapunov dimension of Eden at $u$ is
$$\dim_{\rm L}^{\rm E}(u) = \inf\{d \in [0, n] :
  \limsup_{t \to +\infty} \big(\omega_d(D\varphi^t(u))\big)^{1/t} < 1\},$$
with the convention that it equals $n$ when no such $d$ exists.

A global attractor is a compact set $K$ which is strictly invariant, $\varphi^t(K) = K$ for all
$t \ge 0$, and which attracts every bounded set.

*References:*
- [Wikipedia, Eden's conjecture](https://en.wikipedia.org/wiki/Eden%27s_conjecture)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- A. Eden, *An abstract theory of L-exponents with applications to dimension analysis*,
  PhD thesis, Indiana University (1989), p. 98, Question 1.
- A. Eden, *Local Lyapunov exponents and a local estimate of Hausdorff dimension*,
  Modélisation Mathématique et Analyse Numérique 23 (1989),
  [doi:10.1051/m2an/1989230304051](https://doi.org/10.1051/m2an/1989230304051).
- N. V. Kuznetsov, *The Lyapunov dimension and its estimation via the Leonov method*,
  Physics Letters A 380 (2016), [arXiv:1602.05410](https://arxiv.org/abs/1602.05410).
-/

open Filter Topology Metric
open scoped NNReal

namespace EdensConjecture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The singular values of a linear map `A` on an `n`-dimensional real inner product space, indexed
from `0` and sorted in decreasing order: `singularValue A i` is the square root of the `i`-th
largest eigenvalue of `A* A` for `i < n`, and `0` for `i ≥ n`. -/
noncomputable def singularValue (A : E →ₗ[ℝ] E) (i : ℕ) : ℝ :=
  if h : i < Module.finrank ℝ E then
    Real.sqrt ((LinearMap.isSymmetric_adjoint_mul_self A).eigenvalues rfl ⟨i, h⟩)
  else 0

/-- The singular value function of order `d` of a linear map `A` with singular values
`σ₁ ≥ σ₂ ≥ ⋯ ≥ σₙ`: for `d ∈ [0, n]` it is
`ω_d(A) = σ₁ ⋯ σ_{⌊d⌋} σ_{⌊d⌋ + 1} ^ (d - ⌊d⌋)`, so that `ω_0(A) = 1` and `ω_n(A) = |det A|`. -/
noncomputable def singularValueFunction (A : E →ₗ[ℝ] E) (d : ℝ) : ℝ :=
  (∏ i ∈ Finset.range ⌊d⌋₊, singularValue A i) * singularValue A ⌊d⌋₊ ^ (d - ⌊d⌋₊)

/-- Singular values are nonnegative. -/
@[category API, AMS 15]
theorem singularValue_nonneg (A : E →ₗ[ℝ] E) (i : ℕ) : 0 ≤ singularValue A i := by
  unfold singularValue
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

/-- The singular value function of order `0` is identically `1`. -/
@[category API, AMS 15]
theorem singularValueFunction_zero (A : E →ₗ[ℝ] E) : singularValueFunction A 0 = 1 := by
  simp [singularValueFunction]

/-- The (infinite-time) local Lyapunov dimension in the sense of Eden of a semiflow `φ` on an
`n`-dimensional space at the point `u`:
$$\dim_{\rm L}^{\rm E}(u) = \inf\{d \in [0, n] :
  \limsup_{t \to +\infty} \big(\omega_d(D\varphi^t(u))\big)^{1/t} < 1\},$$
where `ω_d` is the singular value function and `Dφᵗ(u)` is the derivative of the time-`t` map
at `u`. The `limsup` is taken in `[0, ∞]`. If no `d ∈ [0, n]` satisfies the condition, the
dimension is `n`. -/
noncomputable def localLyapunovDim (φ : Flow ℝ≥0 E) (u : E) : ℝ :=
  sInf {d ∈ Set.Icc (0 : ℝ) (Module.finrank ℝ E) | d = Module.finrank ℝ E ∨
    limsup (fun t : ℝ≥0 => ENNReal.ofReal
      (singularValueFunction (fderiv ℝ (φ t) u : E →ₗ[ℝ] E) d ^ (1 / (t : ℝ)))) atTop < 1}

/-- The local Lyapunov dimension takes values in `[0, n]`. -/
@[category API, AMS 37]
theorem localLyapunovDim_mem_Icc (φ : Flow ℝ≥0 E) (u : E) :
    localLyapunovDim φ u ∈ Set.Icc (0 : ℝ) (Module.finrank ℝ E) := by
  have hmem : (Module.finrank ℝ E : ℝ) ∈ {d ∈ Set.Icc (0 : ℝ) (Module.finrank ℝ E) |
      d = Module.finrank ℝ E ∨ limsup (fun t : ℝ≥0 => ENNReal.ofReal
        (singularValueFunction (fderiv ℝ (φ t) u : E →ₗ[ℝ] E) d ^ (1 / (t : ℝ)))) atTop < 1} :=
    ⟨⟨by positivity, le_rfl⟩, Or.inl rfl⟩
  exact ⟨le_csInf ⟨_, hmem⟩ fun d hd => hd.1.1, csInf_le ⟨0, fun d hd => hd.1.1⟩ hmem⟩

/-- `K` is the global attractor of the semiflow `φ`: `K` is compact, strictly invariant
(`φᵗ(K) = K` for all `t ≥ 0`), and attracts every bounded set `B`, i.e. for every `ε > 0` the
set `φᵗ(B)` is contained in the `ε`-neighbourhood of `K` for all sufficiently large `t`.
Such a `K` is automatically nonempty. -/
structure IsGlobalAttractor (φ : Flow ℝ≥0 E) (K : Set E) : Prop where
  isCompact : IsCompact K
  image_eq : ∀ t, φ t '' K = K
  attracts : ∀ B : Set E, Bornology.IsBounded B →
    ∀ ε > 0, ∀ᶠ t in atTop, φ t '' B ⊆ thickening ε K

/-- **Eden's conjecture.** Let `φ` be a smooth dynamical system, i.e. a semiflow
$\{\varphi^t\}_{t \ge 0}$ on a finite-dimensional real inner product space whose time-`t` maps
are continuously differentiable, and let `K` be its global attractor. Then the supremum of the
local Lyapunov dimensions $\dim_{\rm L}^{\rm E}(u)$ over `u ∈ K` is achieved on a stationary
point or on a periodic orbit embedded into `K`: there is `u ∈ K` that is either fixed by every
`φᵗ` or has some period `T > 0`, such that $\dim_{\rm L}^{\rm E}(v) \le \dim_{\rm L}^{\rm E}(u)$
for all `v ∈ K`. The word "unstable" in the original statement is descriptive and is not imposed
as a hypothesis; this keeps the degenerate case in which `K` is itself a stable equilibrium or
cycle. -/
@[category research open, AMS 37]
theorem edens_conjecture (φ : Flow ℝ≥0 E) (hφ : ∀ t, ContDiff ℝ 1 (φ t)) (K : Set E)
    (hK : IsGlobalAttractor φ K) :
    ∃ u ∈ K, ((∀ t, φ t u = u) ∨ ∃ T : ℝ≥0, 0 < T ∧ φ T u = u) ∧
      IsMaxOn (localLyapunovDim φ) K u := by
  sorry

end EdensConjecture
