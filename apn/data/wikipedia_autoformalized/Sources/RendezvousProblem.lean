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
# Rendezvous problem

Two players are placed at two distinct locations among $n$ indistinguishable locations (the
complete graph $K_n$). At each step $t = 1, 2, \dots$ each player either stays put or moves to any
other location, and the players meet at the first time at which they occupy the same location. The
locations carry no common labelling: each player can only describe a strategy in terms of its own
labelling of the locations, and the two labellings are related by an unknown permutation. In the
*symmetric* rendezvous problem (sometimes called the Mozart Café rendezvous problem) both players
must use the same (mixed) strategy, and the aim is to minimise the expected meeting time.

Anderson and Weber (1990) proposed the following strategy and conjectured that it is optimal for
the symmetric problem on $n$ locations: split time into blocks of $n - 1$ steps; at the start of
each block, independently of the past, stay put for the whole block with probability $\theta$ and
with probability $1 - \theta$ visit the other $n - 1$ locations in a uniformly random order, where
$\theta \in [0, 1]$ is chosen optimally. Weber (2012) proved the conjecture for $n = 3$: the
Anderson–Weber strategy with $\theta = 1/3$ is optimal and has expected meeting time $5/2$. Weber
(2009) reported that the Anderson–Weber strategy is not optimal for $n = 4$; the statement below
records the conjecture as it is stated in the source.

The *asymmetric* rendezvous problem, in which the two players may use different strategies, has a
simple optimal solution ("wait for mommy"): one player stays put and the other visits the remaining
locations in a uniformly random order.

## Formalisation

The locations are `Fin n`. Each player labels its own starting location `0`. A pure strategy is a
sequence `f : ℕ → Fin n`, where `f t` is the location, in the player's own labelling, that the
player occupies at time `t + 1` (i.e. after `t + 1` moves). Player II's labels are translated into
player I's labels by a permutation `σ` of `Fin n`; since the starting locations are distinct,
`σ 0 ≠ 0`, and since the locations are indistinguishable, `σ` is uniformly distributed over all such
permutations. The players meet at time `t + 1` when `f t = σ (g t)`.

A mixed strategy is a probability measure on `ℕ → Fin n`. The expected meeting time of a pair of
mixed strategies is the integral of the meeting time (which is `∞` if the players never meet)
against the product of the two mixed strategies, averaged over `σ`.

*References:*
- [Wikipedia, *Rendezvous problem*](https://en.wikipedia.org/wiki/Rendezvous_problem)
- [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Games_and_puzzles)
- E. J. Anderson and R. R. Weber, *The rendezvous problem on discrete locations*,
  J. Appl. Probab. 27 (1990), 839–851. [doi:10.2307/3214827](https://doi.org/10.2307/3214827)
- R. Weber, *Optimal symmetric rendezvous search on three locations*,
  Math. Oper. Res. 37 (2012), 111–122.
  [doi:10.1287/moor.1110.0528](https://doi.org/10.1287/moor.1110.0528)
- R. Weber, *The Anderson–Weber strategy is not optimal for symmetric rendezvous search on K4*,
  [arXiv:0912.0670](https://arxiv.org/abs/0912.0670)
-/

open MeasureTheory
open scoped ENNReal

namespace RendezvousProblem

variable {n : ℕ} [NeZero n]

/-
### The game
-/

variable (n) in
/-- The permutations of `Fin n` that can translate player II's labelling of the locations into
player I's labelling. Both players label their own starting location `0` and the starting
locations are distinct, so such a permutation `σ` satisfies `σ 0 ≠ 0`. -/
def relabellings : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun σ => σ 0 ≠ 0

/-- The meeting time of the pure strategies `f` (player I) and `g` (player II) when `σ` translates
player II's labels into player I's labels: the least `t + 1` such that `f t = σ (g t)`, or `∞` if
the players never meet. -/
noncomputable def meetingTime (f g : ℕ → Fin n) (σ : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : f t = σ (g t)), ((t : ℝ≥0∞) + 1)

/-- The expected meeting time of the pure strategies `f` (player I) and `g` (player II) when the
relabelling `σ` is uniformly distributed over `relabellings n`. -/
noncomputable def meanMeetingTime (f g : ℕ → Fin n) : ℝ≥0∞ :=
  (∑ σ ∈ relabellings n, meetingTime f g σ) / (relabellings n).card

/-- The expected meeting time when player I uses the mixed strategy `μ` and player II
independently uses the mixed strategy `ν`. -/
noncomputable def expectedMeetingTime (μ ν : Measure (ℕ → Fin n)) : ℝ≥0∞ :=
  ∫⁻ p, meanMeetingTime p.1 p.2 ∂(μ.prod ν)

/-- A mixed strategy `μ` is optimal for the symmetric rendezvous problem if it is a probability
measure on pure strategies and, when used by both players, it gives an expected meeting time that
is at most that of any other probability measure used by both players. -/
def IsOptimalSymmetricStrategy (μ : Measure (ℕ → Fin n)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ ν : Measure (ℕ → Fin n), IsProbabilityMeasure ν →
      expectedMeetingTime μ μ ≤ expectedMeetingTime ν ν

/-- A pair of mixed strategies `μ₁` (player I), `μ₂` (player II) is optimal for the asymmetric
rendezvous problem if both are probability measures on pure strategies and their expected meeting
time is at most that of any other pair of probability measures. -/
def IsOptimalStrategyPair (μ₁ μ₂ : Measure (ℕ → Fin n)) : Prop :=
  IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
    ∀ ν₁ ν₂ : Measure (ℕ → Fin n), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      expectedMeetingTime μ₁ μ₂ ≤ expectedMeetingTime ν₁ ν₂

/-
### The Anderson–Weber strategy
-/

/-- `otherLocation c j` is the location `j + 1` steps after `c` in the cyclic order of `Fin n`.
As `j` ranges over `Fin (n - 1)`, this enumerates the `n - 1` locations other than `c`. -/
def otherLocation (c : Fin n) (j : Fin (n - 1)) : Fin n := c + ⟨j + 1, by omega⟩

/-- A choice for one block of `n - 1` steps in the Anderson–Weber strategy: either stay put for the
whole block, or tour the `n - 1` locations other than the current one in the order given by `τ`
(the `j`-th step of the block visits `otherLocation c (τ j)`, where `c` is the current location). -/
inductive BlockChoice (n : ℕ)
  | stay : BlockChoice n
  | tour (τ : Equiv.Perm (Fin (n - 1))) : BlockChoice n
  deriving Fintype

instance : MeasurableSpace (BlockChoice n) := ⊤

instance : MeasurableSingletonClass (BlockChoice n) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Given block choices `c`, `blockStart hn c k` is the location occupied at the start of block `k`,
i.e. at time `k * (n - 1)`. The player starts at `0`. -/
def blockStart (hn : 2 ≤ n) (c : ℕ → BlockChoice n) : ℕ → Fin n
  | 0 => 0
  | k + 1 =>
    match c k with
    | .stay => blockStart hn c k
    | .tour τ => otherLocation (blockStart hn c k) (τ ⟨n - 2, by omega⟩)

/-- The pure strategy determined by the block choices `c`: time `t + 1` lies in block
`k = t / (n - 1)`, at offset `t % (n - 1)`; the player either stays at the location occupied at the
start of the block or visits the other locations in the order prescribed by the block choice. -/
def pathOfBlockChoices (hn : 2 ≤ n) (c : ℕ → BlockChoice n) (t : ℕ) : Fin n :=
  match c (t / (n - 1)) with
  | .stay => blockStart hn c (t / (n - 1))
  | .tour τ =>
    otherLocation (blockStart hn c (t / (n - 1))) (τ ⟨t % (n - 1), Nat.mod_lt _ (by omega)⟩)

variable (n) in
/-- The distribution of a single block choice in the Anderson–Weber strategy with parameter `θ`:
stay put with probability `θ`, and otherwise tour the other locations in a uniformly random order.
This is a probability measure when `θ ≤ 1`. -/
noncomputable def blockChoiceDist (θ : ℝ≥0∞) : Measure (BlockChoice n) :=
  θ • Measure.dirac .stay +
    (1 - θ) • ((PMF.uniformOfFintype (Equiv.Perm (Fin (n - 1)))).map .tour).toMeasure

variable (n) in
/-- The Anderson–Weber strategy with parameter `θ ∈ [0, 1]` on `n ≥ 2` locations, as a mixed
strategy: the choices for the successive blocks of `n - 1` steps are independent and identically
distributed with law `blockChoiceDist n θ`, and they determine the pure strategy via
`pathOfBlockChoices`. -/
noncomputable def andersonWeberStrategy (hn : 2 ≤ n) (θ : ℝ≥0∞) : Measure (ℕ → Fin n) :=
  (Measure.infinitePi fun _ : ℕ => blockChoiceDist n θ).map (pathOfBlockChoices hn)

/-
### The "wait for mommy" strategies
-/

variable (n) in
/-- The mixed strategy of a player who stays put at the starting location forever. -/
noncomputable def waitStrategy : Measure (ℕ → Fin n) := Measure.dirac fun _ => 0

/-- The pure strategy that visits the `n - 1` locations other than the starting location `0` in the
order `τ` during the first `n - 1` steps (and then repeats this tour). -/
def tourPath (hn : 2 ≤ n) (τ : Equiv.Perm (Fin (n - 1))) (t : ℕ) : Fin n :=
  otherLocation 0 (τ ⟨t % (n - 1), Nat.mod_lt _ (by omega)⟩)

variable (n) in
/-- The mixed strategy of a player who visits the `n - 1` locations other than the starting
location in a uniformly random order. -/
noncomputable def randomTourStrategy (hn : 2 ≤ n) : Measure (ℕ → Fin n) :=
  ((PMF.uniformOfFintype (Equiv.Perm (Fin (n - 1)))).map (tourPath hn)).toMeasure

/-
### Basic API
-/

omit [NeZero n] in
/-- The map `j ↦ otherLocation c j` is injective. -/
@[category API, AMS 60]
theorem otherLocation_injective (c : Fin n) : Function.Injective (otherLocation c) := by
  intro j₁ j₂ h
  rw [otherLocation, otherLocation, add_right_inj, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

/-- `otherLocation c j` is never `c` itself. Together with `otherLocation_injective`, this shows
that `otherLocation c` enumerates the `n - 1` locations other than `c`. -/
@[category API, AMS 60]
theorem otherLocation_ne (c : Fin n) (j : Fin (n - 1)) : otherLocation c j ≠ c := by
  intro h
  rw [otherLocation, add_eq_left, Fin.ext_iff] at h
  simp at h

/-- On two locations, the only admissible relabelling swaps the two locations. -/
@[category test, AMS 60]
theorem relabellings_two : relabellings 2 = {Equiv.swap 0 1} := by
  decide

/-- On three locations there are `(3 - 1) * (3 - 1)! = 4` admissible relabellings. -/
@[category test, AMS 60]
theorem card_relabellings_three : (relabellings 3).card = 4 := by
  decide

/-- If the players are at the same location after their first move, they meet at time `1`. -/
@[category test, AMS 60]
theorem meetingTime_example :
    meetingTime (fun _ : ℕ => (0 : Fin 2)) (fun _ => 1) (Equiv.swap 0 1) = 1 := by
  apply le_antisymm
  · exact (iInf₂_le 0 (by decide)).trans (by simp)
  · exact le_iInf₂ fun t _ => le_add_self

omit [NeZero n] in
@[category API, AMS 60]
theorem measurable_meetingTime (σ : Equiv.Perm (Fin n)) :
    Measurable fun p : (ℕ → Fin n) × (ℕ → Fin n) => meetingTime p.1 p.2 σ := by
  unfold meetingTime
  refine Measurable.iInf fun t => ?_
  have h : (fun p : (ℕ → Fin n) × (ℕ → Fin n) => ⨅ (_ : p.1 t = σ (p.2 t)), ((t : ℝ≥0∞) + 1)) =
      fun p => if p.1 t = σ (p.2 t) then ((t : ℝ≥0∞) + 1) else ⊤ := by
    ext p
    split_ifs with hp <;> simp [hp]
  rw [h]
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_pi_apply t).comp measurable_fst)
    ((measurable_of_countable σ).comp ((measurable_pi_apply t).comp measurable_snd))

/-- The integrand defining `expectedMeetingTime` is measurable. -/
@[category API, AMS 60]
theorem measurable_meanMeetingTime :
    Measurable fun p : (ℕ → Fin n) × (ℕ → Fin n) => meanMeetingTime p.1 p.2 := by
  unfold meanMeetingTime
  exact (Finset.measurable_sum _ fun σ _ => measurable_meetingTime σ).div_const _

@[category API, AMS 60]
theorem measurable_blockStart (hn : 2 ≤ n) (k : ℕ) :
    Measurable fun c : ℕ → BlockChoice n => blockStart hn c k := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have : (fun c : ℕ → BlockChoice n => blockStart hn c (k + 1)) =
        (fun p : BlockChoice n × Fin n =>
          match p.1 with
          | .stay => p.2
          | .tour τ => otherLocation p.2 (τ ⟨n - 2, by omega⟩)) ∘
        (fun c => (c k, blockStart hn c k)) := by
      ext c
      simp only [Function.comp, blockStart]
    rw [this]
    exact (measurable_of_countable _).comp ((measurable_pi_apply k).prodMk ih)

@[category API, AMS 60]
theorem measurable_pathOfBlockChoices (hn : 2 ≤ n) : Measurable (pathOfBlockChoices hn) := by
  refine measurable_pi_iff.mpr fun t => ?_
  have : (fun c : ℕ → BlockChoice n => pathOfBlockChoices hn c t) =
      (fun p : BlockChoice n × Fin n =>
        match p.1 with
        | .stay => p.2
        | .tour τ => otherLocation p.2 (τ ⟨t % (n - 1), Nat.mod_lt _ (by omega)⟩)) ∘
      (fun c => (c (t / (n - 1)), blockStart hn c (t / (n - 1)))) := by
    ext c
    simp only [Function.comp, pathOfBlockChoices]
  rw [this]
  exact (measurable_of_countable _).comp
    ((measurable_pi_apply _).prodMk (measurable_blockStart hn _))

omit [NeZero n] in
@[category API, AMS 60]
theorem isProbabilityMeasure_blockChoiceDist {θ : ℝ≥0∞} (hθ : θ ≤ 1) :
    IsProbabilityMeasure (blockChoiceDist n θ) := by
  constructor
  simp [blockChoiceDist, add_tsub_cancel_of_le hθ]

/-- For `θ ≤ 1`, the Anderson–Weber strategy is a genuine mixed strategy. -/
@[category API, AMS 60]
theorem isProbabilityMeasure_andersonWeberStrategy (hn : 2 ≤ n) {θ : ℝ≥0∞} (hθ : θ ≤ 1) :
    IsProbabilityMeasure (andersonWeberStrategy n hn θ) := by
  have := fun _ : ℕ => isProbabilityMeasure_blockChoiceDist (n := n) hθ
  exact Measure.isProbabilityMeasure_map (measurable_pathOfBlockChoices hn).aemeasurable

@[category API, AMS 60]
theorem isProbabilityMeasure_waitStrategy : IsProbabilityMeasure (waitStrategy n) := by
  unfold waitStrategy
  infer_instance

@[category API, AMS 60]
theorem isProbabilityMeasure_randomTourStrategy (hn : 2 ≤ n) :
    IsProbabilityMeasure (randomTourStrategy n hn) := by
  unfold randomTourStrategy
  infer_instance

/-
### Statements
-/

/-- **Anderson–Weber conjecture** (1990). For every $n \geq 2$, the optimal strategy for the
symmetric rendezvous problem on $n$ locations is the Anderson–Weber strategy for a suitable
$\theta \in [0, 1]$: in each block of $n - 1$ steps, stay put with probability $\theta$ and
otherwise tour the other $n - 1$ locations in a uniformly random order. -/
@[category research open, AMS 60 90 91]
theorem rendezvous_problem (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ∃ θ ≤ 1, IsOptimalSymmetricStrategy (andersonWeberStrategy n hn θ) := by
  sorry

/-- **Weber (2012)**: the Anderson–Weber conjecture holds for $n = 3$. The Anderson–Weber strategy
with $\theta = 1/3$ (in each block of two steps, stay put with probability $1/3$ and otherwise
tour the other two locations in a uniformly random order) is optimal for the symmetric rendezvous
problem on three locations, and its expected meeting time is $5/2$. -/
@[category research solved, AMS 60 90 91]
theorem rendezvous_problem.variants.three_locations :
    IsOptimalSymmetricStrategy (andersonWeberStrategy 3 (by norm_num) (1 / 3)) ∧
      expectedMeetingTime (andersonWeberStrategy 3 (by norm_num) (1 / 3))
        (andersonWeberStrategy 3 (by norm_num) (1 / 3)) = 5 / 2 := by
  sorry

/-- The asymmetric rendezvous problem on $n \geq 2$ locations has a simple optimal solution
("wait for mommy"): one player stays put and the other player visits the remaining $n - 1$
locations in a uniformly random order. -/
@[category research solved, AMS 60 90 91]
theorem rendezvous_problem.variants.asymmetric (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    IsOptimalStrategyPair (waitStrategy n) (randomTourStrategy n hn) := by
  sorry

end RendezvousProblem
