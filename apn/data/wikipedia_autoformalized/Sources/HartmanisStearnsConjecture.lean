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
# Hartmanis–Stearns conjecture

An infinite word is *real-time computable* if some multitape Turing machine, run without input,
writes the successive letters of the word on its output tape, taking a bounded amount of time
between two successive letters. Equivalently (Fischer, Meyer and Rosenberg, 1970), some multitape
Turing machine, given a natural number $n$ in unary, outputs the first $n$ letters of the word in
time $O(n)$.

The Hartmanis–Stearns conjecture states that if $x$ is a real number whose expansion in some base
$b \geq 2$ (e.g. the decimal expansion for $b = 10$) is real-time computable, then $x$ is rational
or transcendental. This is the expected negative answer to the question asked by Hartmanis and
Stearns in 1965: do there exist irrational algebraic numbers whose first $n$ digits can be
computed in $O(n)$ operations by a multitape deterministic Turing machine?

We use the second (linear-time) formulation. Multitape Turing machines are modelled by Mathlib's
bundled multi-stack machines `Turing.FinTM2`, the model behind `Turing.TM2ComputableInTime`.
A tape can be simulated by two stacks and a stack by a tape, each with a constant factor overhead
in time, so the class of words computable in linear time does not depend on this choice.

*References:*
- [Wikipedia: Hartmanis–Stearns conjecture](https://en.wikipedia.org/wiki/Hartmanis%E2%80%93Stearns_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [HS65] Hartmanis, J., Stearns, R. E. *On the computational complexity of algorithms.*
  Trans. Amer. Math. Soc. 117 (1965), 285–306.
- [FMR70] Fischer, P. C., Meyer, A. R., Rosenberg, A. L. *Time-restricted sequence generation.*
  J. Comput. System Sci. 4 (1970), 50–73.
- [ACL20] Adamczewski, B., Cassaigne, J., Le Gonidec, M. *On the computational complexity of
  algebraic numbers: the Hartmanis–Stearns problem revisited.* Trans. Amer. Math. Soc. 373
  (2020), 3085–3115. [arXiv:1601.02771](https://arxiv.org/abs/1601.02771)
-/

open Computability Turing NormalNumber

namespace HartmanisStearnsConjecture

/-- The letterwise encoding of finite words over a finite alphabet `α`: a word is encoded by
itself, one tape symbol per letter. -/
def finEncodingList (α : Type) [Fintype α] : FinEncoding (List α) where
  Γ := α
  encode := id
  decode := some
  decode_encode _ := rfl
  ΓFin := inferInstance

/-- The letterwise encoding of a word is the word itself. -/
@[category API, AMS 68]
theorem finEncodingList_encode {α : Type} [Fintype α] (l : List α) :
    (finEncodingList α).encode l = l :=
  rfl

/-- An infinite word `w` over a finite alphabet `α` is *real-time computable* if there is a
multitape Turing machine (here a multi-stack machine `Turing.FinTM2`) which, given `n` in unary,
outputs the first `n` letters `w 0, …, w (n - 1)` of `w` in at most `C * (n + 1)` steps, for a
constant `C` independent of `n`. By a theorem of Fischer, Meyer and Rosenberg this is equivalent
to the existence of a multitape Turing machine that, run without input, writes the successive
letters of `w` with a bounded delay between two successive letters. -/
def IsRealTimeComputable {α : Type} [Fintype α] (w : ℕ → α) : Prop :=
  ∃ M : TM2ComputableInTime unaryFinEncodingNat (finEncodingList α)
      (fun n => (List.range n).map w),
    ∃ C : ℕ, ∀ n : ℕ, M.time n ≤ C * (n + 1)

/-- A real-time computable word is computable: some Turing machine, given `n` in unary,
outputs its first `n` letters. -/
@[category API, AMS 68]
theorem IsRealTimeComputable.tm2Computable {α : Type} [Fintype α] {w : ℕ → α}
    (hw : IsRealTimeComputable w) :
    Nonempty (TM2Computable unaryFinEncodingNat (finEncodingList α)
      fun n => (List.range n).map w) :=
  let ⟨M, _⟩ := hw
  ⟨M.toTM2Computable⟩

/-- The unary encoding of `n` is the word `1 ^ n`. -/
@[category API, AMS 68]
theorem unaryEncodeNat_eq_replicate (n : ℕ) : unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unaryEncodeNat, ih, List.replicate_succ]

/-- The stack alphabets of the machine `constTM`: the input stack `false` holds `Bool`s and the
output stack `true` holds letters of `α`. -/
def constΓ (α : Type) : Bool → Type
  | false => Bool
  | true => α

/-- A two-stack machine which, given `n` in unary, outputs `n` copies of the letter `a`: at each
step it pops one input symbol and pushes `a`, and it halts once the input stack is empty. -/
def constTM {α : Type} (a : α) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := constΓ α
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ := TM2.Stmt.pop false (fun _ o => o.isSome)
    (TM2.Stmt.branch id
      (TM2.Stmt.push true (fun _ => a) (TM2.Stmt.load (fun _ => false) (TM2.Stmt.goto fun _ => ())))
      TM2.Stmt.halt)

/-- `constTM` halts when its input stack is empty. -/
@[category API, AMS 68]
theorem constTM_step_nil {α : Type} (a : α) (S : ∀ k, List ((constTM a).Γ k))
    (h0 : S false = []) :
    (constTM a).step ⟨some (), false, S⟩ = some ⟨none, false, S⟩ := by
  show TM2.step _ _ = _
  simp only [TM2.step, TM2.stepAux, constTM, h0]
  simp only [List.head?_nil, Option.isSome_none, id, cond_false, List.tail_nil, Option.some.injEq]
  congr
  rw [← h0, Function.update_eq_self]

/-- `constTM` pops one input symbol and pushes `a` when its input stack is nonempty. -/
@[category API, AMS 68]
theorem constTM_step_cons {α : Type} (a : α) (S : ∀ k, List ((constTM a).Γ k))
    (b : Bool) (l : List Bool) (h0 : S false = b :: l) :
    (constTM a).step ⟨some (), false, S⟩ =
      some ⟨some (), false, Function.update (Function.update S false l) true (a :: S true)⟩ := by
  show TM2.step _ _ = _
  simp only [TM2.step, TM2.stepAux, constTM, h0]
  simp only [List.head?_cons, Option.isSome_some, id, cond_true, List.tail_cons,
    Function.update_of_ne (show (true : Bool) ≠ false by decide)]

/-- Started with `m` input symbols and `n - m` output letters, `constTM` halts after `m + 1`
steps with `n` output letters. -/
@[category API, AMS 68]
theorem constTM_run {α : Type} (a : α) (n : ℕ) :
    ∀ (m : ℕ) (S : ∀ k, List ((constTM a).Γ k)),
      S false = List.replicate m true → S true = List.replicate (n - m) a → m ≤ n →
      (flip bind (constTM a).step)^[m + 1] (some ⟨some (), false, S⟩) =
        some (haltList (constTM a) (List.replicate n a)) := by
  intro m
  induction m with
  | zero =>
    intro S h0 h1 _
    simp only [zero_add, Function.iterate_one, flip, Option.bind_eq_bind, Option.bind_some,
      constTM_step_nil a S h0, Option.some.injEq]
    congr
    funext k
    cases k
    · simpa [haltList] using h0
    · simpa [haltList] using h1
  | succ m ih =>
    intro S h0 h1 hm
    rw [Function.iterate_succ_apply]
    simp only [flip, Option.bind_eq_bind, Option.bind_some, constTM_step_cons a S true _ h0]
    apply ih
    · rw [Function.update_of_ne (show (false : Bool) ≠ true by decide), Function.update_self]
    · rw [Function.update_self, h1]
      rw [show n - m = (n - (m + 1)) + 1 by omega, List.replicate_succ]
    · omega

/-- A constant word is real-time computable: `constTM` outputs its first `n` letters in `n + 1`
steps. -/
@[category test, AMS 68]
theorem isRealTimeComputable_const {α : Type} [Fintype α] (a : α) :
    IsRealTimeComputable (fun _ : ℕ => a) := by
  refine ⟨{ tm := constTM a
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl α
            time := fun n => n + 1
            outputsFun := fun n => ⟨⟨n + 1, ?_⟩, ?_⟩ }, 1, fun n => le_of_eq (one_mul _).symm⟩
  · have h1 : List.map (Equiv.refl Bool).invFun (unaryFinEncodingNat.encode n) =
        List.replicate n true := by
      simp [unaryFinEncodingNat, unaryEncodeNat_eq_replicate]
    have h2 : List.map (Equiv.refl α).invFun
        ((finEncodingList α).encode (List.map (fun _ => a) (List.range n))) =
        List.replicate n a := by
      simp [finEncodingList]
    rw [h1, h2, Option.map_some]
    exact constTM_run a n n _ (by simp [constTM]) (by simp [constTM]) le_rfl
  · simp [unaryFinEncodingNat, unaryEncodeNat_eq_replicate]

/-- The base-`b` expansion of the real number `x`, viewed as an infinite word over the alphabet
`Fin b`: the `n`-th letter (`0`-indexed) is the `n`-th digit after the radix point in the
base-`b` expansion of `|x|`, namely `⌊b ^ (n + 1) {|x|}⌋ mod b` (see `NormalNumber.digitSeq`).
Whenever `|x|` has two base-`b` expansions, this is the one that does not end in an infinite
string of the digit `b - 1`. The sign of `x` and the finitely many digits of the integer part
of `|x|` are omitted: they do not affect real-time computability. -/
noncomputable def digitWord (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n : ℕ) : Fin b :=
  ⟨digitSeq b |x| n, Nat.mod_lt _ (by omega)⟩

/-- The decimal expansion of `5 / 8 = 0.6250…` starts with the digits `6`, `2`, `5`, `0`. -/
@[category test, AMS 11]
theorem digitWord_five_eighths :
    digitWord 10 (by norm_num) (5 / 8 : ℝ) 0 = 6 ∧ digitWord 10 (by norm_num) (5 / 8 : ℝ) 1 = 2 ∧
      digitWord 10 (by norm_num) (5 / 8 : ℝ) 2 = 5 ∧
        digitWord 10 (by norm_num) (5 / 8 : ℝ) 3 = 0 := by
  have h : Int.fract |(5 / 8 : ℝ)| = 5 / 8 := by
    rw [abs_of_nonneg (by norm_num)]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  simp only [digitWord, digitSeq, h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> norm_num

/-- **Hartmanis–Stearns conjecture.**

If $x$ is a real number whose expansion in some base $b \geq 2$ (e.g. the decimal expansion for
$b = 10$) is real-time computable, then $x$ is rational or transcendental.

The base-$b$ expansion of $x$ is represented by the infinite word `digitWord b hb x` of the
digits of $|x|$ after the radix point. The hypothesis `2 ≤ b` is essential: in base `1` every
digit is `0`. -/
@[category research open, AMS 11 68]
theorem hartmanis_stearns_conjecture (x : ℝ)
    (hx : ∃ (b : ℕ) (hb : 2 ≤ b), IsRealTimeComputable (digitWord b hb x)) :
    (∃ q : ℚ, x = q) ∨ Transcendental ℚ x := by
  sorry

end HartmanisStearnsConjecture
