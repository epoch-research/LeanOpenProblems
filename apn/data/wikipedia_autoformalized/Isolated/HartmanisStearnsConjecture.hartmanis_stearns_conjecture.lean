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

/-- The base-`b` expansion of the real number `x`, viewed as an infinite word over the alphabet
`Fin b`: the `n`-th letter (`0`-indexed) is the `n`-th digit after the radix point in the
base-`b` expansion of `|x|`, namely `⌊b ^ (n + 1) {|x|}⌋ mod b` (see `NormalNumber.digitSeq`).
Whenever `|x|` has two base-`b` expansions, this is the one that does not end in an infinite
string of the digit `b - 1`. The sign of `x` and the finitely many digits of the integer part
of `|x|` are omitted: they do not affect real-time computability. -/
noncomputable def digitWord (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n : ℕ) : Fin b :=
  ⟨digitSeq b |x| n, Nat.mod_lt _ (by omega)⟩

/-- **Hartmanis–Stearns conjecture.**

If $x$ is a real number whose expansion in some base $b \geq 2$ (e.g. the decimal expansion for
$b = 10$) is real-time computable, then $x$ is rational or transcendental.

The base-$b$ expansion of $x$ is represented by the infinite word `digitWord b hb x` of the
digits of $|x|$ after the radix point. The hypothesis `2 ≤ b` is essential: in base `1` every
digit is `0`. -/
theorem hartmanis_stearns_conjecture (x : ℝ)
    (hx : ∃ (b : ℕ) (hb : 2 ≤ b), IsRealTimeComputable (digitWord b hb x)) :
    (∃ q : ℚ, x = q) ∨ Transcendental ℚ x := by
  sorry

end HartmanisStearnsConjecture

theorem HartmanisStearnsConjecture.hartmanis_stearns_conjecture.disproof : ¬ (type_of% @HartmanisStearnsConjecture.hartmanis_stearns_conjecture) := sorry
