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
# Discrete logarithm

Can a discrete logarithm be computed in polynomial time?

The standard instance of the discrete logarithm problem is the following. Given a prime $p$,
a generator $g$ of the multiplicative group $(\mathbb{Z}/p\mathbb{Z})^\times$ and a unit
$x \in (\mathbb{Z}/p\mathbb{Z})^\times$, all written in binary, find an integer $r$ with
$g^r \equiv x \pmod p$. No classical (non-quantum) algorithm running in time polynomial in the
bit length of the input, which is of the order of $\log p$, is known. The best known classical
algorithms (such as the number field sieve) run in subexponential time, and Shor's algorithm
solves the problem in polynomial time on a quantum computer.

Following `FormalConjectures.Millenium.PvsNP`, we model a polynomial-time algorithm by
`Turing.TM2ComputableInPolyTime`: a deterministic Turing machine (in the TM2 model of Mathlib)
which, on the binary encoding of the input, halts with the binary encoding of the output after a
number of steps bounded by a polynomial in the length of the input encoding.

*References:*
- [Wikipedia, Discrete logarithm](https://en.wikipedia.org/wiki/discrete_logarithm)
- [Wikipedia, List of unsolved problems in
  mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- P. W. Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a
  Quantum Computer*, SIAM J. Comput. 26 (1997),
  [arXiv:quant-ph/9508027](https://arxiv.org/abs/quant-ph/9508027)
-/

open Computability Turing

namespace DiscreteLogarithm

/--
The binary encoding of a triple of natural numbers $(p, g, x)$, used as the input encoding of an
instance of the discrete logarithm problem. Each number is written in binary
(least significant bit first, via `Computability.encodeNat`) and the three numbers are separated
by the separator symbol `none`. The length of the encoding of $(p, g, x)$ is the total number
of binary digits of $p$, $g$ and $x$, plus two (see `DiscreteLogarithm.length_encode`).
-/
def finEncodingNatTriple : FinEncoding (ℕ × ℕ × ℕ) where
  Γ := Option Bool
  encode := fun (p, g, x) ↦
    (encodeNat p).map some ++ [none] ++ (encodeNat g).map some ++ [none] ++ (encodeNat x).map some
  decode := fun l ↦
    match l.splitOnP Option.isNone with
    | [l₁, l₂, l₃] => some (decodeNat (l₁.map (Option.getD · false)),
        decodeNat (l₂.map (Option.getD · false)), decodeNat (l₃.map (Option.getD · false)))
    | _ => none
  decode_encode := by
    intro (p, g, x)
    simp
  ΓFin := instFintypeOption

/-- The encoding of the instance $(p, g, x) = (5, 2, 3)$: in binary (least significant bit
first) $5 = 101$, $2 = 01$ and $3 = 11$. -/
@[category test, AMS 68]
theorem finEncodingNatTriple_encode_example :
    finEncodingNatTriple.encode (5, 2, 3) =
      [some true, some false, some true, none, some false, some true, none,
        some true, some true] := by
  simp only [finEncodingNatTriple]
  decide +kernel

/-- Decoding the word `101,01,11` gives back the instance $(5, 2, 3)$. -/
@[category test, AMS 68]
theorem finEncodingNatTriple_decode_example :
    finEncodingNatTriple.decode
      [some true, some false, some true, none, some false, some true, none,
        some true, some true] = some (5, 2, 3) := by
  decide

/-- The length of the encoding of an instance $(p, g, x)$ is the total number of binary digits
of $p$, $g$ and $x$, plus two separator symbols. -/
@[category API, AMS 68]
theorem length_encode (p g x : ℕ) :
    (finEncodingNatTriple.encode (p, g, x)).length =
      Nat.size p + Nat.size g + Nat.size x + 2 := by
  have hlen : ∀ n : ℕ, (encodeNat n).length = Nat.size n := by
    have h₀ : ∀ m : PosNum, (encodePosNum m).length = m.natSize := fun m ↦ by
      induction m with
      | one => rfl
      | bit0 m ih => simp [encodePosNum, PosNum.natSize, ih]
      | bit1 m ih => simp [encodePosNum, PosNum.natSize, ih]
    have h : ∀ m : Num, (encodeNum m).length = m.natSize := by
      rintro (_ | m)
      · rfl
      · exact h₀ m
    intro n
    rw [encodeNat, h, Num.natSize_to_nat, Num.to_of_nat]
  simp only [finEncodingNatTriple, List.length_append, List.length_map, List.length_singleton,
    hlen]
  ring

/-- For a valid instance $(p, g, x)$ with $g, x < p$, the length of the encoding is at most
$3 \lfloor \log_2 p \rfloor + 5$. Hence a running time polynomial in the input length is a
running time polynomial in $\log p$, not in $p$. -/
@[category API, AMS 68]
theorem length_encode_le {p g x : ℕ} (hg : g < p) (hx : x < p) :
    (finEncodingNatTriple.encode (p, g, x)).length ≤ 3 * Nat.log 2 p + 5 := by
  have h₁ : Nat.size p ≤ Nat.log 2 p + 1 :=
    Nat.size_le.2 (Nat.lt_pow_succ_log_self one_lt_two p)
  have h₂ := Nat.size_le_size hg.le
  have h₃ := Nat.size_le_size hx.le
  rw [length_encode]
  omega

/--
The discrete logarithm problem is well posed: if $p$ is prime, $g$ is a generator of
$(\mathbb{Z}/p\mathbb{Z})^\times$ (i.e. $g$ has multiplicative order $p - 1$ modulo $p$) and
$x$ is a unit modulo $p$, then there is a natural number $r$ with $g^r \equiv x \pmod p$.
-/
@[category textbook, AMS 11]
theorem exists_pow_eq {p g x : ℕ} (hp : p.Prime) (hg : orderOf (g : ZMod p) = p - 1)
    (hx : IsUnit (x : ZMod p)) : ∃ r : ℕ, (g : ZMod p) ^ r = x := by
  haveI := Fact.mk hp
  haveI : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.one_lt⟩
  have hg' : IsPrimitiveRoot (g : ZMod p) (p - 1) := hg ▸ IsPrimitiveRoot.orderOf _
  obtain ⟨r, -, hr⟩ := hg'.eq_pow_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx.ne_zero)
  exact ⟨r, hr⟩

/--
**Discrete logarithm problem.** Can a discrete logarithm be computed in polynomial time?

That is, is there a classical deterministic algorithm which, given a prime $p$, a generator
$g$ of $(\mathbb{Z}/p\mathbb{Z})^\times$ and a unit $x \in (\mathbb{Z}/p\mathbb{Z})^\times$
(represented by natural numbers $g, x < p$; all written in binary), outputs a natural number $r$
with $g^r \equiv x \pmod p$, and whose running time is bounded by a polynomial in the bit length
of the input (which is of the order of $\log p$)?

Formally: is there a function $f$ on triples of natural numbers that is computable in polynomial
time by a Turing machine (in the sense of `Turing.TM2ComputableInPolyTime`, with the input in
binary via `DiscreteLogarithm.finEncodingNatTriple` and the output in binary via
`Computability.finEncodingNatBool`) and that returns a discrete logarithm on every valid
instance? Here $g$ is a generator of $(\mathbb{Z}/p\mathbb{Z})^\times$ if and only if its
multiplicative order modulo $p$ is $p - 1$. The machine must halt within the polynomial time
bound on every input, but the value of $f$ on invalid instances (where $p$ is not prime, $g$ is
not a generator or $x$ is not a unit) is unconstrained.
-/
@[category research open, AMS 11 68]
theorem discrete_logarithm :
    answer(sorry) ↔ ∃ f : ℕ × ℕ × ℕ → ℕ,
      Nonempty (TM2ComputableInPolyTime finEncodingNatTriple finEncodingNatBool f) ∧
      ∀ p g x : ℕ, p.Prime → g < p → x < p → orderOf (g : ZMod p) = p - 1 →
        IsUnit (x : ZMod p) → (g : ZMod p) ^ f (p, g, x) = x := by
  sorry

end DiscreteLogarithm
