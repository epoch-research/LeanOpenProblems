import FormalConjecturesUtil

/-!
# Erdős Problem 478

*Reference:* [erdosproblems.com/478](https://www.erdosproblems.com/478)
-/

namespace Erdos478

/--
Let $p$ be a prime and\[A_p = \{ k! \pmod{p} : 1\leq k<p\}.\]Is it true that\[\lvert A_p\rvert \sim (1-\tfrac{1}{e})p?\]
-/
theorem erdos_478 :
    Filter.Tendsto
      (fun p : ℕ =>
        (((Finset.Ico 1 p).image (fun k => Nat.factorial k % p)).card : ℝ) / p)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (nhds (1 - 1 / Real.exp 1))
      := by
  sorry

end Erdos478

theorem Erdos478.erdos_478.disproof : ¬ (type_of% @Erdos478.erdos_478) := sorry
