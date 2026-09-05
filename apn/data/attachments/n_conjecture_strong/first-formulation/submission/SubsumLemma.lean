import FormalConjecturesUtil

/-!
# Subsum lemmas for the strong-four construction

A tuple with one positive entry balancing three strictly negative entries has
zero total sum and no vanishing nonempty proper subsum.
-/

namespace StrongFour

/-- The balancing identity makes the total sum zero. -/
lemma sum_four {A B C D : ℤ} (hA : A = B + C + D) :
    (∑ i, (![A, -B, -C, -D] : Fin 4 → ℤ) i) = 0 := by
  simp [Fin.sum_univ_succ]
  omega

/-- Every nonempty proper subsum of a balanced tuple with three negative entries
is nonzero. -/
lemma no_vanishing_four {A B C D : ℤ}
    (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hA : A = B + C + D) :
    ∀ s : Finset (Fin 4), s.Nonempty → s ≠ Finset.univ →
      ∑ i ∈ s, (![A, -B, -C, -D] : Fin 4 → ℤ) i ≠ 0 := by
  intro s hs hproper
  fin_cases s <;> norm_num +decide at * <;> omega

end StrongFour
