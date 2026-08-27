import FormalConjecturesUtil

/-!
# Erdős Problem 1083

*Reference:* [erdosproblems.com/1083](https://www.erdosproblems.com/1083)
-/

open Filter

namespace Erdos1083

/--
The minimum number of distinct distances determined by an $n$-point subset of
$d$-dimensional Euclidean space.
-/
noncomputable def f (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset (EuclideanSpace ℝ (Fin d)),
    points.card = n ∧ distinctDistances points = m}

/--
Let $d\geq 3$, and let $f_d(n)$ be the minimal $m$ such that every set of $n$ points in $\mathbb{R}^d$ determines at least $m$ distinct distances. Estimate $f_d(n)$ - in particular, is it true that\[f_d(n)=n^{\frac{2}{d}-o(1)}?\]
-/
theorem erdos_1083 :
    (∀ d : ℕ, 3 ≤ d → ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop,
        (f d n : ℝ) = (n : ℝ) ^ ((2 : ℝ) / (d : ℝ) - o n)) := by
  sorry

end Erdos1083

theorem Erdos1083.erdos_1083.disproof : ¬ (type_of% @Erdos1083.erdos_1083) := sorry
