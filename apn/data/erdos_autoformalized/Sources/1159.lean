import FormalConjecturesUtil

/-!
# Erdős Problem 1159

*Reference:*
- [erdosproblems.com/1159](https://www.erdosproblems.com/1159)
-/

open Configuration

namespace Erdos1159

/--
Determine whether there exists a constant $C>1$ such that the following holds.

Let $P$ be a finite <a href="https://en.wikipedia.org/wiki/Projective_plane" rel="nofollow noopener noreferrer ugc" target="_blank">projective plane</a>. Must there exist a set of points $S$ such that $1\leq \lvert S\cap \ell\rvert \leq C$ for all lines $\ell$?
-/
@[category research open, AMS 5 51]
theorem erdos_1159 :
    (∃ C : ℕ, 1 < C ∧
      ∀ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L),
        ∀ _ : ProjectivePlane P L, ∃ S : Set P, ∀ l : L,
          1 ≤ (S ∩ {p : P | p ∈ l}).ncard ∧ (S ∩ {p : P | p ∈ l}).ncard ≤ C) := by
  sorry

end Erdos1159
