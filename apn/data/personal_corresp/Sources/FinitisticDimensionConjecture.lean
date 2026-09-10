import FormalConjecturesUtil

/-!
# The finitistic dimension conjecture

The (little) finitistic dimension of a ring `A` is the supremum of the projective dimensions
of the finitely generated `A`-modules of finite projective dimension. The **finitistic
dimension conjecture** asserts that this supremum is finite for every finite-dimensional
algebra over a field. It was formulated by Bass in 1960 and is one of the central homological
conjectures in the representation theory of finite-dimensional algebras.

*References:*
- [Ba60] Bass, H., *Finitistic dimension and a homological generalization of semi-primary
  rings*, Trans. Amer. Math. Soc. 95 (1960), 466--488.
- [Hu95] Huisgen-Zimmermann, B., *The finitistic dimension conjectures -- a tale of 3.5 decades*,
  in: Abelian groups and modules (Padova, 1994), Kluwer (1995), 501--517.
- [Xi] Xi, C., *Some homological conjectures for finite dimensional algebras*, Oberwolfach
  problem session (2005), [pdf](https://www.math.uni-bielefeld.de/~sek/mfo2005/xi-web.pdf).
-/

universe u v

open CategoryTheory

namespace FinitisticDimension

/-- The little (left) finitistic dimension of `A` is finite: there is a uniform bound `N` on the
projective dimension of the finitely generated `A`-modules of finite projective dimension. -/
def HasFiniteFinitisticDimension (A : Type v) [Ring A] : Prop :=
  ∃ N : ℕ, ∀ M : ModuleCat.{v} A,
    Module.Finite A M →
    (∃ n : ℕ, HasProjectiveDimensionLE M n) →
    HasProjectiveDimensionLE M N

/-- `HasFiniteFinitisticDimension` restated as a numerical bound on `projectiveDimension`. -/
@[category API, AMS 16]
theorem hasFiniteFinitisticDimension_iff (A : Type v) [Ring A] :
    HasFiniteFinitisticDimension A ↔
      ∃ N : ℕ, ∀ M : ModuleCat.{v} A,
        Module.Finite A M →
        projectiveDimension M ≠ ⊤ → projectiveDimension M ≤ N := by
  simp only [HasFiniteFinitisticDimension,
    projectiveDimension_ne_top_iff, projectiveDimension_le_iff]

/-- The **finitistic dimension conjecture**: every finite-dimensional algebra over a field has
finite little finitistic dimension. -/
@[category research open, AMS 16]
theorem finitistic_dimension_conjecture (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A] :
    HasFiniteFinitisticDimension A := by
  sorry

end FinitisticDimension
