import FormalConjecturesUtil

/-!
# The Nakayama conjecture

The **dominant dimension** of a finite-dimensional algebra `A` is the number of leading terms
of a minimal injective resolution of the regular module `A` that are projective. The
**Nakayama conjecture** (1958) asserts that a finite-dimensional algebra of infinite dominant
dimension -- every term of a minimal injective resolution of the regular module is projective --
is self-injective. It is one of the central homological conjectures in the representation
theory of finite-dimensional algebras; the finitistic dimension conjecture implies it.

*References:*
- [Na58] Nakayama, T., *On algebras with complete homology*, Abh. Math. Sem. Univ. Hamburg
  22 (1958), 300--307.
- [Ya96] Yamagata, K., *Frobenius algebras*, in: Handbook of algebra, Vol. 1, North-Holland
  (1996), 841--887.
- [Xi] Xi, C., *Some homological conjectures for finite dimensional algebras*, Oberwolfach
  problem session (2005), [pdf](https://www.math.uni-bielefeld.de/~sek/mfo2005/xi-web.pdf).
-/

universe u v

open CategoryTheory

namespace Nakayama

/-- An injective resolution `I` of `M` is **minimal** if the kernel of every differential is an
essential submodule of its term: for each `n`, every submodule of `I n` meeting
`ker (I n → I (n + 1))` trivially is zero. (For `n = 0` this kernel is the image of `M`.) -/
def IsMinimalInjectiveResolution
    {A : Type v} [Ring A] {M : ModuleCat.{v} A}
    (I : InjectiveResolution M) : Prop :=
  ∀ n : ℕ, ∀ S : Submodule A (I.cocomplex.X n),
    S ⊓ LinearMap.ker (I.cocomplex.d n (n + 1)).hom = ⊥ → S = ⊥

/-- `A` has **infinite dominant dimension**: every term of a minimal injective resolution of the
regular left module `A` is projective. -/
def HasInfiniteDominantDimension (A : Type v) [Ring A] : Prop :=
  ∃ I : InjectiveResolution (ModuleCat.of A A),
    IsMinimalInjectiveResolution I ∧
      ∀ n : ℕ, Projective (I.cocomplex.X n)

/-- The **Nakayama conjecture**: a finite-dimensional algebra over a field of infinite dominant
dimension is self-injective. -/
theorem nakayama_conjecture (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A]
    (h : HasInfiniteDominantDimension A) : Module.Injective A A := by
  sorry

end Nakayama

theorem Nakayama.nakayama_conjecture.disproof : ¬ (type_of% @Nakayama.nakayama_conjecture) := sorry
