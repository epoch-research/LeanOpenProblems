import FormalConjecturesUtil

/-!
# Nilpotent elements closed under multiplication but not under addition

In a commutative ring the nilpotent elements form an ideal (the nilradical), so they are closed
under both addition and multiplication. In a noncommutative ring they need be closed under
neither: in the `2 × 2` matrices over a field the matrix units `e₁₂` and `e₂₁` are nilpotent,
but their sum squares to the identity and their product `e₁₁` is a nonzero idempotent. The two
closure properties can nevertheless be studied separately, and the following question asks
whether one of them can hold without the other:

> Does there exist a ring whose set of nilpotent elements is closed under multiplication but
> not under addition?

The statement below is the negative answer: multiplicative closure of the nilpotent elements
forces additive closure. A counterexample ring disproves it.

The question was asked by Janez Šter (University of Ljubljana). The Lean statement was
contributed by Pace Nielsen (Brigham Young University), who sent it to Tom Adamczewski in
September 2026 and offered it for contribution to formal-conjectures.

*References:*
- [Št16] Šter, J., *Rings in which nilpotents form a subring*, Carpathian J. Math. 32 (2016),
  251--258, [arXiv:1510.07523](https://arxiv.org/abs/1510.07523).
-/

namespace NilpotentClosure

/-- If the nilpotent elements of a ring are closed under multiplication, they are closed under
addition. Equivalently: there is no ring whose set of nilpotent elements is closed under
multiplication but not under addition. -/
theorem nilpotent_mul_closed_implies_add_closed (R : Type*) [Ring R]
    (h : ∀ x y : R, IsNilpotent x → IsNilpotent y → IsNilpotent (x * y)) :
    ∀ x y : R, IsNilpotent x → IsNilpotent y → IsNilpotent (x + y) := by
  sorry

end NilpotentClosure

theorem NilpotentClosure.nilpotent_mul_closed_implies_add_closed.disproof : ¬ (type_of% @NilpotentClosure.nilpotent_mul_closed_implies_add_closed) := sorry
