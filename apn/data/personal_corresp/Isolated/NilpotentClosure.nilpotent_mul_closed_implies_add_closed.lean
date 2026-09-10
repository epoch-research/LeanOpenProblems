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

The question is due to Janez Šter (University of Ljubljana): it is Question 1 of [Št16], where it
is phrased through Köthe's conjecture. Theorem 2.1 there shows that the nilpotent elements of a
ring are additively closed if and only if they are multiplicatively closed and the ring satisfies
Köthe's conjecture (every nil left ideal is contained in a nil two-sided ideal), and Question 1
asks whether a ring whose nilpotent elements are multiplicatively closed must satisfy Köthe's
conjecture -- which, by Theorem 2.1, is equivalent to the statement below. Šter notes that a
counterexample would in particular settle Köthe's conjecture in the negative. The rings in [Št16]
need not be unital, but the unital statement below is equivalent: the nilpotent elements of the
Dorroh extension `ℤ ⊕ S` of a ring `S` are exactly the `(0, s)` with `s` nilpotent in `S`, so
adjoining a unit changes neither closure property.

The Lean statement was contributed by Pace Nielsen (Brigham Young University), who sent it to
Tom Adamczewski in September 2026 and offered it for contribution to formal-conjectures.

*References:*
- [Št16] Šter, J., *Rings in which nilpotents form a subring*, Carpathian J. Math. 32 (2016),
  No. 2, 251--258, [doi:10.37193/CJM.2016.02.13](https://doi.org/10.37193/CJM.2016.02.13),
  [arXiv:1510.07523](https://arxiv.org/abs/1510.07523).
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
