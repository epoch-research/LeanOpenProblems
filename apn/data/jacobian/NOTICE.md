# The Jacobian-conjecture dataset

Upstream source: formal-conjectures' `FormalConjectures/Wikipedia/JacobianConjecture.lean` (Apache 2.0) at the pinned commit in `fc_commit`. FC records the conjecture as `research solved` (false) at that pin, and its file carries the counterexample maps and their proofs, so it is not vendored verbatim.

`Sources/JacobianConjecture.lean` instead restates the conjecture with the resolution withheld:

- `JacobianConjectureProp` is FC's definition verbatim (over the `MvPolynomial.RegularFunction` API in FC's proving library, which the agent image ships).
- The target `jacobian_conjecture` specializes it to `ℂ` and `Fin n` for every `n : ℕ`, matching the task statement in the prompt (`apn.prompts.jacobian_prompt`), rather than FC's `answer(False) ↔ ...` over an arbitrary nontrivial commutative ring.
- The counterexample maps, their Jacobian and non-injectivity lemmas, FC's proof, and the two-variable variant are dropped. FC's `sanity_check_condition_1` is kept as a `@[category API]` check that the unit-determinant condition means a nonzero constant (cut from the isolated spec, like every non-target theorem). The module doc is rewritten so that it does not mention the resolution.

The manifest's `category` is `research solved`, as FC records it; like in the other datasets it never reaches the agent.

`samples.jsonl` has the one research-category statement. There are no predefined subsets.
