# Original evaluation artifacts

These are the original submissions and assessment notes, preserved unchanged
when the repository was consolidated. They are excluded from the active Lean
build. Both original `Spec.lean` files were reproduced with Lean 4.27.0 before
consolidation; their warnings concern the retained challenge placeholders.

- `first-formulation/`: degree-20 construction; quality lower bound `20/19`.
- `quality-formulation/`: degree-1080 construction; quality lower bound `180/179`.

The canonical result is now the single degree-nine construction in
`../StrongFour/`, proving a lower bound of `9/8` for four-tuples only.

The historical notes contain overstatements that should not be carried into
new work: the first estimate is a lower bound, not a proof of convergence to
`20/19`; the correct comparison is `Q_U ≤ Q_R ≤ Q_B`; and neither submission
refutes Vojta's conjecture with an exceptional algebraic set. The original
novelty assessments are not part of the verified result.
