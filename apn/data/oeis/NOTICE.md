# OEIS dataset (vendored)

These are the autoformalized OEIS conjectures attempted with AlphaProof Nexus in
Tsoukalas et al., *Advancing Mathematics Research with AI-Driven Formal Proof
Search* (arXiv:2605.22763v1) — the "OEIS Problems" evaluation (44/492 solved).

- `Auto/*.lean` — 484 Lean files / 492 conjectures (one or more per file).
  **Upstream source of truth.** Each imports `FormalConjectures.Util.ProblemImports`,
  defines the integer sequence, states small-term test lemmas (a misformalization
  guard), and states one or more conjectures as `theorem … := by sorry`.
- `THEOREM_MAPPING.txt` — maps each conjecture theorem name to its file(s).
- `Isolated/<conjecture>.lean` — **derived, one per conjecture (492).** Each is
  the per-conjecture *challenge file*: the source file's definitions plus the
  single target conjecture, with every other `theorem`/`lemma` removed (sibling
  conjectures *and* test lemmas). A `theorem`/`lemma` is kept only if a retained
  definition depends on it (e.g. a nonemptiness proof passed to `Finset.min'`),
  so the spec still compiles; the conjecture to settle is always the lone target.
  This restores per-conjecture scoring — the
  benchmark unit is the conjecture, but SafeVerify requires every theorem in the
  target file to be discharged, so a sample about conjecture *T* was previously
  gated on *all* conjectures in its file. Reproduces the shape of the paper's
  published challenge files (`reference_sources/.../APNOutputs/OEIS/*`); the
  sequence `def` is pinned by value in SafeVerify, so the test lemmas were never
  the anti-cheat guard and are safely dropped. `apn/dataset.py` reads these.

### Regenerating `Isolated/`

`Isolated/` is generated from `Auto/` + `THEOREM_MAPPING.txt` by
`scripts/generate_isolated.py`, which drives the Lean declaration-range extractor
in `apn/lean/extract_ranges/` (cuts are made with Lean's own parser/elaborator,
not text matching). There is no local Lean toolchain, so it runs in the Lean
Docker image (`apn/lean/Dockerfile` `generate` stage). The script only *writes*
the files; validation lives in the tests.

The committed `Isolated/` files are the trusted artifact (as `Auto/` is) and are
guarded on two levels. `tests/test_oeis.py` has always-on pure-Python structural
invariants (every conjecture has a spec; it imports the FC library and declares
its target; one theorem per spec bar the documented dependency-lemma case).
`tests/test_oeis_isolation.py` is the authoritative gate: it brings up a Lean
container and confirms every isolated file elaborates cleanly under the scorer's
exact `lake env lean -o`, contains exactly the target theorem (+ its
definitional-dependency lemmas) with its statement byte-for-byte preserved, and
-- for the paper's solved problems -- matches the published challenge file's
statement. (Shared cut logic and Docker plumbing live in
`scripts/oeis_isolation.py`, imported by both the script and the tests.)

## Source and pinning

Vendored verbatim from the Formal Conjectures repository, `auto_oeis` branch, at
commit `67338a157bbb8d87e9a349d662f82a868bda6327`:

  https://github.com/google-deepmind/formal-conjectures/tree/auto_oeis/FormalConjectures/OEIS/Auto

## Licensing

Copyright 2026 The Formal Conjectures Authors. Licensed under the Apache License,
Version 2.0. The underlying sequence data originates from the On-Line Encyclopedia
of Integer Sequences (OEIS, https://oeis.org), released under CC BY-SA 4.0. The
original OEIS sequence URL is recorded inside each file.
