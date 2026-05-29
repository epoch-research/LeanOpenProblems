# OEIS dataset (vendored)

These are the autoformalized OEIS conjectures attempted with AlphaProof Nexus in
Tsoukalas et al., *Advancing Mathematics Research with AI-Driven Formal Proof
Search* (arXiv:2605.22763v1) — the "OEIS Problems" evaluation (44/492 solved).

- `Auto/*.lean` — 484 Lean files / 492 conjectures (one or more per file).
- `THEOREM_MAPPING.txt` — maps each conjecture theorem name to its file(s).

Each file imports `FormalConjectures.Util.ProblemImports`, defines the integer
sequence, states small-term **test lemmas** (a misformalization guard), and
states the conjecture as `theorem … := by sorry`.

## Source and pinning

Vendored verbatim from the Formal Conjectures repository, `auto_oeis` branch, at
commit `67338a157bbb8d87e9a349d662f82a868bda6327`:

  https://github.com/google-deepmind/formal-conjectures/tree/auto_oeis/FormalConjectures/OEIS/Auto

## Licensing

Copyright 2026 The Formal Conjectures Authors. Licensed under the Apache License,
Version 2.0. The underlying sequence data originates from the On-Line Encyclopedia
of Integer Sequences (OEIS, https://oeis.org), released under CC BY-SA 4.0. The
original OEIS sequence URL is recorded inside each file.
