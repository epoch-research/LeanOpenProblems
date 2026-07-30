# Third-party data

Two sets of files here come from external sources; everything else in this
directory is produced by this repository.

**`Auto/`, `THEOREM_MAPPING.json`** — vendored from the Formal Conjectures
repository (`auto_oeis` branch, commit `67338a157bbb8d87e9a349d662f82a868bda6327`):
https://github.com/google-deepmind/formal-conjectures/tree/auto_oeis/FormalConjectures/OEIS/Auto
© 2026 The Formal Conjectures Authors, Apache License 2.0. The mapping is the
upstream file transcribed to JSON; its `_meta.upstream` records the repository,
branch and commit it came from. (`Isolated/` is derived from these in-repo.)

**`raw/oeis_records.jsonl`, `raw/oeis_history.jsonl`** — fetched from the OEIS
(https://oeis.org), © The OEIS Foundation Inc., subject to the OEIS license
(https://oeis.org/LICENSE).

The underlying integer-sequence data in both originates from the OEIS.
