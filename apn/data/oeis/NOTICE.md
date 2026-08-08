# The OEIS dataset

One sample per autoformalized OEIS conjecture (492), as listed in
`samples.jsonl` -- the manifest is the membership source of truth, one row per
conjecture with its vendored source file and OEIS A-number.

The manifest transcribes upstream's theorem-to-file mapping,
`FormalConjectures/OEIS/Auto/THEOREM_MAPPING.txt` at the same pin as
`Sources/` (sha256
`386c0c6e7abf782077b0eee5bf59ddb0caf67acf11db96502b8b2e11bd64c2fe`); the file
itself is not vendored -- it is recoverable from the pinned public commit, and
the transcription was verified against a byte-verbatim copy at conversion
time. A few conjectures (3/492, only 1 a substantive difference) map to more
than one upstream file; the manifest uses the first as `source` and records
the rest in `other_sources` so the solver can warn at run time.

`Isolated/` (one per-conjecture spec per row: the sequence definitions plus
the single target theorem, sibling conjectures and test lemmas cut) is
generated from `Sources/` by `scripts/generate_oeis_isolated.py` and validated
by `tests/test_oeis_isolation.py`.

Third-party material: `Sources/` (vendored Formal Conjectures files,
Apache-2.0) and `raw/` (OEIS snapshots) each carry a README with their exact
provenance. The underlying integer-sequence data throughout originates from
the OEIS (https://oeis.org), © The OEIS Foundation Inc.
