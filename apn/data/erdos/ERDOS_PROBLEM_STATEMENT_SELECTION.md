# Erdős problem statement selection

Thomas Bloom selected 70 Erdős problem numbers for this benchmark; 48 of them
have formalized statements in FC (reviewed at FC commit
`56534c04092446f2fd549d2865f2496924812da8`). Most of the 48 modules hold either
a single statement or a default statement plus alternatives under
`erdos_N.variants`; two split the problem into statements under
`erdos_N.parts`. The variants mix stronger conjectures, weaker or solved
bounds, special cases, and related questions, with no uniform implication
ordering. This note records which statement represents each problem; the
machine-readable selection is `subsets/bloom_selection.json`.

- Modules with a single statement: use it.
- Modules with variants: use the default (non-variant) statement, even when a
  variant is the mathematically stronger claim.
- The two modules with parts use Thomas Bloom's explicit picks (2026-08-26):
  `erdos_208.parts.i` and `erdos_812.parts.i`.
- Problem 508 (Hadwiger–Nelson): the module's one open statement,
  `HadwigerNelsonProblem`, is value-typed (`χ(ℝ²) = answer(sorry)`) and ships
  as an excluded manifest row. In its place the selection carries three derived
  prove-or-disprove samples, `χ(ℝ²) = 5`, `= 6`, and `= 7` (the value is known
  to lie in {5, 6, 7}) -- see the Hadwiger–Nelson special case in
  `scripts/erdos_isolation.py`.

Every selected statement had the `research open` category at the pin
(asserted by `tests/test_erdos.py`).
