# Erdős problem statement selection

Thomas Bloom selected 70 Erdős problem numbers for this benchmark:

> 1, 3, 5, 7, 20, 23, 28, 30, 39, 41, 52, 61, 66, 68, 74, 77, 86, 89, 97, 101,
> 104, 107, 120, 126, 128, 138, 165, 172, 181, 184, 208, 213, 241, 242, 322,
> 324, 364, 371, 376, 406, 431, 478, 500, 508, 548, 564, 571, 583, 595, 647,
> 672, 713, 714, 723, 773, 812, 821, 829, 901, 952, 970, 972, 975, 1003, 1020,
> 1057, 1083, 1159, 1206, 1207

48 of them have formalized statements in FC (reviewed at FC commit
`56534c04092446f2fd549d2865f2496924812da8`); those are this dataset. Of the
other 22, 18 were formalized by our own autoformalization pipeline (the
`erdos_autoformalized` dataset next door), and the remaining 4 -- 77, 165,
500, 901, whose main questions are estimate-type ("determine the order of
magnitude") -- are not in the benchmark.

Of the 48 modules, 15 hold a single research statement, 30 hold a default
statement plus alternatives under `erdos_N.variants`, two (208 and 812) split
the problem into statements under `erdos_N.parts`, and one (508, which
predates the usual naming scheme) holds `HadwigerNelsonProblem` plus solved
bounds. This note records which statement represents each problem; the
machine-readable selection is `subsets/bloom_selection.json`.

- The 15 single-statement modules: use the statement.
- The 30 modules with variants: use the default (non-variant) statement.
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
