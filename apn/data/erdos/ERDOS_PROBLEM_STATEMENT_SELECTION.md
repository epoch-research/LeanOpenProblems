# Erdős problem statement selection

Thomas Bloom selected 70 Erdős problem numbers for this benchmark:

> 1, 3, 5, 7, 20, 23, 28, 30, 39, 41, 52, 61, 66, 68, 74, 77, 86, 89, 97, 101,
> 104, 107, 120, 126, 128, 138, 165, 172, 181, 184, 208, 213, 241, 242, 322,
> 324, 364, 371, 376, 406, 431, 478, 500, 508, 548, 564, 571, 583, 595, 647,
> 672, 713, 714, 723, 773, 812, 821, 829, 901, 952, 970, 972, 975, 1003, 1020,
> 1057, 1083, 1159, 1206, 1207

Five of them are not in the benchmark: 1207, which Bloom dropped, and 77, 165,
500 and 901, whose main questions are estimate-type ("determine the order of
magnitude"). The remaining 65 are this dataset.

This note records which statement represents each problem; the
machine-readable selection is `subsets/bloom_selection.json`.

- The 30 modules with a single research statement: use the statement.
- The 30 modules with variants (`erdos_N.variants.*`): use the default
  (non-variant) statement.
- The 4 modules with parts use Thomas Bloom's explicit picks (2026-08-26):
  `erdos_208.parts.i`, `erdos_812.parts.i` and `erdos_1206.parts.i`; 713
  stays split, both `erdos_713.parts.i` and `erdos_713.parts.ii`.
- Problem 508 (Hadwiger–Nelson): the module's one open statement,
  `HadwigerNelsonProblem`, is value-typed (`χ(ℝ²) = answer(sorry)`) and ships
  as an excluded manifest row. In its place the selection carries three derived
  prove-or-disprove samples, `χ(ℝ²) = 5`, `= 6`, and `= 7` (the value is known
  to lie in {5, 6, 7}) -- see the Hadwiger–Nelson special case in
  `scripts/erdos_isolation.py`.

That is 68 statements over 65 problems.

## Change in pin
### Recorded resolutions

The FC pin for the results in [Adamczewski and Bloom](https://arxiv.org/pdf/2609.25050)
was `488aade2` (2026-08-22). The pin was later moved to `f5f23b44` (2026-09-18), 
which postdates the 5 resolutions reported in [Adamczewski and Bloom](https://arxiv.org/pdf/2609.25050).
FC therefore recorded these 5 statements as solved in `f5f23b44`.
They ship like the rest, with the recorded verdict un-filled and the
verdict prose stripped. 

However, there is a special case for Erdős 1, where FC negated the
statement itself (which is a hint that someone disproved it since it's a famous problem),
we ship it with the negation removed (special case in `scripts/erdos_isolation.py`) 

### Statement changes

When the pin was moved, two selected statements changed in substance:

- 41: `NtupleCondition` now counts summands with multiplicity
  (formal-conjectures#5241); the previous `Finset` version could not express
  repeated summands such as `1 + 1 + 3 = 1 + 2 + 2`.
- 564: the constant `c` is now real (#5790); previously it elaborated as a
  natural number, making the statement false by the known upper bound
  `R_3(n) < 2^{2^n}`.

No model had ever resolved either problem under the old formulation.