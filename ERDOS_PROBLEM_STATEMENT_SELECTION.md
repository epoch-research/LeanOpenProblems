# Erdős problem statement selection

## Background

Thomas Bloom selected 70 Erdős problem numbers for this review. 48 of those problems have formalized statements in FC and 22 do not. Of the 48 formalized problems, 15 have one substantive research statement and 33 have more than one. This decision concerns statement selection in those 33 multi-statement modules.

This review was performed against FC commit `56534c04092446f2fd549d2865f2496924812da8`.

30 modules have a default theorem named `erdos_N` and place related results or alternative formulations under `erdos_N.variants`. Two modules instead split the source problem into statements under `erdos_N.parts`.

The variants serve several purposes. They include stronger conjectures, weaker or solved bounds, special cases, generalisations, equivalent formulations, and related questions. Consequently, there is not always a single implication ordering among all statements in a module. A review of the 33 modules found a clear strongest or hardest endpoint in 23 cases, a natural but qualified candidate in five cases, and no unique candidate in five cases.

## Decision

Use the following rule when selecting one representative statement from each module:

1. The selected declaration must have the `research open` category.
2. If a module has a default statement and variants, use the default non-variant statement. This rule applies even when a variant is known or intended to be stronger.
3. If the source problem is divided into parts, use the stronger part:
   - For Problem 208, use `erdos_208.parts.ii`.
   - For Problem 812, use `erdos_812.parts.i`.
4. Problem 508 predates the usual naming scheme. Use `HadwigerNelsonProblem`, its main exact-value question.

## Selected statements

| Problem | Selected statement | Reason |
|---:|---|---|
| 1 | `erdos_1` | Default statement; variants present |
| 3 | `erdos_3` | Single statement |
| 5 | `erdos_5` | Default statement; variants present |
| 7 | `erdos_7` | Single statement |
| 20 | `erdos_20` | Default statement; variants present |
| 23 | `erdos_23` | Default statement; variants present |
| 28 | `erdos_28` | Single statement |
| 30 | `erdos_30` | Single statement |
| 39 | `erdos_39` | Single statement |
| 41 | `erdos_41` | Default statement; variants present |
| 52 | `erdos_52` | Single statement |
| 61 | `erdos_61` | Default statement; variants present |
| 66 | `erdos_66` | Single statement |
| 68 | `erdos_68` | Single statement |
| 74 | `erdos_74` | Default statement; variants present |
| 89 | `erdos_89` | Default statement; variants present |
| 97 | `erdos_97` | Default statement; variants present |
| 101 | `erdos_101` | Single statement |
| 107 | `erdos_107` | Default statement; variants present |
| 120 | `erdos_120` | Default statement; variants present |
| 126 | `erdos_126` | Default statement; variants present |
| 128 | `erdos_128` | Single statement |
| 138 | `erdos_138` | Default statement; variants present |
| 172 | `erdos_172` | Single statement |
| 184 | `erdos_184` | Default statement; variants present |
| 208 | `erdos_208.parts.ii` | Stronger part |
| 213 | `erdos_213` | Default statement; variants present |
| 241 | `erdos_241` | Default statement; variants present |
| 242 | `erdos_242` | Default statement; variants present |
| 324 | `erdos_324` | Default statement; variants present |
| 364 | `erdos_364` | Default statement; variants present |
| 371 | `erdos_371` | Single statement |
| 376 | `erdos_376` | Default statement; variants present |
| 406 | `erdos_406` | Default statement; variants present |
| 508 | `HadwigerNelsonProblem` | Main statement; nonstandard naming |
| 564 | `erdos_564` | Single statement |
| 595 | `erdos_595` | Default statement; variants present |
| 647 | `erdos_647` | Default statement; variants present |
| 672 | `erdos_672` | Default statement; variants present |
| 723 | `erdos_723` | Default statement; variants present |
| 812 | `erdos_812.parts.i` | Stronger part |
| 821 | `erdos_821` | Default statement; variants present |
| 829 | `erdos_829` | Default statement; variants present |
| 952 | `erdos_952` | Single statement |
| 972 | `erdos_972` | Single statement |
| 975 | `erdos_975` | Default statement; variants present |
| 1003 | `erdos_1003` | Default statement; variants present |
| 1057 | `erdos_1057` | Default statement; variants present |

## Open-category check

All 48 selected Lean declarations have the `research open` category.

## Why the selected parts are stronger

The comparisons between the parts are mathematical relationships between their statements. They are not currently recorded as Lean implication theorems.

For Problem 208, Part II conjectures the squarefree-number gap bound

\[
s_{n+1}-s_n \leq (1+o(1))\frac{\pi^2}{6}
  \frac{\log s_n}{\log\log s_n}.
\]

This implies the logarithmic-order variant and hence the subpolynomial bound in Part I:

\[
\text{Part II} \Longrightarrow O(\log s_n) \Longrightarrow \text{Part I}.
\]

For Problem 812, Part I conjectures a fixed multiplicative gap between consecutive diagonal Ramsey numbers:

\[
R(n+1)/R(n) \geq 1+c
\]

eventually, for some `c > 0`. It gives `R(n+1) - R(n) >= c R(n)`. The standard exponential growth of `R(n)` then implies the quadratic additive-gap bound in Part II:

\[
\text{Part I} \Longrightarrow \text{Part II}.
\]
