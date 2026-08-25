# The Erdős dataset

Upstream source: Thomas Bloom's Erdős problem statement selection, vendored at
`metadata/ERDOS_PROBLEM_STATEMENT_SELECTION.md`. Bloom chose 70 problem
numbers for review; 48 of them have formalized statements in
google-deepmind/formal-conjectures, and the review -- performed against FC
commit `56534c04092446f2fd549d2865f2496924812da8` -- selected one
representative statement per problem (the default `erdos_N` statement, the
stronger part for the two `parts` modules, `HadwigerNelsonProblem` for 508).

`Sources/` vendors those 48 files at the pinned FC commit (`fc_commit`,
`488aade228ec37880b8fec178c173c07d279bb53`) -- not the review commit, which
sits on Lean v4.33.1 while this harness's toolchain track (PyPantograph repl,
vendored safeverify/extract_ranges) is v4.27.0. The pin is the last FC commit
on v4.27.0, 21 commits before the review commit.
`scripts/erdos_statement_certificate.py` is the auditable link between the
two: it certifies every selected declaration command (attribute list +
statement + `sorry` body) byte-identical between the pin and the review
commit. Vendor-time run: 48/48 certified; 8 files (5, 20, 23, 74, 89, 107,
184, 595) carry residual diffs that never touch a selected statement --
variant/test-lemma proofs, a `formal_proof` URL attribute, and
`open scoped Classical in` on variants.

`scripts/generate_erdos_isolated.py` censuses every research-category
statement in `Sources/`, so `samples.jsonl` is the universe of the 48 files'
research statements -- the selected ids plus their research-category variants
(value-typed and proved-in-file members as excluded rows). The 47 scoreable
selected statements form `subsets/bloom_selection.json`, the default subset of
`apn_erdos`; the 48th, problem 508's `HadwigerNelsonProblem`, is value-typed
(`χ(ℝ²) = answer(sorry)`) and ships as an excluded row.

The previous incarnation of this dataset -- the Tsoukalas paper's 350
attempted statements at FC `67338a15` -- lives in git history (its `Sources/`,
`Isolated/`, manifest, and `subsets/tsoukalas_attempted.json`).
