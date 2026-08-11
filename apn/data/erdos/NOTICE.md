# The Erdős dataset

The Tsoukalas paper's canonical Erdős attempted set (arXiv 2605.22763): one
`samples.jsonl` row per FC ErdosProblems statement the paper's agent
attempted, 350 of the paper's 353 (3 are unresolvable at the pinned FC commit;
the derivation, upstream commit and hash live in
`subsets/tsoukalas_attempted.json`'s `description`). `Sources/` vendors
exactly the 236 files hosting them. Each row records its erdosproblems.com
problem number (`erdos_number`, the source file's stem) and, for tooling only,
`category_at_pin` and `answer_form` -- `apn/dataset.py` deliberately keeps
those two out of sample metadata, since they encode the recorded verdict.

Canonicalization of the shipped `Isolated/` specs (one per row; sibling
theorems and `example` commands cut):

* All `answer(...) ↔` statement forms are rewritten to plain `P` -- recorded
  `True`/`False` verdicts un-filled like the unfilled `answer(sorry)` forms,
  because determining P's truth value is exactly the task and a recorded
  literal is the answer key. The rewrite is certified by re-elaboration
  (`tests/test_erdos_isolation.py`).
* FC's annotations are stripped likewise: every kept declaration's
  `@[category ..., AMS ...]` classification list is dropped whole -- catalogue
  metadata whose `research solved` category and `formal_proof` URL clauses are
  the recorded verdict in human-readable form -- as is the doc-comment prose
  recording resolutions and the module-doc reference lines linking solution
  papers/formalisations (`scripts/erdos_isolation.py:VERDICT_PROSE`, exact
  snippets, each asserted to apply). `tests/test_erdos.py` asserts the markers
  are absent from every shipped sketch.
* A few specs (allowlisted by file in `scripts/erdos_isolation.py`) carry one
  extra sorry'd helper theorem that a kept definition depends on; those
  samples implicitly require proving the helper too.

⚠️ Scope of the verdict-prose strip: the exact-snippet list removes the
DeepMind-prover-agent / AlphaProof resolution prose (the paper's own
provenance channel) and the resolution prose FC recorded on these members
between the paper's attempts and the pin, with three known residuals shipped
as-is for now: `Erdos1141.erdos_1141` and `Erdos318.erdos_318.parts.ii` state
their recorded verdict and link the published solution in their doc comments,
and `Erdos997.erdos_997` keeps the solution paper's module-doc reference line.
Treat results on those three samples accordingly.

Subsets (`subsets/`): `tsoukalas_attempted.json` names the same 350 ids -- the
canonical replication invocation (`subset="tsoukalas_attempted"`); bare
`apn_erdos` runs them all.

`scripts/generate_erdos_isolated.py` is the vendor-time bootstrap that
produced the specs; it censuses *every* research-category statement in
`Sources/`, so re-running it does not reproduce this manifest -- the committed
`samples.jsonl` is curated to the attempted set and is the source of truth.

Third-party material: `Sources/` (vendored Formal Conjectures files,
Apache-2.0) and `metadata/` (data *about* the problems: erdosproblems.com
scrapes and related material) each carry a README with their exact
provenance.
