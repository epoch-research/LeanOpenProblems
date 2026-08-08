# The Erdős dataset

One row per research-category statement in `FormalConjectures/ErdosProblems`
at the pinned FC commit, as listed in `samples.jsonl` -- the manifest is the
universe census, computed from `Sources/` by
`scripts/generate_erdos_isolated.py`: every `theorem`/`lemma` declaration
carrying a `@[category research open]` or `@[category research solved]`
attribute is a member, resolution status notwithstanding. Two member kinds
ship as `excluded` rows with the reason inline: value-typed `answer(sorry)`
statements (a `sorryAx` in the elaborated type; unscoreable by SafeVerify) and
statements whose complete formal proof is in the source file itself (not an
open task, and the spec would leak the proof). Each row records its
erdosproblems.com problem number (`erdos_number`, the source file's stem) and,
for tooling only, `category_at_pin` and `answer_form` -- `apn/dataset.py`
deliberately keeps those two out of sample metadata, since they encode the
recorded verdict.

Canonicalization of the shipped `Isolated/` specs (one per kept row; sibling
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
provenance channel) and the resolution prose recorded on the
`tsoukalas_attempted` members, assembled from the generation census plus an
agentic audit of every member against its source. Members *outside* that
subset -- mostly `research solved` statements added upstream after the paper
-- may still carry resolution prose in their doc comments (attribution of the
known result, occasionally an explicit answer or a pointer to a published
solution). A stronger universe-wide cleanup is deferred; treat full-universe
runs accordingly.

Subsets (`subsets/`): `tsoukalas_attempted.json` -- the Tsoukalas paper's
canonical 350-statement attempted set (arXiv 2605.22763; derivation and
upstream hash in its `description`). Bare `apn_erdos` runs the full universe.

Third-party material: `Sources/` (vendored Formal Conjectures files,
Apache-2.0) and `metadata/` (data *about* the problems: erdosproblems.com
scrapes and related material) each carry a README with their exact
provenance.
