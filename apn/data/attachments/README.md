# Attachments

Supplementary material a run can ship into the agent's sandbox. Each
subdirectory here is one attachment; a task's `attachments: <name>` argument
copies `apn/data/attachments/<name>/` verbatim to `/workspace/attachments` in
the agent's sandbox (Inspect `Sample.files`, expanded recursively; the
comparator sandbox never receives it) and adds a paragraph to the prompt
pointing the agent at it (`apn.prompts.attachments_prompt`). Without the
argument nothing is shipped and the prompt is unchanged, so the default run
condition is untouched.

Everything under an attachment directory reaches the agent, so keep provenance
notes in this file, not inside the attachment.

## `n_conjecture_strong`

A copy of `archive/` from the `n-conjecture-strong` repository
(`/Users/t/repos/math/n-conjecture-strong`, copied 2026-09-05), minus its two
`info.json` files (per-sample eval-log metadata: model, cost, verifier output),
which are not part of the material. The archive holds the two original
AI-written submissions refuting the strong n-conjecture's `n = 4` case (the
`NConjecture.n_conjecture.variants.strong` and `.strong_quality` samples of
the `wikipedia` dataset, 2026-09-04/05), with their challenge files,
analysis notes and final messages. Its `README.md` refers to a
`../StrongFour/` directory that is not included. Intended for the
`ABC.abc` target (`configs/abc-n-conjecture-archive-vega.yaml`).
