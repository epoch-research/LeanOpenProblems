# The Erdős-autoformalized dataset

Upstream source: the 18 `.lean` files in the root of `epoch-research/autoformalization` `results/2026-08-25-erdos-target-run/`, vendored verbatim into `Sources/`. That directory's `raw/README.md` documents how they were produced.

This is our own autoformalization output, not upstream formal-conjectures (the problems were chosen because they were absent from FC at the run's pin). `fc_commit` is the FC commit the run compiled against; it plays only its sandbox-image/proving-library role here.

`samples.jsonl` lists every research-category statement in those files (20 — problems 713 and 1206 are two-part).
