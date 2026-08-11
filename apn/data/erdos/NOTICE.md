# The Erdős dataset

Upstream source: the Tsoukalas paper's attempted list (arXiv 2605.22763;
upstream commit and file hash in `subsets/tsoukalas_attempted.json`'s
`description`). 350 of the paper's 353 statements resolve at the pinned FC
commit (`fc_commit`) and are in `samples.jsonl`; the subset names the same 350 ids, and
bare `apn_erdos` runs them all. `scripts/generate_erdos_isolated.py`
censuses every research-category statement in `Sources/`, so the committed
manifest is curated down to the attempted set.
