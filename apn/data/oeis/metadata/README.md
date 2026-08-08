# Metadata: data *about* the conjectures

Analysis-side material keyed by `oeis_id` (the sequence A-number). Nothing
here is read at runtime, and none of it reaches `Sample.metadata` --
`apn/dataset.py` builds sample metadata from an explicit whitelist.

## `snapshots/` — captures of external sources (unreproducible; treat as read-only evidence)

Fetched from the OEIS (https://oeis.org) by `scripts/fetch_oeis_data.py`;
© The OEIS Foundation Inc., subject to the OEIS license
(https://oeis.org/LICENSE). Point-in-time snapshots of a living site -- unlike
commit-pinned repositories they cannot be re-fetched as-was, which is why they
are vendored.

- `oeis_records.jsonl` -- the full structured entry per sequence (JSON API).
- `oeis_history.jsonl` -- the per-sequence revision log, parsed from the
  history pages into structured revisions (see the fetch script's docstring).

## `derived/` — tables we computed (regenerable from the scripts)

- `provenance.jsonl` -- where each conjecture's text came from in the OEIS
  (matched comment, first-appearance revision/date, confidence); LLM-assisted
  extraction over the snapshots by `scripts/extract_provenance.py`.
- `citations_openalex.jsonl` -- papers citing each sequence, queried from the
  OpenAlex API by `scripts/find_papers.py`.
- `citations_oeis.jsonl` -- structured bibliography entries extracted from the
  sequence records' own links/references by `scripts/extract_bibliography.py`.
