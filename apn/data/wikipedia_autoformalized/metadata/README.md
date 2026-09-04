# Metadata: the run these sources came from

Both files are written by `scripts/vendor_wikipedia_autoformalized.py` from
the run's Inspect log and artifact sidecars. Nothing here is read at runtime,
and none of it reaches `Sample.metadata` -- `apn/dataset.py` builds sample
metadata from an explicit whitelist. The generator
(`scripts/generate_wikipedia_autoformalized_isolated.py`) reads
`run_samples.jsonl` at vendor time to attach each source's run facts to its
manifest rows and to derive the `adjudicated_open` subset.

- `run.json` -- the run's identity (Hawk eval-set id, log file, Inspect run
  id, task args: the generator/adjudicator/probe models), the FC pin, the
  selection rule and its counts.
- `run_samples.jsonl` -- one row per sample of the run (one per Wikipedia
  list entry the pipeline attempted), keyed by `problem_id` (the pipeline's
  `wp-<slug>` id). Per row: the entry's `title`/`reference_url`, the sample
  `uuid` (its `artifacts/<uuid>/` directory), the file's `lean_namespace`,
  the adjudicator's `decision` and `kept_slots` (the sub-questions it accepted
  as faithfully stated; `<lean_namespace>.<slot>` is the manifest id), the
  headline `formalized` score (C/P/N/I, null when the sample errored),
  `adjudicator_confidence`, `slots_kept`/`slots_total`, the settle probe's
  `probe_claim`/`probe_verified`, and the vendoring outcome: `selected` (the
  C/P + confidence rule), `source` (the vendored `Sources/` file, null when
  not vendored) and `not_vendored_reason` for a selected file that could not
  be vendored.
