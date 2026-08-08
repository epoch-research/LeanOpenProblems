# Upstream snapshots

`oeis_records.jsonl` and `oeis_history.jsonl` were fetched from the OEIS
(https://oeis.org) by `scripts/fetch_oeis_data.py`; © The OEIS Foundation
Inc., subject to the OEIS license (https://oeis.org/LICENSE). Rows are keyed
by `oeis_id` (the sequence A-number).

These are point-in-time snapshots of a living site -- unlike commit-pinned
repositories they cannot be re-fetched as-was, which is why they are vendored.
