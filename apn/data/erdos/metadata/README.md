# Metadata: data *about* the problems

Analysis-side material keyed by the erdosproblems.com problem number (the
manifest's `erdos_number`, the `<n>` in `Erdos<n>.erdos_<n>` sample ids).
Nothing here is read at runtime, and none of it reaches `Sample.metadata` --
`apn/dataset.py` builds sample metadata from an explicit whitelist. In
particular the scraped rows record each problem's open/solved status, which
must never flow to the agent.

`ERDOS_PROBLEM_STATEMENT_SELECTION.md` is the dataset's provenance document:
Thomas Bloom's statement selection (the review behind `Sources/` membership
and the `bloom_selection` subset; see `../NOTICE.md`). Exception to the
number-keyed rule above; `scripts/erdos_statement_certificate.py` parses its
table.

## `snapshots/` — captures of external sources (unreproducible; treat as read-only evidence)

Scraped from erdosproblems.com (© Thomas Bloom and the site's contributors;
the site publishes no explicit license) on 2026-07-30 by
`scripts/fetch_erdosproblems_data.py`; point-in-time snapshots of a living
site, which is why they are vendored. The fetch script validates every parsed
count against the site's self-reported totals.

- `erdosproblems_problems.jsonl` -- one row per problem (status, prize,
  statement, source citations, tags), keyed by `number`.
- `erdosproblems_lists.jsonl` -- the site's catalog of the 147 problem-list
  papers Erdős wrote. A problem's membership in any list-paper is the join
  `sources[].code` × this catalog, not a fact baked into the rows.
- `booklet_1999_crosswalk.json`, `bloom_top10.json` -- Thomas Bloom's
  forum/blog posts.
- `green_open_problems.json` -- link annotations extracted from Ben Green's
  *100 Open Problems* PDF, © Ben Green.

## `derived/` — tables we computed

None yet; curated-list joins (e.g. the prestige index) belong here when they
graduate from ad-hoc analysis.
