# Upstream snapshots

Scraped from erdosproblems.com (© Thomas Bloom and the site's contributors;
the site publishes no explicit license) on 2026-07-30 by
`scripts/fetch_erdosproblems_data.py`:

- `erdosproblems_problems.jsonl` -- one row per problem (status, prize,
  statement, source citations, tags), keyed by `number`, the erdosproblems.com
  problem number -- the `<n>` in `Erdos<n>.erdos_<n>` sample ids and the
  manifest's `erdos_number` field.
- `erdosproblems_lists.jsonl` -- the site's catalog of the 147 problem-list
  papers Erdős wrote. A problem's membership in any list-paper is the join
  `sources[].code` × this catalog, not a fact baked into the rows.
- `booklet_1999_crosswalk.json`, `bloom_top10.json` -- Thomas Bloom's
  forum/blog posts.
- `green_open_problems.json` -- link annotations extracted from Ben Green's
  *100 Open Problems* PDF, © Ben Green.

The fetch script validates every parsed count against the site's self-reported
totals. These are point-in-time snapshots of a living site -- unlike
commit-pinned repositories they cannot be re-fetched as-was, which is why they
are vendored.
