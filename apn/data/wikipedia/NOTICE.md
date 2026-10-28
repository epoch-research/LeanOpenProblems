# The Wikipedia dataset

Upstream source: every `FormalConjectures/Wikipedia` file with at least one `@[category research open ...]` statement, at the FC commit pinned in `fc_commit` (FC main as of 2026-10-28). `Sources/` holds those files verbatim.

`samples.jsonl` lists every `research open` statement in those files: 285 rows. 12 are `excluded` because they are value-typed, leaving 273 runnable samples. At this pin FC writes "determine the value" problems as `def X.answer : T := sorry` plus a theorem equating the quantity with `X.answer`, which can be neither proved nor disproved as stated. (No `answer(...)` placeholders remain at this pin.) Statements with a complete in-file proof would also be excluded; there are none. There are no predefined subsets.

The pin postdates upstream's switch to the Lean module system. The isolated specs are cut from de-modulized sources (no `module` header, `import` for `public import`, no `@[expose] public section`), because the scorer compiles specs as ordinary Lean files. Three files import sibling FC problem files that the sandbox images don't build. `SIBLING_IMPORT_PATCHES` in `scripts/wikipedia_isolation.py` drops those imports, and it inlines the one statement that used a sibling declaration (`AmicableNumbers.infinitely_many_amicable`, stated upstream as `type_of% Erdos830.erdos_830.parts.i`).
