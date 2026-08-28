<!-- Vendored from https://github.com/nomeata/loogle (blurb.md and README.md) at rev 9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0 -->
# Loogle

Loogle searches Lean and Mathlib definitions and theorems.

## Query language

Loogle finds definitions and lemmas in various ways:

1. By constant:
   `Real.sin`
   finds all lemmas whose statement somehow mentions the sine function.

2. By lemma name substring:
   `"differ"`
   finds all lemmas that have `"differ"` somewhere in their lemma _name_.

3. By subexpression:
   `_ * (_ ^ _)`
   finds all lemmas whose statements somewhere include a product where the second argument is
   raised to some power.

   The pattern can also be non-linear, as in
   `Real.sqrt ?a * Real.sqrt ?a`

   If the pattern has parameters, they are matched in any order. Both of these will find `List.map`:
   `(?a -> ?b) -> List ?a -> List ?b`
   `List ?a -> (?a -> ?b) -> List ?b`

4. By main conclusion:
   `|- tsum _ = _ * tsum _`
   finds all lemmas where the conclusion (the subexpression to the right of all `→` and `∀`) has the
   given shape.

   As before, if the pattern has parameters, they are matched against the hypotheses of
   the lemma in any order; for example,
   `|- _ < _ → tsum _ < tsum _`
   will find `tsum_lt_tsum` even though the hypothesis `f i < g i` is not the last.

If you pass more than one such search filter, separated by commas, Loogle will return lemmas which match _all_ of them.
The search
`Real.sin, "two", tsum, _ * _, _ ^ _, |- _ < _ → _`
would find all lemmas which mention the constants `Real.sin` and `tsum`, have `"two"` as a
substring of the lemma name, include a product and a power somewhere in the type, *and* have a
hypothesis of the form `_ < _` (if there were any such lemmas). Metavariables (`?a`) are assigned independently in each filter.

## CLI usage

The loogle binary searches any Lake project of the same Lean toolchain. Run it
from the project via `lake env` (which supplies the olean search path):

    $ lake env loogle --module Mathlib '(List.replicate (_ + _) _ = _)'
    Found 5 declarations mentioning List.replicate, HAdd.hAdd and Eq.
    Of these, 3 match your patterns.

    List.replicate_add
    List.replicate_succ
    List.replicate_succ'

The first call builds the search index (slow); by default loogle caches it on
disk next to the module's `.olean` so subsequent calls are fast, and quietly
rebuilds it whenever the underlying `.olean`s change. (In this image the
Mathlib index is prebuilt, so queries are fast from the start.)

    USAGE:
      loogle [OPTIONS] [QUERY]

    OPTIONS:
      --help
      --interactive, -i     read querys from stdin
      --json, -j            print result in JSON format
      --module mod          import this module (default: Mathlib)
      --path path           search for .olean files here (default: the build time path)
      --index-mode MODE     how to manage the on-disk search index. One of:
                              use   (default) load if present and up-to-date,
                                    otherwise build and write
                              read  load existing index; refuse to start if it
                                    is missing or out of date
                              write always (re)build the index and write it
                              none  build in memory and discard on exit
      --index-file PATH     override the default index path. The default lives
                            next to the root module's .olean (with .loogle-index
                            extension); pass this if that location is read-only.
      --max-results n       limit the number of returned hits (default: 200)
