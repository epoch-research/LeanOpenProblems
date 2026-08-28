<!-- Vendored from https://github.com/nomeata/loogle (blurb.md and README.md) at rev 79343e3e37b64046e6b555936682012e80300df1 -->
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

    $ loogle '(List.replicate (_ + _) _ = _)'
    Found 5 declarations mentioning List.replicate, HAdd.hAdd and Eq.
    Of these, 3 match your patterns.

    List.replicate_add
    List.replicate_succ
    List.replicate_succ'

    USAGE:
      loogle [OPTIONS] [QUERY]

    OPTIONS:
      --help
      --interactive, -i     read querys from stdin
      --json, -j            print result in JSON format
      --module mod          import this module (default: Mathlib)
      --path path           search for .olean files here (default: the build time path)
      --write-index file    persists the search index to a file
      --read-index file     read the search index from a file. This file is blindly trusted!

By default, it will create an internal index upon starting, which takes a bit.
You can use `--write-index` and `--read-index` to cache that, but it is your
responsibility to pass the right index for the given module and search path.
