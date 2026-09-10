# The personal-correspondence dataset

Upstream source: Lean formalizations of open conjectures sent to Tom Adamczewski by mathematicians in personal correspondence (email or direct message), each restated here in FC's conventions. They are not upstream formal-conjectures files (FC has none of these conjectures at the pin). The contributions so far:

- `Sources/FinitisticDimensionConjecture.lean`, `Sources/NakayamaConjecture.lean`: two homological conjectures for finite-dimensional algebras -- the finitistic dimension conjecture and the Nakayama conjecture -- contributed by René Marczinzik (University of Bonn) and Bernhard Böhmler (University of Hannover), sent by email on 2026-09-08. René produced the formalizations with GPT-6 Astra.
- `Sources/NilpotentClosure.lean`: whether the nilpotent elements of a ring can be closed under multiplication but not under addition, a question asked by Janez Šter (University of Ljubljana). The Lean statement was contributed by Pace Nielsen (Brigham Young University) in September 2026; he also offered it for contribution to formal-conjectures.

`Sources/` restates the contributed files in FC's conventions so the shared isolation pipeline applies: the `FormalConjecturesUtil` import (which pulls in all of Mathlib) replaces the files' individual Mathlib imports, each conjecture is stated as a `sorry`'d `theorem` carrying `@[category research open, AMS 16]` (the Marczinzik–Böhmler files stated theirs as `def ... : Prop`), and module docs with references are added. The Marczinzik–Böhmler definitions (`HasFiniteFinitisticDimension`, `IsMinimalInjectiveResolution`, `HasInfiniteDominantDimension`) are the contributed ones verbatim; their equivalence lemma `hasFiniteFinitisticDimension_iff` is kept as a `@[category API]` sanity check (cut from the isolated spec, like every non-target theorem). Pace Nielsen's theorem statement is the contributed one verbatim (reflowed).

`fc_commit` is the FC commit the files compile against; it plays only its sandbox-image/proving-library role here. It is FC main as of 2026-09-08 (Lean v4.33.1, Mathlib v4.33.1): the Marczinzik–Böhmler files import `Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension`, which postdates the v4.27.0 Mathlib the other datasets' pins carry.

`samples.jsonl` lists every research-category statement in those files (one per file). There are no predefined subsets.
