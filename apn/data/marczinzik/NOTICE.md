# The Marczinzik–Böhmler dataset

Upstream source: two Lean files formalizing homological conjectures for finite-dimensional algebras -- the finitistic dimension conjecture and the Nakayama conjecture -- contributed by René Marczinzik (University of Bonn) and Bernhard Böhmler (University of Hannover), sent to Tom Adamczewski by email on 2026-09-08. René produced the formalizations with GPT-6 Astra; they are not upstream formal-conjectures files (FC has neither conjecture at the pin).

`Sources/` restates the contributed files in FC's conventions so the shared isolation pipeline applies: the `FormalConjecturesUtil` import (which pulls in all of Mathlib) replaces the files' individual Mathlib imports, each conjecture's `def ... : Prop` is stated as a `sorry`'d `theorem` carrying `@[category research open, AMS 16]`, and module docs with references are added. The definitions (`HasFiniteFinitisticDimension`, `IsMinimalInjectiveResolution`, `HasInfiniteDominantDimension`) are the contributed ones verbatim; the contributed equivalence lemma `hasFiniteFinitisticDimension_iff` is kept as a `@[category API]` sanity check (cut from the isolated spec, like every non-target theorem).

`fc_commit` is the FC commit the files compile against; it plays only its sandbox-image/proving-library role here. It is FC main as of 2026-09-08 (Lean v4.33.1, Mathlib v4.33.1): the contributed files import `Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension`, which postdates the v4.27.0 Mathlib the other datasets' pins carry.

`samples.jsonl` lists every research-category statement in those files (one per file). There are no predefined subsets.
