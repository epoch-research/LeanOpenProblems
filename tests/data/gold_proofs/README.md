# Vendored gold proofs (AlphaProof Nexus, OEIS)

The 38 `.lean` files here are **verbatim copies** of the AlphaProof Nexus paper's
published, complete (`sorry`-free) proofs for the `tsoukalas_proved_38` OEIS conjectures,
taken from the upstream results repo at
`reference_sources/alphaproof-nexus-results/APNOutputs/OEIS/*.lean`.

They are committed (vendored) here on purpose: `reference_sources/` is a local,
gitignored clone of upstream and is **not** present in CI, so any test that read
from it would silently skip or break there. These copies let the gold-proof
regression (`tests/test_gold_proofs.py`) and the isolation oracle
(`tests/test_oeis_isolation.py::test_oracle_matches_published_challenge_files`)
run identically locally and in CI.

Each file names its target theorem `target_theorem_0` (the paper's convention)
and carries its original Apache-2.0 / Google LLC header; they are redistributed
unmodified under that license. To refresh them after the upstream clone changes,
re-copy from `reference_sources/.../APNOutputs/OEIS/`.
