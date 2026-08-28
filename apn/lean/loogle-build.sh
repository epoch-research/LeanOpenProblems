#!/bin/bash
# Build the Loogle search CLI against the FC project's exact Mathlib
# (Dockerfile stage loogle_build; usage: loogle-build.sh <loogle-commit>).
#
# Loogle is built as its own Lake project at /opt/loogle, retargeted to the
# FC project: the project's lean-toolchain verbatim, and loogle's mathlib
# requirement moved from "master" to the rev the project's manifest pins.
# Deleting loogle's own lake-manifest.json makes `lake update` re-resolve all
# transitive deps from that pinned mathlib's manifest -- i.e. to exactly the
# revs the FC project uses. (Do NOT add loogle to the FC project itself:
# `lake update loogle` there pulls transitive deps from loogle's stale
# manifest and drifts the project off its pins.)
#
# Instead of cloning a second multi-GB Mathlib, loogle's .lake/packages is a
# symlink to the FC project's packages -- same revs by construction, already
# built. The binary embeds its olean search path at compile time (all under
# /opt/loogle/.lake/... plus the toolchain), and its index lookup finds
# LoogleMathlibCache.extra next to that module's olean, so at runtime the
# plain binary works with no flags and no wrapper; the agent stage copies the
# binary, /opt/loogle/.lake/build/lib, and recreates the packages symlink.
set -euo pipefail

loogle_commit="$1"
project=/workspace/leanproject

mathlib_rev="$(python3 -c "
import json
packages = json.load(open('$project/lake-manifest.json'))['packages']
print(next(p['rev'] for p in packages if p['name'] == 'mathlib'))
")"

git clone https://github.com/nomeata/loogle.git /opt/loogle
cd /opt/loogle
git checkout --detach "${loogle_commit}"

cp "$project/lean-toolchain" lean-toolchain
sed -i "s|@ \"master\"|@ \"${mathlib_rev}\"|" lakefile.lean
grep -q "${mathlib_rev}" lakefile.lean  # the sed matched
rm lake-manifest.json
mkdir .lake
ln -s "$project/.lake/packages" .lake/packages

lake update
lake build loogle LoogleMathlibCache

# Persist the search index where Find.cachePath looks for it (next to
# LoogleMathlibCache.olean), then prove the flag-less invocation the agent
# will use. Index construction peaks ~10 GB RSS.
bin=.lake/build/bin/loogle
"$bin" --write-index .lake/build/lib/lean/LoogleMathlibCache.extra --json "Nat.Prime" > /tmp/smoke.json
grep -q '"name"' /tmp/smoke.json
"$bin" --json "Nat.Prime" > /tmp/smoke.json
grep -q '"name"' /tmp/smoke.json
rm /tmp/smoke.json

# Only the oleans and the index pickle matter at runtime.
find .lake/build/lib -type f ! -name '*.olean' ! -name '*.extra' -delete
