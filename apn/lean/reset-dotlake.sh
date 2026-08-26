#!/bin/sh
# Trusted per-check reset of the comparator sandbox's `.lake`.
#
# Landrun confines the untrusted `lake build Solution` to writes in `.lake`
# (+ `/dev`), so `.lake` is the only place a submission's bytes can persist
# between checks -- the kill shot being a poisoned Mathlib olean that makes a
# later check's *trusted* Challenge elaborate to something trivial. The checker
# runs this script before every check to restore the invariant: every check
# starts with `.lake` bit-identical to pristine (/opt/pristine, staged at
# image build).
#
# The heavy package artifacts (Mathlib and friends) are never copied: they
# live outside `.lake` at /opt/pristine/packages -- and therefore outside the
# landrun write grant -- and are symlinked into the fresh `.lake`. The symlink
# is plumbing, not protection (a build can replace it within its own check);
# immutability comes from the target's location, freshness from this wipe.
# The copied skeleton is lake's config/trace state plus the FC library build
# artifacts, tens of MB, so the reset stays cheap.
#
# `/dev`, the write grant's other member, is deliberately not touched: no
# trusted step ever reads data from under it (it is a sink -- /dev/null and
# friends), and its device nodes could not be recreated by the image's
# unprivileged user anyway. See comparator-migration-plan.md §3.1.
#
# Scope: this is a *filesystem* reset only. It cannot terminate a process a
# prior check's submission left behind; per-check process isolation needs a
# fresh sandbox service instance, which Inspect does not expose yet (see
# https://github.com/UKGovernmentBEIS/inspect_ai/issues/5034 and
# comparator-migration-plan.md §3.1).
set -eu

PROJECT=/workspace/leanproject
PRISTINE=/opt/pristine

# Destroy .lake and recreate it from the pristine skeleton, with
# .lake/packages pointing at the pristine tree.
rm -rf "$PROJECT/.lake"
cp -a "$PRISTINE/dot-lake" "$PROJECT/.lake"
ln -s "$PRISTINE/packages" "$PROJECT/.lake/packages"
