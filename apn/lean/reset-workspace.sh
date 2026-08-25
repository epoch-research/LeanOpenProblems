#!/bin/sh
# Trusted per-check filesystem reset for the `comparator` sandbox.
#
# The comparator container runs with a read-only rootfs; the only writable
# spots are tmpfs mounts at /workspace/leanproject/.lake, /workspace/leanproject/run
# and /tmp. The untrusted `lake build Solution` (confined by landrun to .lake)
# can leave arbitrary state behind there -- including a poisoned Mathlib under
# .lake/packages if the packages symlink were replaced by a real directory. A
# later check's *challenge* build must never see any of it, so the checker runs
# this script before every check: wipe the mutable spots and rebuild .lake from
# the image's pristine tree (/opt/pristine, staged at image build).
#
# The heavy package artifacts (Mathlib and friends) are never copied: they live
# on the read-only rootfs at /opt/pristine/packages and are symlinked into the
# fresh .lake, so they are immutable by construction and the reset stays cheap
# (the copied skeleton is the FC project's own build artifacts, tens of MB).
#
# Scope: this is a *filesystem* reset only. It cannot terminate a process a
# prior check's submission left behind; per-check process isolation needs a
# fresh sandbox service instance, which Inspect does not expose yet (see
# https://github.com/UKGovernmentBEIS/inspect_ai/issues/5034 and
# comparator-migration-plan.md §3.1).
set -eu

PROJECT=/workspace/leanproject
PRISTINE=/opt/pristine

# Wipe the tmpfs contents without disturbing the mountpoints themselves.
find "$PROJECT/.lake" -mindepth 1 -maxdepth 1 -exec rm -rf {} +
find "$PROJECT/run" -mindepth 1 -maxdepth 1 -exec rm -rf {} +
find /tmp -mindepth 1 -maxdepth 1 -exec rm -rf {} +

# Recreate .lake from the pristine skeleton (lake's config/trace state + the FC
# library build artifacts) and point .lake/packages at the read-only tree.
cp -a "$PRISTINE/dot-lake/." "$PROJECT/.lake/"
ln -s "$PRISTINE/packages" "$PROJECT/.lake/packages"
