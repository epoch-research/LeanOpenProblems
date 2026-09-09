#!/bin/sh
# prover9/mace4: first-order theorem prover + finite-model finder (LADR).
# Upstream (cs.unm.edu LADR-2009-11A) has no releases and Debian dropped the
# package, so this builds a pinned commit of the ai4reason mirror of that final
# release.
set -eu

COMMIT=cdca95a51d3c3459b8fd2ebbb5ac1504be2172e3
SHA256=3a2f7a15367a8a438db0a08349a42204b5a4f08002bd84c29fd202eba1a56f04

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/ai4reason/Prover9/archive/${COMMIT}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src

make all

install -D -m 755 -t /out/bin bin/prover9 bin/mace4 bin/interpformat bin/prooftrans
install -D -m 644 README.md /out/share/doc/prover9/README.md
