#!/bin/sh
# kissat: state-of-the-art CDCL SAT solver (DIMACS in/out).
set -eu

VERSION=rel-4.0.4
SHA256=bfe93eaa6323b48011e4b1fcf74b3f2e20f9de544767e728009e5b2018296193

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/arminbiere/kissat/archive/refs/tags/${VERSION}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src

./configure
make -j"$(nproc)"

install -D -m 755 build/kissat /out/bin/kissat
install -D -m 644 README.md /out/share/doc/kissat/README.md
