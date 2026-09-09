#!/bin/sh
# msolve: multivariate polynomial system solver (Groebner bases, real roots).
# Needs FLINT >= 3, which bookworm lacks, so FLINT is built first, static, into
# this stage's /usr/local, where msolve's configure finds it; only the msolve
# binary ships. It links gmp and mpfr from the bookworm userland (the agent
# stage's apt line installs libmpfr6 for it).
set -eu

FLINT_VERSION=3.6.0
FLINT_SHA256=b95e2c7792f5eea4a1c8d2d42c4098434756832e57a094b295eb5dfdc9b4c36b
VERSION=0.10.1
SHA256=4ea31066005dc38461fe6b85eb96828990340ce68bdc246fd37e1338d2155beb

cd /tmp
curl -sSfL -o flint.tar.gz "https://github.com/flintlib/flint/releases/download/v${FLINT_VERSION}/flint-${FLINT_VERSION}.tar.gz"
echo "${FLINT_SHA256}  flint.tar.gz" | sha256sum -c -
mkdir flint && tar xzf flint.tar.gz --strip-components=1 -C flint
cd flint
./configure --disable-shared --prefix=/usr/local
make -j"$(nproc)"
make install

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/algebraic-solving/msolve/releases/download/v${VERSION}/msolve-${VERSION}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src
./configure --disable-shared
make -j"$(nproc)"

install -D -m 755 msolve /out/bin/msolve
install -D -m 644 README.md /out/share/doc/msolve/README.md
