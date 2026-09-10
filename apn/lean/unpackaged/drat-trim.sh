#!/bin/sh
# drat-trim + lrat-check: proof checkers for SAT solvers' UNSAT certificates
# (DRAT from kissat/cryptominisat; DRAT->LRAT conversion).
set -eu

VERSION=v05.22.2023
SHA256=9ca38a8a95ac047bb71f232f8ef1a30a6eaf157b2b87a098719018eff17c99a6

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/marijnheule/drat-trim/archive/refs/tags/${VERSION}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src

make

install -D -m 755 -t /out/bin drat-trim lrat-check
install -D -m 644 README.md /out/share/doc/drat-trim/README.md
