#!/bin/sh
# redumis (KaMIS): near-optimal maximum independent sets at scales exact solvers
# cannot reach (KaHIP is vendored in the release tarball).
set -eu

VERSION=v3.2
SHA256=4ba5ebb2fe72d8263cacec1550f56e4013bbad45a0b615ac7098d1bb865a8f74

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/KarlsruheMIS/KaMIS/archive/refs/tags/${VERSION}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src

cmake -S src -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j"$(nproc)" --target redumis

install -D -m 755 build/redumis /out/bin/redumis
install -D -m 644 src/README.md /out/share/doc/kamis/README.md
