#!/bin/sh
# msieve: SIQS/NFS integer factorization past gmp-ecm's reach. OPT_FLAGS
# overrides the Makefile's -march=native so the binary is portable across CPUs.
set -eu

VERSION=1.53
SHA256=c5fcbaaff266a43aa8bca55239d5b087d3e3f138d1a95d75b776c04ce4d93bb4

cd /tmp
curl -sSfL -o src.tar.gz "https://downloads.sourceforge.net/project/msieve/msieve/Msieve%20v${VERSION}/msieve$(echo "${VERSION}" | tr -d .)_src.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src

make all -j"$(nproc)" OPT_FLAGS='-O3 -fomit-frame-pointer -D_FILE_OFFSET_BITS=64 -DNDEBUG'

install -D -m 755 msieve /out/bin/msieve
install -D -m 644 -t /out/share/doc/msieve Readme Readme.nfs Readme.qs
