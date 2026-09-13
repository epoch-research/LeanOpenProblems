#!/bin/sh
# march_cu: cube-and-conquer splitter for hard SAT instances (Heule's CnC repo;
# no tags upstream, so commit-pinned). -fcommon: pre-C99 tentative definitions.
set -eu

COMMIT=705b60c6491ef2b61988b3ce6ac674be1b90571d
SHA256=5bc9485cae9f1edfb7291b4d11483ebb0163e958aeb770aa2ecb4686dafbc3c3

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/marijnheule/CnC/archive/${COMMIT}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src/march_cu

make CFLAGS='-O3 -fno-strict-aliasing -Wall -DNDEBUG -fcommon'

install -D -m 755 march_cu /out/bin/march_cu
install -D -m 644 ../README.md /out/share/doc/march_cu/README.md
