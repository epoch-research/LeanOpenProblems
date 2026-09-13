#!/bin/sh
# BreakID: static CNF symmetry breaking (a preprocessor for SAT searches).
# Pinned to the commit behind upstream's release/3.1.3 tag and fetched as that
# commit's archive, so a moved tag cannot change the build.
# BUILD_SHARED_LIBS=OFF: upstream defaults to a shared libbreakid that the
# executable then needs at runtime; only the executable ships, so link the
# library in.
set -eu

COMMIT=e9a5274ff92adc414c06307c28f6683a0960d067   # release/3.1.3
SHA256=0bd360b8dfa3c2d8831adfde2a9eca2032a1943c9427156438b504d9232a3f5a

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/meelgroup/breakid/archive/${COMMIT}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src

cmake -S src -B build -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF
cmake --build build -j"$(nproc)"

install -D -m 755 build/breakid /out/bin/breakid
install -D -m 644 src/README.md /out/share/doc/breakid/README.md
