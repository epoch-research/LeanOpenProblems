#!/bin/sh
# gclc: automated Euclidean geometry proving (area/Wu methods; CLI only, no
# GUI). Pinned to the commit behind upstream's v2026.1 tag and fetched as that
# commit's archive, so a moved tag cannot change the build.
set -eu

COMMIT=88d59dce1b16275762685dc0589adf65da4fcce6   # v2026.1
SHA256=3652c1e96d4a452ed69142744dac3fddaf4d0def8127c15d287a4d2b4ed656f0

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/janicicpredrag/gclc/archive/${COMMIT}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src

cmake -S src -B build -DCMAKE_BUILD_TYPE=Release -Dgui=OFF
cmake --build build -j"$(nproc)"

install -D -m 755 build/gclc /out/bin/gclc
install -D -m 644 src/README.md /out/share/doc/gclc/README.md
install -D -m 644 src/manual/gclc_man.tex /out/share/doc/gclc/gclc_man.tex
