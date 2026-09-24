#!/bin/sh
# CAPD (Computer Assisted Proofs in Dynamics): a C++ library for rigorous
# numerics -- interval arithmetic, validated ODE integration (Taylor/Lohner),
# rigorous derivatives of flows and Poincare maps, interval Newton/Krawczyk.
# Unlike the other unpackaged tools this is a library, not a binary: the agent
# writes C++ against it and compiles with
#   g++ prog.cpp $(capd-config --cflags --libs) -o prog
# so what ships is static libs (libcapd.a, libfilib.a), headers, the
# `capd-config` script (a pkg-config wrapper; the agent apt line installs
# pkg-config for it) and the pkg-config file, all under /usr/local. Docs and the
# projectStarter example go to share/doc/capd.
#
# x86-64 only: the bundled filib interval kernel's CMake hard-fails on any other
# CPU (it needs SSE rounding control). On other architectures this installs
# nothing, so arm64 dev images simply lack it (tests/test_agent_image.py skips
# it there).
#
# Multiprecision is OFF: with it on, capd.pc adds -D__HAVE_MPFR__, which makes
# the public headers include <mpfr.h>/<gmpxx.h>, and the agent image carries
# only the mpfr runtime (libmpfr6), not its headers. Off, the library links
# nothing beyond libstdc++/libm. Tests and examples are not built.
set -eu

VERSION=6.0.0
SHA256=0ae254cb6477896c3c3f2b8cd1c4a6cb073fb1e1e08f71d0e0bd2587d60c9620

if [ "$(uname -m)" != x86_64 ]; then
  echo "capd: filib is x86-64 only; nothing installed on $(uname -m)" >&2
  exit 0
fi

cd /tmp
curl -sSfL -o capd.tar.gz "https://github.com/CAPDGroup/CAPD/archive/refs/tags/v${VERSION}.tar.gz"
echo "${SHA256}  capd.tar.gz" | sha256sum -c -
mkdir src && tar xzf capd.tar.gz --strip-components=1 -C src

mkdir src/build
cd src/build
# The install prefix is baked into capd-config and capd.pc, so configure for
# the final location (/usr/local) and stage the tree with DESTDIR.
cmake .. \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX=/usr/local \
  -DCAPD_ENABLE_MULTIPRECISION=OFF \
  -DCAPD_BUILD_TESTS=OFF \
  -DCAPD_BUILD_EXAMPLES=OFF
make -j"$(nproc)"
make install DESTDIR=/tmp/stage
cp -a /tmp/stage/usr/local/. /out/
# filib installs its headers as top-level include/{interval,rounding_control,
# fp_traits,ieee} (capd's headers include them that way) plus include/test,
# its own self-test snippets, which nothing references.
rm -r /out/include/test

cd /tmp/src
install -D -m 644 README.md /out/share/doc/capd/README.md
install -D -m 644 COPYING /out/share/doc/capd/COPYING
install -D -m 644 -t /out/share/doc/capd/projectStarter \
  capdMake/examples/projectStarter/MyProgram.cpp \
  capdMake/examples/projectStarter/utils.cpp \
  capdMake/examples/projectStarter/utils.h \
  capdMake/examples/projectStarter/output.cpp \
  capdMake/examples/projectStarter/output.h \
  capdMake/examples/projectStarter/Makefile
