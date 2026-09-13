#!/bin/sh
# SMS (smsg): SAT-modulo-symmetries graph search -- find/enumerate graphs with a
# property, modulo isomorphism. Cloned rather than fetched as an archive because
# CaDiCaL is a git submodule; pinned to the commit behind the v2.1.1 tag.
set -eu

COMMIT=d2a572959a48b0432eebc212114f343b4c6050bd   # v2.1.1

mkdir /tmp/src && cd /tmp/src
git init -q
git fetch -q --depth 1 https://github.com/markirch/sat-modulo-symmetries "${COMMIT}"
git checkout -q --detach FETCH_HEAD
git submodule update -q --init --recursive

# Upstream hardcodes shared Boost in src/CMakeLists.txt (a plain set(), which
# overrides -DBoost_USE_STATIC_LIBS=ON on the command line); flip it so
# program_options links statically and the binary needs no libboost at runtime.
# Only the smsg executable is built: upstream's libsms.so target cannot take
# the non-PIC static archive.
grep -q 'set(Boost_USE_STATIC_LIBS OFF)' src/CMakeLists.txt
sed -i 's/set(Boost_USE_STATIC_LIBS OFF)/set(Boost_USE_STATIC_LIBS ON)/' src/CMakeLists.txt

cd cadical_sms
./configure -fPIC
make -j"$(nproc)"
cd ..
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j"$(nproc)" --target smsg

install -D -m 755 build/src/smsg /out/bin/smsg
install -D -m 644 README.md /out/share/doc/sms/README.md
install -D -m 644 -t /out/share/doc/sms docs/*.md
