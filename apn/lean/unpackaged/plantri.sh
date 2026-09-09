#!/bin/sh
# plantri: planar-graph generator (Brinkmann & McKay). Upstream distributes
# numbered source tarballs from the author's site; there are no tags or releases.
set -eu

VERSION=55
SHA256=911cdf5bcca7294eb80f8f79fefc148183f7ba81da15b3aa4d6d2401a3bc7ded

cd /tmp
curl -sSfL -o src.tar.gz "https://users.cecs.anu.edu.au/~bdm/plantri/plantri${VERSION}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src

make plantri

install -D -m 755 plantri /out/bin/plantri
install -D -m 644 plantri-guide.txt /out/share/doc/plantri/plantri-guide.txt
