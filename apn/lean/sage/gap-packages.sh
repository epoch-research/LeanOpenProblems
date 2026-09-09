#!/bin/sh
# GAP packages Sage uses as optional backends (its `gap_packages` spkg list,
# plus grape/guava and hap's dependency nq), and Digraphs with the kernel
# packages it needs (io, orb, datastructures), which the conda GAP does not
# ship. All come from GAP's own packages tarball for the installed GAP release
# -- the set GAP ships as mutually compatible -- into the env's GAP root; the
# compiled ones are built the way GAP's BuildPackages does. VERSION must be the
# gap-defaults release in sage.yaml; the GRAPE and Digraphs smokes in
# tests/test_agent_image.py catch a mismatch. packagemanager is in conda GAP's
# default PackagesToLoad but not shipped, hence the '#I packagemanager package
# is not available' on every startup without it.
set -eu

VERSION=v4.15.1
SHA256=c62234ca31685145737e9e66e1dc20424cbd114dcef3e89a5839670561a2a2e6

export PATH=/opt/sage/bin:$PATH
PKG=/opt/sage/share/gap/pkg

cd /tmp
curl -sSfL -o gap-packages.tar.gz "https://github.com/gap-system/gap/releases/download/${VERSION}/packages-${VERSION}.tar.gz"
echo "${SHA256}  gap-packages.tar.gz" | sha256sum -c -
tar xzf gap-packages.tar.gz -C "$PKG" \
    ./grape ./guava ./nq ./hap ./design ./qpa ./gbnp ./quagroup \
    ./aclib ./crystcat ./cryst ./polymaking ./sonata ./packagemanager \
    ./autodoc ./corelg ./crime ./genss ./hapcryst ./hecke ./images \
    ./liealgdb ./liepring ./liering ./lins ./loops ./mapclass ./repsn \
    ./singular ./sla ./toric \
    ./io ./orb ./datastructures ./digraphs
rm gap-packages.tar.gz

for p in grape guava nq io orb datastructures digraphs; do
  cd "$PKG/$p"
  ./configure /opt/sage/lib/gap || ./configure --with-gaproot=/opt/sage/lib/gap
  make -j"$(nproc)"
done
