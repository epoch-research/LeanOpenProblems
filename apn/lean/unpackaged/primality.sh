#!/bin/sh
# The special-form primality toolchain, x86-64 only: srsieve2 sieves k*b^n+-c
# candidate grids (mtsieve suite; SourceForge SVN, revision-pinned; its makefile
# only knows x86 and 32-bit ARM), then sllr64 (LLR) and pfgw64 (OpenPFGW) prove
# primality at 10^5..10^7 digits (gwnum is x86-64 assembly; no arm route
# exists). On other architectures this installs nothing, so arm64 dev images
# simply lack the three (tests/test_agent_image.py skips them there).
set -eu

MTSIEVE_SVN_REV=469
LLR_VERSION=407
LLR_SHA256=b92424d85d0d37788bb33613ec1af2b6d5cb1f5ce37be5ed062b0aad604a6ab3
PFGW_VERSION=4.1.8
PFGW_SHA256=aadf885e2d6489866bb7eeea2ba3f75a3fa02e679f1d6a86fd2632e042a99c99

if [ "$(uname -m)" != x86_64 ]; then
  echo "primality: srsieve2/sllr64/pfgw64 are x86-64 only; nothing installed on $(uname -m)" >&2
  exit 0
fi

cd /tmp
svn checkout -q -r "${MTSIEVE_SVN_REV}" https://svn.code.sf.net/p/mtsieve/svn/ mtsieve
cd mtsieve
make -j"$(nproc)" srsieve2
install -D -m 755 srsieve2 /out/bin/srsieve2

cd /tmp
# jpenne.free.fr is HTTP-only; integrity comes from the sha256 pin.
curl -sSfL -o llr.zip "http://jpenne.free.fr/llr4/llr${LLR_VERSION}slinux64.zip"
echo "${LLR_SHA256}  llr.zip" | sha256sum -c -
unzip -q llr.zip -d llr
install -D -m 755 "$(find llr -type f -name sllr64)" /out/bin/sllr64

curl -sSfL -o pfgw.7z "https://downloads.sourceforge.net/project/openpfgw/pfgw_linux_${PFGW_VERSION}.7z"
echo "${PFGW_SHA256}  pfgw.7z" | sha256sum -c -
7zr x -opfgw pfgw.7z >/dev/null
install -D -m 755 pfgw/pfgw64 /out/bin/pfgw64
