#!/bin/sh
# cake_lpr: formally verified LRAT proof checker (CakeML), built from the repo's
# pre-generated per-arch assembly with one gcc call. Commit-pinned: the repo cuts
# no releases.
set -eu

COMMIT=a36874a8b750b43fe4b385b8ddbf5b033e46a3fa
SHA256=3aa1257ae39cdb2d29343c0c26d1ab455f6089475dbb4f339393c57613c5073c
case "$(uname -m)" in
  x86_64)  ASM=cake_lpr.S ;;
  aarch64) ASM=cake_lpr_arm8.S ;;
  *) echo "unsupported arch $(uname -m)" >&2; exit 1 ;;
esac

cd /tmp
curl -sSfL -o src.tar.gz "https://github.com/tanyongkiam/cake_lpr/archive/${COMMIT}.tar.gz"
echo "${SHA256}  src.tar.gz" | sha256sum -c -
mkdir src && tar xzf src.tar.gz --strip-components=1 -C src
cd src

gcc -O2 -std=c99 basis_ffi.c "$ASM" -o cake_lpr

install -D -m 755 cake_lpr /out/bin/cake_lpr
install -D -m 644 README.md /out/share/doc/cake_lpr/README.md
