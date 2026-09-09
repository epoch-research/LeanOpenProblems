#!/bin/sh
# vampire: superposition first-order prover + finite-model builder (--mode fmb),
# the official release binaries (they link only libc/libstdc++). The release
# zip carries no documentation.
set -eu

VERSION=v5.1.0
case "$(uname -m)" in
  x86_64)  ZIP=vampire-Linux-X64.zip;   SHA256=495828dc76cb17a27080d62dedce755e46de96f47f06f5f0ad4be9cdaf6f968f ;;
  aarch64) ZIP=vampire-Linux-ARM64.zip; SHA256=7abc39224fdf41bdb2c241f8b180a80b7c1a4bce1e46dc79df02cfea2798ad5c ;;
  *) echo "unsupported arch $(uname -m)" >&2; exit 1 ;;
esac

cd /tmp
curl -sSfL -o vampire.zip "https://github.com/vprover/vampire/releases/download/${VERSION}/${ZIP}"
echo "${SHA256}  vampire.zip" | sha256sum -c -
unzip -q vampire.zip -d vampire

install -D -m 755 "$(find vampire -type f -name vampire)" /out/bin/vampire
