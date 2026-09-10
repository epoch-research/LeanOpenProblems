#!/bin/sh
# cvc5: SMT solver, the official static release binary. The python API comes
# from the cvc5 wheel in conda.yaml; tests/test_agent_image.py asserts that the
# two versions agree. The release zip carries no documentation.
set -eu

VERSION=1.3.4
case "$(uname -m)" in
  x86_64)  ARCH=x86_64; SHA256=dcdbfada0ce493ee98259c0816e0daafc561c223aadb3af298c2968e73ea39c6 ;;
  aarch64) ARCH=arm64;  SHA256=2a4c108367f20b0c8990abd6b9535a5d62e08908d471d4671c00734e408f85bc ;;
  *) echo "unsupported arch $(uname -m)" >&2; exit 1 ;;
esac

cd /tmp
curl -sSfL -o cvc5.zip "https://github.com/cvc5/cvc5/releases/download/cvc5-${VERSION}/cvc5-Linux-${ARCH}-static.zip"
echo "${SHA256}  cvc5.zip" | sha256sum -c -
unzip -q cvc5.zip

install -D -m 755 "cvc5-Linux-${ARCH}-static/bin/cvc5" /out/bin/cvc5
