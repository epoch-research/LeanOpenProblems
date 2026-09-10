#!/bin/sh
# sagemath-giac: Sage's Giac backend (Groebner bases via giac, giac as an
# integration engine), split out of sagelib upstream and distributed only as a
# GitHub release. Built with meson against the env's giac, with the env's own
# toolchain (sage brings cython and its compilers), and without build isolation
# because its build-requires include sagemath-standard, which IS the installed
# sage. meson-python and ninja are build-only and come from PyPI here.
set -eu

VERSION=0.1.4
SHA256=44b8bfc406d3272d634509d50a00208b4a96b7f81641cdb6db455e5e0f860a4b

export PATH=/opt/sage/bin:$PATH
pip install --no-cache-dir meson-python==0.21.0 ninja

cd /tmp
curl -sSfL -o sagemath-giac.tar.gz "https://github.com/sagemath/sagemath-giac/archive/refs/tags/${VERSION}.tar.gz"
echo "${SHA256}  sagemath-giac.tar.gz" | sha256sum -c -
mkdir sagemath-giac && tar xzf sagemath-giac.tar.gz --strip-components=1 -C sagemath-giac
pip install --no-cache-dir --no-build-isolation ./sagemath-giac
rm -rf /tmp/sagemath-giac /tmp/sagemath-giac.tar.gz
