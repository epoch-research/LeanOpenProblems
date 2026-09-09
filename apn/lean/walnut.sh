#!/bin/sh
# Walnut: the decision procedure for automatic sequences / base-k digit
# statements (Buechi arithmetic). Java; built once with the repo's own gradle
# wrapper and shipped as the /opt/walnut tree, run via upstream's launcher
# /opt/walnut/walnut.sh (the JRE comes from the agent stage's apt line).
# Upstream's build.sh is its gradle invocation + chmod followed by an
# interactive "Press enter" prompt that exits 1 in a non-interactive build, so
# the two commands run directly here.
set -eu

VERSION=v7.1.0
SHA256=2d65e039e6b78ce6e8082740ce053abf3e4018e16e007b9eb37682f724f15aba

cd /tmp
curl -sSfL -o walnut.tar.gz "https://github.com/Walnut-Theorem-Prover/Walnut/archive/refs/tags/${VERSION}.tar.gz"
echo "${SHA256}  walnut.tar.gz" | sha256sum -c -
mkdir -p /opt/walnut
tar xzf walnut.tar.gz --strip-components=1 -C /opt/walnut
rm walnut.tar.gz

cd /opt/walnut
./gradlew clean customFatJar
chmod +x walnut.sh
rm -rf /root/.gradle
