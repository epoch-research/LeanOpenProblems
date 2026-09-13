#!/bin/sh
# Julia + OSCAR/Hecke (computer algebra: Galois groups, number fields, group
# theory) as a fully precompiled, offline-usable depot. The depot stays at
# Julia's default location, /root/.julia, so the agent image needs no
# JULIA_DEPOT_PATH (Julia >= 1.11 pkgimages are relocatable and content-hashed;
# the depot is complete, so loading never touches the network). The multi-target
# JULIA_CPU_TARGET lists are the ones the official binaries use, so the baked
# pkgimages load on any deploy CPU. NEVER run this under qemu emulation:
# precompilation crashes there (native-only, both arches verified).
set -eu

JULIA_VERSION=1.12.7
OSCAR_VERSION=1.8.1
HECKE_VERSION=0.39.22

# sha256s from https://julialang-s3.julialang.org/bin/checksums/julia-1.12.7.sha256
case "$(uname -m)" in
  x86_64)
    TARBALL="x64/1.12/julia-${JULIA_VERSION}-linux-x86_64.tar.gz"
    SHA256=4e7e9e776634d24835250de67cde39b0d4af15bc432eb20697e6be6c28ea69e8
    JULIA_CPU_TARGET='generic;sandybridge,-xsaveopt,clone_all;haswell,-rdrnd,base(1);x86-64-v4,-rdrnd,base(1)' ;;
  aarch64)
    TARBALL="aarch64/1.12/julia-${JULIA_VERSION}-linux-aarch64.tar.gz"
    SHA256=9243c0b524c7f300883240a1ee5ea3916a30e070bff718acf8ccaee31a731ef2
    JULIA_CPU_TARGET='generic;cortex-a57;thunderx2t99;carmel,clone_all;apple-m1,base(3);neoverse-512tvb,-rand,-fpac,base(3)' ;;
  *) echo "unsupported arch $(uname -m)" >&2; exit 1 ;;
esac
export JULIA_CPU_TARGET

cd /tmp
curl -sSfL -o julia.tar.gz "https://julialang-s3.julialang.org/bin/linux/${TARBALL}"
echo "${SHA256}  julia.tar.gz" | sha256sum -c -
mkdir -p /opt/julia
tar xzf julia.tar.gz --strip-components=1 -C /opt/julia
rm julia.tar.gz

/opt/julia/bin/julia -e "using Pkg; Pkg.add([
    PackageSpec(name=\"Oscar\", version=\"${OSCAR_VERSION}\"),
    PackageSpec(name=\"Hecke\", version=\"${HECKE_VERSION}\")]);
  Pkg.precompile(); Pkg.gc()"

# The depot must be complete: loading may not touch the network.
JULIA_PKG_OFFLINE=true /opt/julia/bin/julia -e \
  'using Oscar; using Hecke; println("Oscar ", Oscar.VERSION_NUMBER)'
