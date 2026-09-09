#!/bin/sh
# Sage's optional databases, from Sage's own upstream tarballs (versions and
# sha256s from sage 10.9's build/pkgs/<name>/checksums.ini), installed where
# sage.features.databases looks (SAGE_SHARE=/opt/sage/share) per each spkg's
# install recipe. Cremona: the full elliptic-curve tables (conductor < 500000;
# conda sage ships only cremona_mini). Jones: number fields of small degree
# with restricted ramification. Odlyzko: 2M zeta zeros, pickled by sage as its
# recipe does. polytopes_db_4d (9.2 GB) is deliberately NOT installed.
# KnotInfo/matroid/cubic-Hecke databases are pip packages (sage.yaml).
set -eu

M=https://mirrors.mit.edu/sage/spkg/upstream
SHARE=/opt/sage/share

cd /tmp
curl -sSfL -o cremona.tar.bz2 "$M/database_cremona_ellcurve/database_cremona_ellcurve-20190911.tar.bz2"
echo "5d1d6aa35a95f9df123c87c1894791580d067444e1145bbd6ec20b4840f22053  cremona.tar.bz2" | sha256sum -c -
mkdir -p "$SHARE/cremona"
tar xjf cremona.tar.bz2 -C "$SHARE/cremona" --strip-components=1

curl -sSfL -o jones.tar.gz "$M/database_jones_numfield/database_jones_numfield-4.tar.gz"
echo "704d70101bc504bbdd2d7ac5847cb3bbc43e017c0ee163a9b4ab3ed2e572a001  jones.tar.gz" | sha256sum -c -
mkdir -p "$SHARE/jones"
tar xzf jones.tar.gz -C "$SHARE/jones" --strip-components=1

curl -sSfL -o odlyzko.tar.bz2 "$M/database_odlyzko_zeta/database_odlyzko_zeta-20061209.tar.bz2"
echo "8919f01992718b9bf5c0602dbf16dd9d6f58b141b25f67f5cfd59f6cd0f9a0d4  odlyzko.tar.bz2" | sha256sum -c -
mkdir -p odlyzko "$SHARE/odlyzko"
tar xjf odlyzko.tar.bz2 -C odlyzko --strip-components=1
/opt/sage/bin/python3 -c "from sage.all import save; save([float(x) for x in open('odlyzko/zeros6')], '$SHARE/odlyzko/zeros.sobj')"

rm -rf /tmp/cremona.tar.bz2 /tmp/jones.tar.gz /tmp/odlyzko.tar.bz2 /tmp/odlyzko
# The build-time imports above left bytecode caches across the env; drop them.
find /opt/sage -name '__pycache__' -type d -prune -exec rm -rf {} +
