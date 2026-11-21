#!/bin/sh
# Build the WFDB library and the EC38/EC57 comparators (bxb, epicmp, sumstats)
# plus wrann/rdann from the pinned GitHub revision, without libcurl or FLAC.
# Observed: GCC 15.2.0 (Debian), x86-64 Linux; -std=gnu89 is needed because
# the K&R-style sources do not compile under GCC 15's default C23 dialect.
set -eu
: "${WORK:=/tmp/aed-probe}"
REV=de6b1d3981d69060e6a4d1b4e86375fb0d3ed2d1
mkdir -p "$WORK"; cd "$WORK"
curl -sSL -H "User-Agent: research-bot" -o wfdb.tar.gz \
  "https://codeload.github.com/bemoody/wfdb/tar.gz/$REV"
sha256sum wfdb.tar.gz   # observed 8fbcc215b4ecb6b15c0d2588658a1f7b3ab1629b3e0a7f189b823a7571397df5
rm -rf wfdb-10.7.0 && tar xzf wfdb.tar.gz && mv "wfdb-$REV" wfdb-10.7.0
cd wfdb-10.7.0
# configure derives the version from the directory name (wfdb-X.Y.Z) and
# otherwise prompts on stdin; NEWS at this revision starts with 10.7.0.
./configure --static --without-netfiles --without-flac --without-xview \
  --prefix="$WORK/inst" </dev/null
time make -C lib install MFLAGS="-std=gnu89"
cd app && time make bxb epicmp wrann rdann sumstats MFLAGS="-std=gnu89"
wc -c bxb epicmp wrann rdann sumstats
size bxb epicmp
