#!/usr/bin/env bash
# Reproducible from-source build of vt at the pinned revision, from GitHub source
# archives only. The vt archive does not contain its lib/htslib git submodule, so
# the submodule commits recorded in the vt and htslib trees are fetched separately.
# Host prerequisites observed to be missing on the build host: bzip2 and libcurl
# development headers/symlinks; this recipe disables them in htslib and links vt
# against the runtime .so files through a shim directory.
set -euo pipefail
OUT=${1:?usage: build_vt.sh OUTDIR}
VT=c6bd1591a23a1d116d52834a627c00bbf7ed4a64       # atks/vt
HTS=5b684ce625d772dc558c68fd360c8af3ac155f7e      # samtools/htslib (vt lib/htslib submodule pin)
CODECS=d7e357946ead219b81cc1becbe0de8a99d96ca84   # jkbonfield/htscodecs (htslib submodule pin)
mkdir -p "$OUT" && cd "$OUT"
curl -sSL -o vt.tgz "https://codeload.github.com/atks/vt/tar.gz/$VT"
curl -sSL -o hts.tgz "https://codeload.github.com/samtools/htslib/tar.gz/$HTS"
curl -sSL -o codecs.tgz "https://codeload.github.com/jkbonfield/htscodecs/tar.gz/$CODECS"
sha256sum vt.tgz hts.tgz codecs.tgz
tar xzf vt.tgz && tar xzf hts.tgz && tar xzf codecs.tgz
rmdir "vt-$VT/lib/htslib" && mv "htslib-$HTS" "vt-$VT/lib/htslib"
rmdir "vt-$VT/lib/htslib/htscodecs" 2>/dev/null || true
mv "htscodecs-$CODECS" "vt-$VT/lib/htslib/htscodecs"
cp /usr/share/misc/config.guess /usr/share/misc/config.sub "vt-$VT/lib/htslib/"
echo '#define HTSCODECS_VERSION_TEXT "d7e3579"' > "vt-$VT/lib/htslib/htscodecs/htscodecs/version.h"
mkdir -p shim
ln -sf /usr/lib/x86_64-linux-gnu/libbz2.so.1 shim/libbz2.so
ln -sf /usr/lib/x86_64-linux-gnu/libcurl.so.4 shim/libcurl.so
cd "vt-$VT"
( cd lib/libdeflate && make -j16 >/dev/null )
( cd lib/htslib && autoheader && autoconf && \
  LDFLAGS=-L$PWD/../libdeflate CPPFLAGS=-I$PWD/../libdeflate ./configure --disable-bz2 --disable-libcurl >/dev/null && \
  make -j16 libhts.a >/dev/null )
make -j16 CXXFLAGS="-pipe -std=c++0x -O3 -I./lib -I. -I./lib/htslib -I./lib/Rmath -I./lib/pcre2 -D__STDC_LIMIT_MACROS -L$OUT/shim" >/dev/null
ls -l vt
