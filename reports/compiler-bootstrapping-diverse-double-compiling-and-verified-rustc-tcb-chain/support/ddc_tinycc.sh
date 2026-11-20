#!/usr/bin/env bash
# Diverse Double-Compiling (DDC) of TinyCC with two unrelated host C compilers.
#
# Real execution on a real self-hosting compiler; it is NOT a DDC of rustc.
# Notation follows Wheeler (2009): sA = sP = the TinyCC source at one commit,
# cA = the compiler under test (TinyCC compiled by a TinyCC that GCC built),
# cT = the diverse "trusted" compiler (Clang), stage1 = compile(sP, cT),
# stage2 = compile(sA, stage1). DDC passes when stage2 is bit-identical to cA.
#
# Usage:
#   ddc_tinycc.sh <workdir> <gcc-like compiler> <clang-like compiler> [extra clang flags]
# Example (the run recorded in ddc_tinycc_result.json):
#   LT=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1
#   ddc_tinycc.sh /tmp/ddc_tinycc gcc "$LT/bin/clang" "-isystem $LT/include/clang"
#
# Requires: bash, curl, tar, make, sha256sum, cmp, and two C compilers able to
# build TinyCC. Every digest printed is computed from files this script builds.
set -euo pipefail

WORK=${1:?workdir}
CC_A=${2:?first host compiler (e.g. gcc)}
CC_T=${3:?second, diverse host compiler (e.g. clang)}
CC_T_EXTRA=${4:-}

TINYCC_COMMIT=56b75101ef323cca9e45c925ba17042ce87134de
TARBALL_URL="https://codeload.github.com/TinyCC/tinycc/tar.gz/${TINYCC_COMMIT}"

rm -rf "$WORK"
mkdir -p "$WORK/out" "$WORK/bin"
cd "$WORK"

curl -sSLf --http1.1 --max-time 120 -o tinycc.tar.gz "$TARBALL_URL"
TARBALL_SHA=$(sha256sum tinycc.tar.gz | cut -d' ' -f1)

# Wrapper so that `configure` sees a plain compiler name for the second compiler.
printf '#!/bin/sh\nexec %s %s "$@"\n' "$CC_T" "$CC_T_EXTRA" > "$WORK/bin/clang"
chmod +x "$WORK/bin/clang"

# Every generation is built at the same path ($WORK/build) with the same
# command line, so build paths cannot differ between the two chains. The
# compiler used for a TinyCC-hosted generation is always reached through the
# same symlink ($WORK/cur).
build() {  # build <name> <cc command> [patch-script]
  local name=$1 cc=$2 patch=${3:-}
  rm -rf "$WORK/build"
  mkdir -p "$WORK/build"
  tar xzf "$WORK/tinycc.tar.gz" -C "$WORK/build" --strip-components=1
  if [ -n "$patch" ]; then (cd "$WORK/build" && eval "$patch"); fi
  (cd "$WORK/build" && ./configure --cc="$cc" > configure.log 2>&1 \
     && make tcc libtcc1.a > make.log 2>&1) || {
       echo "BUILD FAILED: $name" >&2; tail -20 "$WORK/build/make.log" >&2; return 1; }
  rm -rf "$WORK/out/$name"
  mkdir -p "$WORK/out/$name"
  cp "$WORK/build/tcc" "$WORK/build/libtcc1.a" "$WORK/build/config.h" \
     "$WORK/build/configure.log" "$WORK/build/make.log" "$WORK/out/$name/"
  cp -r "$WORK/build/include" "$WORK/out/$name/include"
}

use() {  # point $WORK/cur at a finished generation
  rm -f "$WORK/cur"
  ln -s "$WORK/out/$1" "$WORK/cur"
}
TCC_AS_CC="$WORK/cur/tcc -B$WORK/cur"

t0=$(date +%s)
build A1 "$CC_A"                 # TinyCC built by the first host compiler
use A1; build A2 "$TCC_AS_CC"    # cA: TinyCC built by A1
use A2; build A3 "$TCC_AS_CC"    # self-regeneration check: must equal A2
PATH="$WORK/bin:$PATH" build B1 clang   # stage1 = compile(sP, cT)
use B1; build B2 "$TCC_AS_CC"    # stage2 = compile(sA, stage1)
# Negative control: a compiler under test built from source that differs from
# the audited source by one string constant ("simulated payload").
use A1; build N2 "$TCC_AS_CC" \
  "sed -i 's/\"tcc version \"/\"tcc version (payload) \"/' tcc.c libtcc.c tcc.h 2>/dev/null; grep -l 'tcc version (payload)' *.c *.h > patched_files.txt"
t1=$(date +%s)

sha() { sha256sum "$WORK/out/$1/$2" | cut -d' ' -f1; }
same() { if cmp -s "$WORK/out/$1/$3" "$WORK/out/$2/$3"; then echo true; else echo false; fi; }

cat > "$WORK/result.json" <<EOF
{
  "subject": "TinyCC/tinycc",
  "tinycc_commit": "${TINYCC_COMMIT}",
  "tarball_sha256": "${TARBALL_SHA}",
  "tinycc_version": "$("$WORK/out/A2/tcc" -v | head -1)",
  "negative_control_banner": "$("$WORK/out/N2/tcc" -v | head -1)",
  "host": "$(uname -sm)",
  "config_os_release_lines_in_config_h": $(grep -c CONFIG_OS_RELEASE "$WORK/out/A2/config.h"),
  "host_kernel_release_string_occurrences_in_binaries": {
    "A1": $(grep -c -a -F "$(uname -r)" "$WORK/out/A1/tcc" || true),
    "A2": $(grep -c -a -F "$(uname -r)" "$WORK/out/A2/tcc" || true),
    "B1": $(grep -c -a -F "$(uname -r)" "$WORK/out/B1/tcc" || true),
    "B2": $(grep -c -a -F "$(uname -r)" "$WORK/out/B2/tcc" || true)
  },
  "compiler_A": "$($CC_A --version | head -1)",
  "compiler_T": "$($CC_T --version | head -1)",
  "wall_seconds_all_six_builds": $((t1 - t0)),
  "sha256": {
    "A1_tcc_built_by_compiler_A": "$(sha A1 tcc)",
    "B1_stage1_tcc_built_by_compiler_T": "$(sha B1 tcc)",
    "A2_cA_tcc_built_by_A1": "$(sha A2 tcc)",
    "A3_tcc_built_by_A2": "$(sha A3 tcc)",
    "B2_stage2_tcc_built_by_B1": "$(sha B2 tcc)",
    "N2_tcc_from_modified_source_built_by_A1": "$(sha N2 tcc)",
    "A2_libtcc1": "$(sha A2 libtcc1.a)",
    "B2_libtcc1": "$(sha B2 libtcc1.a)"
  },
  "bytes": {
    "A1_tcc": $(stat -c %s "$WORK/out/A1/tcc"),
    "B1_tcc": $(stat -c %s "$WORK/out/B1/tcc"),
    "A2_tcc": $(stat -c %s "$WORK/out/A2/tcc"),
    "B2_tcc": $(stat -c %s "$WORK/out/B2/tcc"),
    "N2_tcc": $(stat -c %s "$WORK/out/N2/tcc")
  },
  "checks": {
    "stage1_compilers_differ_A1_vs_B1": $( [ "$(same A1 B1 tcc)" = false ] && echo true || echo false ),
    "self_regeneration_A3_equals_A2": $(same A2 A3 tcc),
    "ddc_stage2_equals_cA_B2_vs_A2": $(same A2 B2 tcc),
    "ddc_runtime_library_equal_B2_vs_A2": $(same A2 B2 libtcc1.a),
    "negative_control_detected_B2_differs_from_N2": $( [ "$(same B2 N2 tcc)" = false ] && echo true || echo false )
  }
}
EOF
cat "$WORK/result.json"
