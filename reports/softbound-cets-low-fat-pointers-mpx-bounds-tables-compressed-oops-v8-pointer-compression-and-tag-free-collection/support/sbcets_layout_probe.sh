#!/usr/bin/env bash
# Check, with the C compiler, the metadata-entry size declared by the
# SoftBound+CETS runtime header at the pinned revision.
# Requires: bash, curl, gcc (LP64 Linux). Nothing is executed except the compiler.
set -euo pipefail
REV=9a9c09f04e16f2d1ef3a906fd138a7b89df44996
WORK="${WORK:-/tmp/sbcets_probe}"; mkdir -p "$WORK"; cd "$WORK"
curl -sSL "https://raw.githubusercontent.com/santoshn/softboundcets-34/$REV/softboundcets-lib/softboundcets.h" -o softboundcets.h
sha256sum softboundcets.h
cat > layout.c <<'C'
#include <stddef.h>
#include "softboundcets.h"
_Static_assert(sizeof(__softboundcets_trie_entry_t) == 32, "entry is 32 bytes (base, bound, key, lock)");
_Static_assert(__SOFTBOUNDCETS_METADATA_NUM_FIELDS == 4, "four metadata fields");
C
# The runtime Makefile builds the library with -D__SOFTBOUNDCETS_SPATIAL_TEMPORAL.
# GCC rejects always_inline on weak functions; inlining is irrelevant to these assertions.
gcc -w -fsyntax-only -D__always_inline__=__noinline__ -D__SOFTBOUNDCETS_SPATIAL_TEMPORAL layout.c \
  && echo "SPATIAL_TEMPORAL: static assertions hold: sizeof(__softboundcets_trie_entry_t) == 32, __SOFTBOUNDCETS_METADATA_NUM_FIELDS == 4"
# Single-component configurations, checked without the always_inline workaround:
for mode in __SOFTBOUNDCETS_SPATIAL __SOFTBOUNDCETS_TEMPORAL; do
  if gcc -w -fsyntax-only -D$mode layout.c 2>err_$mode.txt; then echo "-D$mode compiles"; else
    echo "-D$mode does not compile: $(grep -m1 -o "softboundcets.h:[0-9]*:[0-9]*: error: too many arguments to function[^;]*" err_$mode.txt)"; fi
done
gcc --version | head -1
