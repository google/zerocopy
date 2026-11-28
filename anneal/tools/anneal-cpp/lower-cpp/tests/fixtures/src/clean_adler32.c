// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Clean-room Adler-32 (RFC 1950 section 8.2) used as the Rung-0 canary.
//
// `CLEAN_ADLER_NMAX` is the largest n such that
// 255 * n * (n + 1) / 2 + (n + 1) * (CLEAN_ADLER_MOD - 1) <= 2^32 - 1, so
// neither 32-bit accumulator can wrap before the deferred reduction.

#include <stddef.h>
#include <stdint.h>

#define CLEAN_ADLER_MOD 65521u
#define CLEAN_ADLER_NMAX 5552u

uint32_t clean_adler32_update(uint32_t adler, const uint8_t *buf, size_t len) {
  uint32_t s1 = adler & 0xffffu;
  uint32_t s2 = (adler >> 16) & 0xffffu;
  while (len > 0) {
    size_t chunk = len < CLEAN_ADLER_NMAX ? len : CLEAN_ADLER_NMAX;
    len -= chunk;
    while (chunk > 0) {
      s1 += *buf++;
      s2 += s1;
      chunk--;
    }
    s1 %= CLEAN_ADLER_MOD;
    s2 %= CLEAN_ADLER_MOD;
  }
  return (s2 << 16) | s1;
}
