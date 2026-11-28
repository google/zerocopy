// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Expressions with exactly one side effect per scalar per full expression.
#include <stddef.h>
#include <stdint.h>

unsigned pos_ssenf_ok(unsigned x, const uint8_t *buf, unsigned *p, size_t i,
                      size_t len) {
  unsigned s1 = 0;
  x = x + 1;
  x += 1;
  ++x;
  s1 += *buf++;
  p[i] = p[i] + 1;
  while (len > 0) {
    s1 += x;
    len--;
  }
  return s1;
}
