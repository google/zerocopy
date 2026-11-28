// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Struct member access through pointers and a call to a defined helper.
#include <stdint.h>

struct pair {
  uint32_t lo;
  uint16_t hi;
};

static uint32_t mix(uint32_t a, uint32_t b) { return (a << 5) ^ b; }

uint32_t pos_struct_ptr(struct pair *p, const struct pair *q) {
  p->lo = mix(q->lo, (uint32_t)q->hi);
  p->hi = (uint16_t)(p->lo >> 16);
  return p->lo;
}
