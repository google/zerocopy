// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Read-only function-local statics: a scalar and a lookup table whose last
// entry is implicitly zero.
unsigned long long pos_static_const(unsigned long long x) {
  static const int kRounds = 3;
  static const unsigned long long kTable[4] = {0x1, 0x8082,
                                               0x800000000000808aULL};
  for (int r = 0; r < kRounds; r++) {
    x ^= kTable[r];
  }
  return x + kTable[3];
}
