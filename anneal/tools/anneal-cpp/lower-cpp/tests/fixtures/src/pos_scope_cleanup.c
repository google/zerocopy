// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Block-scoped locals die at the end of each loop iteration, including on
// `continue` and `break`.
unsigned long long pos_scope_cleanup(const unsigned long long *in, int n) {
  unsigned long long acc = 0;
  for (int round = 0; round < n; round++) {
    unsigned long long c[5];
    for (int x = 0; x < 5; x++) {
      c[x] = in[x] ^ (unsigned long long)round;
    }
    if (c[0] == 0) continue;
    acc ^= c[0] ^ c[4];
    if (acc == 7) break;
  }
  return acc;
}
