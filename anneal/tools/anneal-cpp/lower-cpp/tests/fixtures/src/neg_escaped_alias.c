// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `x` is address-taken, so `*q = 1` may write it: unsequenced with the read.
int neg_escaped_alias(void) {
  int x = 0;
  int *q = &x;
  return x + (*q = 1);
}
