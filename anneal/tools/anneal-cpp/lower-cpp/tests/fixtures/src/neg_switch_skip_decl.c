// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Jumping to `case 0` skips the declaration of `y`.
int neg_switch_skip_decl(int x) {
  switch (x) {
    int y;
    case 0:
      y = 42;
      return y;
  }
  return 0;
}
