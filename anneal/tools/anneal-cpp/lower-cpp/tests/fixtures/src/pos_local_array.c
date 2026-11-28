// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Indexing a local array is not an escape of its address.
int pos_local_array(int n) {
  int acc = 0;
  for (int k = 0; k < 2; k++) {
    int a[4];
    a[0] = n;
    a[1] = a[0] + 1;
    acc += a[1];
  }
  return acc;
}
