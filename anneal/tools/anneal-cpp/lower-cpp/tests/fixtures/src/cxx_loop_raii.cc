// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

struct Guard2 {
  int* c;
  ~Guard2() { *c = *c + 1; }
};

int loop_raii(int n, int* c) {
  for (int i = 0; i < n; ++i) {
    Guard2 g{c};
    if (i == 3) break;
  }
  return *c;
}
