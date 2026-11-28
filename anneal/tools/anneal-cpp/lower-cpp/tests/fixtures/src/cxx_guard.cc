// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// The destructor observes `x` after the return value was captured.
struct Guard {
  int* p;
  int* log;
  ~Guard() { *log = *p; }
};

int guard_return(int v, int* log) {
  int x = v;
  Guard g{&x, log};
  return (x = 42);
}
