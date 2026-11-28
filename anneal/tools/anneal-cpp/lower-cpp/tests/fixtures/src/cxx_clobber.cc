// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// The destructor clobbers `x` after the return value was captured, so the
// caller must observe the old value (return-slot normalization).
struct Clobber {
  int* p;
  ~Clobber() { *p = 99; }
};

int clobber_return(int v) {
  int x = v;
  Clobber c{&x};
  return x;
}
