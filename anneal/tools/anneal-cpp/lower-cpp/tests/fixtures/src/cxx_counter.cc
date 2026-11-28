// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

struct Counter {
  int n;
  Counter() : n(0) {}
  void add(int k) { n = n + k; }
  int get() const { return n; }
};

int counter_sum(int a, int b) {
  Counter c;
  c.add(a);
  c.add(b);
  return c.get();
}
