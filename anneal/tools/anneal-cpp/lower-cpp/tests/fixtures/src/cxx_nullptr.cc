// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `std::nullptr_t` parameters and locals (spelled without headers).
using nullptr_t = decltype(nullptr);

struct V {
  int *p;
  explicit V(nullptr_t) : p(nullptr) {}
  void Set(nullptr_t n) { p = n; }
};

int nullptr_use(int *q) {
  V v(nullptr);
  v.Set(nullptr);
  nullptr_t z = nullptr;
  return (v.p == z) + (q != nullptr);
}
