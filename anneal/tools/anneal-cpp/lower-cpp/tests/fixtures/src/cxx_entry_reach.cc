// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// A deduction guide (never called, cannot be mangled), a scoped enumeration
// constant, disabled-assertion `void()` statements, and a sibling function
// the entry never calls that uses an unsupported construct.
template <typename T>
struct Box {
  T v;
  Box(T x) : v(x) {}
};
template <typename T>
Box(T) -> Box<T>;

enum class Kind { kOne = 1, kThree = 3 };

inline void check(int x) {
  (false ? static_cast<void>(x) : void());
  void();
}

int unreachable_sibling(int x) {
  while (int y = x) {
    return y;
  }
  return 0;
}

int entry_reach(int x) {
  Box b(x);
  check(x);
  return b.v + static_cast<int>(Kind::kThree);
}
