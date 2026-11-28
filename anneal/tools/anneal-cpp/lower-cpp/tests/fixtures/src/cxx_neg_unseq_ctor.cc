// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

struct Foo {
  int a;
  int b;
  Foo(int x, int y) : a(x), b(y) {}
};

int unseq_ctor(int x) {
  Foo f(++x, ++x);
  return f.a;
}
