// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// C11 6.5.8p6 / 6.5.9p3: relational and equality operators yield `int`, so
// comparisons may feed arithmetic, `^`, and scalar returns.
int pos_cmp_int(int a, int b, const int *p, const int *q) {
  int sign = (a < 0) ^ (b < 0);
  int sum = (a <= b) + (p != q);
  if (a > b) sum += 2;
  return sign + sum + (a == b);
}
