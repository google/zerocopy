// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Brace initializers and compound literals for a local struct and array,
// including omitted (value-initialized) trailing elements.
typedef struct {
  int num;
  int den;
} ratio;

int pos_init_list(int n, int d, int *out_num, int *out_den) {
  ratio a = {0, 1}, b = {1, 0};
  unsigned char bytes[8] = {1, 2};
  for (int i = 0; i < 2; i++) {
    ratio next = (ratio){a.num + n, b.den + d};
    a = b;
    b = next;
  }
  b = (ratio){b.num * 2, b.den};
  *out_num = b.num;
  *out_den = b.den;
  return bytes[0] + bytes[7] + (b.den == 0);
}
