// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Structured and unstructured control flow plus short-circuit operators.
int pos_control_flow(int n, const unsigned char *s) {
  int acc = 0;
  for (int i = 0; i < n; i++) {
    if (s[i] == 0) break;
    if (s[i] == 1 || (s[i] == 2 && n > 3)) continue;
    acc += s[i] > 100 ? 1 : -1;
  }
  do {
    acc--;
  } while (acc > 1000 && !(acc & 1));
  switch (acc & 3) {
    case 0:
      acc = 7;
      break;
    case 1:
      acc++;
      /* fallthrough */
    case 2:
      acc += 2;
      break;
    default:
      goto out;
  }
  acc *= 2;
out:
  return acc;
}
