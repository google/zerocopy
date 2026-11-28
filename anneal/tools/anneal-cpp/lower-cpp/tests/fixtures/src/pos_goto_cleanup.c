// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// An error exit through `goto` leaves a loop body: the locals of the scopes
// it leaves die on the way out.
int pos_goto_cleanup(int n) {
  int status = 0;
  for (int i = 0; i < n; i++) {
    int buf[2];
    buf[0] = i;
    if (buf[0] == 3) {
      status = 1;
      goto cleanup;
    }
  }
cleanup:
  return status;
}
