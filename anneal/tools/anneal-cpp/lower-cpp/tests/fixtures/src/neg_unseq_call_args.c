// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// C11 6.5.2.2p10 + 6.5p2: unsequenced increments of `x` in call arguments.
int sink(int a, int b);
int neg_unseq_call_args(int x) { return sink(++x, ++x); }
