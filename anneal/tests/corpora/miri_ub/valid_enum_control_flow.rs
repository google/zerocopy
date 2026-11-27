// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[repr(u8)]
enum Step {
    First = 1,
    Second = 2,
    Third = 3,
}

const CURRENT: Step = Step::Second;

fn main() {
    let acc: i32 = match CURRENT {
        Step::First => 10,
        Step::Second => 20,
        Step::Third => 30,
    };
    let _ = acc ^ 5;
}
