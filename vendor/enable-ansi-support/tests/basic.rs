// Copyright (c) The enable-ansi-support Contributors
// SPDX-License-Identifier: MIT

#[test]
fn test_basic() {
    let res = enable_ansi_support::enable_ansi_support();
    println!("enable_ansi_support status: {:?}", res);
    if res.is_ok() {
        println!("\x1b[31mHello, world\x1b[0m");
    }
}
