// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

pub fn correlated_diamond(flag: bool) -> u32 {
    let x: u32 = if flag { 1 } else { 2 };
    if x == 1 { 10 } else { 20 }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn custom_jt_preserves_join_prefix(a: u32, cond: bool) -> u32 {
    mir! {
        let tag: u32;
        let acc: u32;
        {
            acc = 0_u32;
            match cond {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = {
            tag = 1_u32;
            Goto(bb3)
        }
        bb2 = {
            tag = 2_u32;
            Goto(bb3)
        }
        bb3 = {
            acc = a + 5_u32;
            match tag {
                1 => bb4,
                _ => bb5,
            }
        }
        bb4 = {
            RET = acc + 100_u32;
            Return()
        }
        bb5 = {
            RET = acc + 200_u32;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn custom_read_after_move_scalar() -> u32 {
    mir! {
        let x: u32;
        let y: u32;
        {
            x = 7_u32;
            y = Move(x);
            RET = x + y;
            Return()
        }
    }
}

fn main() {
    assert_eq!(correlated_diamond(true), 10);
    assert_eq!(correlated_diamond(false), 20);
    assert_eq!(custom_jt_preserves_join_prefix(10, true), 115);
    assert_eq!(custom_jt_preserves_join_prefix(10, false), 215);
    let ram = custom_read_after_move_scalar();
    println!("DIAMOND_OK JT_PREFIX_OK READ_AFTER_MOVE={ram}");
}
