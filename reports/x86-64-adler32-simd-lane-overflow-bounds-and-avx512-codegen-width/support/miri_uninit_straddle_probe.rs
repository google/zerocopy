// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Miri probe for `MaybeUninit<u8>` overlap-copy aliasing:
//! - Reading 8 bytes at `out_pos - dist` passes Miri when `dist >= 8`.
//! - Reading `[out_pos - 16 .. out_pos)` passes Miri when `out_pos >= 16` even for `1 <= dist < 16`.
//! - Reading 8 bytes at `out_pos - 4` straddles uninitialized tail `[out_pos .. buf.len())`
//!   and is rejected by Miri with UB (`encountered uninitialized memory`).

use core::mem::MaybeUninit;

pub unsafe fn wild_copy_8b_read(buf: &mut [MaybeUninit<u8>], out_pos: usize, dist: usize) -> u64 {
    let p = buf.as_mut_ptr();
    let val = unsafe { (p.add(out_pos - dist) as *const u64).read_unaligned() };
    unsafe { (p.add(out_pos) as *mut u64).write_unaligned(val) };
    val
}

pub unsafe fn period_copy_16b_before_pos(buf: &mut [MaybeUninit<u8>], out_pos: usize, dist: usize) {
    assert!(out_pos >= 16 && (1..16).contains(&dist) && out_pos + 16 <= buf.len());
    let p = buf.as_mut_ptr().cast::<u8>();
    let mut win = [0u8; 16];
    unsafe { core::ptr::copy_nonoverlapping(p.add(out_pos - 16), win.as_mut_ptr(), 16) };
    let mut out16 = [0u8; 16];
    let start = 16 - dist;
    for (i, slot) in out16.iter_mut().enumerate() {
        *slot = win[start + (i % dist)];
    }
    unsafe { core::ptr::copy_nonoverlapping(out16.as_ptr(), p.add(out_pos), 16) };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ok_dist8_initialized() {
        let mut buf = [MaybeUninit::uninit(); 64];
        for (i, slot) in buf[..12].iter_mut().enumerate() {
            slot.write(i as u8);
        }
        unsafe { wild_copy_8b_read(&mut buf, 12, 8) };
        assert_eq!(unsafe { buf[12].assume_init() }, 4);
    }

    #[test]
    fn ok_period_16b_dist3() {
        let mut buf = [MaybeUninit::uninit(); 64];
        for (i, slot) in buf[..16].iter_mut().enumerate() {
            slot.write((i % 3 + 10) as u8);
        }
        unsafe { period_copy_16b_before_pos(&mut buf, 16, 3) };
        assert_eq!(unsafe { buf[16].assume_init() }, 11);
    }

    #[test]
    #[ignore]
    fn ub_dist4_straddles_uninit() {
        let mut buf = [MaybeUninit::uninit(); 64];
        for (i, slot) in buf[..12].iter_mut().enumerate() {
            slot.write(i as u8);
        }
        let x = unsafe { wild_copy_8b_read(&mut buf, 12, 4) };
        assert_eq!(x & 0xFFFF_FFFF, 0x0b0a_0908);
    }
}
