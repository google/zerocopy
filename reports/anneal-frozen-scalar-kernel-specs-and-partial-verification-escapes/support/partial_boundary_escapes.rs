// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Runnable Rust + Miri demonstration of partial-verification boundary escapes:
//! 1. Literal-prefixed wild-copy overshoot (`4 + 288 = 292 > 290` guard) when a
//!    scalar guard omits fused literal bytes or physical slice coupling (`out_max`
//!    vs. `dst.len()`).
//! 2. Wrapping ring-buffer clobbering (`wildOvershoot` overwriting valid history
//!    entries at distances `> R - W`).
//! 3. `MaybeUninit<u8>` 8-byte lookback UB for `dist = 4 < 8` vs. sound `dist >= 8`
//!    and valid initialized prefix copies.

use core::mem::MaybeUninit;

/// Simulates a 4-byte literal prefix followed by a 32-byte-stride wild splat
/// of `match_len` bytes (`dist == 1`). Touches `4 + ceil(match_len / 32) * 32`
/// bytes past `out_pos`: for `match_len = 258`, touches `4 + 288 = 292` bytes,
/// escaping a `>= 290` guard if `dst.len() - out_pos < 292`.
pub fn wild_splat_after_double_lit(
    dst: &mut [u8],
    out_pos: usize,
    lit4: [u8; 4],
    match_len: usize,
) -> Result<usize, usize> {
    let touched = lit4.len() + ((match_len + 31) / 32) * 32;
    if out_pos + touched > dst.len() {
        return Err(out_pos + touched - dst.len());
    }
    dst[out_pos..out_pos + 4].copy_from_slice(&lit4);
    let fill = lit4[3];
    let mut off = out_pos + 4;
    let end = off + match_len;
    while off < end {
        dst[off..off + 32].fill(fill);
        off += 32;
    }
    Ok(out_pos + 4 + match_len)
}

/// 8-byte-stride wild copy into a cyclic ring buffer of length `R`, clobbering
/// history at distances in `(R - 8, R]`.
pub fn ring_wild_copy(ring: &mut [u8], head: usize, dist: usize, match_len: usize) {
    let rlen = ring.len();
    let total = ((match_len + 7) / 8) * 8;
    for k in 0..total {
        let src_idx = (head + k + rlen - dist) % rlen;
        let dst_idx = (head + k) % rlen;
        ring[dst_idx] = ring[src_idx];
    }
}

/// Unaligned 8-byte lookback into a buffer whose initialized live prefix is
/// `[0..out_pos)`. Reading at `out_pos - dist` straddles uninitialized bytes
/// in `[out_pos..buf.len())` whenever `dist < 8`.
pub unsafe fn wild_copy_8b_read(buf: &mut [MaybeUninit<u8>], out_pos: usize, dist: usize) -> u64 {
    let p = buf.as_mut_ptr();
    let val = unsafe { (p.add(out_pos - dist) as *const u64).read_unaligned() };
    unsafe { (p.add(out_pos) as *mut u64).write_unaligned(val) };
    val
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_prefixed_292_escapes_290_guard() {
        let mut guard_only_buf = vec![0u8; 290];
        let err = wild_splat_after_double_lit(&mut guard_only_buf, 0, [1, 2, 3, 4], 258);
        assert_eq!(err, Err(2));

        let mut slack_304_buf = vec![0u8; 304];
        let ok = wild_splat_after_double_lit(&mut slack_304_buf, 0, [1, 2, 3, 4], 258);
        assert_eq!(ok, Ok(262));
    }

    #[test]
    fn wrapping_ring_clobbers_max_distance() {
        let mut ring: Vec<u8> = (0..16u8).collect();
        ring_wild_copy(&mut ring, 0, 8, 3);
        // After writing 3 bytes, new head is 3, so byte at index 3 is distance 16.
        // An exact 3-byte copy leaves ring[3] == 3; 8-byte wild copy clobbers it to 11.
        assert_eq!(ring[3], 11);
    }

    #[test]
    fn ok_dist8_initialized_lookback() {
        let mut buf = [MaybeUninit::uninit(); 64];
        for i in 0..12 {
            buf[i].write(i as u8);
        }
        let v = unsafe { wild_copy_8b_read(&mut buf, 12, 8) };
        assert_eq!(v & 0xFF, 4);
        assert_eq!(unsafe { buf[12].assume_init() }, 4);
    }
}
