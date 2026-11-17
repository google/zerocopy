// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Minimal safe-Rust crate exposing common `Runtime(PostCleanup)` MIR idioms:
//! `Box<[u8; 32]>` indexing (`Transmute` in 1.98 vs `BoxDerefTransmute` in 1.102),
//! `Cell::from_mut(out).as_slice_of_cells()`, `&mut dyn FnMut`, capturing closures,
//! `chunks_exact`/`zip` iterators, fieldless enum construction + discriminant switch,
//! and unchecked/unary ops.

#![allow(dead_code)]
use std::cell::Cell;

#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(i8)]
pub enum MiniStatus {
    Failed = -1,
    Done = 0,
    HasMoreOutput = 1,
}

impl MiniStatus {
    pub fn is_failure(self) -> bool {
        (self as i8) < 0
    }

    pub fn from_flag(fail: bool) -> Self {
        if fail { Self::Failed } else { Self::Done }
    }
}

pub fn read_box_array(b: &Box<[u8; 32]>, i: usize) -> u8 {
    b[i]
}

pub fn cell_apply(out: &mut [u8], src: usize, dst: usize) {
    let c = Cell::from_mut(out).as_slice_of_cells();
    c[dst].set(c[src].get());
}

pub fn dyn_cb(cb: &mut dyn FnMut(&[u8]) -> bool, s: &[u8]) -> bool {
    cb(s)
}

pub fn closure_map(a: &[u8], bias: u8) -> u8 {
    let f = |x: u8| x.wrapping_add(bias);
    f(a[0])
}

pub fn iter_zip_dot(a: &[u8], b: &[u8]) -> u32 {
    a.chunks_exact(4)
        .zip(b.chunks_exact(4))
        .map(|(x, y)| u32::from(x[0]) * u32::from(y[0]))
        .sum()
}

pub fn scalar_ops(x: u32, y: i32) -> (u32, i32) {
    (!x / 3, -y % 5)
}
