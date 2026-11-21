// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]

pub struct U64Range {
    pub min: u64,
    pub max: u64,
}

impl U64Range {
    pub const fn new(min: u64, max: u64) -> Self {
        Self { min, max }
    }

    pub const fn max() -> Self {
        Self::new(0, u64::MAX)
    }

    pub fn add_range(self, rhs: Self) -> Self {
        let (min, min_overflowed) = self.min.overflowing_add(rhs.min);
        let (max, max_overflowed) = self.max.overflowing_add(rhs.max);
        if min_overflowed != max_overflowed {
            Self::max()
        } else {
            Self { min, max }
        }
    }

    pub fn mul_range(self, rhs: Self) -> Self {
        let Some(min) = self.min.checked_mul(rhs.min) else {
            return Self::max();
        };
        let Some(max) = self.max.checked_mul(rhs.max) else {
            return Self::max();
        };
        Self { min, max }
    }
}
