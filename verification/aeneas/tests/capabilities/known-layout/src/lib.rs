// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy::{DstLayout, KnownLayout};

pub fn layout<T: ?Sized + KnownLayout<PointerMetadata = usize>>() -> DstLayout {
    T::LAYOUT
}

pub fn slice_u32_layout() -> DstLayout {
    layout::<[u32]>()
}

pub fn layout_unconstrained<T: KnownLayout>() -> DstLayout {
    T::LAYOUT
}

pub fn slice_u32_layout_direct() -> DstLayout {
    <[u32] as KnownLayout>::LAYOUT
}
