// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Specifies `layout::add_scaled_metadata` (`zerocopy/src/layout.rs`), the
// `unsafe fn` computing the affine metadata map `base + metadata * multiple`.
// Its safety contract, which its Kani contract also states, is that the
// mathematical result is at most `usize::MAX`; under it the call returns
// exactly that result.
anneal::external_spec! {
    mod layout {
        #[anneal::spec(
            total,
            requires(math(base) + math(metadata) * math(multiple)
                <= 18446744073709551615),
            ensures(|ret| math(ret) == math(base) + math(metadata) * math(multiple)),
        )]
        unsafe fn add_scaled_metadata(base: usize, metadata: usize, multiple: usize) -> usize;
    }
}
