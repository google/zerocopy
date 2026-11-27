// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Specifies `<() as PointerMetadata>::{from_elem_count, to_elem_count}`
// (`zerocopy/src/lib.rs`): sized types carry no metadata, so any element
// count maps to `()` and `()` reports zero elements.
anneal::external_spec! {
    impl PointerMetadata for () {
        #[anneal::spec(total, ensures(|ret| ret == ()))]
        fn from_elem_count(_elems: usize) -> Self;

        #[anneal::spec(total, ensures(|count| count == 0))]
        fn to_elem_count(self) -> usize;
    }
}
