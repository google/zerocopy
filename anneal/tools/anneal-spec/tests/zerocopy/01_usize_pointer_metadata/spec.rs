// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Specifies `<usize as PointerMetadata>::{from_elem_count, to_elem_count}`
// (`zerocopy/src/lib.rs`): for slice DSTs the pointer metadata is the element
// count itself, so both conversions are the identity on every `usize`.
anneal::external_spec! {
    impl PointerMetadata for usize {
        #[anneal::spec(total, ensures(|ret| ret == elems))]
        fn from_elem_count(elems: usize) -> Self;

        #[anneal::spec(total, ensures(|count| count == self))]
        fn to_elem_count(self) -> usize;
    }
}
