// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Specifies `<usize as PointerMetadata>::{from_elem_count, to_elem_count}`
// (`zerocopy/src/lib.rs`) with tight MIR small-step bounds (`max_steps = 2`):
// each body executes one `Copy` assignment step and one `Return` step.
anneal::external_spec! {
    impl PointerMetadata for usize {
        #[anneal::spec(terminates, no_panic, max_steps = 2, ensures(|ret| ret == elems))]
        fn from_elem_count(elems: usize) -> Self;

        #[anneal::spec(terminates, no_panic, max_steps = 2, ensures(|count| count == self))]
        fn to_elem_count(self) -> usize;
    }
}
