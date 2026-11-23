// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Specifies `util::macros::__unsafe` (`zerocopy/src/util/macros.rs`), the
// empty `const unsafe fn` that macro expansions call to force their caller
// into an `unsafe` block. It has no safety precondition and always returns.
anneal::external_spec! {
    mod util::macros {
        #[anneal::spec(total, ensures(|ret| ret == ()))]
        unsafe fn __unsafe();
    }
}
