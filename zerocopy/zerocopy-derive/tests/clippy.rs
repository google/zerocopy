// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![forbid(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::missing_inline_in_public_items,
    clippy::unwrap_used,
)]

// Regression test for https://github.com/google/zerocopy/issues/3721 and for
// generated-code lint hygiene generally. The dedicated downstream-mode Clippy
// CI step compiles this test without zerocopy's internal generated-code lint
// mode. These `forbid` settings ensure that production expansions are both
// Clippy-clean and free of generated Clippy `allow` attributes which would
// illegally try to lower the caller's lint level. The ordinary zerocopy-derive
// Clippy step compiles every integration test in internal lint mode.
use zerocopy_renamed::{Immutable, TryFromBytes};

#[derive(TryFromBytes, Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum Kind {
    A = 1,
}

#[test]
fn generated_try_from_bytes_code_is_clippy_clean() {
    let _ = Kind::A;
}
