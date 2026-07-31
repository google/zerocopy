// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Many of our UI tests require the "derive" feature to function properly. In
// particular:
// - Some tests directly include `zerocopy-derive/tests/include.rs`, which
//   derives traits on the `AU16` type.
// - The file `invalid-impls.rs` directly includes `src/util/macros.rs` in order
//   to test the `impl_or_verify!` macro which is defined in that file.
//   Specifically, it tests the verification portion of that macro, which is
//   enabled when `cfg(any(feature = "derive", test))`. While `--cfg test` is of
//   course passed to the code in the file you're reading right now, `trybuild`
//   does not pass `--cfg test` when it invokes Cargo. As a result, this
//   `trybuild` test only tests the correct behavior when the "derive" feature
//   is enabled.
//
// Cargo.toml therefore declares `derive` as this target's required feature.
// Keep that as the sole whole-target gate: a second cfg here could drift and
// let Cargo report a successful test executable containing zero tests.

use testutil::UiTestRunner;

#[test]
// UI fixtures spawn external compiler processes, so Miri and source coverage
// must not execute them. Ignoring coverage here lets CI use an unfiltered
// default `cargo test` without attributing the subprocess's code to the test
// process. Diagnostic snapshots exist only for the three pinned toolchains;
// cargo-zerocopy emits the final cfg only for those semantic descriptors.
#[cfg_attr(
    any(miri, coverage_nightly, not(__ZEROCOPY_INTERNAL_USE_ONLY_UI_TEST_TOOLCHAIN)),
    ignore
)]
fn test_ui() {
    UiTestRunner::new()
        .rustc_arg("-Wwarnings") // To reflect typical user experience in stderr
        .run();
}
