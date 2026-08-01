// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use testutil::UiTestRunner;

#[test]
// Keep this predicate synchronized with `tests/ui.rs`. UI fixtures spawn
// external compiler processes, which Miri and source coverage must not run.
// Diagnostic snapshots exist only for the pinned toolchains; cargo-zerocopy
// emits the final cfg only for those semantic descriptors.
#[cfg_attr(
    any(miri, coverage_nightly, not(__ZEROCOPY_INTERNAL_USE_ONLY_UI_TEST_TOOLCHAIN)),
    ignore
)]
fn ui() {
    // This tests the behavior when `--cfg zerocopy_derive_union_into_bytes` is
    // present.
    UiTestRunner::new()
        .rustc_arg("--cfg=zerocopy_derive_union_into_bytes")
        .rustc_arg("--cfg=zerocopy_unstable_linux")
        .rustc_arg("-Wwarnings") // To ensure .stderr files reflect typical user encounter
        .run();

    // This tests the behavior when various `--cfg` flags are not present.
    UiTestRunner::new()
        .subdir("cfgs")
        .rustc_arg("-Wwarnings") // To ensure .stderr files reflect typical user encounter
        .run();
}
