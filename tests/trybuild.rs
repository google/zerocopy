// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// UI tests depend on the exact error messages emitted by rustc, but those error
// messages are not stable, and sometimes change between Rust versions. Thus, we
// maintain one set of UI tests for each Rust version that we test in CI, and we
// pin to specific versions in CI (a specific stable version, a specific date of
// the nightly compiler, and a specific MSRV). Updating those pinned versions
// may also require updating these tests.
// - `tests/ui-nightly` - Contains the source of truth for our UI test source
//   files (`.rs`), and contains `.err` and `.out` files for nightly
// - `tests/ui-stable` - Contains symlinks to the `.rs` files in
//   `tests/ui-nightly`, and contains `.err` and `.out` files for stable
// - `tests/ui-msrv` - Contains symlinks to the `.rs` files in
//   `tests/ui-nightly`, and contains `.err` and `.out` files for MSRV

#[rustversion::nightly]
const SOURCE_FILES_DIR: &str = "tests/ui-nightly";
#[rustversion::stable(1.69.0)]
const SOURCE_FILES_DIR: &str = "tests/ui-stable";
#[rustversion::stable(1.61.0)]
const SOURCE_FILES_DIR: &str = "tests/ui-msrv";

#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.compile_fail(format!("{SOURCE_FILES_DIR}/*.rs"));
}

// The file `invalid-impls.rs` directly includes `src/macros.rs` in order to
// test the `impl_or_verify!` macro which is defined in that file. Specifically,
// it tests the verification portion of that macro, which is enabled when
// `cfg(any(feature = "derive", test))`. While `--cfg test` is of course passed
// to the code in the file you're reading right now, `trybuild` does not pass
// `--cfg test` when it invokes Cargo. As a result, this `trybuild` test only
// tests the correct behavior when the "derive" feature is enabled.
#[cfg(feature = "derive")]
#[test]
fn ui_invalid_impls() {
    let t = trybuild::TestCases::new();
    t.compile_fail(format!("{SOURCE_FILES_DIR}/invalid-impls/*.rs"));
}
