// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// UI tests depend on the exact error messages emitted by rustc, but those error
// messages are not stable, and sometimes change between Rust versions. Thus, we
// maintain one set of UI tests for each Rust version that we test in CI, and we
// pin to specific versions in CI (a specific stable version, a specific date of
// the nightly compiler, and a specific MSRV). Updating those pinned versions
// may also require updating these tests.
// - `tests/ui` - Contains the source of truth for our UI test source files
//   (`.rs`), and contains `.err` and `.out` files for nightly and beta
// - `tests/ui-stable` - Contains symlinks to the `.rs` files in `tests/ui`, and
//   contains `.err` and `.out` files for stable
// - `tests/ui-msrv` - Contains symlinks to the `.rs` files in `tests/ui`, and
//   contains `.err` and `.out` files for MSRV

#[rustversion::any(nightly, beta)]
const SOURCE_FILES_GLOB: &str = "tests/ui/*.rs";
#[rustversion::all(stable, not(stable(1.56.1)))]
const SOURCE_FILES_GLOB: &str = "tests/ui-stable/*.rs";
#[rustversion::stable(1.56.1)]
const SOURCE_FILES_GLOB: &str = "tests/ui-msrv/*.rs";

#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.compile_fail(SOURCE_FILES_GLOB);
}
