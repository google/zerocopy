// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use testutil::set_rustflags_w_warnings;

#[test]
#[cfg_attr(miri, ignore)]
fn ui() {
    let version = testutil::ToolchainVersion::extract_from_pwd().unwrap();
    // See the doc comment on this method for an explanation of what this does
    // and why we store source files in different directories.
    let source_files_dirname = version.get_ui_source_files_dirname_and_maybe_print_warning();

    // Set `-Wwarnings` in the `RUSTFLAGS` environment variable to ensure that
    // `.stderr` files reflect what the typical user would encounter.
    set_rustflags_w_warnings();

    let t = trybuild::TestCases::new();
    t.compile_fail(format!("tests/{}/*.rs", source_files_dirname));
}
