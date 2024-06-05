// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::env;

const RUSTFLAGS: &str = "RUSTFLAGS";
const WARN_LINT_GROUP: &str = "-Wwarnings";

#[test]
#[cfg_attr(miri, ignore)]
fn ui() {
    let version = testutil::ToolchainVersion::extract_from_pwd().unwrap();
    // See the doc comment on this method for an explanation of what this does
    // and why we store source files in different directories.
    let source_files_dirname = version.get_ui_source_files_dirname_and_maybe_print_warning();

    assert!(
        has_warnings_in_rustflags(),
        "skipping {} tests. `{}` was not passed into {}.",
        source_files_dirname,
        WARN_LINT_GROUP,
        RUSTFLAGS
    );

    let t = trybuild::TestCases::new();
    t.compile_fail(format!("tests/{}/*.rs", source_files_dirname));
}

fn has_warnings_in_rustflags() -> bool {
    let rustflags = match env::var(RUSTFLAGS) {
        Ok(flags) => flags.chars().filter(|c| !c.is_whitespace()).collect(),
        Err(_) => String::new(),
    };
    rustflags.contains(WARN_LINT_GROUP)
}
