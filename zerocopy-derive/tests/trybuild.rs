// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#[test]
#[cfg_attr(miri, ignore)]
fn ui() {
    let version = testutil::ToolchainVersion::extract_from_pwd().unwrap();
    // See the doc comment on this method for an explanation of what this does
    // and why we store source files in different directories.
    let source_files_dirname = version.get_ui_source_files_dirname_and_maybe_print_warning();

    let t = trybuild::TestCases::new();
    t.compile_fail(format!("tests/{source_files_dirname}/*.rs"));
}
