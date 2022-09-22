// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use std::path::PathBuf;

use compiletest_rs::{common::Mode, Config};

#[test]
fn ui() {
    let mut config = Config {
        // Uncomment to bless tests
        // bless: true,
        mode: Mode::Ui,
        src_base: PathBuf::from("tests/ui"),
        target_rustcflags: Some("-L target/debug -L target/debug/deps".to_string()),
        build_base: PathBuf::from("target/ui"),
        ..Default::default()
    };

    config.link_deps();
    config.clean_rmeta();

    compiletest_rs::run_tests(&config);
}
