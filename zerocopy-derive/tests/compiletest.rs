// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use std::path::PathBuf;

use compiletest_rs::{common::Mode, Config};

#[test]
fn ui() {
    let mut config = Config {
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

// extern crate compiletest_rs as compiletest;

// use std::path::PathBuf;

// fn run_mode(mode: &'static str) {
//     let mut config = compiletest::Config::default();

//     config.filter = std::env::var("COMPILETEST_FILTER").ok();
//     config.mode = mode.parse().expect("Invalid mode");
//     config.src_base = PathBuf::from(format!("tests/{}", mode));
//     config.target_rustcflags = Some("-L target/debug -L target/debug/deps".to_string());
//     config.link_deps(); // Populate config.target_rustcflags with dependencies on the path
//     config.clean_rmeta(); // If your tests import the parent crate, this helps with E0464

//     compiletest::run_tests(&config);
// }

// #[test]
// fn compile_error() {
//     run_mode("compile-fail");
// }
