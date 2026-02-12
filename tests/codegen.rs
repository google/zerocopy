// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//#![cfg(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS)]

use std::{fs::OpenOptions, io::{self, Read, Write}, path::PathBuf, process::{Command, ExitStatus}};

fn run_codegen_test(bench_name: &str, target_cpu: &str, bless: bool) {
    let manifest_path = env!("CARGO_MANIFEST_PATH");
    let target_dir = env!("CARGO_TARGET_DIR");

    let output = Command::new("cargo")
        .args([
            "asm",
            "-p", "zerocopy",
            "--manifest-path", manifest_path,
            "--target-dir", target_dir,
            "--bench", bench_name,
            "--target-cpu", target_cpu,
            "--mca",
            "codegen_test"
        ]).output()
        .expect("failed to execute process");

    let actual_result= output.stdout;

    if !(output.status.success()) {
        panic!("{}", String::from_utf8_lossy(&output.stderr));
    }

    let expected_file_path = {
        let mut path: PathBuf = env!("CARGO_MANIFEST_DIR").into();
        path.push("benches");
        let file_name = format!("{bench_name}.{target_cpu}.mca");
        path.push(file_name);
        path
    };

    let mut expected_file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .append(false)
        .truncate(true)
        .open(expected_file_path)
        .unwrap();
    
    let expected_result = {
        let mut buf = Vec::new();
        expected_file.read_to_end(&mut buf).unwrap();
        buf
    };
        
    if bless {
        expected_file.write_all(&actual_result).unwrap();
    } else {
        if actual_result == expected_result {
            ; // Success
        } else {
            panic!("Bless codegen tests with BLESS=1");
        }
    }

}

#[test]
#[cfg_attr(miri, ignore)]
fn test() {
    let bless = std::env::var("BLESS").ok().filter(|s| s == "1").is_some();
    let paths = std::fs::read_dir("benches").unwrap();
    for path in paths {
        let path = path.unwrap().path();
        if !path.extension().map(|s| s == "rs").unwrap_or(false) {
            continue;
        }
        let path = path.file_stem().unwrap().to_str().unwrap();
        run_codegen_test(&path, "icelake-server", bless);
    }
}
