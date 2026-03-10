// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![cfg(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS)]

use std::{
    panic,
    path::PathBuf,
    process::Command,
    sync::{Arc, Mutex},
    thread,
};

enum Directive {
    Asm,
    Mca,
}

impl Directive {
    fn arg(&self) -> &'static str {
        match self {
            Directive::Asm => "--asm",
            Directive::Mca => "--mca",
        }
    }

    fn ext(&self) -> &'static str {
        match self {
            Directive::Asm => "",
            Directive::Mca => ".mca",
        }
    }
}

/// A configuration for an instruction set architecture (ISA) being tested.
///
/// We define an explicit structure to represent this because not all target ISAs
/// support `llvm-mca`. Generic CPUs (like `cortex-m3` or `generic-rv32`) lack
/// pipeline scheduling models upstream in LLVM, causing `--mca` extraction to
/// abort. Thus, `llvm-mca` generation is conditionally evaluated based upon
/// `supports_mca`.
#[derive(Clone)]
struct IsaConfig {
    target_triple: Option<&'static str>,
    target_cpu: &'static str,
    supports_mca: bool,
}

fn run_codegen_test(bench_name: &str, config: &IsaConfig, bless: bool) {
    let target_cpu = config.target_cpu;
    println!("Testing {bench_name}.{target_cpu}");

    // We isolate the `cargo-show-asm` target directories to avoid workspace
    // `Cargo.lock` contention. Generating artifacts that overlap standard
    // `target/...` directories triggers lock blocks when testing concurrently.
    // Statically mapping the build execution uniquely to the OS temporary
    // directory circumvents Cargo's recursive lock boundary logic.
    let mut inner_target_dir = std::env::temp_dir();
    inner_target_dir.push(format!("codegen_benches_{}_{}", target_cpu, bench_name));

    let cargo_asm = |directive: &Directive| {
        let mut args = vec![
            "asm",
            "--quiet",
            "-p",
            "codegen-benches",
            "--manifest-path",
            "tools/codegen-benches/Cargo.toml",
            "--lib",
        ];
        if let Some(triple) = config.target_triple {
            args.extend(["--target", triple]);
        }
        args.extend(["--target-cpu", config.target_cpu, "--simplify", directive.arg()]);
        let bench_name_arg = format!("bench_{bench_name}");
        args.push(&bench_name_arg);
        args.push("0");

        // The outer `cargo test` explicitly injects `CARGO_MAKEFLAGS` to
        // configure POSIX pipeline jobserver logic for threaded runs. We strip
        // this environment variable to prevent child `cargo-show-asm` pipelines
        // from attempting to read file descriptor tokens from the active outer
        // testing pipe, which causes immediate "os error 2" read failures from
        // the host system.
        Command::new("cargo")
            .env_remove("CARGO_MAKEFLAGS")
            .env("CARGO_PROFILE_RELEASE_PANIC", "abort")
            .env("CARGO_TARGET_DIR", &inner_target_dir)
            .args(&args)
            .output()
            .expect("failed to execute process")
    };

    let test_directive = |directive: Directive| {
        let output = cargo_asm(&directive);
        let actual_result = output.stdout;

        if !(output.status.success()) {
            panic!(
                "{}\n{}",
                String::from_utf8_lossy(&actual_result),
                String::from_utf8_lossy(&output.stderr)
            );
        }

        let expected_file_path = {
            let ext = directive.ext();
            let mut path: PathBuf = env!("CARGO_MANIFEST_DIR").into();
            path.push("benches");
            let file_name = format!("{bench_name}.{target_cpu}{ext}",);
            path.push(file_name);
            path
        };

        if bless {
            std::fs::write(expected_file_path, &actual_result).unwrap();
        } else {
            let expected_result = std::fs::read(expected_file_path).unwrap_or_default();
            if actual_result != expected_result {
                println!("Expected output:\n{}", String::from_utf8_lossy(&expected_result));
                println!("Actual output:\n{}", String::from_utf8_lossy(&actual_result));
                panic!("Bless codegen tests with BLESS=1");
            }
        }
    };

    test_directive(Directive::Asm);
    if config.supports_mca {
        test_directive(Directive::Mca);
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn codegen() {
    let bless = std::env::var("BLESS").is_ok();
    let isas = vec![
        IsaConfig { target_triple: None, target_cpu: "x86-64", supports_mca: true },
        IsaConfig {
            target_triple: Some("thumbv7m-none-eabi"),
            target_cpu: "cortex-m3",
            supports_mca: false,
        },
        IsaConfig {
            target_triple: Some("riscv32imc-unknown-none-elf"),
            target_cpu: "generic-rv32",
            supports_mca: false,
        },
    ];

    let mut tasks = Vec::new();
    for entry in std::fs::read_dir("benches").unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "rs") {
            let bench_name = path.file_stem().unwrap().to_str().unwrap().to_owned();
            for config in &isas {
                tasks.push((bench_name.clone(), config.clone()));
            }
        }
    }

    // We explicitly restrict thread spawning into a bounded thread pool due to
    // resource limits. Launching hundreds of native `cargo rustc` cross-
    // compilation binaries simultaneously overwhelms the host operating
    // system's file descriptor and memory limits, resulting in silent test
    // failures or internal panics.
    let max_threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
    let mut failed = false;

    let tasks = Arc::new(Mutex::new(tasks.into_iter()));
    let mut handles = Vec::new();

    for _ in 0..max_threads {
        let tasks = tasks.clone();
        handles.push(thread::spawn(move || {
            let mut failed = false;
            loop {
                let task = {
                    let mut tasks = tasks.lock().unwrap();
                    tasks.next()
                };
                if let Some((bench_name, config)) = task {
                    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                        run_codegen_test(&bench_name, &config, bless);
                    }));
                    if result.is_err() {
                        failed = true;
                    }
                } else {
                    break;
                }
            }
            if failed {
                panic!("codegen test failed");
            }
        }));
    }

    for handle in handles {
        if handle.join().is_err() {
            failed = true;
        }
    }

    if failed {
        panic!("One or more codegen tests failed. See panics above for details.");
    }
}
