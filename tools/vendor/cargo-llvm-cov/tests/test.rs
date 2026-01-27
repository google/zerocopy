// SPDX-License-Identifier: Apache-2.0 OR MIT

#![cfg(not(miri))] // Miri doesn't support file with non-default mode: https://github.com/rust-lang/miri/pull/2720

mod auxiliary;

use std::{collections::HashSet, path::Path};

use cargo_config2::Flags;
use fs_err as fs;
use test_helper::cli::CommandExt as _;

use self::auxiliary::*;

const SUBCOMMANDS: &[&str] = &["", "run", "report", "clean", "show-env", "nextest"];

fn test_set() -> Vec<(&'static str, &'static [&'static str])> {
    let mut set: Vec<(&'static str, &'static [&'static str])> = vec![
        ("summary.txt", &[]),
        ("txt", &["--text", "--show-instantiations"]),
        ("hide-instantiations.txt", &["--text"]),
        ("lcov.info", &["--lcov", "--summary-only"]),
        // TODO: test Cobertura output
        ("codecov.json", &["--codecov"]),
    ];
    if rustversion::cfg!(since(1.91)) {
        // LLVM 21 (1.91) bumped llvm.coverage.json.export version.
        set.push(("json", &["--json", "--summary-only"]));
        // TODO: full JSON output is unstable between platform.
        // ("full.json", &["--json"]),
    }
    set
}

fn run(model: &str, name: &str, args: &[&str], envs: &[(&str, &str)]) {
    for (extension, args2) in test_set() {
        test_report(model, name, extension, None, &[args, args2].concat(), envs);
    }
}

// TODO:
// - add tests for non-crates.io dependencies

// 1.88 fixed bug in report generation, so the latest report is not the same as the old report.
#[rustversion::attr(before(1.88), ignore)]
#[test]
fn real1() {
    run("real1", "workspace_root", &[], &[]);
    run("real1", "all", &["--all"], &[]);
    run("real1", "manifest_path", &["--manifest-path", "member1/member2/Cargo.toml"], &[]);
    run("real1", "package1", &["--package", "member2"], &[]);
    run("real1", "exclude", &["--all", "--exclude", "crate1"], &[]);
}

// 1.88 fixed bug in report generation, so the latest report is not the same as the old report.
#[rustversion::attr(before(1.88), ignore)]
#[test]
fn virtual1() {
    run("virtual1", "workspace_root", &[], &[]);
    run("virtual1", "package1", &["--package", "member1"], &[]);
    run("virtual1", "package2", &["--package", "member1", "--package", "member2"], &[]);
    run("virtual1", "package3", &["--package", "member2"], &[]);
    run("virtual1", "package4", &["--package", "member3"], &[]);
    run("virtual1", "package5", &["--package", "member4"], &[]);
    run("virtual1", "package6", &["--package", "member3", "--package", "member4"], &[]);
    run("virtual1", "exclude1", &["--workspace", "--exclude", "member1"], &[]);
    run("virtual1", "exclude2", &["--workspace", "--exclude", "member2"], &[]);
    run(
        "virtual1",
        "exclude-from-report1",
        &["--workspace", "--exclude-from-report", "member1"],
        &[],
    );
    run(
        "virtual1",
        "exclude-from-report2",
        &["--workspace", "--exclude-from-report", "member2"],
        &[],
    );
    run("virtual1", "exclude-from-test1", &["--workspace", "--exclude-from-test", "member1"], &[]);
    run("virtual1", "exclude-from-test2", &["--workspace", "--exclude-from-test", "member2"], &[]);
}

// 1.88 fixed bug in report generation, so the latest report is not the same as the old report.
#[rustversion::attr(before(1.88), ignore)]
#[test]
fn no_test() {
    run("no_test", "no_test", &[], &[]);
    if !(cfg!(windows) && cfg!(target_env = "msvc")) {
        run("no_test", "link_dead_code", &[], &[("RUSTFLAGS", "-C link-dead-code")]);
    }
}

// 1.88 fixed bug in report generation, so the latest report is not the same as the old report.
#[rustversion::attr(before(1.88), ignore)]
#[test]
fn bin_crate() {
    run("bin_crate", "bin_crate", &[], &[]);

    let model = "bin_crate";
    let name = "run";
    for (extension, args2) in test_set() {
        test_report(model, name, extension, Some("run"), &[args2, &["--", "1"]].concat(), &[]);
    }
}

// 1.88 fixed bug in report generation, so the latest report is not the same as the old report.
#[rustversion::attr(before(1.88), ignore)]
#[test]
fn instantiations() {
    // TODO: fix https://github.com/taiki-e/cargo-llvm-cov/issues/43
    run("instantiations", "instantiations", &[], &[]);
}

// 1.88 fixed bug in report generation, so the latest report is not the same as the old report.
#[rustversion::attr(before(1.88), ignore)]
#[test]
fn cargo_config() {
    run("cargo_config", "cargo_config", &[], &[]);
    run("cargo_config_toml", "cargo_config_toml", &[], &[]);
}

// build-dir requires Cargo 1.91.
#[rustversion::attr(before(1.91), ignore)]
#[test]
fn build_dir() {
    run("build_dir", "build_dir", &[], &[]);
}

// feature(coverage_attribute) requires nightly
#[rustversion::attr(not(nightly), ignore)]
#[test]
fn no_coverage() {
    let model = "no_coverage";
    for (extension, args2) in test_set() {
        // TODO: On windows, the order of the instantiations in the generated coverage report will be different.
        if extension == "full.json" && cfg!(windows) {
            continue;
        }
        test_report(model, model, extension, None, args2, &[]);
    }

    let name = "no_cfg_coverage";
    for (extension, args2) in test_set() {
        // TODO: On windows, the order of the instantiations in the generated coverage report will be different.
        if extension == "full.json" && cfg!(windows) {
            continue;
        }
        test_report(model, name, extension, None, &[args2, &["--no-cfg-coverage"]].concat(), &[]);
    }
}

// The order of the instantiations in the generated coverage report will be different depending on the version.
#[rustversion::attr(not(nightly), ignore)]
#[test]
fn merge() {
    // The order of the instantiations in the generated coverage report will be different depending on the platform.
    if !cfg!(any(
        all(target_arch = "x86_64", target_os = "linux"),
        all(target_arch = "aarch64", target_os = "macos"),
    )) {
        return;
    }
    let output_dir = fixtures_dir().join("coverage-reports").join("merge");
    merge_with_failure_mode(&output_dir, false);
}

#[test]
fn merge_failure_mode_all() {
    let tempdir = tempfile::tempdir().unwrap();
    merge_with_failure_mode(tempdir.path(), true);
}

fn merge_with_failure_mode(output_dir: &Path, failure_mode_all: bool) {
    let model = "merge";
    fs::create_dir_all(output_dir).unwrap();
    for (extension, args) in test_set() {
        let workspace_root = test_project(model);
        let output_path = &output_dir.join(model).with_extension(extension);
        let expected = &fs::read_to_string(output_path).unwrap_or_default();
        cargo_llvm_cov("")
            .args(["--color", "never", "--no-report", "--features", "a"])
            .arg("--remap-path-prefix")
            .current_dir(workspace_root.path())
            .assert_success();
        cargo_llvm_cov("")
            .args(["--color", "never", "--no-report", "--features", "b"])
            .arg("--remap-path-prefix")
            .current_dir(workspace_root.path())
            .assert_success();
        let mut cmd = cargo_llvm_cov("report");
        cmd.args(["--color", "never", "--output-path"])
            .arg(output_path)
            .arg("--remap-path-prefix")
            .args(args)
            .current_dir(workspace_root.path());
        cmd.assert_success();

        if failure_mode_all {
            perturb_one_header(workspace_root.path()).unwrap();
            cmd.assert_failure()
                .stderr_contains("unrecognized instrumentation profile encoding format");
            cmd.args(["--failure-mode", "all"]);
            cmd.assert_success();
        } else {
            normalize_output(output_path, args);
            assert_output(output_path, expected);
        }
    }
}

// 1.88 fixed bug in report generation, so the latest report is not the same as the old report.
#[rustversion::attr(before(1.88), ignore)]
#[test]
fn clean_ws() {
    let model = "merge";
    let name = "clean_ws";
    let output_dir = fixtures_dir().join("coverage-reports").join(model);
    fs::create_dir_all(&output_dir).unwrap();
    for (extension, args) in test_set() {
        let workspace_root = test_project(model);
        let output_path = &output_dir.join(name).with_extension(extension);
        let expected = &fs::read_to_string(output_path).unwrap_or_default();
        cargo_llvm_cov("")
            .args(["--color", "never", "--no-report", "--features", "a"])
            .arg("--remap-path-prefix")
            .current_dir(workspace_root.path())
            .assert_success();
        cargo_llvm_cov("report")
            .args(["--color", "never", "--output-path"])
            .arg(output_path)
            .arg("--remap-path-prefix")
            .args(args)
            .current_dir(workspace_root.path())
            .assert_success();

        normalize_output(output_path, args);
        assert_output(output_path, expected);

        cargo_llvm_cov("")
            .args(["clean", "--color", "never", "--workspace"])
            .current_dir(workspace_root.path())
            .assert_success();
        cargo_llvm_cov("")
            .args(["--color", "never", "--no-report", "--features", "a"])
            .arg("--remap-path-prefix")
            .current_dir(workspace_root.path())
            .assert_success();
        cargo_llvm_cov("report")
            .args(["--color", "never", "--output-path"])
            .arg(output_path)
            .arg("--remap-path-prefix")
            .args(args)
            .current_dir(workspace_root.path())
            .assert_success();

        normalize_output(output_path, args);
        assert_output(output_path, expected);
    }
}

#[test]
fn clean_profraw_only() {
    let model = "real1";
    let workspace_root = test_project(model);

    cargo_llvm_cov("")
        .args(["--color", "never", "--no-report"])
        .arg("--remap-path-prefix")
        .current_dir(workspace_root.path())
        .assert_success();

    let entries_before =
        walkdir::WalkDir::new(&workspace_root).into_iter().map(Result::unwrap).collect::<Vec<_>>();

    let paths_before = entries_before.iter().map(walkdir::DirEntry::path).collect::<HashSet<_>>();

    assert!(
        paths_before
            .iter()
            .any(|path| path.extension().is_some_and(|extension| extension == "profraw"))
    );

    cargo_llvm_cov("clean")
        .args(["--color", "never", "--profraw-only"])
        .current_dir(workspace_root.path())
        .assert_success();

    assert!(workspace_root.path().join("target/llvm-cov-target").exists());

    let entries_after =
        walkdir::WalkDir::new(&workspace_root).into_iter().map(Result::unwrap).collect::<Vec<_>>();

    let paths_after = entries_after.iter().map(walkdir::DirEntry::path).collect::<HashSet<_>>();

    for path in &paths_before {
        if path.extension().is_some_and(|extension| extension == "profraw") {
            continue;
        }
        assert!(paths_after.contains(path), "{} was deleted by clean", path.display());
    }

    for path in paths_after {
        assert!(path.extension().is_none_or(|extension| extension != "profraw"));
        assert!(paths_before.contains(path), "{} was created by clean", path.display());
    }
}

#[test]
#[cfg_attr(windows, ignore)] // `echo` may not be available
fn open_report() {
    let model = "real1";
    let workspace_root = test_project(model);
    cargo_llvm_cov("")
        .args(["--color", "never", "--open"])
        .current_dir(workspace_root.path())
        .env("BROWSER", "echo")
        .assert_success()
        .stdout_contains(
            workspace_root.path().join("target/llvm-cov/html/index.html").to_string_lossy(),
        );
}

#[test]
fn show_env() {
    cargo_llvm_cov("show-env").assert_success().stdout_not_contains("export");
    cargo_llvm_cov("show-env").arg("--export-prefix").assert_success().stdout_contains("export");

    let mut flags = Flags::default();
    flags.push("--deny warnings");
    flags.push("--cfg=tests");
    let flags = flags.encode().unwrap();

    cargo_llvm_cov("show-env")
        .env("CARGO_ENCODED_RUSTFLAGS", flags)
        .arg("--with-pwsh-env-prefix")
        .assert_success()
        // Verify the prefix related content + the encoding of "--"
        .stdout_contains("$env:CARGO_ENCODED_RUSTFLAGS=\"`u{2d}`u{2d}")
        // Verify binary character didn't lead to incompatible output for pwsh
        .stdout_contains("`u{1f}");
    cargo_llvm_cov("show-env")
        .arg("--export-prefix")
        .arg("--with-pwsh-env-prefix")
        .assert_failure()
        .stderr_contains("may not be used together with");
}

#[test]
fn invalid_arg() {
    for subcommand in
        ["", "test", "run", "report", "clean", "show-env", "nextest", "nextest-archive"]
    {
        if subcommand != "show-env" {
            cargo_llvm_cov(subcommand)
                .arg("--export-prefix")
                .assert_failure()
                .stderr_contains("invalid option '--export-prefix'");
            cargo_llvm_cov(subcommand)
                .arg("--with-pwsh-env-prefix")
                .assert_failure()
                .stderr_contains("invalid option '--with-pwsh-env-prefix'");
        }
        if !matches!(subcommand, "" | "test") {
            if matches!(subcommand, "nextest" | "nextest-archive") {
                cargo_llvm_cov(subcommand)
                    .arg("--doc")
                    .assert_failure()
                    .stderr_contains("doctest is not supported for nextest");
                cargo_llvm_cov(subcommand)
                    .arg("--doctests")
                    .assert_failure()
                    .stderr_contains("doctest is not supported for nextest");
            } else {
                cargo_llvm_cov(subcommand)
                    .arg("--doc")
                    .assert_failure()
                    .stderr_contains("invalid option '--doc'");
                if !matches!(subcommand, "report" | "show-env") {
                    cargo_llvm_cov(subcommand)
                        .arg("--doctests")
                        .assert_failure()
                        .stderr_contains("invalid option '--doctests'");
                }
            }
        }
        if !matches!(subcommand, "" | "test" | "nextest" | "nextest-archive") {
            for arg in [
                "--lib",
                "--bins",
                "--examples",
                "--test=v",
                "--tests",
                "--bench=v",
                "--benches",
                "--all-targets",
                "--no-run",
                "--no-fail-fast",
                "--exclude=v",
                "--exclude-from-test=v",
            ] {
                cargo_llvm_cov(subcommand).arg(arg).assert_failure().stderr_contains(format!(
                    "invalid option '{}' for subcommand '{subcommand}'",
                    arg.strip_suffix("=v").unwrap_or(arg)
                ));
            }
        }
        if !matches!(subcommand, "" | "test" | "run" | "nextest" | "nextest-archive") {
            for arg in [
                "--bin=v",
                "--example=v",
                "--exclude-from-report=v",
                "--no-report",
                "--no-clean",
                "--ignore-run-fail",
            ] {
                cargo_llvm_cov(subcommand).arg(arg).assert_failure().stderr_contains(format!(
                    "invalid option '{}' for subcommand '{subcommand}'",
                    arg.strip_suffix("=v").unwrap_or(arg)
                ));
            }
        }
        if !matches!(subcommand, "" | "test" | "run" | "nextest" | "nextest-archive" | "show-env") {
            for arg in ["--no-cfg-coverage", "--no-cfg-coverage-nightly"] {
                cargo_llvm_cov(subcommand).arg(arg).assert_failure().stderr_contains(format!(
                    "invalid option '{}' for subcommand '{subcommand}'",
                    arg.strip_suffix("=v").unwrap_or(arg)
                ));
            }
        }
        if !matches!(subcommand, "" | "test" | "nextest" | "nextest-archive" | "clean") {
            for arg in ["--workspace", "--all"] {
                cargo_llvm_cov(subcommand).arg(arg).assert_failure().stderr_contains(format!(
                    "invalid option '{}' for subcommand '{subcommand}'",
                    if arg == "--all" {
                        "--workspace"
                    } else {
                        arg.strip_suffix("=v").unwrap_or(arg)
                    }
                ));
            }
        }
    }
}

#[test]
fn invalid_arg_no_passthrough() {
    // These subcommands don't allow passthrough args.
    // In other subcommands, if passthrough args are invalid,
    // it will be detected by cargo or cargo-nextest.
    for subcommand in ["report", "clean", "show-env"] {
        cargo_llvm_cov(subcommand)
            .arg("-a")
            .assert_failure()
            .stderr_contains(format!("invalid option '-a' for subcommand '{subcommand}'"));
        cargo_llvm_cov(subcommand)
            .arg("--b")
            .assert_failure()
            .stderr_contains(format!("invalid option '--b' for subcommand '{subcommand}'"));
        cargo_llvm_cov(subcommand)
            .arg("c")
            .assert_failure()
            .stderr_contains("unexpected argument \"c\"");
    }
}

#[test]
fn help() {
    for &subcommand in SUBCOMMANDS {
        let short = cargo_llvm_cov(subcommand).arg("-h").assert_success();
        let long = cargo_llvm_cov(subcommand).arg("--help").assert_success();
        let expected_pat = &format!("cargo llvm-cov {subcommand}");
        short.stdout_contains(expected_pat);
        long.stdout_contains(expected_pat);
        assert_eq!(short.stdout, long.stdout);
    }
}

#[test]
fn version() {
    let expected = &format!("cargo-llvm-cov {}", env!("CARGO_PKG_VERSION"));
    for &subcommand in SUBCOMMANDS {
        if subcommand.is_empty() {
            cargo_llvm_cov(subcommand).arg("-V").assert_success().stdout_eq(expected);
            cargo_llvm_cov(subcommand).arg("--version").assert_success().stdout_eq(expected);
        } else {
            cargo_llvm_cov(subcommand).arg("-V").assert_failure().stderr_contains(format!(
                "invalid option '--version' for subcommand '{subcommand}'"
            ));
            cargo_llvm_cov(subcommand).arg("--version").assert_failure().stderr_contains(format!(
                "invalid option '--version' for subcommand '{subcommand}'"
            ));
        }
    }
}

#[test]
fn update_readme() {
    let new = cargo_llvm_cov("").arg("--help").assert_success().stdout;
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("README.md");
    let command = "cargo llvm-cov --help";
    test_helper::doc::sync_command_output_to_markdown(path, "readme-long-help", command, new);
}
