// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::{
    env,
    ffi::OsStr,
    io::{Read as _, Seek as _, Write as _},
    mem,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    str,
    sync::Once,
};

use fs_err as fs;
use test_helper::cli::CommandExt as _;

pub(crate) fn fixtures_dir() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures"))
}

fn ensure_llvm_tools_installed() {
    static TEST_VERSION: Once = Once::new();
    TEST_VERSION.call_once(|| {
        // Install component first to avoid component installation conflicts.
        let _ = Command::new("rustup").args(["component", "add", "llvm-tools-preview"]).output();
    });
}

pub(crate) fn cargo_llvm_cov(subcommand: &str) -> Command {
    ensure_llvm_tools_installed();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-llvm-cov"));
    cmd.arg("llvm-cov");
    if !subcommand.is_empty() {
        cmd.arg(subcommand);
    }
    cmd.env("CARGO_LLVM_COV_DENY_WARNINGS", "1");
    cmd.env_remove("RUSTFLAGS")
        .env_remove("RUSTDOCFLAGS")
        .env_remove("CARGO_BUILD_RUSTFLAGS")
        .env_remove("CARGO_BUILD_RUSTDOCFLAGS")
        .env_remove("CARGO_TERM_VERBOSE")
        .env_remove("CARGO_TERM_COLOR")
        .env_remove("BROWSER")
        .env_remove("RUST_LOG")
        .env_remove("CI");
    cmd
}

#[track_caller]
pub(crate) fn test_report(
    model: &str,
    name: &str,
    extension: &str,
    subcommand: Option<&str>,
    args: &[&str],
    envs: &[(&str, &str)],
) {
    eprintln!("model={model}/name={name}");
    let workspace_root = test_project(model);
    let output_dir = fixtures_dir().join("coverage-reports").join(model);
    fs::create_dir_all(&output_dir).unwrap();
    let output_path = &output_dir.join(name).with_extension(extension);
    let expected = &fs::read_to_string(output_path).unwrap_or_default();
    let mut cmd = cargo_llvm_cov("");
    if let Some(subcommand) = subcommand {
        cmd.arg(subcommand);
    }
    cmd.args(["--color", "never", "--output-path"])
        .arg(output_path)
        .arg("--remap-path-prefix")
        .args(args)
        .current_dir(workspace_root.path());
    for (key, val) in envs {
        cmd.env(key, val);
    }
    cmd.assert_success();

    normalize_output(output_path, args);
    assert_output(output_path, expected);
}

#[track_caller]
pub(crate) fn assert_output(output_path: &Path, expected: &str) {
    if env::var_os("CI").is_some() {
        let color = if env::var_os("GITHUB_ACTIONS").is_some() {
            &["-c", "color.ui=always"][..]
        } else {
            &[]
        };
        let mut child = Command::new("git")
            .arg("--no-pager")
            .args(color)
            .args(["diff", "--no-index", "--"])
            .arg("-")
            .arg(output_path)
            .stdin(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.as_mut().unwrap().write_all(expected.as_bytes()).unwrap();
        assert!(child.wait().unwrap().success());
    }
}

#[track_caller]
pub(crate) fn normalize_output(output_path: &Path, args: &[&str]) {
    if args.contains(&"--json") {
        let s = fs::read_to_string(output_path).unwrap();
        let mut json = serde_json::from_str::<cargo_llvm_cov::json::LlvmCovJsonExport>(&s).unwrap();
        if !args.contains(&"--summary-only") {
            json.demangle();
        }
        fs::write(output_path, serde_json::to_vec_pretty(&json).unwrap()).unwrap();
    }
    if cfg!(windows) {
        let s = fs::read_to_string(output_path).unwrap();
        // In json \ is escaped ("\\\\"), in other it is not escaped ("\\").
        fs::write(output_path, s.replace("\\\\", "/").replace('\\', "/")).unwrap();
    }
}

#[track_caller]
pub(crate) fn test_project(model: &str) -> tempfile::TempDir {
    let tmpdir = tempfile::tempdir().unwrap();
    test_helper::git::copy_tracked_files(fixtures_dir().join("crates").join(model), tmpdir.path());
    tmpdir
}

pub(crate) fn perturb_one_header(workspace_root: &Path) -> Option<PathBuf> {
    let target_dir = workspace_root.join("target").join("llvm-cov-target");
    let path = fs::read_dir(target_dir).unwrap().find_map(|entry| {
        let path = entry.ok().unwrap().path();
        if path.extension() == Some(OsStr::new("profraw")) { Some(path) } else { None }
    });
    if let Some(path) = &path {
        perturb_header(path);
    }
    path
}

#[allow(clippy::decimal_bitwise_operands)]
const INSTR_PROF_RAW_MAGIC_64: u64 = (255_u64 << 56)
    | (('l' as u64) << 48)
    | (('p' as u64) << 40)
    | (('r' as u64) << 32)
    | (('o' as u64) << 24)
    | (('f' as u64) << 16)
    | (('r' as u64) << 8)
    | 129_u64;
const INSTR_PROF_RAW_MAGIC_32: u64 = 18405209413953933953;

fn perturb_header(path: &Path) {
    let mut file = fs::OpenOptions::new().read(true).write(true).open(path).unwrap(); // Not buffered because it is read and written only once each.
    let mut magic = {
        let mut buf = [0_u8; mem::size_of::<u64>()];
        file.read_exact(&mut buf).unwrap();
        u64::from_ne_bytes(buf)
    };
    if cfg!(target_pointer_width = "64") {
        assert_eq!(magic, INSTR_PROF_RAW_MAGIC_64);
    } else {
        assert_eq!(magic, INSTR_PROF_RAW_MAGIC_32);
    }
    magic += 1;
    file.rewind().unwrap();
    file.write_all(&magic.to_ne_bytes()).unwrap();
}
