// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Check the `anneal-scaffold` command line: writing, drift checks, and the
//! file-handling refusals.

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

fn scaffold() -> Command {
    Command::new(env!("CARGO_BIN_EXE_anneal-scaffold"))
}

fn capture(identities: &[&str]) -> String {
    let bodies: Vec<_> = identities
        .iter()
        .map(|identity| {
            serde_json::json!({
                "identity": identity,
                "arg_count": 1,
                "is_unsafe": false,
                "local_tys": [
                    { "kind": "int", "width": "isize", "signed": false },
                    { "kind": "int", "width": "isize", "signed": false },
                ],
                "blocks": [{ "statements": [{}], "terminator": { "kind": "ret" } }],
            })
        })
        .collect();
    serde_json::json!({
        "schema_version": 5,
        "program": { "mir_profile_version": 1, "bodies": bodies },
    })
    .to_string()
}

struct Dir {
    dir: PathBuf,
}

impl Dir {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir()
            .join(format!("anneal-scaffold-test-{}-{name}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        Self { dir }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.dir.join(name)
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.path(name);
        fs::write(&path, text).unwrap();
        path
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}

fn run(args: &[&Path]) -> Output {
    let mut command = scaffold();
    for arg in args {
        command.arg(arg);
    }
    command.output().unwrap()
}

fn code(output: &Output) -> Option<i32> {
    output.status.code()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn write_then_check_detects_drift_and_reordering() {
    let dir = Dir::new("drift");
    let forward = dir.write("forward.json", &capture(&["rust-path-v1::a", "rust-path-v1::b"]));
    let reverse = dir.write("reverse.json", &capture(&["rust-path-v1::b", "rust-path-v1::a"]));
    let out = dir.path("AutoScaffold.lean");
    let flag = |s: &str| PathBuf::from(s);

    let output = run(&[&flag("--capture"), &forward, &flag("--out"), &out]);
    assert_eq!(code(&output), Some(0), "{}", stderr(&output));
    let written = fs::read_to_string(&out).unwrap();
    assert!(written.contains("namespace AutoScaffold"));
    assert!(written.contains("namespace b_a"));

    // Writing is deterministic, and --check accepts the file it wrote.
    let output = run(&[&flag("--capture"), &forward, &flag("--out"), &out]);
    assert_eq!(code(&output), Some(0));
    assert_eq!(fs::read_to_string(&out).unwrap(), written);
    let output = run(&[&flag("--capture"), &forward, &flag("--check"), &out]);
    assert_eq!(code(&output), Some(0), "{}", stderr(&output));

    // Reordered bodies, a hand edit, and a missing file are all drift.
    let output = run(&[&flag("--capture"), &reverse, &flag("--check"), &out]);
    assert_eq!(code(&output), Some(1));
    assert!(stderr(&output).contains("is stale"), "{}", stderr(&output));
    fs::write(&out, written.replace("rfl", "sorry")).unwrap();
    let output = run(&[&flag("--capture"), &forward, &flag("--check"), &out]);
    assert_eq!(code(&output), Some(1));
    let output = run(&[&flag("--capture"), &forward, &flag("--check"), &dir.path("absent.lean")]);
    assert_eq!(code(&output), Some(1));

    // A custom module name names the namespace.
    let output = scaffold()
        .args(["--module", "Proof.AutoScaffold", "--capture"])
        .arg(&forward)
        .arg("--out")
        .arg(&out)
        .output()
        .unwrap();
    assert_eq!(code(&output), Some(0), "{}", stderr(&output));
    assert!(fs::read_to_string(&out).unwrap().contains("namespace Proof.AutoScaffold"));
}

#[test]
fn unusable_captures_exit_one_and_usage_errors_exit_two() {
    let dir = Dir::new("errors");
    let out = dir.path("AutoScaffold.lean");
    let flag = |s: &str| PathBuf::from(s);

    let stale_schema = dir.write("old.json", r#"{"schema_version": 4, "program": {}}"#);
    let output = run(&[&flag("--capture"), &stale_schema, &flag("--out"), &out]);
    assert_eq!(code(&output), Some(1));
    assert!(stderr(&output).contains("schema_version"), "{}", stderr(&output));
    assert!(!out.exists(), "a rejected capture must not write output");

    let malformed = dir.write("bad.json", "{");
    assert_eq!(code(&run(&[&flag("--capture"), &malformed, &flag("--out"), &out])), Some(1));

    let good = dir.write("good.json", &capture(&["rust-path-v1::a"]));
    for args in [
        vec![flag("--capture"), good.clone()],
        vec![flag("--out"), out.clone()],
        vec![
            flag("--capture"),
            good.clone(),
            flag("--out"),
            out.clone(),
            flag("--check"),
            out.clone(),
        ],
        vec![flag("--capture"), good.clone(), flag("--out"), out.clone(), flag("--bogus")],
        vec![
            flag("--capture"),
            good.clone(),
            flag("--out"),
            out.clone(),
            flag("--module"),
            flag("lower"),
        ],
        vec![
            flag("--capture"),
            good.clone(),
            flag("--out"),
            out.clone(),
            flag("--module"),
            flag("Trusted.AutoScaffold"),
        ],
        vec![flag("--capture"), dir.path("missing.json"), flag("--out"), out.clone()],
    ] {
        let refs: Vec<&Path> = args.iter().map(PathBuf::as_path).collect();
        assert_eq!(code(&run(&refs)), Some(2), "{args:?}");
        assert!(!out.exists(), "a usage error must not write output: {args:?}");
    }
}

#[test]
fn refuses_parent_components_symlinks_and_non_files() {
    let dir = Dir::new("paths");
    let flag = |s: &str| PathBuf::from(s);
    let good = dir.write("good.json", &capture(&["rust-path-v1::a"]));

    let traversal = dir.path("sub").join("..").join("AutoScaffold.lean");
    assert_eq!(code(&run(&[&flag("--capture"), &good, &flag("--out"), &traversal])), Some(2));
    let traversal_in = dir.path("sub").join("..").join("good.json");
    let out = dir.path("AutoScaffold.lean");
    assert_eq!(code(&run(&[&flag("--capture"), &traversal_in, &flag("--out"), &out])), Some(2));

    // An output directory is not overwritten.
    fs::create_dir(dir.path("outdir")).unwrap();
    assert_eq!(
        code(&run(&[&flag("--capture"), &good, &flag("--out"), &dir.path("outdir")])),
        Some(2)
    );

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        // A symlinked capture is refused rather than followed.
        let linked_capture = dir.path("linked.json");
        symlink(&good, &linked_capture).unwrap();
        assert_eq!(
            code(&run(&[&flag("--capture"), &linked_capture, &flag("--out"), &out])),
            Some(2)
        );
        // A symlinked output is refused, and its target is left untouched.
        let target = dir.write("target.lean", "untouched");
        let linked_out = dir.path("linked.lean");
        symlink(&target, &linked_out).unwrap();
        assert_eq!(code(&run(&[&flag("--capture"), &good, &flag("--out"), &linked_out])), Some(2));
        assert_eq!(fs::read_to_string(&target).unwrap(), "untouched");
        assert_eq!(
            code(&run(&[&flag("--capture"), &good, &flag("--check"), &linked_out])),
            Some(2)
        );
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_arguments_are_usage_errors_or_paths() {
    use std::{ffi::OsStr, os::unix::ffi::OsStrExt as _};

    let dir = Dir::new("non-utf8");
    let good = dir.write("good.json", &capture(&["rust-path-v1::a"]));
    let out = dir.path("AutoScaffold.lean");
    let bad = OsStr::from_bytes(b"A\xff");
    let flag = |s: &str| PathBuf::from(s);
    // A non-UTF-8 flag or `--module` value is a usage error, not a panic.
    for args in [
        vec![flag("--capture"), good.clone(), flag("--out"), out.clone(), PathBuf::from(bad)],
        vec![
            flag("--capture"),
            good.clone(),
            flag("--out"),
            out.clone(),
            flag("--module"),
            PathBuf::from(bad),
        ],
    ] {
        let refs: Vec<&Path> = args.iter().map(PathBuf::as_path).collect();
        assert_eq!(code(&run(&refs)), Some(2), "{args:?}");
        assert!(!out.exists(), "a usage error must not write output: {args:?}");
    }
    // A non-UTF-8 output path is an ordinary path.
    let odd_out = dir.path("x").with_file_name(bad);
    let output = run(&[&flag("--capture"), &good, &flag("--out"), &odd_out]);
    assert_eq!(code(&output), Some(0), "{}", stderr(&output));
    assert!(odd_out.is_file());
}

#[test]
fn refuses_an_output_that_names_the_capture() {
    let dir = Dir::new("alias");
    let text = capture(&["rust-path-v1::a"]);
    let good = dir.write("capture.json", &text);
    let flag = |s: &str| PathBuf::from(s);
    // Another spelling of the capture's path, and a hard link to it.
    let spelled = dir.path(".").join("capture.json");
    let linked = dir.path("linked.json");
    fs::hard_link(&good, &linked).unwrap();
    for out in [good.clone(), spelled, linked] {
        let output = run(&[&flag("--capture"), &good, &flag("--out"), &out]);
        assert_eq!(code(&output), Some(2), "{out:?}: {}", stderr(&output));
        assert!(stderr(&output).contains("names the --capture file"), "{}", stderr(&output));
        assert_eq!(fs::read_to_string(&good).unwrap(), text, "{out:?}");
    }
    // `--check` against the capture only reads it, so it is not refused.
    let output = run(&[&flag("--capture"), &good, &flag("--check"), &good]);
    assert_eq!(code(&output), Some(1), "{}", stderr(&output));
}
