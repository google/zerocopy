// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]

mod support;

use std::fs;
use std::time::Duration;

use support::{Invocation, RunDirectory};

fn run_directory() -> RunDirectory {
    RunDirectory::new("fixture-path-regression", Duration::from_secs(2)).unwrap()
}

#[test]
fn nested_regular_writes_and_disjoint_copies_still_work() {
    let fixture = tempfile::tempdir().unwrap();
    fs::create_dir(fixture.path().join("directory")).unwrap();
    fs::write(fixture.path().join("directory/value"), b"copied").unwrap();
    let run = run_directory();
    let case = run.case("regular").unwrap();
    case.write("nested/value", b"first").unwrap();
    case.write("nested/value", b"replacement").unwrap();
    case.copy(fixture.path(), "copied").unwrap();
    case.copy(&fixture.path().join("directory/value"), "single-file")
        .unwrap();
    assert_eq!(
        fs::read(case.path().join("nested/value")).unwrap(),
        b"replacement"
    );
    assert_eq!(
        fs::read(case.path().join("copied/directory/value")).unwrap(),
        b"copied"
    );
    assert_eq!(
        fs::read(case.path().join("single-file")).unwrap(),
        b"copied"
    );
}

#[test]
fn writes_replace_hard_links_without_changing_the_external_file() {
    let outside = tempfile::tempdir().unwrap();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    let run = run_directory();
    let case = run.case("write-hard-link").unwrap();
    fs::hard_link(&sentinel, case.path().join("value")).unwrap();

    case.write("value", b"replacement").unwrap();

    assert_eq!(fs::read(&sentinel).unwrap(), b"keep");
    assert_eq!(fs::read(case.path().join("value")).unwrap(), b"replacement");
}

#[cfg(unix)]
#[test]
fn rewriting_an_executable_fixture_keeps_it_executable() {
    use std::os::unix::fs::PermissionsExt;

    let run = run_directory();
    let mut case = run.case("executable-rewrite").unwrap();
    case.write("script", b"#!/bin/sh\nexit 1\n").unwrap();
    let script = case.path().join("script");
    fs::set_permissions(&script, fs::Permissions::from_mode(0o751)).unwrap();

    case.write("script", b"#!/bin/sh\nexit 23\n").unwrap();

    assert_eq!(
        fs::metadata(&script).unwrap().permissions().mode() & 0o777,
        0o751
    );
    case.run(&Invocation::new(script, &[]))
        .unwrap()
        .expect_code(23)
        .unwrap();
}

#[test]
fn copies_replace_direct_and_nested_hard_links_without_changing_targets() {
    for copy_directory in [false, true] {
        let fixture = tempfile::tempdir().unwrap();
        fs::create_dir(fixture.path().join("nested")).unwrap();
        let source = fixture.path().join("nested/value");
        fs::write(&source, b"source").unwrap();
        let outside = tempfile::tempdir().unwrap();
        let sentinel = outside.path().join("sentinel");
        fs::write(&sentinel, b"keep").unwrap();
        let run = run_directory();
        let case = run.case("copy-hard-link").unwrap();
        let destination = if copy_directory {
            let nested = case.path().join("copied/nested");
            fs::create_dir_all(&nested).unwrap();
            nested.join("value")
        } else {
            case.path().join("copied")
        };
        fs::hard_link(&sentinel, &destination).unwrap();

        case.copy(
            if copy_directory {
                fixture.path()
            } else {
                &source
            },
            "copied",
        )
        .unwrap();

        assert_eq!(fs::read(&sentinel).unwrap(), b"keep");
        assert_eq!(fs::read(destination).unwrap(), b"source");
    }
}

#[cfg(unix)]
#[test]
fn copied_replacements_keep_source_permissions_without_chmoding_aliases() {
    use std::os::unix::fs::PermissionsExt;

    let fixture = tempfile::NamedTempFile::new().unwrap();
    fs::write(fixture.path(), b"source").unwrap();
    fs::set_permissions(fixture.path(), fs::Permissions::from_mode(0o751)).unwrap();
    let outside = tempfile::tempdir().unwrap();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    fs::set_permissions(&sentinel, fs::Permissions::from_mode(0o640)).unwrap();
    let run = run_directory();
    let case = run.case("copy-mode").unwrap();
    let destination = case.path().join("copied");
    fs::hard_link(&sentinel, &destination).unwrap();

    case.copy(fixture.path(), "copied").unwrap();

    assert_eq!(
        fs::metadata(&sentinel).unwrap().permissions().mode() & 0o777,
        0o640
    );
    assert_eq!(
        fs::metadata(destination).unwrap().permissions().mode() & 0o777,
        0o751
    );
    assert_eq!(fs::read(sentinel).unwrap(), b"keep");
}

#[test]
fn json_writes_to_an_empty_destination_return_an_error() {
    assert!(
        support::write_json(
            std::path::Path::new(""),
            &serde_json::json!({"result": "unused"}),
        )
        .is_err()
    );
}

#[cfg(unix)]
#[test]
fn json_writes_to_a_root_destination_return_an_error() {
    assert!(
        support::write_json(
            std::path::Path::new("/"),
            &serde_json::json!({"result": "unused"}),
        )
        .is_err()
    );
}

#[test]
fn json_replacements_preserve_external_hard_link_targets() {
    let outside = tempfile::tempdir().unwrap();
    let run = run_directory();
    let root = run.path().to_path_buf();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    fs::hard_link(&sentinel, root.join("summary.json")).unwrap();

    support::write_json(
        &root.join("summary.json"),
        &serde_json::json!({"result": "replacement"}),
    )
    .unwrap();
    assert_eq!(fs::read(sentinel).unwrap(), b"keep");
    let summary: serde_json::Value =
        serde_json::from_slice(&fs::read(root.join("summary.json")).unwrap()).unwrap();
    assert_eq!(summary["result"], "replacement");
}

#[test]
fn failure_text_replacements_preserve_external_hard_link_targets() {
    let outside = tempfile::tempdir().unwrap();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    let run = run_directory();
    let root = run.path().to_path_buf();
    fs::hard_link(&sentinel, root.join("failure.txt")).unwrap();

    let error = run
        .finish(Err("original failure".into()), None)
        .unwrap_err();

    assert!(error.contains("original failure"), "{error}");
    assert!(error.contains("evidence retained at"), "{error}");
    assert_eq!(fs::read(sentinel).unwrap(), b"keep");
    assert_eq!(
        fs::read(root.join("failure.txt")).unwrap(),
        b"original failure"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn evidence_export_replaces_hard_links_without_changing_external_files() {
    let outside = tempfile::tempdir().unwrap();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    let run = run_directory();
    let root = run.path().to_path_buf();
    let diagnostics = tempfile::tempdir().unwrap();
    let exported = diagnostics.path().join(root.file_name().unwrap());
    fs::create_dir(&exported).unwrap();
    fs::hard_link(&sentinel, exported.join("failure.txt")).unwrap();

    let error = run
        .finish(Err("original failure".into()), Some(diagnostics.path()))
        .unwrap_err();

    assert!(error.contains("original failure"), "{error}");
    assert!(error.contains("evidence exported to"), "{error}");
    assert_eq!(fs::read(&sentinel).unwrap(), b"keep");
    assert_eq!(
        fs::read(exported.join("failure.txt")).unwrap(),
        b"original failure"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn copy_rejects_sources_containing_the_destination_before_creation() {
    for source_is_run in [false, true] {
        let run = run_directory();
        let case = run.case("overlap").unwrap();
        case.write("sentinel", b"keep").unwrap();
        // A long component bounds accidental recursion on an old helper to a
        // few directory levels before the filesystem's path-length limit.
        let relative = "nested".repeat(35);
        let source = if source_is_run {
            run.path()
        } else {
            case.path()
        };
        let error = case.copy(source, &relative).unwrap_err();
        assert!(error.contains("must be disjoint"), "{error}");
        assert!(!case.path().join(relative).exists());
        assert_eq!(fs::read(case.path().join("sentinel")).unwrap(), b"keep");
    }
}

#[test]
fn copy_rejects_equal_and_reverse_overlaps_without_changing_sources() {
    let run = run_directory();
    let case = run.case("overlap").unwrap();
    case.write("fixture/nested/sentinel", b"keep").unwrap();
    for source in ["fixture", "fixture/nested"] {
        let error = case.copy(&case.path().join(source), "fixture").unwrap_err();
        assert!(error.contains("must be disjoint"), "{error}");
        assert_eq!(
            fs::read(case.path().join("fixture/nested/sentinel")).unwrap(),
            b"keep"
        );
    }
}

#[cfg(unix)]
#[test]
fn writes_reject_directory_file_and_dangling_symlinks() {
    use std::os::unix::fs::symlink;

    let outside = tempfile::tempdir().unwrap();
    fs::write(outside.path().join("sentinel"), b"keep").unwrap();
    let run = run_directory();
    let case = run.case("write-links").unwrap();
    symlink(outside.path(), case.path().join("directory")).unwrap();
    symlink(outside.path().join("sentinel"), case.path().join("file")).unwrap();
    symlink(outside.path().join("absent"), case.path().join("dangling")).unwrap();
    for relative in [
        "directory/sentinel",
        "directory/new/file",
        "file",
        "dangling",
    ] {
        let error = case.write(relative, b"changed").unwrap_err();
        assert!(error.contains("symlink"), "{error}");
    }
    assert_eq!(fs::read(outside.path().join("sentinel")).unwrap(), b"keep");
    assert!(!outside.path().join("new").exists());
    assert!(!outside.path().join("absent").exists());
}

#[cfg(unix)]
#[test]
fn copies_reject_linked_destinations_including_nested_existing_entries() {
    use std::os::unix::fs::symlink;

    let fixture = tempfile::tempdir().unwrap();
    fs::create_dir(fixture.path().join("nested")).unwrap();
    fs::write(fixture.path().join("nested/value"), b"source").unwrap();
    let outside = tempfile::tempdir().unwrap();
    fs::write(outside.path().join("sentinel"), b"keep").unwrap();
    let run = run_directory();
    let case = run.case("copy-links").unwrap();
    symlink(outside.path(), case.path().join("directory")).unwrap();
    symlink(outside.path().join("sentinel"), case.path().join("file")).unwrap();
    symlink(outside.path().join("absent"), case.path().join("dangling")).unwrap();
    for relative in ["directory/new", "file", "dangling"] {
        let error = case
            .copy(&fixture.path().join("nested/value"), relative)
            .unwrap_err();
        assert!(error.contains("symlink"), "{error}");
    }
    fs::create_dir(case.path().join("copied")).unwrap();
    symlink(outside.path(), case.path().join("copied/nested")).unwrap();
    let error = case.copy(fixture.path(), "copied").unwrap_err();
    assert!(error.contains("symlink"), "{error}");
    assert_eq!(fs::read(outside.path().join("sentinel")).unwrap(), b"keep");
    assert!(!outside.path().join("new").exists());
    assert!(!outside.path().join("absent").exists());
    assert!(!outside.path().join("value").exists());
}

#[cfg(unix)]
#[test]
fn writes_and_copies_reject_replaced_case_roots_and_ancestors() {
    use std::os::unix::fs::symlink;

    for replace_case_parent in [false, true] {
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("sentinel"), b"keep").unwrap();
        let fixture = tempfile::NamedTempFile::new().unwrap();
        fs::write(fixture.path(), b"source").unwrap();
        let run = run_directory();
        let case = run.case("replaced").unwrap();
        let replaced = if replace_case_parent {
            case.path().parent().unwrap()
        } else {
            case.path()
        };
        let saved = run.path().join("saved-cases");
        fs::rename(replaced, &saved).unwrap();
        symlink(outside.path(), replaced).unwrap();
        let write = case.write("sentinel", b"changed").unwrap_err();
        let copy = case.copy(fixture.path(), "sentinel").unwrap_err();
        assert!(write.contains("symlink"), "{write}");
        assert!(copy.contains("symlink"), "{copy}");
        assert_eq!(fs::read(outside.path().join("sentinel")).unwrap(), b"keep");
        assert!(!outside.path().join("replaced").exists());
        fs::remove_file(replaced).unwrap();
        fs::rename(saved, replaced).unwrap();
    }
}

#[test]
fn command_logs_do_not_reuse_existing_fixture_directories() {
    let run = run_directory();
    let mut case = run.case("existing-logs").unwrap();
    case.write("commands/0000/stdout", b"keep").unwrap();
    let missing = case.path().join("missing-tool");
    let error = case.run(&Invocation::new(missing, &[])).unwrap_err();
    assert!(error.contains("commands/0000"), "{error}");
    assert_eq!(
        fs::read(case.path().join("commands/0000/stdout")).unwrap(),
        b"keep"
    );
    assert!(!case.path().join("commands/0000/invocation.json").exists());
}

#[cfg(unix)]
#[test]
fn command_logs_reject_linked_roots_and_preexisting_output_links() {
    use std::os::unix::fs::symlink;

    for linked_log_root in [false, true] {
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("sentinel"), b"keep").unwrap();
        let run = run_directory();
        let mut case = run.case("linked-logs").unwrap();
        if linked_log_root {
            symlink(outside.path(), case.path().join("commands")).unwrap();
        } else {
            fs::create_dir_all(case.path().join("commands/0000")).unwrap();
            symlink(
                outside.path().join("sentinel"),
                case.path().join("commands/0000/stdout"),
            )
            .unwrap();
        }
        let missing = case.path().join("missing-tool");
        let error = case.run(&Invocation::new(missing, &[])).unwrap_err();
        assert!(error.contains("commands"), "{error}");
        assert_eq!(fs::read(outside.path().join("sentinel")).unwrap(), b"keep");
        assert!(!outside.path().join("0000").exists());
        assert!(!case.path().join("commands/0000/invocation.json").exists());
    }
}

#[cfg(unix)]
#[test]
fn child_created_outcome_links_preserve_the_target_and_process_status() {
    let outside = tempfile::tempdir().unwrap();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    let run = run_directory();
    let mut case = run.case("child-outcome-link").unwrap();
    let mut invocation = Invocation::new(
        std::env::current_exe().unwrap(),
        &["--exact", "outcome_link_child_fixture", "--ignored"],
    );
    invocation.environment.insert(
        "ANNEAL_FIXTURE_OUTCOME_TARGET".into(),
        sentinel.to_str().unwrap().into(),
    );
    let error = case.run(&invocation).unwrap_err();
    assert!(
        error.contains("child exited") && error.contains("23"),
        "{error}"
    );
    assert!(error.contains("retain process outcome"), "{error}");
    assert!(error.contains("symlink"), "{error}");
    assert_eq!(fs::read(sentinel).unwrap(), b"keep");
}

#[cfg(unix)]
#[test]
#[ignore = "internal subprocess fixture"]
fn outcome_link_child_fixture() {
    std::os::unix::fs::symlink(
        std::env::var_os("ANNEAL_FIXTURE_OUTCOME_TARGET").unwrap(),
        "commands/0000/outcome.json",
    )
    .unwrap();
    std::process::exit(23);
}

#[test]
fn child_created_outcome_hard_links_preserve_external_files_and_status() {
    let outside = tempfile::tempdir().unwrap();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    let run = run_directory();
    let mut case = run.case("child-outcome-hard-link").unwrap();
    let mut invocation = Invocation::new(
        std::env::current_exe().unwrap(),
        &["--exact", "outcome_hard_link_child_fixture", "--ignored"],
    );
    invocation.environment.insert(
        "ANNEAL_FIXTURE_OUTCOME_TARGET".into(),
        sentinel.to_str().unwrap().into(),
    );

    let outcome = case.run(&invocation).unwrap();

    outcome.expect_code(23).unwrap();
    assert_eq!(fs::read(sentinel).unwrap(), b"keep");
    let metadata: serde_json::Value =
        serde_json::from_slice(&fs::read(case.path().join("commands/0000/outcome.json")).unwrap())
            .unwrap();
    assert_eq!(metadata["kind"], "exited");
    assert_eq!(metadata["code"], 23);
}

#[test]
#[ignore = "internal subprocess fixture"]
fn outcome_hard_link_child_fixture() {
    fs::hard_link(
        std::env::var_os("ANNEAL_FIXTURE_OUTCOME_TARGET").unwrap(),
        "commands/0000/outcome.json",
    )
    .unwrap();
    std::process::exit(23);
}

#[cfg(unix)]
#[test]
fn run_evidence_links_do_not_overwrite_targets_or_hide_the_failure() {
    use std::os::unix::fs::symlink;

    let outside = tempfile::tempdir().unwrap();
    let sentinel = outside.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    let run = run_directory();
    let root = run.path().to_path_buf();
    symlink(&sentinel, root.join("summary.json")).unwrap();
    symlink(&sentinel, root.join("failure.txt")).unwrap();
    let json_error = support::write_json(
        &root.join("summary.json"),
        &serde_json::json!({"result": "changed"}),
    )
    .unwrap_err();
    assert!(json_error.contains("symlink"), "{json_error}");
    let error = run
        .finish(Err("original failure".into()), None)
        .unwrap_err();
    assert!(error.contains("original failure"), "{error}");
    assert!(error.contains("retain failure text"), "{error}");
    assert!(error.contains("symlink"), "{error}");
    assert!(error.contains("evidence retained at"), "{error}");
    assert_eq!(fs::read(sentinel).unwrap(), b"keep");
    fs::remove_dir_all(root).unwrap();
}
