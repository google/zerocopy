// Copyright (c) The datatest-stable Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

static EXPECTED_LINES: &[&str] = &[
    "datatest-stable::example test_artifact_utf8::dir/a.txt",
    "datatest-stable::example test_artifact_utf8::b.txt",
    "datatest-stable::example test_artifact_utf8::c.skip.txt",
    "datatest-stable::example test_artifact_utf8_abs::dir/a.txt",
    "datatest-stable::example test_artifact_utf8_abs::b.txt",
    "datatest-stable::example test_artifact_utf8_abs::c.skip.txt",
    "datatest-stable::example test_artifact::dir/a.txt",
    "datatest-stable::example test_artifact::b.txt",
    "datatest-stable::example with_contents::test_artifact_bytes::dir/a.txt",
    "datatest-stable::example with_contents::test_artifact_bytes::b.txt",
    "datatest-stable::example with_contents::test_artifact_bytes::c.skip.txt",
    "datatest-stable::example with_contents::test_artifact_string::dir/a.txt",
    "datatest-stable::example with_contents::test_artifact_string::b.txt",
    "datatest-stable::example with_contents::test_artifact_string::c.skip.txt",
    "datatest-stable::example with_contents::test_artifact_utf8_bytes::dir/a.txt",
    "datatest-stable::example with_contents::test_artifact_utf8_bytes::b.txt",
    "datatest-stable::example with_contents::test_artifact_utf8_bytes::c.skip.txt",
    "datatest-stable::example with_contents::test_artifact_bytes::other.json",
    "datatest-stable::example with_contents::test_artifact_utf8_string::dir/a.txt",
    "datatest-stable::example with_contents::test_artifact_utf8_string::b.txt",
    "datatest-stable::example with_contents::test_artifact_utf8_string::c.skip.txt",
];

#[test]
fn run_example() {
    let output = std::process::Command::new(cargo_bin())
        .args(["nextest", "run", "--test=example", "--color=never"])
        .env("__DATATEST_FULL_SCAN_FORBIDDEN", "1")
        .output()
        .expect("`cargo nextest` was successful");

    // It's a pain to make assertions on byte slices (even a subslice check isn't easy)
    // and it's also difficult to print nice error messages. So we just assume all
    // nextest output will be utf8 and convert it.
    let stderr = std::str::from_utf8(&output.stderr).expect("cargo nextest stderr should be utf-8");

    assert!(
        output.status.success(),
        "nextest exited with 0 (exit status: {}, stderr: {stderr})",
        output.status
    );

    for line in EXPECTED_LINES
        .iter()
        .copied()
        .chain(std::iter::once("21 tests run: 21 passed, 0 skipped"))
    {
        assert!(
            stderr.contains(line),
            "Expected to find substring\n  {line}\nin stderr\n  {stderr}",
        );
    }
}

#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile-fail/*.rs");
}

#[cfg(unix)]
mod unix {
    use super::*;
    use camino_tempfile::Utf8TempDir;

    static EXPECTED_UNIX_LINES: &[&str] = &[
        "datatest-stable::example test_artifact_utf8::::colon::dir/::.txt",
        "datatest-stable::example test_artifact_utf8::::colon::dir/a.txt",
        "datatest-stable::example test_artifact_utf8::dir/a.txt",
        "datatest-stable::example test_artifact_utf8::b.txt",
        "datatest-stable::example test_artifact_utf8::c.skip.txt",
        "datatest-stable::example test_artifact_utf8_abs::dir/a.txt",
        "datatest-stable::example test_artifact_utf8_abs::b.txt",
        "datatest-stable::example test_artifact_utf8_abs::c.skip.txt",
        "datatest-stable::example test_artifact::::colon::dir/::.txt",
        "datatest-stable::example test_artifact::::colon::dir/a.txt",
        "datatest-stable::example test_artifact::dir/a.txt",
        "datatest-stable::example test_artifact::b.txt",
        "datatest-stable::example with_contents::test_artifact_bytes::::colon::dir/::.txt",
        "datatest-stable::example with_contents::test_artifact_bytes::::colon::dir/a.txt",
        "datatest-stable::example with_contents::test_artifact_bytes::dir/a.txt",
        "datatest-stable::example with_contents::test_artifact_bytes::b.txt",
        "datatest-stable::example with_contents::test_artifact_bytes::c.skip.txt",
        "datatest-stable::example with_contents::test_artifact_string::dir/a.txt",
        "datatest-stable::example with_contents::test_artifact_string::b.txt",
        "datatest-stable::example with_contents::test_artifact_string::c.skip.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_bytes::::colon::dir/::.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_bytes::::colon::dir/a.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_bytes::dir/a.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_bytes::b.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_bytes::c.skip.txt",
        "datatest-stable::example with_contents::test_artifact_bytes::other.json",
        "datatest-stable::example with_contents::test_artifact_utf8_string::::colon::dir/::.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_string::::colon::dir/a.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_string::dir/a.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_string::b.txt",
        "datatest-stable::example with_contents::test_artifact_utf8_string::c.skip.txt",
    ];

    #[test]
    fn run_example_with_colons() {
        let temp_dir = Utf8TempDir::with_prefix("datatest-stable").expect("created temp dir");
        std::fs::create_dir_all(temp_dir.path().join("tests")).expect("created dir");
        let dest = temp_dir.path().join("tests/files");

        // Make a copy of tests/files inside the temp dir.
        fs_extra::dir::copy(
            "tests/files",
            temp_dir.path().join("tests"),
            &fs_extra::dir::CopyOptions::new(),
        )
        .expect("copied files");

        // Add some files with colons in their names. (They can't be checked into the repo because
        // it needs to be cloned on Windows.)
        let colon_dir = dest.join("::colon::dir");
        std::fs::create_dir_all(&colon_dir).expect("created dir with colons");
        std::fs::write(colon_dir.join("::.txt"), b"floop").expect("wrote file with colons");
        std::fs::write(colon_dir.join("a.txt"), b"flarp").expect("wrote file with colons");

        // Now run the tests.
        let output = std::process::Command::new(cargo_bin())
            .args(["nextest", "run", "--test=example", "--color=never"])
            .env("__DATATEST_FULL_SCAN_FORBIDDEN", "1")
            .env("__DATATEST_CWD", temp_dir.path())
            .output()
            .expect("`cargo nextest` was successful");

        let stderr =
            std::str::from_utf8(&output.stderr).expect("cargo nextest stderr should be utf-8");

        assert!(
            output.status.success(),
            "nextest exited with 0 (exit status: {}, stderr: {stderr})",
            output.status
        );

        for line in EXPECTED_LINES
            .iter()
            .chain(EXPECTED_UNIX_LINES.iter())
            .copied()
            .chain(std::iter::once("31 tests run: 31 passed, 0 skipped"))
        {
            assert!(
                stderr.contains(line),
                "Expected to find substring\n  {line}\nin stderr\n  {stderr}",
            );
        }
    }
}

fn cargo_bin() -> String {
    std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string())
}
