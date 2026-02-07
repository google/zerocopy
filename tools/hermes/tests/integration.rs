use std::{fs, path::Path};

use tempfile::tempdir;
use walkdir::WalkDir;

datatest_stable::harness! { { test = run_integration_test, root = "tests/fixtures", pattern = "hermes.toml$" } }

fn run_integration_test(path: &Path) -> datatest_stable::Result<()> {
    // `path` is `tests/fixtures/<test_case>/hermes.toml`
    let test_case_root = path.parent().unwrap();
    let test_name = test_case_root.file_name().unwrap().to_str().unwrap();
    let source_dir = test_case_root.join("source");

    // Perform all work in a sandbox directory. This ensures that we don't
    // get interference from `Cargo.toml` files in any parent directories.
    let temp = tempdir()?;
    let sandbox_root = temp.path().join(test_name);
    copy_dir_contents(&source_dir, &sandbox_root)?;

    let mut cmd = assert_cmd::cargo_bin_cmd!("hermes");
    cmd.env("CARGO_TARGET_DIR", sandbox_root.join("target"))
        .env_remove("RUSTFLAGS")
        .env("HERMES_TEST_SHADOW_NAME", "hermes_shadow");

    // Tests can specify the cwd to invoke from.
    let cwd_file = test_case_root.join("cwd.txt");
    if cwd_file.exists() {
        let rel_path = fs::read_to_string(cwd_file)?;
        cmd.current_dir(sandbox_root.join(rel_path.trim()));
    } else {
        cmd.current_dir(&sandbox_root);
    }

    // Tests can specify the arguments to pass to `hermes verify`.
    let args_file = test_case_root.join("args.txt");
    if args_file.exists() {
        let args_str = fs::read_to_string(args_file)?;
        cmd.args(args_str.trim().split_whitespace());
    } else {
        cmd.arg("verify");
    }

    let assert = cmd.assert();

    // Tests can specify the expected exit status.
    let expected_status_file = test_case_root.join("expected_status.txt");
    let assert = if expected_status_file.exists() {
        let status = fs::read_to_string(&expected_status_file)?;
        if status.trim() == "failure" {
            assert.failure()
        } else {
            assert.success()
        }
    } else {
        // Default to expecting success
        assert.success()
    };

    // Tests can specify the expected stderr.
    let expected_stderr_file = test_case_root.join("expected_stderr.txt");
    if expected_stderr_file.exists() {
        let needle = fs::read_to_string(expected_stderr_file)?;
        assert.stderr(predicates::str::contains(needle.trim()));
    }

    // Tests can specify the expected shadow crate content.
    let actual_shadow = sandbox_root.join("target/hermes_shadow");
    let expected_shadow = test_case_root.join("expected");

    if expected_shadow.exists() {
        assert_directories_match(&expected_shadow, &actual_shadow)?;
    } else {
        // If the test expects failure, we may not have a shadow crate to check.
        // Only warn if we expected success but found no 'expected' dir.
        if !expected_status_file.exists()
            || fs::read_to_string(&expected_status_file)?.trim() != "failure"
        {
            eprintln!("WARNING: No 'expected' directory found for test case '{}'", test_name);
        }
    }

    Ok(())
}

/// Recursively checks that every file in 'expected' exists in 'actual'
/// and has identical content.
fn assert_directories_match(expected: &Path, actual: &Path) -> std::io::Result<()> {
    for entry in WalkDir::new(expected) {
        let entry = entry?;
        if !entry.file_type().is_file() {
            continue;
        }

        let expected_path = entry.path();
        let relative_path = expected_path.strip_prefix(expected).unwrap();
        let actual_path = actual.join(relative_path);

        if !actual_path.exists() {
            panic!(
                "Missing File in Shadow Crate!\nFile: {:?}\nTest Case: {:?}",
                relative_path,
                expected.parent().unwrap().file_name()
            );
        }

        let expected_content = fs::read_to_string(expected_path)?;
        let actual_content = fs::read_to_string(&actual_path)?;

        // Normalize line endings to prevent Windows/Linux CI failures
        let expected_norm = expected_content.replace("\r\n", "\n");
        let actual_norm = actual_content.replace("\r\n", "\n");

        if expected_norm != actual_norm {
            eprintln!("=== CONTENT MISMATCH: {:?} ===", relative_path);
            eprintln!("--- Expected ---\n{}", expected_norm);
            eprintln!("--- Actual ---\n{}", actual_norm);
            panic!("Mismatch in {:?}", relative_path);
        }
    }

    Ok(())
}

/// Copies the *contents* of src into dst recursively.
fn copy_dir_contents(src: &Path, dst: &Path) -> std::io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_contents(&entry.path(), &dst.join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.join(entry.file_name()))?;
        }
    }
    Ok(())
}
