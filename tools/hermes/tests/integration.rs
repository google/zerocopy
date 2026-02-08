use std::{fs, path::Path};

use serde::Deserialize;
use tempfile::tempdir;
use walkdir::WalkDir;

datatest_stable::harness! { { test = run_integration_test, root = "tests/fixtures", pattern = "hermes.toml$" } }

#[derive(Deserialize)]
struct TestConfig {
    #[serde(default)]
    artifact: Vec<ArtifactExpectation>,
}

#[derive(Deserialize)]
struct ArtifactExpectation {
    package: String,
    target: String,
    should_exist: bool,
}

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
        // Forces deterministic output path: target/hermes/hermes_test_target
        // (normally, the path includes a hash of the crate's path).
        .env("HERMES_TEST_SHADOW_NAME", "hermes_test_target");

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

    let mut assert = cmd.assert();

    // Tests can specify the expected exit status.
    let expected_status_file = test_case_root.join("expected_status.txt");
    if expected_status_file.exists() {
        let status = fs::read_to_string(&expected_status_file)?;
        if status.trim() == "failure" {
            assert = assert.failure();
        } else {
            assert = assert.success();
        }
    } else {
        assert = assert.success();
    };

    // Tests can specify the expected stderr.
    let expected_stderr_file = test_case_root.join("expected_stderr.txt");
    if expected_stderr_file.exists() {
        let needle = fs::read_to_string(expected_stderr_file)?;
        let output = assert.get_output();
        let stderr = std::str::from_utf8(&output.stderr).unwrap();
        if !stderr.contains(needle.trim()) {
            panic!(
                "Stderr mismatch.\nExpected substring: {}\nActual stderr:\n{}",
                needle.trim(),
                stderr
            );
        }
    }

    // Tests can specify the expected shadow crate content.
    let actual_shadow = sandbox_root.join("target/hermes/hermes_test_target/shadow");
    let expected_shadow = test_case_root.join("expected");

    if expected_shadow.exists() {
        assert_directories_match(&expected_shadow, &actual_shadow)?;
    }

    // 2. Verify Artifacts (New Logic)
    let artifacts_file = test_case_root.join("expected_artifacts.toml");
    if artifacts_file.exists() {
        let content = fs::read_to_string(&artifacts_file)?;
        let config: TestConfig = toml::from_str(&content)?;

        let charon_dir = sandbox_root.join("target/hermes/hermes_test_target/charon");
        assert_artifacts_match(&charon_dir, &config.artifact)?;
    }

    Ok(())
}

fn assert_artifacts_match(
    charon_dir: &Path,
    expectations: &[ArtifactExpectation],
) -> std::io::Result<()> {
    if !charon_dir.exists() {
        if expectations.iter().any(|e| e.should_exist) {
            panic!("Charon output directory does not exist: {:?}", charon_dir);
        }
        return Ok(());
    }

    // Collect all generated .llbc files
    let mut generated_files = Vec::new();
    for entry in fs::read_dir(charon_dir)? {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().to_string();
        if name.ends_with(".llbc") {
            generated_files.push(name);
        }
    }

    for exp in expectations {
        // We expect filenames format: "{package}-{target}-{hash}.llbc"
        // Since hash is dynamic, we match on prefix.
        let prefix = format!("{}-{}-", exp.package, exp.target);

        let found = generated_files.iter().any(|f| f.starts_with(&prefix));

        if exp.should_exist && !found {
            panic!(
                "Missing expected artifact for package='{}', target='{}'.\nExpected prefix: '{}'\nFound files: {:?}",
                exp.package, exp.target, prefix, generated_files
            );
        } else if !exp.should_exist && found {
            panic!(
                "Found unexpected artifact for package='{}', target='{}'.\nMatched prefix: '{}'\nFound files: {:?}",
                exp.package, exp.target, prefix, generated_files
            );
        }
    }

    Ok(())
}

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

        // Normalize line endings to prevent Windows/Linux CI failures.
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
