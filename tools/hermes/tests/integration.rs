use std::{fs, os::unix::fs::PermissionsExt, path::Path};

use serde::Deserialize;
use tempfile::tempdir;
use walkdir::WalkDir;

datatest_stable::harness! { { test = run_integration_test, root = "tests/fixtures", pattern = "hermes.toml$" } }

#[derive(Deserialize)]
struct TestConfig {
    #[serde(default)]
    artifact: Vec<ArtifactExpectation>,
    #[serde(default)]
    command: Vec<CommandExpectation>,
}

#[derive(Deserialize)]
struct ArtifactExpectation {
    package: String,
    target: String,
    should_exist: bool,
}

#[derive(Deserialize)]
struct CommandExpectation {
    args: Vec<String>,
    #[serde(default)]
    should_not_exist: bool,
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

    // --- SETUP CHARON SHIM ---
    let shim_dir = temp.path().join("bin");
    fs::create_dir_all(&shim_dir)?;

    let real_charon = which::which("charon").unwrap();
    let log_file = sandbox_root.join("charon_args.log");
    let shim_path = shim_dir.join("charon");
    let shim_content = format!(
        "#!/bin/sh\n\
# Log each argument on a new line\n\
for arg in \"$@\"; do\n\
    echo \"ARG:$arg\" >> \"{}\"\n\
done\n\
echo \"---END-INVOCATION---\" >> \"{}\"\n\
\n\
# Execute real charon\n\
exec \"{}\" \"$@\"\n",
        log_file.display(),
        log_file.display(),
        real_charon.display()
    );

    fs::write(&shim_path, shim_content)?;

    let mut perms = fs::metadata(&shim_path)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&shim_path, perms)?;

    let mut cmd = assert_cmd::cargo_bin_cmd!("hermes");

    // Prepend shim_dir to PATH (make sure our shim comes first).
    let original_path = std::env::var_os("PATH").unwrap_or_default();
    let new_path = std::env::join_paths(
        std::iter::once(shim_dir).chain(std::env::split_paths(&original_path)),
    )?;

    cmd.env("CARGO_TARGET_DIR", sandbox_root.join("target"))
        .env("PATH", new_path)
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

    // Load Config
    let mut config = TestConfig { artifact: vec![], command: vec![] };
    let config_file = test_case_root.join("expected_config.toml");
    if config_file.exists() {
        let content = fs::read_to_string(&config_file)?;
        config = toml::from_str(&content)?;
    }

    // Backward compatibility for the previous step instructions
    let artifacts_file = test_case_root.join("expected_artifacts.toml");
    if artifacts_file.exists() {
        let content = fs::read_to_string(&artifacts_file)?;
        let partial: TestConfig = toml::from_str(&content)?;
        config.artifact.extend(partial.artifact);
    }

    if !config.artifact.is_empty() {
        let charon_dir = sandbox_root.join("target/hermes/hermes_test_target/charon");
        assert_artifacts_match(&charon_dir, &config.artifact)?;
    }

    if !config.command.is_empty() {
        if !log_file.exists() {
            panic!("Command log file not found! Was the shim called?");
        }
        let log_content = fs::read_to_string(log_file)?;
        let invocations = parse_command_log(&log_content);
        assert_commands_match(&invocations, &config.command);
    }

    Ok(())
}

fn parse_command_log(content: &str) -> Vec<Vec<String>> {
    let mut invocations = Vec::new();
    let mut current_args = Vec::new();

    for line in content.lines() {
        if line == "---END-INVOCATION---" {
            invocations.push(current_args);
            current_args = Vec::new();
        } else if let Some(arg) = line.strip_prefix("ARG:") {
            current_args.push(arg.to_string());
        }
    }
    invocations
}

fn assert_commands_match(invocations: &[Vec<String>], expectations: &[CommandExpectation]) {
    for exp in expectations {
        let mut found = false;
        for cmd in invocations {
            // Check if exp.args is a subsequence of cmd
            if is_subsequence(cmd, &exp.args) {
                found = true;
                break;
            }
        }

        if !exp.should_not_exist && !found {
            panic!("Expected command invocation with args {:?} was not found.\nCaptured Invocations: {:#?}", exp.args, invocations);
        } else if exp.should_not_exist && found {
            panic!("Unexpected command invocation with args {:?} WAS found.", exp.args);
        }
    }
}

fn is_subsequence(haystack: &[String], needle: &[String]) -> bool {
    if needle.is_empty() {
        return true;
    }
    let mut needle_iter = needle.iter();
    let mut next_needle = needle_iter.next();

    for item in haystack {
        if let Some(n) = next_needle {
            if item == n {
                next_needle = needle_iter.next();
            }
        } else {
            return true;
        }
    }
    next_needle.is_none()
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
        let rel = entry.path().strip_prefix(expected).unwrap();
        let act = actual.join(rel);
        if !act.exists() {
            panic!("Missing file {:?}", rel);
        }
        let e_txt = fs::read_to_string(entry.path())?.replace("\r\n", "\n");
        let a_txt = fs::read_to_string(&act)?.replace("\r\n", "\n");
        if e_txt != a_txt {
            panic!("Mismatch in {:?}", rel);
        }
    }
    Ok(())
}

fn copy_dir_contents(src: &Path, dst: &Path) -> std::io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            copy_dir_contents(&entry.path(), &dst.join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.join(entry.file_name()))?;
        }
    }
    Ok(())
}
