use std::{fs, os::unix::fs::PermissionsExt, path::Path};

use serde::Deserialize;
use tempfile::tempdir;

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
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    content_contains: Vec<String>,
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

    // Copy extra.rs if it exists (for external_path_dep test)
    let extra_rs = test_case_root.join("extra.rs");
    if extra_rs.exists() {
        fs::copy(&extra_rs, temp.path().join("extra.rs"))?;
    }

    // --- SETUP CHARON SHIM ---
    let shim_dir = temp.path().join("bin");
    fs::create_dir_all(&shim_dir)?;

    let real_charon = which::which("charon").unwrap();
    let log_file = sandbox_root.join("charon_args.log");
    let shim_path = shim_dir.join("charon");
    let shim_content = format!(
        r#"#!/bin/sh
# Log each argument on a new line
for arg in "$@"; do
    echo "ARG:$arg" >> "{0}"
done
echo "---END-INVOCATION---" >> "{0}"

# If mock JSON is set, bypass charon and return mock payload to stdout
if [ -n "$HERMES_MOCK_CHARON_JSON" ]; then
    cat "$HERMES_MOCK_CHARON_JSON"
    exit 101
fi

# Execute real charon
exec "{1}" "$@"
"#,
        log_file.display(),
        real_charon.display(),
    );

    fs::write(&shim_path, shim_content)?;

    let mut perms = fs::metadata(&shim_path)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&shim_path, perms)?;

    // SHIM AENEAS
    let aeneas_shim_path = shim_dir.join("aeneas");
    // For now, we mock aeneas by doing nothing but logging arguments.
    // Real aeneas invocation in tests would require aeneas to be installed.
    // If we want to mock aeneas output (files), we can do that in the test fixture setup,
    // or improve this shim to copy files from a mock source.
    let aeneas_shim_content = format!(
        r#"#!/bin/sh
echo "AENEAS INVOKED" >> "{0}"
for arg in "$@"; do
    echo "AENEAS_ARG:$arg" >> "{0}"
done
echo "---END-INVOCATION---" >> "{0}"
"#,
        log_file.display(),
    );
    fs::write(&aeneas_shim_path, aeneas_shim_content)?;
    let mut perms = fs::metadata(&aeneas_shim_path)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&aeneas_shim_path, perms)?;

    let mut cmd = assert_cmd::cargo_bin_cmd!("hermes");
    cmd.env("HERMES_FORCE_TTY", "1");
    cmd.env("FORCE_COLOR", "1");

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
        .env("HERMES_TEST_DIR_NAME", "hermes_test_target");

    // Tests can specify the log level.
    let log_level = fs::read_to_string(test_case_root.join("rust_log.txt"))
        .unwrap_or_else(|_| "warn".to_string());
    cmd.env("RUST_LOG", log_level.trim());

    // Mock JSON integration
    let mock_json_file = test_case_root.join("mock_charon_output.json");
    if let Ok(mock_src) = fs::read_to_string(&mock_json_file) {
        let processed_mock = mock_src.replace("[PROJECT_ROOT]", sandbox_root.to_str().unwrap());

        let processed_mock_file = sandbox_root.join("mock_charon_output.json");
        fs::write(&processed_mock_file, &processed_mock).unwrap();

        let abs_processed = std::env::current_dir().unwrap().join(&processed_mock_file);

        cmd.env("HERMES_MOCK_CHARON_JSON", abs_processed);
    }

    // Tests can specify the cwd to invoke from.
    let rel_path = fs::read_to_string(test_case_root.join("cwd.txt")).unwrap_or_default();
    cmd.current_dir(sandbox_root.join(rel_path.trim()));

    // Tests can specify the arguments to pass to `hermes verify`.
    if let Ok(args_str) = fs::read_to_string(test_case_root.join("args.txt")) {
        cmd.args(args_str.split_whitespace());
    } else {
        cmd.arg("verify");
    }

    let mut assert = cmd.assert();

    // Tests can specify the expected exit status.
    if let Ok(status) = fs::read_to_string(test_case_root.join("expected_status.txt")) {
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
    let stderr_regex_path = test_case_root.join("expected_stderr.regex.txt");

    if stderr_regex_path.exists() {
        let expected_regex = fs::read_to_string(&stderr_regex_path)?;
        let output = assert.get_output();
        let actual_stderr = String::from_utf8_lossy(&output.stderr);
        let actual_stripped = strip_ansi_escapes::strip(&*actual_stderr);
        let actual_str = String::from_utf8_lossy(&actual_stripped).into_owned().replace("\r", "");
        let replace_path = sandbox_root.to_str().unwrap();
        let stderr = actual_str.replace(replace_path, "[PROJECT_ROOT]");

        let rx = regex::Regex::new(expected_regex.trim()).unwrap();
        if !rx.is_match(&stderr) {
            panic!(
                "Stderr regex mismatch.\nExpected regex: {}\nActual stderr:\n{}",
                expected_regex, stderr
            );
        }
    } else if expected_stderr_file.exists() {
        let needle = fs::read_to_string(expected_stderr_file)?;
        let output = assert.get_output();
        let actual_stderr = String::from_utf8_lossy(&output.stderr);
        let actual_stripped = strip_ansi_escapes::strip(&*actual_stderr);
        let actual_str = String::from_utf8_lossy(&actual_stripped).into_owned().replace("\r", "");
        let replace_path = sandbox_root.to_str().unwrap();
        let stderr = actual_str.replace(replace_path, "[PROJECT_ROOT]");

        if !stderr.contains(needle.trim()) {
            panic!(
                "Stderr mismatch.\nExpected substring: {}\nActual stderr:\n{}",
                needle.trim(),
                stderr
            );
        }
    }

    // Load Config
    let mut config = TestConfig { artifact: vec![], command: vec![] };
    if let Ok(content) = fs::read_to_string(test_case_root.join("expected_config.toml")) {
        config = toml::from_str(&content)?;
    }

    // Backward compatibility for the previous step instructions
    if let Ok(content) = fs::read_to_string(test_case_root.join("expected_artifacts.toml")) {
        let partial: TestConfig = toml::from_str(&content)?;
        config.artifact.extend(partial.artifact);
    }

    if !config.artifact.is_empty() {
        let hermes_run_root = sandbox_root.join("target/hermes/hermes_test_target");
        assert_artifacts_match(&hermes_run_root, &config.artifact)?;
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
        let found = invocations.iter().any(|cmd| is_subsequence(cmd, &exp.args));

        if !exp.should_not_exist && !found {
            panic!("Expected command invocation with args {:?} was not found.\nCaptured Invocations: {:#?}", exp.args, invocations);
        } else if exp.should_not_exist && found {
            panic!("Unexpected command invocation with args {:?} WAS found.", exp.args);
        }
    }
}

fn is_subsequence(haystack: &[String], needle: &[String]) -> bool {
    let mut needle_iter = needle.iter();
    let mut n = needle_iter.next();

    for item in haystack {
        if Some(item) == n {
            n = needle_iter.next();
        }
    }
    n.is_none()
}

fn assert_artifacts_match(
    hermes_run_root: &Path,
    expectations: &[ArtifactExpectation],
) -> std::io::Result<()> {
    let llbc_root = hermes_run_root.join("llbc");
    let lean_root = hermes_run_root.join("lean").join("generated");

    for exp in expectations {
        let kind = exp.kind.as_deref().unwrap_or("llbc");
        let (scan_dir, is_dir_match, suffix) = match kind {
            "llbc" => (&llbc_root, false, ".llbc"),
            "lean" => (&lean_root, true, ""),
            _ => panic!("Unknown artifact kind: {}", kind),
        };

        if !scan_dir.exists() {
            if exp.should_exist {
                panic!("Artifact directory does not exist: {:?}", scan_dir);
            }
            continue;
        }

        let mut found_items = Vec::new();
        for entry in fs::read_dir(scan_dir)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().to_string();
            if is_dir_match {
                if entry.file_type()?.is_dir() {
                    found_items.push(name);
                }
            } else if name.ends_with(suffix) {
                found_items.push(name);
            }
        }

        // We match strictly on the slug prefix: "{package}-{target}-"
        let prefix = format!("{}-{}-", exp.package, exp.target);
        let found = found_items.iter().any(|f| f.starts_with(&prefix));

        if exp.should_exist && !found {
            panic!(
                "Missing expected artifact for package='{}', target='{}', kind='{}'.\nExpected prefix: '{}'\nFound items in {:?}: {:?}",
                exp.package, exp.target, kind, prefix, scan_dir, found_items
            );
        } else if !exp.should_exist && found {
            panic!(
                "Found unexpected artifact for package='{}', target='{}', kind='{}'.\nMatched prefix: '{}'\nFound items in {:?}: {:?}",
                exp.package, exp.target, kind, prefix, scan_dir, found_items
            );
        }

        if found && !exp.content_contains.is_empty() {
            // Find the actual file/dir
            let file_name = found_items.iter().find(|f| f.starts_with(&prefix)).unwrap();
            let path = scan_dir.join(file_name);

            let content = if path.is_dir() {
                // For Lean artifacts, the content is in Specs.lean
                fs::read_to_string(path.join("Specs.lean"))?
            } else {
                fs::read_to_string(&path)?
            };

            for needle in &exp.content_contains {
                if !content.contains(needle) {
                    panic!(
                         "Artifact '{}' missing expected content.\nMissing: '{}'\nPath: {:?}\n\nFull Content:\n{}",
                         file_name, needle, path, content
                     );
                }
            }
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
