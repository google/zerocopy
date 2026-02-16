use std::{
    fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
};

use fs2::FileExt;
use serde::Deserialize;

datatest_stable::harness! { { test = run_integration_test, root = "tests/fixtures", pattern = "hermes.toml$" } }

#[derive(Deserialize)]
struct HermesToml {
    #[serde(default)]
    test: Option<TestConfig>,
}

#[derive(Deserialize)]
struct TestConfig {
    #[serde(default)]
    args: Option<Vec<String>>,
    #[serde(default)]
    cwd: Option<String>,
    #[serde(default)]
    log: Option<String>,
    #[serde(default)]
    expected_status: Option<String>,
    #[serde(default)]
    expected_stderr: Option<String>,
    #[serde(default)]
    expected_stderr_regex: Option<String>,
    #[serde(default)]
    artifact: Vec<ArtifactExpectation>,
    #[serde(default)]
    command: Vec<CommandExpectation>,
}

#[derive(Deserialize, Clone)]
struct ArtifactExpectation {
    package: String,
    target: String,
    should_exist: bool,
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    content_contains: Vec<String>,
}

#[derive(Deserialize, Clone)]
struct CommandExpectation {
    args: Vec<String>,
    #[serde(default)]
    should_not_exist: bool,
}

static SHARED_CACHE_PATH: OnceLock<PathBuf> = OnceLock::new();

fn get_or_init_shared_cache() -> (PathBuf, PathBuf) {
    // Resolve target directory relative to this test file or CARGO_MANIFEST_DIR
    let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let target_dir = manifest_dir.join("target");
    let cache_dir = target_dir.join("hermes_integration_cache");

    if let Some(p) = SHARED_CACHE_PATH.get() {
        return (p.clone(), target_dir);
    }
    let lean_backend_dir = cache_dir.join("backends/lean");
    let lock_path = target_dir.join("hermes_integration_cache.lock");

    std::fs::create_dir_all(&target_dir).unwrap();

    let lock_file = fs::File::create(&lock_path).unwrap();
    // Block until we get exclusive access
    lock_file.lock_exclusive().unwrap();

    // Check if valid cache exists (simple check: lakefile in backends/lean exists)
    if !lean_backend_dir.join("lakefile.lean").exists() {
        // eprintln!("Initializing shared Aeneas cache at {:?}...", cache_dir);

        // 1. Clone Aeneas repo to cache_dir
        let status = Command::new("git")
            .args(["clone", "https://github.com/AeneasVerif/aeneas", "--depth", "1"])
            .arg(&cache_dir)
            .status()
            .expect("Failed to execute git clone");
        assert!(status.success(), "Failed to clone Aeneas");

        // 2. Download Pre-built Mathlib binaries (must run in backends/lean)
        let status = Command::new("lake")
            .args(["exe", "cache", "get"])
            .current_dir(&lean_backend_dir)
            .status()
            .expect("Failed to execute lake exe cache get");
        assert!(status.success(), "Failed to run 'lake exe cache get'");

        // 3. Pre-build Aeneas
        let status = Command::new("lake")
            .arg("build")
            .current_dir(&lean_backend_dir)
            .status()
            .expect("Failed to execute lake build");
        assert!(status.success(), "Failed to pre-build Aeneas");
    }

    lock_file.unlock().unwrap();

    let _ = SHARED_CACHE_PATH.set(cache_dir.clone());
    let _ = SHARED_CACHE_PATH.set(cache_dir.clone());
    (cache_dir, target_dir)
}

fn run_integration_test(path: &Path) -> datatest_stable::Result<()> {
    // `path` is `tests/fixtures/<test_case>/hermes.toml`
    let test_case_root = path.parent().unwrap();
    let test_name = test_case_root.file_name().unwrap().to_str().unwrap();
    let source_dir = test_case_root.join("source");

    // We need the cache dir and the target dir (for temp files on same FS)
    let (cache_dir, target_dir) = get_or_init_shared_cache();
    let lean_backend_dir = cache_dir.join("backends/lean");

    // Perform all work in a sandbox directory. This ensures that we don't
    // get interference from `Cargo.toml` files in any parent directories.
    //
    // We use `tempdir_in` to ensure we are on the same filesystem as the cache,
    // which allows `cp -rl` (hardlinks) to work optimization.
    let temp = tempfile::Builder::new().prefix("hermes-test-").tempdir_in(&target_dir)?;
    let sandbox_root = temp.path().join(test_name);
    copy_dir_contents(&source_dir, &sandbox_root)?;

    // Copy extra.rs if it exists (for external_path_dep test)
    let extra_rs = test_case_root.join("extra.rs");
    if extra_rs.exists() {
        fs::copy(&extra_rs, temp.path().join("extra.rs"))?;
    }

    // Ensure the sandboxed crate is treated as a standalone workspace.
    // This is necessary because we are creating the sandbox inside `target/`,
    // which is inside the main workspace. Without this, cargo metadata fails.
    let cargo_toml_path = sandbox_root.join("Cargo.toml");
    if cargo_toml_path.exists() {
        let mut content = fs::read_to_string(&cargo_toml_path)?;
        if !content.contains("[workspace]") {
            content.push_str("\n[workspace]\n");
            fs::write(&cargo_toml_path, content)?;
        }
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

    // Use shared cache for Aeneas
    // Use shared cache for Aeneas
    // We already resolved this above
    cmd.env("HERMES_AENEAS_DIR", &cache_dir);
    cmd.env("HERMES_INTEGRATION_TEST_LEAN_CACHE_DIR", &lean_backend_dir);

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

    // Load Config from hermes.toml
    let hermes_toml_path = test_case_root.join("hermes.toml");
    let hermes_toml_content = fs::read_to_string(&hermes_toml_path)?;
    let hermes_toml: HermesToml = toml::from_str(&hermes_toml_content)?;
    let config = hermes_toml.test.unwrap_or_else(|| TestConfig {
        args: None,
        cwd: None,
        log: None,
        expected_status: None,
        expected_stderr: None,
        expected_stderr_regex: None,
        artifact: vec![],
        command: vec![],
    });

    // Tests can specify the log level.
    let log_level = config.log.clone().unwrap_or_else(|| "warn".to_string());
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
    if let Some(cwd) = &config.cwd {
        cmd.current_dir(sandbox_root.join(cwd));
    } else {
        cmd.current_dir(&sandbox_root);
    }


    // Tests can specify the arguments to pass to `hermes verify`.
    if let Some(args) = &config.args {
        cmd.args(args);
    } else {
        cmd.arg("verify");
    }

    let mut assert = cmd.assert();

    // Tests can specify the expected exit status.
    if let Some(status) = &config.expected_status {
        if status.trim() == "failure" {
            assert = assert.failure();
        } else {
            assert = assert.success();
        }
    } else {
        assert = assert.success();
    };

    if let Some(regex) = &config.expected_stderr_regex {
        check_stderr_regex(&assert, regex, &sandbox_root);
    } else if let Some(stderr) = &config.expected_stderr {
        check_stderr_contains(&assert, stderr, &sandbox_root);
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

fn check_stderr_regex(assert: &assert_cmd::assert::Assert, regex_str: &str, sandbox_root: &Path) {
    let output = assert.get_output();
    let actual_stderr = String::from_utf8_lossy(&output.stderr);
    let actual_stripped = strip_ansi_escapes::strip(&*actual_stderr);
    let actual_str = String::from_utf8_lossy(&actual_stripped).into_owned().replace("\r", "");
    let replace_path = sandbox_root.to_str().unwrap();
    let stderr = actual_str.replace(replace_path, "[PROJECT_ROOT]");

    let rx = regex::Regex::new(regex_str.trim()).unwrap();
    if !rx.is_match(&stderr) {
        panic!(
            "Stderr regex mismatch.\nExpected regex: {}\nActual stderr:\n{}",
            regex_str, stderr
        );
    }
}

fn check_stderr_contains(assert: &assert_cmd::assert::Assert, needle: &str, sandbox_root: &Path) {
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
