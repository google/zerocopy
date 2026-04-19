use std::{
    fs, io,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
    thread,
};

use serde::Deserialize;
use sha2::Digest;
use walkdir::WalkDir;

fn new_sorted_walkdir(path: impl AsRef<Path>) -> WalkDir {
    WalkDir::new(path).sort_by_file_name()
}

datatest_stable::harness! { { test = run_integration_test, root = "tests/fixtures", pattern = "anneal.toml$" } }

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AnnealToml {
    description: String,
    #[serde(default)]
    test: Option<TestConfig>,
}

#[derive(Debug, Deserialize, PartialEq, Eq, Default, Clone)]
#[serde(rename_all = "snake_case")]
enum ExpectedStatus {
    #[default]
    Success,
    Failure,
    KnownBug,
    KnownFlaky,
}

// A note on our "no implicit files" philosophy: We prefer explicit
// configuration to implicit conventions. Thus, unless explicitly specified in
// `anneal.toml` (e.g., via `stderr_file` or `matches_expected_directory`), the
// test runner will completely ignore all other files in
// `tests/fixtures/<test_case>`. It will not implicitly search for "implicit
// files" (like `expected.stderr`) if they are not named in the TOML
// configuration block. That ensures that when you read `anneal.toml`, you
// immediately know every single input and constraint of the test. Note that
// there are still a few implicit files/directories, but most are explicit.
#[derive(Deserialize, Default, Clone)]
#[serde(deny_unknown_fields)]
struct TestConfig {
    args: Option<Vec<String>>,
    cwd: Option<String>,
    #[serde(default)]
    extra_inputs: Vec<String>,
    stderr_file: Option<String>,
    stdout_file: Option<String>,
    #[serde(default)]
    expected_status: ExpectedStatus,
    #[serde(default)]
    artifact: Vec<ArtifactExpectation>,
    #[serde(default)]
    command: Vec<CommandExpectation>,
    mock: Option<MockConfig>,
    #[serde(default)]
    setup_mock: bool, // New field
    #[serde(default)]
    env: std::collections::HashMap<String, String>,
    #[serde(default)]
    phases: Vec<TestPhase>,
}

#[derive(Deserialize, Debug, PartialEq, Clone)]
#[serde(deny_unknown_fields)]
struct TestPhase {
    name: String,
    action: Option<String>,
    expected_status: Option<ExpectedStatus>,
    stderr_file: Option<String>,
    stdout_file: Option<String>,
    args: Option<Vec<String>>,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct MockConfig {
    charon: Option<String>,
    aeneas: Option<String>,
}

#[derive(Clone)]
enum MockMode {
    FailWithOutput(PathBuf),
    Script(PathBuf),
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct ArtifactExpectation {
    package: String,
    target: String,
    should_exist: bool,
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    content_contains: Vec<String>,
    #[serde(default)]
    content_lacks: Vec<String>,
    #[serde(default)]
    matches_expected_dir: Option<String>,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct CommandExpectation {
    args: Vec<String>,
    #[serde(default)]
    should_not_exist: bool,
}

static TARGET_DIR: OnceLock<PathBuf> = OnceLock::new();
static TOOLCHAIN_PATH: OnceLock<PathBuf> = OnceLock::new();

fn get_target_dir() -> PathBuf {
    TARGET_DIR
        .get_or_init(|| {
            if let Ok(override_dir) = std::env::var("ANNEAL_INTEGRATION_TARGET_DIR") {
                PathBuf::from(override_dir)
            } else {
                let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
                manifest_dir.join("target")
            }
        })
        .clone()
}

fn get_toolchain_path() -> PathBuf {
    TOOLCHAIN_PATH
        .get_or_init(|| {
            let cargo_bin = env!("CARGO_BIN_EXE_cargo-anneal");
            let output = Command::new(cargo_bin)
                .arg("toolchain-path")
                .output()
                .expect("Failed to execute cargo-anneal toolchain-path");

            if !output.status.success() {
                panic!(
                    "cargo-anneal toolchain-path failed: {:?}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }

            let path_str = String::from_utf8(output.stdout).unwrap();
            let toolchain_path = PathBuf::from(path_str.trim());

            if !toolchain_path.exists() {
                panic!(
                    "Resolved toolchain path does not exist: {:?}. Please run `cargo run setup` first.",
                    toolchain_path
                );
            }

            toolchain_path
        })
        .clone()
}

fn check_source_freshness(source_dir: &Path) -> Result<(), anyhow::Error> {
    // Recursively scan the source directory for blacklisted files/directories.
    //
    // The integration test harness enforces a strict "fresh sandbox" policy.
    // If the `source` directory in `tests/fixtures` contains any build
    // artifacts (e.g., `target`, `.lake`, `generated`, or compiled objects),
    // we fail immediately.
    //
    // This prevents accidental contamination of the test environment, where
    // stale artifacts from a previous manual run might mask errors or cause
    // non-deterministic behavior in the test runner.
    if !source_dir.exists() {
        return Ok(());
    }

    let walker = new_sorted_walkdir(source_dir).follow_links(true);
    for entry in walker {
        let entry = entry.map_err(|e| anyhow::anyhow!("Failed to walk source dir: {}", e))?;
        let name = entry.file_name().to_string_lossy();
        let path = entry.path();

        // Check for blacklisted DIRECTORIES.
        //
        // These directories contain build artifacts or generated code that
        // should never be present in the source fixture.
        //
        // Note: we use `entry.file_type().is_dir()` instead of `path.is_dir()`
        // so that if a developer symlinks `target` into the directory (e.g.
        // `ln -s ../../../target target`), we identify the symlink target as a
        // directory and reject it. `path.is_dir()` would return false for the
        // symlink itself.
        if entry.file_type().is_dir()
            && (name == "target"
                || name == ".lake"
                || name == "generated"
                || name == "llbc"
                || name == "cargo_target")
        {
            anyhow::bail!(
                "Stale build artifact directory found in fixture source: {:?}\n\
                    Please remove it to ensure a clean test environment.",
                path
            );
        }

        // Check for blacklisted FILES.
        //
        // These specific files are auto-generated by the build system
        // (Lake/Cargo) or by Anneal itself. Their presence indicates a dirty
        // source tree.
        if entry.file_type().is_file()
            && (name == "lake-manifest.json"
                || name == "lakefile.lean"
                || name == "lean-toolchain"
                || name.ends_with(".olean")
                || name.ends_with(".ilean")
                || name.ends_with(".c")
                || name.ends_with(".o"))
        {
            anyhow::bail!(
                "Found blacklisted file in source: {}\n\
                     This indicates a stale or dirty source. Please clean the source directory.",
                path.display()
            );
        }
    }
    Ok(())
}

/// Returns the path to Lake's content-addressed artifact cache, populated
/// at toolchain setup time and consumed (read-only) by every test process.
///
/// The cache is colocated with the toolchain rather than `~/.cache/lake`
/// because integration tests redirect `HOME` to a per-test sandbox; without
/// pinning the cache to a stable path, every test would observe an empty
/// `~/.cache/lake` and cold-build Mathlib.
fn lake_cache_dir() -> PathBuf {
    get_toolchain_path().join("lake_cache")
}

/// Asserts once per test process that the Aeneas Lean backend is fully
/// precompiled and that the Lake artifact cache is reachable. Runs
/// `lake build --no-build Mathlib` from the toolchain's `backends/lean`
/// directory; this succeeds only if every required `.olean` is resolvable
/// either from the toolchain's own `.lake/` or the artifact cache.
///
/// Runs at most once per test process via `OnceLock`. Panics on failure —
/// the test suite cannot proceed without a working Lean cache, and a panic
/// here surfaces the root cause far more clearly than a multi-hour Mathlib
/// recompile inside an unrelated test.
fn verify_lean_cache_warm() {
    static VERIFIED: OnceLock<()> = OnceLock::new();
    VERIFIED.get_or_init(|| {
        let lean_dir = get_toolchain_path().join("backends/lean");
        let output = Command::new("lake")
            .args(["build", "--no-build", "Mathlib.Tactic"])
            .env("LAKE_CACHE_DIR", lake_cache_dir())
            .current_dir(&lean_dir)
            .output()
            .unwrap_or_else(|e| {
                panic!("Failed to invoke `lake` to verify cache at {:?}: {}", lean_dir, e)
            });

        if !output.status.success() {
            panic!(
                "Lean cache is not fully precompiled. `lake build --no-build Mathlib` at {:?} \
                 reported missing artifacts. Re-run `cargo run setup` to repopulate the toolchain \
                 and Lake artifact cache.\nstdout:\n{}\nstderr:\n{}",
                lean_dir,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
        }
    });
}

struct TestContext {
    test_case_root: PathBuf,
    test_name: String,
    sandbox_root: PathBuf,
    _temp_dir: Option<tempfile::TempDir>, // Kept alive to prevent deletion
    home_dir: PathBuf,
}

impl TestContext {
    fn new(path: &Path, config: &TestConfig) -> datatest_stable::Result<Self> {
        let test_case_root = path.parent().unwrap().to_path_buf();
        let test_name = test_case_root.file_name().unwrap().to_string_lossy().to_string();
        let source_dir = test_case_root.join("source");
        check_source_freshness(&source_dir).map_err(|e| e.to_string())?;

        let target_dir = get_target_dir();
        fs::create_dir_all(&target_dir)?;
        let toolchain_path = get_toolchain_path();
        let temp = tempfile::Builder::new().prefix("anneal-test-").tempdir_in(&target_dir)?;

        let sandbox_root = temp.path().join(&test_name);
        let home_dir = temp.path().join("home");
        fs::create_dir_all(&home_dir)?;
        copy_dir_contents(&source_dir, &sandbox_root)?;

        // Check if we should keep the test directory for debugging
        let temp_dir_to_store = if std::env::var("ANNEAL_KEEP_TEST_DIR").as_deref() == Ok("1")
            || std::env::var("KEEP_TEST_DIR").as_deref() == Ok("1")
        {
            #[allow(deprecated)]
            let path = temp.into_path();
            eprintln!("========================================================================");
            eprintln!("KEEP_TEST_DIR enabled! Test directory preserved at:");
            eprintln!("{}", path.display());
            eprintln!("========================================================================");
            None
        } else {
            Some(temp)
        };

        let lean_root = sandbox_root.join("target/anneal/anneal_test_target/lean");
        fs::create_dir_all(&lean_root)?;

        // We skip seeding the Lean workspace cache for mock setup tests because
        // they do not run the full verification pipeline and do not need Lean.
        if !config.setup_mock {
            // Verify once per test process that the toolchain's Lean cache and
            // the Lake artifact cache are both populated. Catches a partially
            // installed or wiped toolchain before it manifests as a multi-hour
            // Mathlib recompile inside an unrelated test.
            verify_lean_cache_warm();

            // The Lean manifest dictates which dependencies Lake needs to
            // resolve. We copy this directly from the toolchain to ensure the
            // test sandbox observes exactly the same dependency tree as the
            // precompiled artifacts. If we did not copy this lockfile, Lake
            // would attempt to resolve dependencies from scratch. Since our
            // dependencies specify floating branches rather than explicit git
            // hashes in their configuration files, a fresh resolution could
            // map to newer commits. A mismatch in a single commit hash
            // invalidates the shared compilation cache, causing Lean to
            // redundantly recompile the entire dependency tree (e.g.,
            // Mathlib) from source. Copying the manifest guarantees a cache
            // hit.
            let aeneas_backend_lean = toolchain_path.join("backends/lean");
            let source_manifest = aeneas_backend_lean.join("lake-manifest.json");
            let target_manifest = lean_root.join("lake-manifest.json");
            if source_manifest.exists() {
                fs::copy(&source_manifest, &target_manifest)?;
                let mut perms = fs::metadata(&target_manifest)?.permissions();
                #[allow(clippy::permissions_set_readonly_false)]
                perms.set_readonly(false);
                fs::set_permissions(&target_manifest, perms)?;

                // We must manually inject the `aeneas` package into the
                // manifest. Otherwise Lake would consider the workspace
                // unresolved and run global post-update hooks. These hooks
                // trigger operations such as large cloud cache downloads for
                // Mathlib, resulting in severe performance regressions (e.g.,
                // tens of minutes per test run).
                //
                // By manually constructing the `aeneas` path dependency entry
                // and injecting it into the manifest, we trick Lake into
                // accepting the workspace configuration as fully resolved,
                // preventing the execution of these expensive hooks. The dep
                // points directly at the (read-only) toolchain backend; Lake
                // pulls compiled `.olean`s either from the backend's own
                // `.lake/` or from `LAKE_CACHE_DIR`, so no per-test writable
                // copy is needed.
                if let Ok(content) = fs::read_to_string(&target_manifest) {
                    if let Ok(mut json) = serde_json::from_str::<serde_json::Value>(&content) {
                        if let Some(packages) =
                            json.get_mut("packages").and_then(|v| v.as_array_mut())
                        {
                            let aeneas_url = aeneas_backend_lean.display().to_string();
                            let entry = serde_json::json!({
                                "dir": aeneas_url,
                                "type": "path",
                                "name": "aeneas",
                                "subDir": null,
                                "scope": "",
                                "rev": null,
                                "inputRev": null,
                                "inherited": false,
                                "configFile": "lakefile.lean",
                                "manifestFile": "lake-manifest.json"
                            });
                            packages.push(entry);

                            if let Ok(new_content) = serde_json::to_string_pretty(&json) {
                                let _ = fs::write(&target_manifest, new_content);
                            }
                        }
                    }
                }
            }

            // Share the toolchain's already-checked-out dependency source trees
            // (Mathlib, batteries, etc., each with its own multi-hundred-MB
            // `.git/`) by symlinking the entire `packages/` directory into the
            // sandbox. Without this, Lake re-clones every dep from scratch into
            // each test's sandbox `.lake/packages/`. The dep-internal `.lake/
            // build/` subdirs are shared across parallel tests as a result; that
            // is safe as long as `LAKE_CACHE_DIR` keeps tests on the cache-read
            // path so Lake never writes there.
            let toolchain_packages = aeneas_backend_lean.join(".lake/packages");
            if toolchain_packages.exists() {
                let sandbox_lake = lean_root.join(".lake");
                fs::create_dir_all(&sandbox_lake)?;
                std::os::unix::fs::symlink(&toolchain_packages, sandbox_lake.join("packages"))
                    .map_err(|e| {
                        anyhow::anyhow!("Failed to symlink toolchain packages dir: {}", e)
                    })?;
            }
        }

        // Copy extra inputs based on config.
        for extra in &config.extra_inputs {
            let extra_path = test_case_root.join(extra);
            if extra_path.exists() {
                let dest = sandbox_root.join(extra);
                if let Some(parent) = dest.parent() {
                    // Create parent directories for the destination to support
                    // copying extra inputs into nested paths within the
                    // sandbox.
                    fs::create_dir_all(parent)?;
                }
                fs::copy(&extra_path, dest)?;
            }
        }

        Ok(Self { test_case_root, test_name, sandbox_root, _temp_dir: temp_dir_to_store, home_dir })
    }

    fn create_shim(
        &self,
        binary: &str,
        real_path: &Path,
        mock_mode: Option<MockMode>,
    ) -> io::Result<PathBuf> {
        let shim_dir = self.sandbox_root.join("bin_shim");
        fs::create_dir_all(&shim_dir)?;

        let log_file = self.sandbox_root.join("tool_args.log");
        let shim_path = shim_dir.join(binary);

        let mut shim_content = String::new();
        shim_content.push_str("#!/bin/sh\n");

        // For backward compatibility with legacy tests, we log "AENEAS INVOKED"
        // for Aeneas. This allows existing tests to verify that Aeneas was
        // actually called.
        if binary == "aeneas" {
            use std::fmt::Write;
            writeln!(shim_content, "echo \"AENEAS INVOKED\" >> \"{}\"", log_file.display())
                .unwrap();
        }

        shim_content.push_str(&format!(
            r#"for arg in "$@"; do
    echo "{}_ARG:$arg" >> "{}"
done
echo "---END-INVOCATION---" >> "{}"
"#,
            binary.to_uppercase(),
            log_file.display(),
            log_file.display()
        ));

        // If a mock mode is specified, we configure the shim to either fail with
        // a specific output or execute a provided script. Otherwise, we exec
        // the real binary.
        match mock_mode {
            Some(MockMode::FailWithOutput(mock_file)) => {
                use std::fmt::Write;
                writeln!(shim_content, "cat \"{}\"\nexit 101", mock_file.display()).unwrap();
            }
            Some(MockMode::Script(script_path)) => {
                use std::fmt::Write;
                writeln!(shim_content, "exec \"{}\" \"$@\"", script_path.display()).unwrap();
            }
            Option::None => {
                use std::fmt::Write;
                writeln!(shim_content, "exec \"{}\" \"$@\"", real_path.display()).unwrap();
            }
        }

        fs::write(&shim_path, &shim_content)?;
        let mut perms = fs::metadata(&shim_path)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&shim_path, perms)?;

        Ok(shim_dir)
    }

    fn run_anneal(&self, config: &TestConfig) -> assert_cmd::assert::Assert {
        let mut cmd = assert_cmd::cargo_bin_cmd!("cargo-anneal");
        cmd.env_clear();

        // After clearing the environment to prevent scope leakage, we must
        // manually forward essential host variables required for toolchains.
        for var in [
            "RUSTUP_HOME",
            "CARGO_HOME",
            "RUSTUP_TOOLCHAIN",
            "ELAN_HOME",
            "LD_LIBRARY_PATH",
            "TMPDIR",
            "TMP",
            "TEMP",
            "USER",
            "USERNAME",
            "ANNEAL_TOOLCHAIN_DIR",
        ] {
            if var == "ANNEAL_TOOLCHAIN_DIR"
                && (self.test_name == "setup_e2e" || self.test_name == "setup_repair")
            {
                continue;
            }
            if let Some(val) = std::env::var_os(var) {
                cmd.env(var, val);
            }
        }

        cmd.env("HOME", &self.home_dir);

        if let Ok(elan_home) = std::env::var("ELAN_HOME") {
            cmd.env("ELAN_HOME", elan_home);
        } else {
            let elan_home = if std::env::var("__ZEROCOPY_LOCAL_DEV").is_ok() {
                get_target_dir().join("anneal-home/.elan")
            } else {
                PathBuf::from(std::env::var("HOME").unwrap()).join(".elan")
            };
            cmd.env("ELAN_HOME", elan_home);
        }

        let toolchain_path = get_toolchain_path();
        let lean_backend_dir = toolchain_path.join("backends/lean");

        // Resolve Mocks

        // Re-organizing execution flow:
        // 1. Prepare mocks (if any)
        let mut charon_mock_mode = None;
        let mut aeneas_mock_mode = None;

        if let Some(mock_config) = &config.mock {
            if let Some(charon_mock) = &mock_config.charon {
                let mock_src = self.test_case_root.join(charon_mock);

                if charon_mock.ends_with(".sh") {
                    let bin_dir = self.sandbox_root.join("bin");
                    fs::create_dir_all(&bin_dir).unwrap();
                    let script_dest = bin_dir.join(charon_mock);
                    fs::copy(&mock_src, &script_dest).unwrap();

                    let mut perms = fs::metadata(&script_dest).unwrap().permissions();
                    perms.set_mode(0o755);
                    fs::set_permissions(&script_dest, perms).unwrap();

                    charon_mock_mode = Some(MockMode::Script(script_dest));
                } else {
                    let mock_content =
                        fs::read_to_string(&mock_src).expect("Failed to read mock file");

                    let processed_mock =
                        mock_content.replace("[PROJECT_ROOT]", self.sandbox_root.to_str().unwrap());
                    let processed_mock_file = self.sandbox_root.join("mock_charon.json");
                    fs::write(&processed_mock_file, &processed_mock).unwrap();
                    charon_mock_mode = Some(MockMode::FailWithOutput(processed_mock_file));
                }
            }
            if let Some(aeneas_script) = &mock_config.aeneas {
                let script_src = self.test_case_root.join(aeneas_script);
                let bin_dir = self.sandbox_root.join("bin");
                fs::create_dir_all(&bin_dir).unwrap();
                let script_dest = bin_dir.join("mock_aeneas.sh");
                fs::copy(&script_src, &script_dest).unwrap();

                let mut perms = fs::metadata(&script_dest).unwrap().permissions();
                perms.set_mode(0o755);
                fs::set_permissions(&script_dest, perms).unwrap();

                aeneas_mock_mode = Some(MockMode::Script(script_dest));
            }
        }

        // Create shims for Charon and Aeneas.
        //
        // Even if we are using the "real" binary, we wrap it in a shim to
        // capture the arguments passed to it. This allows us to assert that
        // Anneal calls the tools with the expected arguments.

        let toolchain_path = get_toolchain_path();
        let real_charon = toolchain_path.join("charon");
        let shim_dir = self.create_shim("charon", &real_charon, charon_mock_mode).unwrap();

        let real_aeneas = toolchain_path.join("aeneas");
        self.create_shim("aeneas", &real_aeneas, aeneas_mock_mode).unwrap();

        if config.setup_mock {
            let server =
                tiny_http::Server::http("127.0.0.1:0").expect("Failed to start mock server");
            let port = server.server_addr().to_ip().unwrap().port();
            let base_url = format!("http://127.0.0.1:{}", port);
            cmd.env("ANNEAL_SETUP_AENEAS_BASE_URL", &base_url);
            cmd.env("ANNEAL_SETUP_RUST_BASE_URL", &base_url);
            cmd.env("__ANNEAL_USE_MOCK_RUST_HASHES", "1");
            // Skip the Lean library prebuild during setup-flow tests. Those
            // fixtures only assert which binaries land on disk; running
            // `prebuild_lean_library` would invoke `lake exe cache get` against
            // real Mathlib infrastructure on every test.
            cmd.env("__ANNEAL_SKIP_PREBUILD_LEAN", "1");

            let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
            let testdata_setup = manifest_dir.join("testdata/setup");

            thread::spawn(move || {
                for request in server.incoming_requests() {
                    let url = request.url();
                    // URL is e.g. /build-HASH/charon-linux-x86_64.tar.gz
                    let parts: Vec<&str> = url.split('/').collect();
                    if let Some(filename) = parts.last() {
                        let file_path = testdata_setup.join(filename);
                        if file_path.exists() {
                            let file = std::fs::File::open(file_path).unwrap();
                            let response = tiny_http::Response::from_file(file);
                            request.respond(response).unwrap();
                            continue;
                        }
                    }
                    request
                        .respond(
                            tiny_http::Response::from_string("Not Found").with_status_code(404),
                        )
                        .unwrap();
                }
            });
        }

        cmd.env("ANNEAL_FORCE_TTY", "1");
        cmd.env("FORCE_COLOR", "1");
        let isolated_aeneas_dir = self.sandbox_root.join("aeneas_cache");
        fs::create_dir_all(&isolated_aeneas_dir).unwrap();
        cmd.env("ANNEAL_AENEAS_DIR", isolated_aeneas_dir);
        cmd.env("ANNEAL_INTEGRATION_TEST_LEAN_CACHE_DIR", &lean_backend_dir);
        cmd.env("ANNEAL_USE_PATH_FOR_TOOLS", "1");
        cmd.env("RAYON_NUM_THREADS", "1");
        // Pin Lake's content-addressed artifact cache to the toolchain-local
        // path populated at setup time. `HOME` is redirected to a per-test
        // sandbox below, so without this pin Lake would look in an empty
        // `<sandbox>/home/.cache/lake` and cold-build Mathlib every test.
        // `LAKE_ARTIFACT_CACHE` is intentionally NOT set: tests should be
        // pure readers of the cache, never writers.
        cmd.env("LAKE_CACHE_DIR", lake_cache_dir());
        // Suppress Mathlib's post-update hook that would otherwise attempt to
        // download Mathlib's CI cloud cache. We rely entirely on the toolchain's
        // pre-populated artifact cache.
        cmd.env("MATHLIB_NO_CACHE_ON_UPDATE", "1");

        let original_path = std::env::var_os("PATH").unwrap_or_default();
        let new_path = std::env::join_paths(
            std::iter::once(shim_dir).chain(std::env::split_paths(&original_path)),
        )
        .unwrap();

        // Ensure deterministic LLBC generation within the integration test
        // sandbox by rebasing the `workspace_root` off the absolute filesystem
        // onto `/dummy`.
        let rustflags = format!("--remap-path-prefix={}=/dummy", self.test_case_root.display());

        cmd.env("CARGO_TARGET_DIR", self.sandbox_root.join("target"))
            .env("PATH", new_path)
            .env("RUSTFLAGS", rustflags)
            // Redirect HOME to the persistent home directory within the sandbox.
            // This ensures that the toolchain is looked up and potentially
            // repaired/reinstalled in a location that is isolated from the
            // user's actual home directory but remains persistent across
            // multiple `anneal` invocations within this single test context.
            .env("HOME", &self.home_dir)
            .env("ANNEAL_TEST_DIR_NAME", "anneal_test_target")
            .env("ANNEAL_HASH_WITH_REMOVED_PREFIX", &self.sandbox_root);

        for (k, v) in &config.env {
            cmd.env(k, v);
        }

        if !self.sandbox_root.exists() {
            panic!("sandbox_root does NOT exist! {:?}", self.sandbox_root);
        }
        if let Some(cwd) = &config.cwd {
            cmd.current_dir(self.sandbox_root.join(cwd));
        } else {
            cmd.current_dir(&self.sandbox_root);
        }

        if let Some(args) = &config.args {
            cmd.args(args);
        } else {
            cmd.arg("verify");
        }

        cmd.assert()
    }
}

fn run_integration_test(path: &Path) -> datatest_stable::Result<()> {
    let path_str = path.to_string_lossy();

    let anneal_toml_content = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", path.display(), e));
    let anneal_toml: AnnealToml = toml::from_str(&anneal_toml_content)
        .unwrap_or_else(|e| panic!("Failed to parse {}: {}", path.display(), e));
    let test_case_root = path.parent().unwrap();
    let test_name = test_case_root.file_name().unwrap().to_string_lossy().to_string();
    assert!(
        !anneal_toml.description.trim().is_empty(),
        "Test {} is missing a non-empty `description` field in anneal.toml",
        test_name
    );

    // Special handling for the "dirty_sandbox" test case.
    if path_str.contains("dirty_sandbox/anneal.toml") {
        return run_dirty_sandbox_test(path);
    }
    // // Special handling for the "atomic_writes" test case.
    // if path_str.contains("atomic_writes/anneal.toml") {
    //     return run_atomic_writes_test(path);
    // }
    // Special handling for the "toolchain_versioning" test case.
    if path_str.contains("toolchain_versioning/anneal.toml") {
        return run_toolchain_versioning_test(path);
    }

    // Load the test configuration from the associated 'anneal.toml' manifest.
    let config = anneal_toml.test.unwrap_or_default();

    // `path` is `tests/fixtures/<test_case>/anneal.toml`
    let ctx = TestContext::new(path, &config)?;

    if config.phases.is_empty() {
        run_single_phase(&ctx, &config, None)?;
    } else {
        for phase in &config.phases {
            run_single_phase(&ctx, &config, Some(phase))?;
        }
    }

    if config.expected_status == ExpectedStatus::KnownBug
        || config.expected_status == ExpectedStatus::KnownFlaky
    {
        return Ok(());
    }

    // Verify that the artifacts generated by the toolchain match the expected
    // outputs.
    if !config.artifact.is_empty() {
        let anneal_run_root = ctx.sandbox_root.join("target/anneal/anneal_test_target");
        assert_artifacts_match(&anneal_run_root, &ctx.test_case_root, &config.artifact)?;
    }

    // Verify Commands
    if !config.command.is_empty() {
        let log_file = ctx.sandbox_root.join("tool_args.log");
        if !log_file.exists() {
            panic!("Command log file not found! Was the shim called?");
        }
        let log_content = fs::read_to_string(log_file)?;
        let invocations = parse_command_log(&log_content);
        assert_commands_match(&invocations, &config.command);
    }

    assert_no_unmapped_files(&ctx, &config);

    Ok(())
}

fn assert_no_unmapped_files(ctx: &TestContext, config: &TestConfig) {
    let mut allowed_paths = std::collections::HashSet::new();

    // Always allowed baseline files/directories
    allowed_paths.insert(ctx.test_case_root.join("source"));
    allowed_paths.insert(ctx.test_case_root.join("anneal.toml"));

    // Track artifacts that are explicitly defined in the test configuration
    // TOML. This allows them to bypass the unmapped file directory check.
    if let Some(mock) = &config.mock {
        if let Some(charon) = &mock.charon {
            allowed_paths.insert(ctx.test_case_root.join(charon));
        }
        if let Some(aeneas) = &mock.aeneas {
            allowed_paths.insert(ctx.test_case_root.join(aeneas));
        }
    }

    for extra in &config.extra_inputs {
        allowed_paths.insert(ctx.test_case_root.join(extra));
    }

    if let Some(stderr_file) = &config.stderr_file {
        allowed_paths.insert(ctx.test_case_root.join(stderr_file));
    }
    if let Some(stdout_file) = &config.stdout_file {
        allowed_paths.insert(ctx.test_case_root.join(stdout_file));
    }
    for phase in &config.phases {
        if let Some(stderr_file) = &phase.stderr_file {
            allowed_paths.insert(ctx.test_case_root.join(stderr_file));
        }
        if let Some(stdout_file) = &phase.stdout_file {
            allowed_paths.insert(ctx.test_case_root.join(stdout_file));
        }
    }

    // Mock testing payloads
    if let Some(mock) = &config.mock {
        if let Some(charon) = &mock.charon {
            allowed_paths.insert(ctx.test_case_root.join(charon));
        }
        if let Some(aeneas) = &mock.aeneas {
            allowed_paths.insert(ctx.test_case_root.join(aeneas));
        }
    }

    // Explicit compilation golden directories
    for exp in &config.artifact {
        if let Some(dir) = &exp.matches_expected_dir {
            allowed_paths.insert(ctx.test_case_root.join(dir));
        }
    }

    // Iterate through everything physically present in the test's root fixture
    // directory.
    let walker = new_sorted_walkdir(&ctx.test_case_root).into_iter();
    for entry in walker.filter_entry(|e| !e.path().ends_with(".git")) {
        let entry = entry.unwrap();
        let path = entry.path();

        if !entry.file_type().is_file() {
            continue;
        }

        let mut is_allowed = false;
        for allowed in &allowed_paths {
            if path == *allowed || path.starts_with(allowed) {
                is_allowed = true;
                break;
            }
        }

        if !is_allowed {
            let rel = path.strip_prefix(&ctx.test_case_root).unwrap();
            panic!(
                "Unmapped file or directory in test fixture: {:?}\nIf this file is part of the test payload, it must be explicitly configured in anneal.toml (e.g., via `matches_expected_dir`, `stderr_file`, or `mock`). If it is an obsolete snapshot or temporary file, please delete it.",
                rel
            );
        }
    }
}

fn run_single_phase(
    ctx: &TestContext,
    base_config: &TestConfig,
    phase: Option<&TestPhase>,
) -> datatest_stable::Result<()> {
    if let Some(phase) = phase
        && let Some(action) = &phase.action
    {
        if action == "touch_stale_file" {
            let target_dir = ctx.sandbox_root.join("target");
            let generated_root = find_generated_root(&target_dir)?;

            let mut slug_dir = None;
            for entry in fs::read_dir(&generated_root)? {
                let entry = entry?;
                if entry.file_type()?.is_dir() {
                    slug_dir = Some(entry.path());
                    break;
                }
            }
            let slug_dir = slug_dir.ok_or_else(|| {
                io::Error::new(io::ErrorKind::NotFound, "No slug directory found in generated root")
            })?;

            let stale_file = slug_dir.join("Stale.lean");
            std::fs::write(&stale_file, "INVALID LEAN CODE").unwrap();
            assert!(stale_file.exists());

            return Ok(());
        } else if action == "delete_lake_dir" {
            // Delete Lake's build outputs to force regeneration of locally-
            // compiled artifacts (e.g. the per-test `Generated.olean`),
            // ensuring stale cached data doesn't mask bugs in artifact
            // generation or synchronization. Scoped to `.lake/build/` so the
            // sibling `.lake/packages/` symlink to the toolchain's dep
            // checkouts is preserved — without that, Lake would re-clone
            // every dependency from scratch.
            let lean_root = ctx.sandbox_root.join("target/anneal/anneal_test_target/lean");
            let build_dir = lean_root.join(".lake/build");
            if build_dir.exists() {
                fs::remove_dir_all(&build_dir).expect("Failed to delete .lake/build directory");
            }
            return Ok(());
        } else if action.starts_with("delete_toolchain_file ") {
            let file_name = action.strip_prefix("delete_toolchain_file ").unwrap();
            let toolchain_root = ctx.home_dir.join(".anneal/toolchain");

            // The toolchain directory name includes a short hash of the version,
            // which changes whenever the managed dependencies are updated. To
            // remain robust across version changes, we scan for any directory
            // existing within the toolchain root.
            let build_dir = fs::read_dir(&toolchain_root)?
                .filter_map(|e| e.ok())
                .find(|e| e.file_type().map(|t| t.is_dir()).unwrap_or(false))
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::NotFound, "Toolchain build directory not found")
                })?
                .path();
            let target_file = build_dir.join(file_name);
            if target_file.exists() {
                fs::remove_file(&target_file).expect("Failed to delete toolchain file");
            }
            return Ok(());
        } else if action.starts_with("corrupt_toolchain_file ") {
            let file_name = action.strip_prefix("corrupt_toolchain_file ").unwrap();
            let toolchain_root = ctx.home_dir.join(".anneal/toolchain");

            // Scan for the hash-prefixed toolchain directory.
            let build_dir = fs::read_dir(&toolchain_root)?
                .filter_map(|e| e.ok())
                .find(|e| e.file_type().map(|t| t.is_dir()).unwrap_or(false))
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::NotFound, "Toolchain build directory not found")
                })?
                .path();
            let target_file = build_dir.join(file_name);
            if target_file.exists() {
                // We corrupt the file with a known string that our assertions can
                // identify later.
                fs::write(&target_file, "CORRUPTED CONTENT")
                    .expect("Failed to corrupt toolchain file");
            }
            return Ok(());
        } else if action.starts_with("assert_toolchain_binary ") {
            let rest = action.strip_prefix("assert_toolchain_binary ").unwrap();
            let mut parts = rest.split_whitespace();
            let file_name = parts
                .next()
                .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "Missing file name"))?;
            let expected_hash = parts.next();

            let toolchain_root = ctx.home_dir.join(".anneal/toolchain");
            if !toolchain_root.exists() {
                let home_exists = ctx.home_dir.exists();
                let mut entries = Vec::new();
                if home_exists && let Ok(rd) = fs::read_dir(&ctx.home_dir) {
                    for e in rd.filter_map(|e| e.ok()) {
                        entries.push(e.file_name().to_string_lossy().to_string());
                    }
                }
                panic!(
                    "Toolchain root missing at {:?}! home exists: {}, home contents: {:?}",
                    toolchain_root, home_exists, entries
                );
            }
            // Scan for the hash-prefixed toolchain directory.
            let build_dir = fs::read_dir(&toolchain_root)?
                .filter_map(|e| e.ok())
                .find(|e| e.file_type().map(|t| t.is_dir()).unwrap_or(false))
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::NotFound, "Toolchain build directory not found")
                })?
                .path();
            let target_file = build_dir.join(file_name);

            match expected_hash {
                Some("missing") => {
                    // Assert that the file has been successfully deleted/removed.
                    if target_file.exists() {
                        panic!(
                            "Expected toolchain file '{}' to be missing, but it exists",
                            file_name
                        );
                    }
                }
                Some("corrupted") => {
                    // Assert that the file exists and contains the "CORRUPTED
                    // CONTENT" string written by a previous
                    // `corrupt_toolchain_file` action.
                    if !target_file.exists() {
                        panic!(
                            "Expected toolchain file '{}' to exist (corrupted), but it doesn't",
                            file_name
                        );
                    }
                    let content =
                        fs::read_to_string(&target_file).expect("Failed to read toolchain file");
                    if content != "CORRUPTED CONTENT" {
                        panic!(
                            "Expected toolchain file '{}' to be corrupted with 'CORRUPTED CONTENT', but it has different content",
                            file_name
                        );
                    }
                }
                Some(expected_hash) => {
                    // Normal hash verification mode.
                    if !target_file.exists() {
                        panic!("Expected toolchain file '{}' to exist, but it doesn't", file_name);
                    }
                    let mut file = fs::File::open(&target_file)?;
                    let mut hasher = sha2::Sha256::new();
                    std::io::copy(&mut file, &mut hasher)?;
                    let actual_hash = format!("{:x}", hasher.finalize());

                    if actual_hash != expected_hash {
                        panic!(
                            "Hash mismatch for toolchain file '{}'.\nExpected: {}\nActual:   {}",
                            file_name, expected_hash, actual_hash
                        );
                    }
                }
                None => {
                    // If no hash is specified, just assert existence.
                    if !target_file.exists() {
                        panic!("Expected toolchain file '{}' to exist, but it doesn't", file_name);
                    }
                }
            }
            return Ok(());
        } else if action.starts_with("assert_toolchain_file_missing ") {
            let file_name = action.strip_prefix("assert_toolchain_file_missing ").unwrap();
            let toolchain_root = ctx.home_dir.join(".anneal/toolchain");
            if let Ok(entries) = fs::read_dir(&toolchain_root) {
                for entry in entries.filter_map(|e| e.ok()) {
                    if entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
                        let target_file = entry.path().join(file_name);
                        if target_file.exists() {
                            panic!(
                                "Expected toolchain file '{}' to be missing, but it exists",
                                file_name
                            );
                        }
                    }
                }
            }
            return Ok(());
        } else {
            panic!("Unknown action: {}", action);
        }
    }

    let mut config = base_config.clone();
    if let Some(phase) = phase {
        if let Some(args) = &phase.args {
            config.args = Some(args.clone());
        }
        if let Some(status) = &phase.expected_status {
            config.expected_status = status.clone();
        }
        if phase.stderr_file.is_some() {
            config.stderr_file = phase.stderr_file.clone();
        }
        if phase.stdout_file.is_some() {
            config.stdout_file = phase.stdout_file.clone();
        }
    }

    let assert = ctx.run_anneal(&config);

    // Verify Exit Status
    let assert = match config.expected_status {
        ExpectedStatus::Failure => assert.failure(),
        ExpectedStatus::KnownBug => {
            if assert.try_success().is_ok() {
                panic!("Expected a known bug, but it succeeded!");
            }
            // For known_bugs, the toolchain crashed or failed verification.
            // Artifact and stderr emissions are undefined and partially
            // incomplete. We do not validate them.
            return Ok(());
        }
        ExpectedStatus::KnownFlaky => {
            return Ok(());
        }
        ExpectedStatus::Success => assert.success(),
    };

    // Verify the standard error output of the simulated command.
    //
    // We require the expected standard error output to be defined via an
    // explicit `stderr_file` configuration, which specifies an output file
    // relative to the test root. We enforce this strictness to ensure that no
    // legacy fallback configurations or implicit files can accidentally mask
    // the actual stderr output and decouple it from its intended TOML
    // manifest.
    let output = assert.get_output();
    if let Some(stderr_file) = &config.stderr_file {
        assert_output_file(
            &ctx.test_case_root,
            &ctx.sandbox_root,
            &ctx.test_name,
            &ctx.home_dir,
            stderr_file,
            &output.stderr,
            "Stderr",
        );
    }

    if let Some(stdout_file) = &config.stdout_file {
        assert_output_file(
            &ctx.test_case_root,
            &ctx.sandbox_root,
            &ctx.test_name,
            &ctx.home_dir,
            stdout_file,
            &output.stdout,
            "Stdout",
        );
    }

    Ok(())
}

fn assert_output_file(
    test_case_root: &Path,
    sandbox_root: &Path,
    test_name: &str,
    home_dir: &Path,
    expected_file: &str,
    actual_output: &[u8],
    stream_name: &str,
) {
    let expected_path = test_case_root.join(expected_file);
    let bless = std::env::var("BLESS").as_deref() == Ok("1")
        || std::env::var("ANNEAL_BLESS").as_deref() == Ok("1");
    let actual_str = String::from_utf8_lossy(actual_output);
    let actual_stripped = strip_ansi_escapes::strip(&*actual_str);
    let actual_str = String::from_utf8_lossy(&actual_stripped).into_owned().replace("\r", "");
    let replace_path = sandbox_root.to_str().unwrap();

    let target_dir = get_target_dir();
    let toolchain_path = get_toolchain_path();
    let target_path_str = target_dir.to_str().unwrap();
    let toolchain_path_str = toolchain_path.to_str().unwrap();
    let home_path_str = home_dir.to_str().unwrap();
    // Replace volatile environment-specific paths with static placeholders.
    //
    // - `replace_path` corresponds to the sandbox root, which varies per
    //   test run.
    // - `toolchain_path_str` corresponds to the global toolchain.
    // - `target_path_str` corresponds to the cargo target directory or override.
    // - `home_path_str` corresponds to the user's home directory (redirected in
    //   tests).
    let actual_clean = sanitize_output(
        &actual_str
            .replace(replace_path, "[PROJECT_ROOT]")
            .replace(toolchain_path_str, "[CACHE_ROOT]")
            .replace(home_path_str, "[HOME]")
            .replace(target_path_str, "[TARGET_DIR]"),
        test_name == "setup_e2e",
    );

    if bless {
        fs::write(&expected_path, &actual_clean).unwrap();
    } else {
        let expected_txt = fs::read_to_string(&expected_path).unwrap().replace("\r\n", "\n");
        if expected_txt != actual_clean {
            use similar::{ChangeTag, TextDiff};
            let diff = TextDiff::from_lines(&expected_txt, &actual_clean);
            let mut diff_str = String::new();
            for change in diff.iter_all_changes() {
                let sign = match change.tag() {
                    ChangeTag::Delete => "-",
                    ChangeTag::Insert => "+",
                    ChangeTag::Equal => " ",
                };
                diff_str.push_str(&format!("{sign}{change}"));
            }
            panic!(
                "{} mismatch for {}! Run with BLESS=1 to update.\n{}",
                stream_name, test_name, diff_str
            );
        }
    }
}

fn parse_command_log(content: &str) -> Vec<Vec<String>> {
    let mut invocations = Vec::new();
    let mut current_args = Vec::new();

    for line in content.lines() {
        if line == "---END-INVOCATION---" {
            invocations.push(current_args);
            current_args = Vec::new();
        } else if let Some(arg) = line.strip_prefix("CHARON_ARG:") {
            current_args.push(arg.to_string());
        } else if let Some(arg) = line.strip_prefix("ARG:") {
            // Backward compat/fallback
            current_args.push(arg.to_string());
        }
    }
    invocations
}

/// Verifies that the generating `lakefile.lean` and `lean-toolchain` files
/// contain the correct Aeneas commit hash and Lean toolchain version,
/// matching the values specified in `Cargo.toml`.
fn run_toolchain_versioning_test(path: &Path) -> datatest_stable::Result<()> {
    let config = TestConfig {
        args: Some(vec!["verify".into(), "--allow-sorry".into()]),
        ..Default::default()
    };

    // 1. Setup TestContext
    let ctx = TestContext::new(path, &config)?;

    // 3. Run
    let assert = ctx.run_anneal(&config);
    assert.success();

    // 4. Verify generated lakefile.lean and lean-toolchain
    let target_dir = ctx.sandbox_root.join("target");

    // Parse `Cargo.toml` to get the expected values. We expect the tests to be
    // running in the workspace root, so we can find `Cargo.toml` there.
    let cargo_toml_path =
        PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("Cargo.toml");
    let cargo_toml_content = fs::read_to_string(&cargo_toml_path)?;
    let cargo_toml: toml::Value = toml::from_str(&cargo_toml_content)?;
    let metadata = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("build_rs"))
        .expect("Cargo.toml must have [package.metadata.build_rs]");

    let expected_rev = metadata.get("aeneas_rev").and_then(|v| v.as_str()).unwrap();
    let expected_toolchain = metadata.get("lean_toolchain").and_then(|v| v.as_str()).unwrap();

    // Check `lakefile.lean` for the Aeneas revision. Even if using a local
    // Aeneas path (which the test likely is), we expect the revision to be
    // present in a comment.
    let lean_dir = target_dir.join("anneal/anneal_test_target/lean");

    let lakefile_path = lean_dir.join("lakefile.lean");
    let lakefile_content = fs::read_to_string(&lakefile_path)?;

    if !lakefile_content.contains(expected_rev) {
        panic!(
            "lakefile.lean does not contain expected aeneas_rev '{}'. Content:\n{}",
            expected_rev, lakefile_content
        );
    }

    // Check `lean-toolchain` for the correct Lean version.
    let toolchain_path = lean_dir.join("lean-toolchain");
    let toolchain_content = fs::read_to_string(&toolchain_path)?;

    // toolchain content usually has a newline
    if !toolchain_content.trim().contains(expected_toolchain) {
        panic!(
            "lean-toolchain does not contain expected toolchain '{}'. Content:\n{}",
            expected_toolchain, toolchain_content
        );
    }

    Ok(())
}

fn assert_commands_match(invocations: &[Vec<String>], expectations: &[CommandExpectation]) {
    for exp in expectations {
        let found = invocations.iter().any(|cmd| is_subsequence(cmd, &exp.args));

        if !exp.should_not_exist && !found {
            panic!(
                "Expected command invocation with args {:?} was not found.\nCaptured Invocations: {:#?}",
                exp.args, invocations
            );
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

fn to_pascal(s: &str) -> String {
    s.split(['-', '_'])
        .map(|segment| {
            let mut chars = segment.chars();
            match chars.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().collect::<String>() + chars.as_str(),
            }
        })
        .collect::<String>()
}

fn assert_artifacts_match(
    anneal_run_root: &Path,
    test_case_root: &Path,
    expectations: &[ArtifactExpectation],
) -> io::Result<()> {
    let llbc_root = anneal_run_root.join("llbc");
    let lean_root = anneal_run_root.join("lean").join("generated");

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
        // Updated to use PascalCase to match scanner.rs logic
        // let prefix = format!("{}-{}-", exp.package, exp.target);
        let pkg_pascal = to_pascal(&exp.package);
        let target_pascal = to_pascal(&exp.target);
        let prefix = format!("{}{}", pkg_pascal, target_pascal);

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
            // Multiple artifacts may share the same package/target prefix when
            // building a workspace with multiple dependency libraries. We must
            // iterate through all matching artifacts because the hash suffixes
            // are non-deterministic from the perspective of the test harness.
            // If any artifact fully matches the required content strings, the
            // expectation is met.
            let matching_items: Vec<_> =
                found_items.iter().filter(|f| f.starts_with(&prefix)).collect();
            let mut any_matched_all = false;
            let mut collected_errors = String::new();

            for file_name in matching_items {
                let path = scan_dir.join(file_name);

                let content = if path.is_dir() {
                    let mut combined = String::new();
                    for entry in new_sorted_walkdir(&path) {
                        let Ok(entry) = entry else { continue };
                        if entry.file_type().is_file()
                            && let Ok(s) = fs::read_to_string(entry.path())
                        {
                            combined.push_str(&s);
                        }
                    }
                    combined
                } else {
                    fs::read_to_string(&path)?
                };

                let mut matched_all = true;
                for needle in &exp.content_contains {
                    if !content.contains(needle) {
                        matched_all = false;
                        collected_errors.push_str(&format!(
                            "Artifact '{}' missing expected content.\nMissing: '{}'\nPath: {:?}\n\n",
                            file_name, needle, path
                        ));
                        break;
                    }
                }

                if matched_all {
                    for needle in &exp.content_lacks {
                        if content.contains(needle) {
                            matched_all = false;
                            collected_errors.push_str(&format!(
                                "Artifact '{}' contains unexpected content.\nUnexpected: '{}'\nPath: {:?}\n\n",
                                file_name, needle, path
                            ));
                            break;
                        }
                    }
                }

                if matched_all {
                    any_matched_all = true;
                    break;
                }
            }

            if !any_matched_all {
                panic!(
                    "No matching artifact contained the expected content:\n{}",
                    collected_errors
                );
            }
        }
        if found && let Some(expected_dir_name) = &exp.matches_expected_dir {
            let matching_items: Vec<_> =
                found_items.iter().filter(|f| f.starts_with(&prefix)).collect();
            let expected_path = test_case_root.join(expected_dir_name);

            let bless = std::env::var("BLESS").as_deref() == Ok("1")
                || std::env::var("ANNEAL_BLESS").as_deref() == Ok("1");

            if bless {
                // Wipe the existing expected directory before copying over the new
                // payload. This ensures that we do not accidentally retain
                // orphaned files from a previous output if the new toolchain
                // invocation generated fewer files than before.
                let file_name = matching_items.first().unwrap();
                let actual_path = scan_dir.join(file_name);

                if expected_path.exists() {
                    if expected_path.is_dir() {
                        let _ = fs::remove_dir_all(&expected_path);
                    } else {
                        let _ = fs::remove_file(&expected_path);
                    }
                }
                if actual_path.is_dir() {
                    fs::create_dir_all(&expected_path).unwrap();
                    copy_dir_contents(actual_path.as_path(), expected_path.as_path()).unwrap();
                } else {
                    if let Some(parent) = expected_path.parent() {
                        fs::create_dir_all(parent).unwrap();
                    }
                    fs::copy(actual_path.as_path(), expected_path.as_path()).unwrap();
                }
            } else {
                if !expected_path.exists() {
                    panic!(
                        "`matches_expected_dir` was set to '{}', but path does not exist: {:?}\nRun with BLESS=1 to automatically create it.",
                        expected_dir_name, expected_path
                    );
                }

                // Because hash suffixes are opaque to the harness, multiple
                // artifacts might match the package prefix. We use catch_unwind
                // to test each candidate against the expected golden directory. The
                // expectation passes if any one artifact matches.
                // The expectation passes if any one artifact matches.
                let mut any_matched = false;
                let mut collected_errors = String::new();

                for file_name in matching_items {
                    let actual_path = scan_dir.join(file_name);

                    let result = std::panic::catch_unwind(|| {
                        if actual_path.is_dir() != expected_path.is_dir() {
                            panic!(
                                "Type mismatch: expected {:?} (is_dir: {}), actual {:?} (is_dir: {})",
                                expected_path,
                                expected_path.is_dir(),
                                actual_path,
                                actual_path.is_dir()
                            );
                        }

                        if actual_path.is_dir() {
                            assert_directories_match(&expected_path, &actual_path).unwrap();
                        } else {
                            let e_txt =
                                fs::read_to_string(&expected_path).unwrap().replace("\r\n", "\n");
                            let a_txt =
                                fs::read_to_string(&actual_path).unwrap().replace("\r\n", "\n");
                            if e_txt != a_txt {
                                use similar::{ChangeTag, TextDiff};
                                let diff = TextDiff::from_lines(&e_txt, &a_txt);
                                let mut diff_str = String::new();
                                for change in diff.iter_all_changes() {
                                    let sign = match change.tag() {
                                        ChangeTag::Delete => "-",
                                        ChangeTag::Insert => "+",
                                        ChangeTag::Equal => " ",
                                    };
                                    diff_str.push_str(&format!("{sign}{change}"));
                                }
                                panic!("Mismatch in {:?}:\n{}", expected_path, diff_str);
                            }
                        }
                    });

                    match result {
                        Ok(_) => {
                            any_matched = true;
                            break;
                        }
                        Err(e) => {
                            let err_msg = if let Some(s) = e.downcast_ref::<&str>() {
                                s.to_string()
                            } else {
                                "Unknown panic during assertion".to_string()
                            };
                            collected_errors.push_str(&format!(
                                "Artifact '{}' mismatch:\n{}\n",
                                file_name, err_msg
                            ));
                        }
                    }
                }

                if !any_matched {
                    panic!(
                        "No matching artifact matched the expected directory:\n{}",
                        collected_errors
                    );
                }
            }
        }
    }

    Ok(())
}

fn assert_directories_match(expected: &Path, actual: &Path) -> io::Result<()> {
    for entry in new_sorted_walkdir(expected) {
        let entry = entry.map_err(io::Error::other)?;
        if !entry.file_type().is_file() {
            continue;
        }
        let rel = entry.path().strip_prefix(expected).unwrap();
        let act = actual.join(rel);
        if !act.exists() {
            panic!(
                "Missing file in actual artifact:\nExpected: {:?}\nActual is missing: {:?}",
                entry.path(),
                act
            );
        }
        let e_txt = fs::read_to_string(entry.path())?.replace("\r\n", "\n");
        let a_txt = fs::read_to_string(&act)?.replace("\r\n", "\n");
        if e_txt != a_txt {
            use similar::{ChangeTag, TextDiff};
            let diff = TextDiff::from_lines(&e_txt, &a_txt);
            let mut diff_str = String::new();
            for change in diff.iter_all_changes() {
                let sign = match change.tag() {
                    ChangeTag::Delete => "-",
                    ChangeTag::Insert => "+",
                    ChangeTag::Equal => " ",
                };
                diff_str.push_str(&format!("{sign}{change}"));
            }
            panic!("Mismatch in {:?}:\n{}", rel, diff_str);
        }
    }
    // Check for extra files in actual
    for entry in new_sorted_walkdir(actual) {
        let entry = entry.map_err(io::Error::other)?;
        if !entry.file_type().is_file() {
            continue;
        }
        let rel = entry.path().strip_prefix(actual).unwrap();
        let exp = expected.join(rel);
        if !exp.exists() {
            panic!("Extra file found in actual artifact that is not in expected:\n{:?}", rel);
        }
    }
    Ok(())
}

fn copy_dir_contents(src: &Path, dst: &Path) -> io::Result<()> {
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

// Sanitizes non-deterministic log output generated by external tools.
//
// Tools like Cargo, Aeneas, and the Rust standard library panic handler inject
// highly dynamic strings into `stderr` (e.g., execution timings, randomized
// thread IDs, varying length hexadecimal hashes). We scrub these dynamically
// generated values and replace them with static `<PLACERHOLDER>` tokens so
// that we can deterministically compare the output across different host
// machines and executions.
//
// Specifically, we handle:
// - RFC 3339 timestamps (replaced with `[YYYY-MM-DDTHH:MM:SSZ `)
// - Thread IDs in panic messages (replaced with `<ID>`)
// - Lock-waiting messages from Cargo or other tools (removed)
// - Hexadecimal hashes in file paths or versions (replaced with `<HASH>`)
// - Execution timings (replaced with `<TIME>`)
// - Randomized worker directory IDs (replaced with `<ID>`)
// - Local IP/port combinations used in mock servers (replaced with
//   `127.0.0.1:<PORT>`)
// - Rustup toolchain paths (replaced with `[RUSTUP_TOOLCHAIN]`)
fn sanitize_output(output: &str, sanitize_sorry: bool) -> String {
    let re_thread_id = regex::Regex::new(r"thread '([^']+)' \(\d+\) panicked").unwrap();
    let re_file_lock =
        regex::Regex::new(r"(?m)^.*Blocking waiting for file lock on.*$\n?").unwrap();
    let re_cargo_hash = regex::Regex::new(r"([-=_])([a-f0-9]{5,16})\b").unwrap();

    let re_timing = regex::Regex::new(r"took \d+(\.\d*)?(m?s)").unwrap();
    let re_lake_timing = regex::Regex::new(r"\(\d+(\.\d*)?m?s\)").unwrap();
    let re_aeneas_time = regex::Regex::new(r"Total execution time: \d+\.\d+ seconds").unwrap();
    let re_unpacked_time = regex::Regex::new(r"Unpacked in \d+ ms").unwrap();
    let re_lean_full_install = regex::Regex::new(
        r"(?m)^leanprover/lean4:[^\n]*\n\nLean toolchain [^\n]* installed successfully\.\n",
    )
    .unwrap();
    let re_ip_port = regex::Regex::new(r"127\.0\.0\.1:\d+").unwrap();
    let re_rustup =
        regex::Regex::new(r"[^\s]*/(?:\.rustup|opt/rustup)/toolchains/[^/\s]+").unwrap();
    let re_elan = regex::Regex::new(r"[^\s]*/(?:\.elan|opt/elan)/toolchains/[^/\s]+").unwrap();
    // Lake's build progress indicators are volatile because they depend on
    // artifact-cache hit/miss state. We strip the entire line.
    let re_lake_progress = regex::Regex::new(r"(?m)^.*\[\d+/\d+\].*$\n?").unwrap();
    // Aeneas pre-built library might produce warnings about `sorry` usage.
    // We strip them to make test output deterministic.
    let re_sorry_warning = regex::Regex::new(r"(?m)^.*declaration uses `sorry`.*$\n?").unwrap();
    // Aeneas progress bars contain volatile spinner characters. We strip them.
    let re_applied_prepasses = regex::Regex::new(r"(?m)^.*Applied prepasses:.*$\n?").unwrap();
    // Pre-building Aeneas Lean library produces volatile output depending on cache state.
    let re_prebuild_output = regex::Regex::new(r"(?m)^(Pre-building Aeneas Lean library|Fetching Mathlib cache|installing leantar|Fetching ProofWidgets|Current branch:|Using cache|Attempting to download|Decompressing|Unpacked in|Completed successfully!|Building Aeneas Lean library|Build completed successfully|Successfully pre-built).*$\n?").unwrap();
    // Strip ANSI escape codes.
    let re_ansi_escape = regex::Regex::new(r"\x1B\[[0-9;]*[a-zA-Z]").unwrap();

    let mut clean = output.to_string();

    clean = re_thread_id.replace_all(&clean, "thread '$1' (<ID>) panicked").into_owned();
    clean = re_file_lock.replace_all(&clean, "").into_owned();
    clean = re_cargo_hash.replace_all(&clean, "${1}<HASH>").into_owned();

    clean = re_timing.replace_all(&clean, "took <TIME>").into_owned();
    clean = re_lake_timing.replace_all(&clean, "(<TIME>)").into_owned();
    clean = re_aeneas_time.replace_all(&clean, "Total execution time: <TIME> seconds").into_owned();
    clean = re_unpacked_time.replace_all(&clean, "Unpacked in <TIME> ms").into_owned();
    clean = re_lean_full_install
        .replace_all(&clean, "Lean toolchain leanprover/lean4:v4.28.0-rc1 is already installed.\n")
        .into_owned();
    clean = re_ip_port.replace_all(&clean, "127.0.0.1:<PORT>").into_owned();
    clean = re_rustup.replace_all(&clean, "[RUSTUP_TOOLCHAIN]").into_owned();
    clean = re_elan.replace_all(&clean, "[ELAN_TOOLCHAIN]").into_owned();
    clean = re_lake_progress.replace_all(&clean, "").into_owned();
    clean = re_applied_prepasses.replace_all(&clean, "").into_owned();
    clean = re_prebuild_output.replace_all(&clean, "").into_owned();
    clean = re_ansi_escape.replace_all(&clean, "").into_owned();
    if sanitize_sorry {
        clean = re_sorry_warning.replace_all(&clean, "").into_owned();
    }

    clean
}

fn find_generated_root(target_dir: &Path) -> datatest_stable::Result<PathBuf> {
    // Verify that the Anneal output directory structure exists.
    // Expected path: target/anneal
    let anneal_dir = target_dir.join("anneal");
    if !anneal_dir.exists() {
        return Err(format!("Anneal output directory not found at {}", anneal_dir.display()).into());
    }

    for entry in fs::read_dir(anneal_dir)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            let generated = entry.path().join("lean/generated");
            if generated.exists() {
                return Ok(generated);
            }
        }
    }
    Err("Could not find generated directory".into())
}

fn run_dirty_sandbox_test(path: &Path) -> datatest_stable::Result<()> {
    // Tests that Anneal correctly detects and fails when the source directory
    // contains stale artifacts or blacklisted files (e.g., target/, .lake/).

    // 1. Attempt to create TestContext (should fail immediately)
    let config = TestConfig::default();
    let result = TestContext::new(path, &config);

    // 2. Verify failure
    match result {
        Ok(_) => panic!("TestContext should have failed due to dirty source!"),
        Err(e) => {
            let error_msg = e.to_string();
            if !error_msg.contains("Stale build artifact directory found in fixture source")
                && !error_msg.contains("Found blacklisted file in source")
            {
                panic!("Unexpected error message: {}", error_msg);
            }
        }
    }

    Ok(())
}
