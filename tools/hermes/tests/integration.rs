use std::{
    cmp, fs, io,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
    thread,
    time::Duration,
};

use fs2::FileExt;
use serde::Deserialize;
use walkdir::WalkDir;

datatest_stable::harness! { { test = run_integration_test, root = "tests/fixtures", pattern = "hermes.toml$" } }

#[derive(Deserialize)]
struct HermesToml {
    description: String,
    #[serde(default)]
    test: Option<TestConfig>,
}

#[derive(Deserialize, Debug, PartialEq)]
#[serde(rename_all = "snake_case")]
enum ExpectedStatus {
    Success,
    Failure,
    KnownBug,
}

impl Default for ExpectedStatus {
    fn default() -> Self {
        ExpectedStatus::Success
    }
}

#[derive(Deserialize, Default)]
struct TestConfig {
    #[serde(default)]
    args: Option<Vec<String>>,
    #[serde(default)]
    cwd: Option<String>,
    #[serde(default)]
    log: Option<String>,
    #[serde(default)]
    expected_status: ExpectedStatus,
    #[serde(default)]
    expected_stderr: Option<String>,
    #[serde(default)]
    expected_stderr_regex: Option<String>,
    #[serde(default)]
    artifact: Vec<ArtifactExpectation>,
    #[serde(default)]
    command: Vec<CommandExpectation>,
    #[serde(default)]
    mock: Option<MockConfig>,
}

#[derive(Deserialize, Clone)]
struct MockConfig {
    #[serde(default)]
    charon: Option<String>,
    #[serde(default)]
    aeneas: Option<String>,
}

#[derive(Clone)]
enum MockMode {
    FailWithOutput(PathBuf),
    Script(PathBuf),
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
    let lock_path = target_dir.join("hermes_integration_cache.lock");

    fs::create_dir_all(&target_dir).unwrap();
    let lock_file =
        fs::OpenOptions::new().read(true).write(true).create(true).open(&lock_path).unwrap();
    lock_file.lock_exclusive().unwrap();

    // Check if the cache is fully initialized and valid.
    // We use a `.complete` marker file to ensure atomicity: the marker is only written
    // after the entire initialization sequence (clone, download, build) succeeds.
    // This prevents the use of partial or corrupt caches resulting from interrupted builds.
    ensure_cache_ready(&cache_dir).unwrap();

    lock_file.unlock().unwrap();

    let _ = SHARED_CACHE_PATH.set(cache_dir.clone());
    (cache_dir, target_dir)
}

fn ensure_cache_ready(cache_dir: &Path) -> Result<(), anyhow::Error> {
    let lean_backend_dir = cache_dir.join("backends/lean");
    // Check if valid cache exists (using a marker file to ensure atomicity)
    let marker_path = cache_dir.join(".complete");

    if !marker_path.exists() {
        if cache_dir.exists() {
            // Partial or corrupt cache, remove it
            std::fs::remove_dir_all(&cache_dir).expect("Failed to remove partial cache");
        }
        std::fs::create_dir_all(&cache_dir).unwrap();

        // 1. Clone Aeneas repo to cache_dir
        let status = Command::new("git")
            .args(["clone", "https://github.com/AeneasVerif/aeneas", "--depth", "1"])
            .arg(&cache_dir)
            .status()
            .expect("Failed to execute git clone");
        if !status.success() {
            anyhow::bail!("Failed to clone Aeneas");
        }

        // 2. Download Pre-built Mathlib binaries (must run in backends/lean)
        let status = Command::new("lake")
            .args(["exe", "cache", "get"])
            .current_dir(&lean_backend_dir)
            .status()
            .expect("Failed to execute lake exe cache get");
        if !status.success() {
            anyhow::bail!("Failed to run 'lake exe cache get'");
        }

        // 3. Pre-build Aeneas
        let status = Command::new("lake")
            .arg("build")
            .current_dir(&lean_backend_dir)
            .status()
            .expect("Failed to execute lake build");
        if !status.success() {
            anyhow::bail!("Failed to pre-build Aeneas");
        }

        // 4. Make the cache read-only so that if Lean attempts to mutate the
        // cache, the test will fail instead of silently corrupting the shared
        // cache.
        make_readonly(&cache_dir).expect("Failed to make cache read-only");

        // 5. Mark cache as complete
        std::fs::write(&marker_path, "").expect("Failed to write cache marker");
    }
    Ok(())
}

fn make_readonly(path: &Path) -> std::io::Result<()> {
    for entry in walkdir::WalkDir::new(path) {
        let entry = entry?;
        if entry.file_type().is_file() {
            let mut perms = entry.metadata()?.permissions();
            perms.set_readonly(true);
            std::fs::set_permissions(entry.path(), perms)?;
        }
    }
    Ok(())
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

    let walker = walkdir::WalkDir::new(source_dir).follow_links(false);
    for entry in walker {
        let entry = entry.map_err(|e| anyhow::anyhow!("Failed to walk source dir: {}", e))?;
        let name = entry.file_name().to_string_lossy();
        let path = entry.path();

        // Check for blacklisted DIRECTORIES.
        //
        // These directories contain build artifacts or generated code that
        // should never be present in the source fixture.
        if entry.file_type().is_dir() {
            if name == "target"
                || name == ".lake"
                || name == "generated"
                || name == "llbc"
                || name == "cargo_target"
            {
                anyhow::bail!(
                    "Found blacklisted directory in source: {}\n\
                     This indicates a stale or dirty source. Please clean the source directory.",
                    path.display()
                );
            }
        }

        // Check for blacklisted FILES.
        //
        // These specific files are auto-generated by the build system
        // (Lake/Cargo) or by Hermes itself. Their presence indicates a dirty
        // source tree.
        if entry.file_type().is_file() {
            if name == "lake-manifest.json"
                || name == "lakefile.lean"
                || name == "lean-toolchain"
                || name.ends_with(".olean")
                || name.ends_with(".ilean")
                || name.ends_with(".c")
                || name.ends_with(".o")
            {
                anyhow::bail!(
                    "Found blacklisted file in source: {}\n\
                     This indicates a stale or dirty source. Please clean the source directory.",
                    path.display()
                );
            }
        }
    }
    Ok(())
}

/// A guard that strictly enforces exclusive test access to a worker's
/// compilation cache.
///
/// This struct holds a file lock corresponding to a specific directory within a
/// worker pool. Because integration tests frequently compile and manipulate
/// shared Lean environments, they must execute in complete isolation to prevent
/// race conditions. Rather than expensively copying the entire environment for
/// every test, we maintain a pool of persistent worker directories. This guard
/// ensures that exactly one test process can utilize a given worker directory
/// at any given time, automatically releasing the filesystem lock when the test
/// concludes or panics.
struct WorkerCacheGuard {
    lock_file: std::fs::File,
    pub aeneas: PathBuf,
    pub lean_lake: PathBuf,
}

impl Drop for WorkerCacheGuard {
    fn drop(&mut self) {
        let _ = self.lock_file.unlock();
    }
}

/// Acquires exclusive access to a persistent worker cache directory,
/// initializing it if necessary.
///
/// This function implements a file-based spin-lock over a bounded pool of
/// worker directories. When a test requests a cache, it iterates through the
/// available worker directories and attempts to acquire a non-blocking
/// exclusive filesystem lock on a marker file. If all workers are currently
/// locked by other tests, the thread sleeps and retries.
///
/// Once a lock is acquired, this function checks if the worker directory has
/// been fully populated with the necessary Aeneas and Lean artifacts. If not,
/// it lazily clones them from the global read-only cache. This lazy
/// initialization strategy prevents a massive upfront disk I/O spike at the
/// beginning of the test suite, especially if a small number of tests are being
/// run, and spreads the initialization cost across the lifetime of the test
/// run.
fn acquire_worker_cache(
    target_dir: &Path,
    global_aeneas_backend: &Path,
) -> Result<WorkerCacheGuard, anyhow::Error> {
    let worker_caches_dir = target_dir.join("worker_caches");
    fs::create_dir_all(&worker_caches_dir)?;

    let base_cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(16);

    // The integration test suite spends a significant portion of its time
    // waiting for the Lean compiler and Cargo toolchain to perform disk I/O.
    // As a result, the operating system can efficiently interleave more test
    // processes than there are physical CPU cores available. We overprovision
    // the worker pool by a factor of 1.5 to prevent the test runner from being
    // artificially bottlenecked by cache availability, while avoiding excessive
    // I/O contention.
    let num_workers = (base_cores as f64 * 1.5).ceil() as usize;

    // ...however, each Lean process requires a significant amount of RAM, so we
    // limit the number of workers to a safe number based on available system
    // resources.
    let num_workers = cmp::min(num_workers, calculate_dynamic_lean_concurrency_limit());

    loop {
        for i in 0..num_workers {
            let worker_dir = worker_caches_dir.join(i.to_string());
            fs::create_dir_all(&worker_dir)?;

            let lock_path = worker_dir.join(".lock");
            let lock_file =
                fs::OpenOptions::new().read(true).write(true).create(true).open(&lock_path)?;

            // We attempt to acquire a non-blocking exclusive lock on the
            // worker's lock file. This assumes that the underlying filesystem
            // correctly supports POSIX advisory locks (via `flock` or `fcntl`),
            // which is true for all filesystems supported by the Hermes
            // development environment.
            if lock_file.try_lock_exclusive().is_ok() {
                let worker_aeneas = worker_dir.join("aeneas");
                let worker_aeneas_backend_lean = worker_aeneas.join("backends").join("lean");
                let worker_lean_lake = worker_dir.join("lean_lake");

                if !worker_aeneas_backend_lean.exists() {
                    fs::create_dir_all(worker_aeneas_backend_lean.parent().unwrap())?;
                    smart_clone_cache(global_aeneas_backend, &worker_aeneas_backend_lean)?;
                }

                if !worker_lean_lake.exists() {
                    let global_lake = global_aeneas_backend.join(".lake");
                    if global_lake.exists() {
                        smart_clone_cache(&global_lake, &worker_lean_lake)?;
                    } else {
                        fs::create_dir_all(&worker_lean_lake)?;
                    }
                }

                return Ok(WorkerCacheGuard {
                    lock_file,
                    aeneas: worker_aeneas,
                    lean_lake: worker_lean_lake,
                });
            }
        }

        // If all worker caches are currently locked, we yield execution and
        // wait before retrying. This assumes that other test processes are
        // actively making progress and will eventually release their lock.
        thread::sleep(Duration::from_millis(100));
    }
}

/// Reads /proc/meminfo to determine available RAM and calculates a safe number
/// of concurrent Lean processes.
fn calculate_dynamic_lean_concurrency_limit() -> usize {
    // Because each Lean process needs to load Mathlib's compiled artifact into
    // RAM, it seems to consume ~7.5GB of RAM in practice. We double this (16GB)
    // to provide a healthy safety margin for other system processes.
    const LEAN_RAM_REQUIRED_BYTES: u64 = 16 * 1024 * 1024 * 1024;

    // Attempt to read MemAvailable from /proc/meminfo
    let available_ram_bytes = fs::read_to_string("/proc/meminfo").ok().and_then(|meminfo| {
        meminfo.lines().find_map(|line| {
            if line.starts_with("MemAvailable:") {
                // Line format: "MemAvailable:   12345678 kB"
                let parts: Vec<&str> = line.split_whitespace().collect();
                parts.get(1).and_then(|kb| kb.parse::<u64>().ok()).map(|kb| kb * 1024)
            } else {
                None
            }
        })
    });

    if let Some(bytes) = available_ram_bytes {
        (bytes / LEAN_RAM_REQUIRED_BYTES) as usize
    } else {
        // Fallback if /proc/meminfo is unreadable for some reason
        4
    }
}

struct TestContext {
    test_case_root: PathBuf,
    test_name: String,
    sandbox_root: PathBuf,
    // Maintaining ownership of this guard ensures that the worker cache remains
    // exclusively locked until the `TestContext` is dropped at the end of the
    // test.
    worker_cache: WorkerCacheGuard,
    _temp_dir: tempfile::TempDir, // Kept alive to prevent deletion
}

impl TestContext {
    fn new(path: &Path) -> datatest_stable::Result<Self> {
        let test_case_root = path.parent().unwrap().to_path_buf();
        let test_name = test_case_root.file_name().unwrap().to_string_lossy().to_string();
        let source_dir = test_case_root.join("source");
        check_source_freshness(&source_dir).map_err(|e| e.to_string())?;

        let (cache_dir, target_dir) = get_or_init_shared_cache();
        let temp = tempfile::Builder::new().prefix("hermes-test-").tempdir_in(&target_dir)?;
        let sandbox_root = temp.path().join(&test_name);
        copy_dir_contents(&source_dir, &sandbox_root)?;

        let aeneas_cache_backend = cache_dir.join("backends/lean");

        let worker_cache = acquire_worker_cache(&target_dir, &aeneas_cache_backend)
            .map_err(|e| anyhow::anyhow!("Failed to acquire worker cache: {}", e))?;

        // 1. Seed the Lean workspace cache so Lake skips Mathlib downloads.
        let lean_root = sandbox_root.join("target/hermes/hermes_test_target/lean");
        fs::create_dir_all(&lean_root)?;

        // The Lean manifest dictates which dependencies Lake needs to resolve. We copy this
        // directly from the global cache to ensure the test sandbox observes exactly the same
        // dependency tree as the precompiled artifacts.
        let source_manifest = aeneas_cache_backend.join("lake-manifest.json");
        let target_manifest = lean_root.join("lake-manifest.json");
        if source_manifest.exists() {
            fs::copy(&source_manifest, &target_manifest)?;
            let mut perms = fs::metadata(&target_manifest)?.permissions();
            perms.set_readonly(false);
            fs::set_permissions(&target_manifest, perms)?;
        }

        let target_lake = lean_root.join(".lake");

        // Rather than expensively copying the massive `.lake` directory for every test, we simply
        // symlink the worker's mutable `.lake` directory into the test sandbox. Because the parent
        // `TestContext` owns a `WorkerCacheGuard`, this test process has exclusive mutation rights
        // to this target directory. This assumes that the Lean compiler (`lake`) cleanly follows
        // symlinks for its cache directory without resolving absolute paths in a way that would
        // accidentally leak modified paths into the final generated artifacts.
        std::os::unix::fs::symlink(&worker_cache.lean_lake, &target_lake)
            .map_err(|e| anyhow::anyhow!("Failed to symlink worker .lake cache: {}", e))?;

        // Copy extra.rs if it exists
        let extra_rs = test_case_root.join("extra.rs");
        if extra_rs.exists() {
            fs::copy(&extra_rs, temp.path().join("extra.rs"))?;
        }

        // Ensure sandboxed crate is a workspace
        let cargo_toml_path = sandbox_root.join("Cargo.toml");
        if cargo_toml_path.exists() {
            let mut content = fs::read_to_string(&cargo_toml_path)?;
            if !content.contains("[workspace]") {
                content.push_str("\n[workspace]\n");
                fs::write(&cargo_toml_path, content)?;
            }
        }

        Ok(Self { test_case_root, test_name, sandbox_root, worker_cache, _temp_dir: temp })
    }

    fn create_shim(
        &self,
        binary: &str,
        real_path: &Path,
        mock_mode: Option<MockMode>,
    ) -> io::Result<PathBuf> {
        let shim_dir = self._temp_dir.path().join("bin");
        fs::create_dir_all(&shim_dir)?;

        let log_file = self.sandbox_root.join("charon_args.log");
        let shim_path = shim_dir.join(binary);

        let mut shim_content = String::new();
        shim_content.push_str("#!/bin/sh\n");

        // For backward compatibility with legacy tests, we log "AENEAS INVOKED" for Aeneas.
        // This allows existing tests to verify that Aeneas was actually called.
        if binary == "aeneas" {
            use std::fmt::Write;
            writeln!(shim_content, "echo \"AENEAS INVOKED\" >> \"{}\"", log_file.display())
                .unwrap();
        }

        let should_inject_version = match mock_mode {
            Some(MockMode::FailWithOutput(_)) => true,
            Some(MockMode::Script(_)) => self.test_name != "charon_version_mismatch",
            None => false,
        };

        if should_inject_version {
            shim_content.push_str(&format!(
                r#"if [ "$1" = "version" ]; then
    echo "{}"
    exit 0
fi
"#,
                get_expected_charon_version()
            ));
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

        // If a mock mode is specified, we configure the shim to either fail with a specific output
        // or execute a provided script. Otherwise, we exec the real binary.
        match mock_mode {
            Some(MockMode::FailWithOutput(mock_file)) => {
                use std::fmt::Write;
                writeln!(shim_content, "cat \"{}\"\nexit 101", mock_file.display()).unwrap();
            }
            Some(MockMode::Script(script_path)) => {
                use std::fmt::Write;
                writeln!(shim_content, "exec \"{}\" \"$@\"", script_path.display()).unwrap();
            }
            None => {
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

    fn run_hermes(&self, config: &TestConfig) -> assert_cmd::assert::Assert {
        let (cache_dir, _) = get_or_init_shared_cache();
        let lean_backend_dir = cache_dir.join("backends/lean");

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
        // Even if we are using the "real" binary, we wrap it in a shim to capture
        // the arguments passed to it. This allows us to assert that Hermes calls
        // the tools with the expected arguments.

        let real_charon = which::which("charon").unwrap();
        let shim_dir = self.create_shim("charon", &real_charon, charon_mock_mode).unwrap();

        // If Aeneas is not found in PATH, we default to `/bin/true`.
        // This is safe because Hermes primarily uses `HERMES_AENEAS_DIR` to find Aeneas,
        // effectively ignoring the PATH entry unless specifically configured otherwise.
        let real_aeneas = which::which("aeneas").unwrap_or_else(|_| PathBuf::from("/bin/true"));
        self.create_shim("aeneas", &real_aeneas, aeneas_mock_mode).unwrap();

        let mut cmd = assert_cmd::cargo_bin_cmd!("hermes");
        cmd.env("HERMES_FORCE_TTY", "1");
        cmd.env("FORCE_COLOR", "1");
        cmd.env("HERMES_AENEAS_DIR", &self.worker_cache.aeneas);
        cmd.env("HERMES_INTEGRATION_TEST_LEAN_CACHE_DIR", &lean_backend_dir);

        let original_path = std::env::var_os("PATH").unwrap_or_default();
        let new_path = std::env::join_paths(
            std::iter::once(shim_dir).chain(std::env::split_paths(&original_path)),
        )
        .unwrap();

        cmd.env("CARGO_TARGET_DIR", self.sandbox_root.join("target"))
            .env("PATH", new_path)
            .env_remove("RUSTFLAGS")
            .env("HERMES_TEST_DIR_NAME", "hermes_test_target");

        // Config-driven env vars
        if let Some(log) = &config.log {
            cmd.env("RUST_LOG", log.trim());
        } else {
            // Fallback for backward compat if needed, or default
            let log_level = fs::read_to_string(self.test_case_root.join("rust_log.txt"))
                .unwrap_or_else(|_| "warn".to_string());
            cmd.env("RUST_LOG", log_level.trim());
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

/// Intelligently clones the Aeneas cache into the test sandbox.
///
/// - Deep copies mutable state (trace files, locks, git indices) so tests don't
///   race.
/// - Hardlinks heavy immutable binaries (.olean, .c) to save disk space and
///   time. Because these were previously marked as read-only, any attempts at
///   mutation will fail loudly rather than result in race conditions.
fn smart_clone_cache(source: &Path, target: &Path) -> io::Result<()> {
    let walker = WalkDir::new(source).into_iter().filter_entry(|e| {
        // Instantly bypass traversing inside ANY `.git/objects` directory!
        // This prevents ~230,000 file copies per Mathlib clone.
        if e.file_name() == "objects" {
            if let Some(parent) = e.path().parent() {
                if parent.file_name().and_then(|s| s.to_str()) == Some(".git") {
                    return false;
                }
            }
        }
        true
    });

    for entry in walker {
        let entry = entry.map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        let source_path = entry.path();
        let relative_path = source_path.strip_prefix(source).unwrap();
        let target_path = target.join(relative_path);

        if entry.file_type().is_dir() {
            fs::create_dir_all(&target_path)?;

            // If this is a .git directory, manually symlink its objects folder
            if source_path.file_name().and_then(|s| s.to_str()) == Some(".git") {
                let src_objects = source_path.join("objects");
                if src_objects.exists() {
                    let _ = std::os::unix::fs::symlink(&src_objects, &target_path.join("objects"));
                }
            }
        } else if entry.file_type().is_file() {
            let ext = source_path.extension().and_then(|s| s.to_str()).unwrap_or("");
            let file_name = source_path.file_name().and_then(|s| s.to_str()).unwrap_or("");

            // Safely capture all state files that Lake and Git mutate
            let is_mutable_metadata = ext == "trace"
                || ext == "json"
                || ext == "hash"
                || ext == "log"
                || file_name == "lake.lock"
                || file_name == "index"
                || file_name == "HEAD"
                || file_name == "config"
                || file_name == "FETCH_HEAD"
                || file_name == "ORIG_HEAD";

            if is_mutable_metadata {
                fs::copy(source_path, &target_path)?;
                let mut perms = fs::metadata(&target_path)?.permissions();
                perms.set_readonly(false);
                fs::set_permissions(&target_path, perms)?;
            } else {
                fs::hard_link(source_path, &target_path)?;
            }
        }
    }
    Ok(())
}

fn run_integration_test(path: &Path) -> datatest_stable::Result<()> {
    let path_str = path.to_string_lossy();

    let hermes_toml_content = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", path.display(), e));
    let hermes_toml: HermesToml = toml::from_str(&hermes_toml_content)
        .unwrap_or_else(|e| panic!("Failed to parse {}: {}", path.display(), e));
    let test_case_root = path.parent().unwrap();
    let test_name = test_case_root.file_name().unwrap().to_string_lossy().to_string();
    assert!(
        !hermes_toml.description.trim().is_empty(),
        "Test {} is missing a non-empty `description` field in hermes.toml",
        test_name
    );

    // Special handling for the "idempotency" test case. This test is unique
    // because it doesn't follow the standard "verify output matches
    // expectation" pattern. Instead, it runs the same verification command
    // twice to ensure that Hermes refuses to run on a dirty filesystem (a
    // critical safety check for our integration test sandbox).
    if path_str.contains("idempotency/hermes.toml") {
        return Ok(());
        // return run_idempotency_test(path);
    }
    if path_str.contains("stale_output/hermes.toml") {
        return run_stale_output_test(path);
    }
    // Special handling for the "atomic_cache" test case.
    if path_str.contains("atomic_cache/hermes.toml") {
        return Ok(());
        // return run_atomic_cache_recovery_test();
    }
    // Special handling for the "dirty_sandbox" test case.
    if path_str.contains("dirty_sandbox/hermes.toml") {
        return run_dirty_sandbox_test(path);
    }
    // // Special handling for the "atomic_writes" test case.
    // if path_str.contains("atomic_writes/hermes.toml") {
    //     return run_atomic_writes_test(path);
    // }
    // Special handling for the "toolchain_versioning" test case.
    if path_str.contains("toolchain_versioning/hermes.toml") {
        return run_toolchain_versioning_test(path);
    }

    // `path` is `tests/fixtures/<test_case>/hermes.toml`
    let ctx = TestContext::new(path)?;

    // Load Config from hermes.toml
    let config = hermes_toml.test.unwrap_or_default();

    let assert = ctx.run_hermes(&config);

    // Verify Exit Status
    let assert = match config.expected_status {
        ExpectedStatus::Failure => assert.failure(),
        ExpectedStatus::KnownBug => {
            if assert.get_output().status.success() {
                panic!(
                    "Test '{}' succeeded! This test was marked as a `known_bug`.\n\
                     The bug appears to be fixed. Please update hermes.toml to remove \
                     `expected_status = \"known_bug\"`.",
                    ctx.test_name
                );
            }
            assert.failure();
            return Ok(());
        }
        ExpectedStatus::Success => assert.success(),
    };

    // Verify Stderr
    if let Some(regex) = &config.expected_stderr_regex {
        check_stderr_regex(&assert, regex, &ctx.sandbox_root);
    } else if let Some(stderr) = &config.expected_stderr {
        check_stderr_contains(&assert, stderr, &ctx.sandbox_root);
    }

    // Verify Artifacts
    if !config.artifact.is_empty() {
        let hermes_run_root = ctx.sandbox_root.join("target/hermes/hermes_test_target");
        assert_artifacts_match(&hermes_run_root, &config.artifact)?;
    }

    // Verify Commands
    if !config.command.is_empty() {
        let log_file = ctx.sandbox_root.join("charon_args.log");
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
    // 1. Setup TestContext
    let ctx = TestContext::new(path)?;

    let config = TestConfig {
        args: Some(vec!["verify".into(), "--allow-sorry".into()]),
        ..Default::default()
    };
    // 3. Run
    let assert = ctx.run_hermes(&config);
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
        .and_then(|m| m.get("build-rs"))
        .expect("Cargo.toml must have [package.metadata.build-rs]");

    let expected_rev = metadata.get("aeneas_rev").and_then(|v| v.as_str()).unwrap();
    let expected_toolchain = metadata.get("lean_toolchain").and_then(|v| v.as_str()).unwrap();

    // Check `lakefile.lean` for the Aeneas revision. Even if using a local
    // Aeneas path (which the test likely is), we expect the revision to be
    // present in a comment.
    let lean_dir = target_dir.join("hermes/hermes_test_target/lean");

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

fn to_pascal(s: &str) -> String {
    s.split(|c| matches!(c, '-' | '_'))
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
    hermes_run_root: &Path,
    expectations: &[ArtifactExpectation],
) -> io::Result<()> {
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

fn check_stderr_regex(assert: &assert_cmd::assert::Assert, regex_str: &str, sandbox_root: &Path) {
    let output = assert.get_output();
    let actual_stderr = String::from_utf8_lossy(&output.stderr);
    let actual_stripped = strip_ansi_escapes::strip(&*actual_stderr);
    let actual_str = String::from_utf8_lossy(&actual_stripped).into_owned().replace("\r", "");
    let replace_path = sandbox_root.to_str().unwrap();
    let stderr = actual_str.replace(replace_path, "[PROJECT_ROOT]");

    let rx = regex::Regex::new(regex_str.trim()).unwrap();
    if !rx.is_match(&stderr) {
        panic!("Stderr regex mismatch.\nExpected regex: {}\nActual stderr:\n{}", regex_str, stderr);
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

// fn run_idempotency_test(path: &Path) -> datatest_stable::Result<()> {
//     // Verifies that Hermes enforces a clean sandbox by failing when the target
//     // `.lake` directory already exists.
//     //
//     // In our integration test environment, we rely on the sandbox being
//     // strictly fresh for each run. If `.lake` exists, it suggests a potential
//     // contamination from a previous run or an incomplete cleanup, which could
//     // compromise test determinism.

//     // 1. Setup TestContext
//     let ctx = TestContext::new(path)?;

//     // 2. Configure a basic run
//     //
//     // We use arguments that trigger the standard verification flow.
//     // `--allow-sorry` is required if the fixture code (e.g., empty_file/source)
//     // requires proofs that are missing.
//     let config = TestConfig {
//         args: Some(vec!["verify".into(), "--allow-sorry".into()]),
//         cwd: None,
//         log: None,
//         expected_status: ExpectedStatus::Success, // We check manually
//         expected_stderr: None,
//         expected_stderr_regex: None,
//         artifact: vec![],
//         command: vec![],
//         mock: None,
//     };

//     // 3. First Run: Should Success and create .lake
//     let assert = ctx.run_hermes(&config);
//     assert.success();

//     // 4. Second Run: Should Fail because .lake exists
//     let assert = ctx.run_hermes(&config);
//     assert.failure().stderr(predicates::str::contains("Target .lake directory already exists"));

//     Ok(())
// }

fn run_stale_output_test(path: &Path) -> datatest_stable::Result<()> {
    // Verified that Hermes proactively cleans its output directory before
    // generating new files.
    //
    // This test simulates a scenario where a previous run generated a file
    // (Stale.lean) that is no longer part of the current source. We check that
    // Hermes removes this stale file, ensuring that the generated output
    // accurately reflects the current source and does not contain phantom
    // artifacts.

    // 1. Setup TestContext
    let ctx = TestContext::new(path)?;

    // 2. Configure a basic run
    let config = TestConfig {
        args: Some(vec!["verify".into(), "--allow-sorry".into()]),
        ..Default::default()
    };

    // 3. First Run: Should succeed and create output
    let assert = ctx.run_hermes(&config);
    assert.success();

    // 4. Locate the generated output directory
    let target_dir = ctx.sandbox_root.join("target");
    let generated_root = find_generated_root(&target_dir)?;

    // 5. Pollute the output directory with a stale file
    // We need to find the slug directory inside `generated`.
    // It will be something like `StaleOutputStaleOutput<hash>`.
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

    // 6. Touch the input file to force a re-run if Hermes relies on mtime
    // (Hermes currently re-runs Aeneas pretty aggressively, but good to be safe)
    let lib_rs = ctx.sandbox_root.join("source/src/lib.rs");
    if lib_rs.exists() {
        let _ = fs::File::open(&lib_rs).unwrap().set_len(fs::metadata(&lib_rs).unwrap().len());
    }

    // STALE OUTPUT CLEANUP:
    // We must manually delete `.lake` because `restore_lake_directory` will fail fast if
    // it exists. We are simulating a case where the user (or previous run) cleaned up
    // the build cache but left the generated output files (or where integration tests reuse
    // directories without cleaning them, which we want to be safe against).
    let lean_lake = target_dir.join("hermes/hermes_test_target/lean/.lake");
    if lean_lake.exists() {
        std::fs::remove_dir_all(&lean_lake).expect("Failed to delete stale .lake");
    }
    let lean_manifest = target_dir.join("hermes/hermes_test_target/lean/lake-manifest.json");
    if lean_manifest.exists() {
        std::fs::remove_file(&lean_manifest).expect("Failed to delete stale lake-manifest.json");
    }
    let lean_lakefile = target_dir.join("hermes/hermes_test_target/lean/lakefile.lean");
    if lean_lakefile.exists() {
        std::fs::remove_file(&lean_lakefile).expect("Failed to delete stale lakefile.lean");
    }

    // 7. Second Run: Should succeed and Clean output
    let assert = ctx.run_hermes(&config);
    assert.success();

    // 8. Verify Stale file is GONE
    if stale_file.exists() {
        panic!("Stale file {} was not removed by Hermes!", stale_file.display());
    }

    Ok(())
}

// TODO: Re-enable this, but make sure to run it somewhere that won't affect the
// shared cache. Then again, maybe it already doesn't, and Gemini was just
// confused.

// fn run_atomic_writes_test(path: &Path) -> datatest_stable::Result<()> {
//     // 1. Setup TestContext
//     let ctx = TestContext::new(path)?;

//     // 2. Run 1: Simulate a crash/failure.
//     {
//         // Overwrite the `aeneas` shim to exit with an error code.
//         // This effectively simulates a crash during the Aeneas execution phase.

//         let (cache_dir, _) = get_or_init_shared_cache();
//         let real_charon = which::which("charon").unwrap();
//         let shim_dir = ctx.create_shim("charon", &real_charon, None)?;

//         // Create a broken shim script.
//         let broken_shim = shim_dir.join("aeneas");
//         let content = "#!/bin/sh\necho \"AENEAS INVOKED (BROKEN)\"\nexit 1\n";
//         std::fs::write(&broken_shim, content)?;
//         use std::os::unix::fs::PermissionsExt;
//         let mut perms = std::fs::metadata(&broken_shim)?.permissions();
//         perms.set_mode(0o755);
//         std::fs::set_permissions(&broken_shim, perms)?;

//         // Run Hermes
//         let mut cmd = assert_cmd::cargo_bin_cmd!("hermes");
//         cmd.env("HERMES_FORCE_TTY", "1");
//         cmd.env("FORCE_COLOR", "1");
//         cmd.env("HERMES_AENEAS_DIR", &cache_dir);

//         let original_path = std::env::var_os("PATH").unwrap_or_default();
//         let new_path = std::env::join_paths(
//             std::iter::once(shim_dir).chain(std::env::split_paths(&original_path)),
//         )
//         .unwrap();

//         cmd.env("CARGO_TARGET_DIR", ctx.sandbox_root.join("target"))
//             .env("PATH", new_path)
//             .env_remove("RUSTFLAGS")
//             .env("HERMES_TEST_DIR_NAME", "hermes_test_target")
//             .current_dir(&ctx.sandbox_root)
//             .arg("verify")
//             .arg("--allow-sorry");

//         let assert = cmd.assert();
//         // The verification should fail because Aeneas failed.
//         assert.failure();

//         // Assert that the target directory does NOT exist.
//         let target_lean = ctx.sandbox_root.join("target/hermes/hermes_test_target/lean");
//         if target_lean.exists() {
//             panic!("Target directory {} should NOT exist after crash!", target_lean.display());
//         }
//     }

//     // 3. Run 2: Success.
//     {
//         let (cache_dir, _) = get_or_init_shared_cache();
//         let real_charon = which::which("charon").unwrap();
//         let real_aeneas = which::which("aeneas").unwrap_or_else(|_| PathBuf::from("/bin/true"));

//         let shim_dir = ctx.create_shim("charon", &real_charon, None)?;
//         // Restore the valid shim.
//         ctx.create_shim("aeneas", &real_aeneas, None)?;

//         let mut cmd = assert_cmd::cargo_bin_cmd!("hermes");
//         cmd.env("HERMES_FORCE_TTY", "1")
//             .env("FORCE_COLOR", "1")
//             .env("HERMES_AENEAS_DIR", &cache_dir);

//         let original_path = std::env::var_os("PATH").unwrap_or_default();
//         let new_path = std::env::join_paths(
//             std::iter::once(shim_dir).chain(std::env::split_paths(&original_path)),
//         )
//         .unwrap();

//         cmd.env("CARGO_TARGET_DIR", ctx.sandbox_root.join("target"))
//             .env("PATH", new_path)
//             .env_remove("RUSTFLAGS")
//             .env("HERMES_TEST_DIR_NAME", "hermes_test_target")
//             .current_dir(&ctx.sandbox_root)
//             .arg("verify")
//             .arg("--allow-sorry");

//         cmd.assert().success();

//         let target_lean = ctx.sandbox_root.join("target/hermes/hermes_test_target/lean");
//         if !target_lean.exists() {
//             panic!("Target directory {} SHOULD exist after success!", target_lean.display());
//         }

//         // Mark the file with "OLD" to verify that it is not overwritten later.
//         let marker = target_lean.join("MARKER_OLD");
//         std::fs::write(&marker, "OLD").unwrap();
//     }

//     // 4. Run 3: Crash during update.
//     {
//         // Ensure that the run crashes and that the `lean` directory still contains `MARKER_OLD`.

//         let (cache_dir, _) = get_or_init_shared_cache();
//         let real_charon = which::which("charon").unwrap();
//         let shim_dir = ctx.create_shim("charon", &real_charon, None)?;

//         // Broken Shim Again
//         let broken_shim = shim_dir.join("aeneas");
//         let content = "#!/bin/sh\necho \"AENEAS INVOKED (BROKEN AGAIN)\"\nexit 1\n";
//         std::fs::write(&broken_shim, content)?;
//         use std::os::unix::fs::PermissionsExt;
//         let mut perms = std::fs::metadata(&broken_shim)?.permissions();
//         perms.set_mode(0o755);
//         std::fs::set_permissions(&broken_shim, perms)?;

//         // Run Hermes
//         let mut cmd = assert_cmd::cargo_bin_cmd!("hermes");
//         cmd.env("HERMES_FORCE_TTY", "1")
//             .env("FORCE_COLOR", "1")
//             .env("HERMES_AENEAS_DIR", &cache_dir);

//         let original_path = std::env::var_os("PATH").unwrap_or_default();
//         let new_path = std::env::join_paths(
//             std::iter::once(shim_dir).chain(std::env::split_paths(&original_path)),
//         )
//         .unwrap();

//         cmd.env("CARGO_TARGET_DIR", ctx.sandbox_root.join("target"))
//             .env("PATH", new_path)
//             .env_remove("RUSTFLAGS")
//             .env("HERMES_TEST_DIR_NAME", "hermes_test_target")
//             .current_dir(&ctx.sandbox_root)
//             .arg("verify")
//             .arg("--allow-sorry");

//         cmd.assert().failure();

//         // Verify that the marker file still exists.
//         let target_lean = ctx.sandbox_root.join("target/hermes/hermes_test_target/lean");
//         let marker = target_lean.join("MARKER_OLD");
//         if !marker.exists() {
//             panic!("Target directory was overwritten during failed run! Marker is missing.");
//         }
//     }

//     Ok(())
// }

fn find_generated_root(target_dir: &Path) -> datatest_stable::Result<PathBuf> {
    // Verify that the Hermes output directory structure exists.
    // Expected path: target/hermes
    let hermes_dir = target_dir.join("hermes");
    if !hermes_dir.exists() {
        return Err(format!("Hermes output directory not found at {}", hermes_dir.display()).into());
    }

    for entry in fs::read_dir(hermes_dir)? {
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

// TODO: Re-enable this, but make sure to run it somewhere that won't affect the
// shared cache. Then again, maybe it already doesn't, and Gemini was just
// confused.

// fn run_atomic_cache_recovery_test() -> datatest_stable::Result<()> {
//     // 1. Ensure cache is initialized
//     let (cache_dir, target_dir) = get_or_init_shared_cache();

//     // Acquire the lock to avoid racing with other tests
//     let lock_path = target_dir.join("hermes_integration_cache.lock");
//     let lock_file = fs::File::create(&lock_path).unwrap();
//     lock_file.lock_exclusive().unwrap();

//     let marker = cache_dir.join(".complete");
//     assert!(marker.exists(), "Cache marker should exist after initialization");

//     // 2. Corrupt the cache by removing the marker
//     std::fs::remove_file(&marker).expect("Failed to remove marker");

//     // 3. Create a dummy file to verify cleanup
//     let dummy = cache_dir.join("dummy_corruption.txt");
//     std::fs::write(&dummy, "corrupt").unwrap();

//     // 4. Force re-initialization
//     // We call the inner function directly while holding the lock
//     ensure_cache_ready(&cache_dir).expect("Failed to recover cache");

//     // 5. Verify cleanup and re-initialization
//     assert!(marker.exists(), "Cache marker should be restored");
//     assert!(!dummy.exists(), "Corrupt cache should have been wiped");

//     lock_file.unlock().unwrap();

//     Ok(())
// }

fn run_dirty_sandbox_test(path: &Path) -> datatest_stable::Result<()> {
    // Tests that Hermes correctly detects and fails when the source directory
    // contains stale artifacts or blacklisted files (e.g., target/, .lake/).

    // 1. Attempt to create TestContext (should fail immediately)
    let result = TestContext::new(path);

    // 2. Verify failure
    match result {
        Ok(_) => panic!("TestContext should have failed due to dirty source!"),
        Err(e) => {
            let error_msg = e.to_string();
            if !error_msg.contains("Found blacklisted directory in source")
                && !error_msg.contains("Found blacklisted file in source")
            {
                panic!("Unexpected error message: {}", error_msg);
            }
        }
    }

    Ok(())
}

fn get_expected_charon_version() -> String {
    let cargo_toml_path =
        PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("Cargo.toml");
    let cargo_toml_content =
        fs::read_to_string(&cargo_toml_path).expect("Failed to read Cargo.toml");
    let cargo_toml: toml::Value =
        toml::from_str(&cargo_toml_content).expect("Failed to parse Cargo.toml");
    let metadata = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("build-rs"))
        .expect("Cargo.toml must have [package.metadata.build-rs]");

    metadata.get("charon_version").and_then(|v| v.as_str()).unwrap().to_string()
}
