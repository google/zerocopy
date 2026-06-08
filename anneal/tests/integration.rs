use std::{
    fs, io,
    io::Write as _,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{self, Stdio},
    sync::{Arc, Condvar, Mutex, OnceLock},
    thread,
    time::{Duration, Instant},
};

use assert_cmd::assert::Assert;
use fs2::FileExt as _;
use serde::Deserialize;
use serde_json::{Value, json};
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
// `anneal.toml` (e.g., via `stderr_file` or `matches_expected_dir`), the
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
    matches_expected_dir: Option<String>,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct CommandExpectation {
    args: Vec<String>,
}

static TARGET_DIR: OnceLock<PathBuf> = OnceLock::new();
static TOOLCHAIN_BASE_DIR: OnceLock<PathBuf> = OnceLock::new();
static TOOLCHAIN_INSTALL_DIR: OnceLock<PathBuf> = OnceLock::new();
static TOOLCHAIN_RUN_JOBS: OnceLock<usize> = OnceLock::new();
static PROFILE_LOG: OnceLock<Option<ProfileLog>> = OnceLock::new();
static PROFILE_SAMPLE_MS: OnceLock<u64> = OnceLock::new();
static PROFILE_EMIT_SAMPLES: OnceLock<bool> = OnceLock::new();

struct ProfileLog {
    file: Mutex<fs::File>,
    start: Instant,
}

struct ProfileScope {
    test: String,
    phase: Option<String>,
    name: &'static str,
    start: Instant,
}

impl ProfileScope {
    fn new(test: &str, phase: Option<&str>, name: &'static str) -> Self {
        Self {
            test: test.to_string(),
            phase: phase.map(str::to_string),
            name,
            start: Instant::now(),
        }
    }
}

impl Drop for ProfileScope {
    fn drop(&mut self) {
        emit_profile_event(json!({
            "event": "duration",
            "test": self.test,
            "phase": self.phase,
            "name": self.name,
            "start_ms": profile_elapsed_ms(self.start),
            "duration_ms": self.start.elapsed().as_millis(),
        }));
    }
}

#[derive(Clone, Default)]
struct ProcessMetrics {
    samples: usize,
    max_processes: usize,
    max_threads: u64,
    max_open_fds: u64,
    max_rss_kb: u64,
    max_read_bytes: u64,
    max_write_bytes: u64,
}

struct CommandRun {
    assert: Assert,
}

fn profile_step<T>(
    test: &str,
    phase: Option<&str>,
    name: &'static str,
    f: impl FnOnce() -> T,
) -> T {
    let _scope = ProfileScope::new(test, phase, name);
    f()
}

fn profile_log() -> Option<&'static ProfileLog> {
    PROFILE_LOG
        .get_or_init(|| {
            let path = std::env::var_os("ANNEAL_INTEGRATION_PROFILE")?;
            let path = PathBuf::from(path);
            if let Some(parent) = path.parent()
                && !parent.as_os_str().is_empty()
            {
                fs::create_dir_all(parent).unwrap_or_else(|e| {
                    panic!("failed to create profile directory {}: {e}", parent.display())
                });
            }

            let file =
                fs::OpenOptions::new().create(true).append(true).open(&path).unwrap_or_else(|e| {
                    panic!("failed to open profile log {}: {e}", path.display())
                });
            Some(ProfileLog { file: Mutex::new(file), start: Instant::now() })
        })
        .as_ref()
}

fn profile_elapsed_ms(instant: Instant) -> u128 {
    profile_log().map(|log| instant.saturating_duration_since(log.start).as_millis()).unwrap_or(0)
}

fn emit_profile_event(mut event: serde_json::Value) {
    let Some(log) = profile_log() else { return };
    if let Some(obj) = event.as_object_mut() {
        obj.insert("pid".to_string(), json!(process::id()));
        obj.insert("thread".to_string(), json!(format!("{:?}", thread::current().id())));
    }
    let mut file = log.file.lock().expect("profile log mutex poisoned");
    writeln!(file, "{event}").expect("failed to write profile event");
}

fn profile_sample_ms() -> u64 {
    *PROFILE_SAMPLE_MS.get_or_init(|| {
        std::env::var("ANNEAL_INTEGRATION_PROFILE_SAMPLE_MS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(500)
    })
}

fn profile_emit_samples() -> bool {
    *PROFILE_EMIT_SAMPLES.get_or_init(|| {
        std::env::var("ANNEAL_INTEGRATION_PROFILE_EMIT_SAMPLES").as_deref() == Ok("1")
    })
}

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

fn get_toolchain_base_dir() -> PathBuf {
    TOOLCHAIN_BASE_DIR
        .get_or_init(|| {
            std::env::var_os("ANNEAL_TOOLCHAIN_DIR").map(PathBuf::from).expect(
                "Anneal integration tests require ANNEAL_TOOLCHAIN_DIR to point at a \
                     directory where `cargo run setup --local-archive ...` has already run.",
            )
        })
        .clone()
}

fn get_toolchain_install_dir() -> PathBuf {
    TOOLCHAIN_INSTALL_DIR
        .get_or_init(|| {
            let dir = get_toolchain_base_dir()
                .join("anneal")
                .join("toolchain")
                .join(env!("ANNEAL_EXOCRATE_VERSION_SLUG"));
            if !dir.exists() {
                panic!(
                    "Anneal toolchain is not installed at {}. Run `cargo run setup \
                     --local-archive ...` once before running integration tests.",
                    dir.display()
                );
            }

            for path in [
                dir.join("aeneas/bin/charon"),
                dir.join("aeneas/bin/aeneas"),
                dir.join("lean/bin/lake"),
            ] {
                if !path.exists() {
                    panic!(
                        "Anneal toolchain installation is missing {}. Re-run `cargo run setup \
                         --local-archive ...` before running integration tests.",
                        path.display()
                    );
                }
            }

            dir
        })
        .clone()
}

fn get_toolchain_bin_dir() -> PathBuf {
    get_toolchain_install_dir().join("aeneas").join("bin")
}

fn run_archive_lake_cache_reuse_test(test_name: &str) -> datatest_stable::Result<()> {
    let _permit =
        profile_step(test_name, None, "wait_toolchain_run_slot", || acquire_toolchain_run_slot());
    let temp = tempfile::Builder::new()
        .prefix("anneal-archive-cache-reuse-")
        .tempdir_in(get_target_dir())?;
    assert_archive_lake_cache_reuse(test_name, &get_toolchain_install_dir(), temp.path())
}

fn assert_archive_lake_cache_reuse(
    test_name: &str,
    toolchain_root: &Path,
    temp_root: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let aeneas_root = toolchain_root.join("aeneas");
    let aeneas_lean = aeneas_root.join("backends/lean");
    let lean_root = toolchain_root.join("lean");
    let workspace = temp_root.join("generated-workspace");

    assert_no_write_bits(&aeneas_root)?;

    fs::create_dir_all(workspace.join("generated"))?;
    fs::copy(aeneas_lean.join("lean-toolchain"), workspace.join("lean-toolchain"))?;
    fs::write(workspace.join("generated/Generated.lean"), "import Aeneas\n")?;
    fs::write(
        workspace.join("lakefile.lean"),
        format!(
            r#"import Lake
open Lake DSL

require aeneas from "{}"

package anneal_verification

@[default_target]
lean_lib Generated where
  srcDir := "generated"
  roots := #[`Generated]
"#,
            lake_string(&aeneas_lean)
        ),
    )?;
    write_relative_archive_manifest(&workspace, &aeneas_lean)?;

    // This mirrors v1's generated workspace contract with the Nix-built
    // archive: dependency paths are locked relative to the workspace, package
    // caches are read-only, and `--old` must reuse the prebuilt Lake outputs.
    run_lake_archive_command(
        test_name,
        &workspace,
        &lean_root,
        &["--keep-toolchain", "--old", "build", "Generated"],
    )?;
    run_lake_archive_command(
        test_name,
        &workspace,
        &lean_root,
        &["--keep-toolchain", "env", "lean", "--json", "generated/Generated.lean"],
    )?;

    Ok(())
}

fn assert_no_write_bits(root: &Path) -> Result<(), Box<dyn std::error::Error>> {
    for entry in new_sorted_walkdir(root) {
        let entry = entry?;
        let metadata = fs::symlink_metadata(entry.path())?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        if metadata.permissions().mode() & 0o222 != 0 {
            panic!("archive path should be read-only: {}", entry.path().display());
        }
    }
    Ok(())
}

fn write_relative_archive_manifest(
    workspace: &Path,
    aeneas_lean: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let aeneas_lean = fs::canonicalize(aeneas_lean)?;
    let workspace = fs::canonicalize(workspace)?;
    let manifest_path = aeneas_lean.join("lake-manifest.json");
    let manifest: Value = serde_json::from_reader(fs::File::open(&manifest_path)?)?;
    let aeneas_packages = manifest.get("packages").and_then(Value::as_array).ok_or_else(|| {
        invalid_data(format!(
            "Aeneas Lake manifest {} is missing packages",
            manifest_path.display()
        ))
    })?;

    let aeneas_dir = relative_manifest_string(&aeneas_lean, &workspace)?;
    let mut packages = vec![json!({
        "type": "path",
        "name": "aeneas",
        "dir": aeneas_dir,
        "inherited": false,
    })];

    for entry in aeneas_packages {
        let mut entry = entry
            .as_object()
            .cloned()
            .ok_or_else(|| invalid_data("Aeneas Lake manifest package entry is not an object"))?;
        let package_type = entry
            .get("type")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid_data("Aeneas Lake manifest package entry is missing type"))?;
        if package_type != "path" {
            return Err(invalid_data(format!(
                "Aeneas Lake manifest package entry is {package_type:?}, not a path dependency"
            ))
            .into());
        }
        let package_dir = entry
            .get("dir")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid_data("Aeneas Lake manifest package entry is missing dir"))?;
        let package_dir = Path::new(package_dir);
        let package_dir = if package_dir.is_absolute() {
            package_dir.to_path_buf()
        } else {
            aeneas_lean.join(package_dir)
        };
        let package_dir = fs::canonicalize(package_dir)?;
        entry.insert("dir".to_string(), json!(relative_manifest_string(&package_dir, &workspace)?));
        entry.insert("inherited".to_string(), json!(true));
        packages.push(Value::Object(entry));
    }

    let manifest = json!({
        "version": "1.2.0",
        "packagesDir": ".lake/packages",
        "packages": packages,
        "name": "anneal_verification",
        "lakeDir": ".lake",
        "fixedToolchain": false,
    });
    fs::write(
        workspace.join("lake-manifest.json"),
        format!("{}\n", serde_json::to_string_pretty(&manifest)?),
    )?;
    Ok(())
}

fn relative_manifest_string(
    path: &Path,
    base: &Path,
) -> Result<String, Box<dyn std::error::Error>> {
    let path = pathdiff::diff_paths(path, base).ok_or_else(|| {
        invalid_data(format!(
            "failed to compute relative path from {} to {}",
            base.display(),
            path.display()
        ))
    })?;
    Ok(path.to_string_lossy().into_owned())
}

fn lake_string(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "\\\\").replace('"', "\\\"")
}

fn run_lake_archive_command(
    test_name: &str,
    workspace: &Path,
    lean_root: &Path,
    args: &[&str],
) -> Result<(), Box<dyn std::error::Error>> {
    let lean_bin = lean_root.join("bin");
    let mut cmd = process::Command::new(lean_bin.join("lake"));
    cmd.args(args)
        .current_dir(workspace)
        .env_remove("CI")
        .env("LEAN_SYSROOT", lean_root)
        .env("MATHLIB_NO_CACHE_ON_UPDATE", "1")
        .env("PATH", prepend_env_paths("PATH", &[lean_bin])?);

    let lib_var = if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" };
    cmd.env(
        lib_var,
        prepend_env_paths(lib_var, &[lean_root.join("lib"), lean_root.join("lib/lean")])?,
    );

    run_command_with_profile(test_name, Some("archive_lake_cache_reuse"), cmd)?.assert.success();
    Ok(())
}

fn prepend_env_paths(
    var_name: &str,
    new_paths: &[PathBuf],
) -> Result<std::ffi::OsString, Box<dyn std::error::Error>> {
    let mut paths = new_paths.to_vec();
    if let Some(existing) = std::env::var_os(var_name) {
        paths.extend(std::env::split_paths(&existing));
    }
    Ok(std::env::join_paths(paths)?)
}

fn invalid_data(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn toolchain_run_jobs() -> usize {
    *TOOLCHAIN_RUN_JOBS.get_or_init(|| {
        std::env::var("ANNEAL_INTEGRATION_REAL_JOBS")
            .ok()
            .and_then(|s| s.parse().ok())
            .filter(|jobs| *jobs > 0)
            .unwrap_or(1)
    })
}

struct ToolchainRunPermit {
    _lock: fs::File,
    slot: usize,
    jobs: usize,
    wait: Duration,
    acquired_at: Instant,
}

impl ToolchainRunPermit {
    fn hold_duration(&self) -> Duration {
        self.acquired_at.elapsed()
    }
}

fn acquire_toolchain_run_slot() -> ToolchainRunPermit {
    let started = Instant::now();
    let jobs = toolchain_run_jobs();
    let target_dir = get_target_dir();
    fs::create_dir_all(&target_dir).expect("failed to create integration target directory");

    loop {
        for slot in 0..jobs {
            let lock_path = target_dir.join(format!("anneal-toolchain-run-{slot}.lock"));
            let lock =
                fs::OpenOptions::new().create(true).write(true).open(&lock_path).unwrap_or_else(
                    |e| panic!("failed to open integration lock {}: {e}", lock_path.display()),
                );
            match lock.try_lock_exclusive() {
                Ok(()) => {
                    return ToolchainRunPermit {
                        _lock: lock,
                        slot,
                        jobs,
                        wait: started.elapsed(),
                        acquired_at: Instant::now(),
                    };
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => continue,
                Err(e) => panic!("failed to lock {}: {e}", lock_path.display()),
            }
        }

        thread::sleep(Duration::from_millis(25));
    }
}

fn run_command_with_profile(
    test: &str,
    phase: Option<&str>,
    mut cmd: process::Command,
) -> io::Result<CommandRun> {
    let argv: Vec<_> = std::iter::once(cmd.get_program().to_string_lossy().to_string())
        .chain(cmd.get_args().map(|arg| arg.to_string_lossy().to_string()))
        .collect();
    let cwd = cmd.get_current_dir().map(|dir| dir.display().to_string());
    let started = Instant::now();

    cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let child = cmd.spawn()?;
    let child_pid = child.id();
    let sampler = ProcessSampler::start(test, phase, child_pid);
    let output = child.wait_with_output()?;
    let metrics = sampler.map(ProcessSampler::finish);

    let metrics_json = metrics.as_ref().map(|metrics| {
        json!({
            "samples": metrics.samples,
            "max_processes": metrics.max_processes,
            "max_threads": metrics.max_threads,
            "max_open_fds": metrics.max_open_fds,
            "max_rss_kb": metrics.max_rss_kb,
            "max_read_bytes": metrics.max_read_bytes,
            "max_write_bytes": metrics.max_write_bytes,
        })
    });

    emit_profile_event(json!({
        "event": "command",
        "test": test,
        "phase": phase,
        "argv": argv,
        "cwd": cwd,
        "status_code": output.status.code(),
        "success": output.status.success(),
        "start_ms": profile_elapsed_ms(started),
        "duration_ms": started.elapsed().as_millis(),
        "stdout_bytes": output.stdout.len(),
        "stderr_bytes": output.stderr.len(),
        "process_metrics": metrics_json,
    }));

    Ok(CommandRun { assert: Assert::new(output) })
}

struct ProcessSampler {
    stop: Arc<(Mutex<bool>, Condvar)>,
    handle: thread::JoinHandle<ProcessMetrics>,
}

impl ProcessSampler {
    fn start(test: &str, phase: Option<&str>, root_pid: u32) -> Option<Self> {
        profile_log()?;
        let sample_ms = profile_sample_ms();
        if sample_ms == 0 {
            return None;
        }

        let stop = Arc::new((Mutex::new(false), Condvar::new()));
        let thread_stop = Arc::clone(&stop);
        let test = test.to_string();
        let phase = phase.map(str::to_string);
        let handle = thread::spawn(move || {
            let started = Instant::now();
            let mut metrics = ProcessMetrics::default();
            loop {
                if *thread_stop.0.lock().expect("process sampler mutex poisoned") {
                    break;
                }

                if let Some(sample) = collect_process_sample(root_pid) {
                    metrics.samples += 1;
                    metrics.max_processes = metrics.max_processes.max(sample.processes);
                    metrics.max_threads = metrics.max_threads.max(sample.threads);
                    metrics.max_open_fds = metrics.max_open_fds.max(sample.open_fds);
                    metrics.max_rss_kb = metrics.max_rss_kb.max(sample.rss_kb);
                    metrics.max_read_bytes = metrics.max_read_bytes.max(sample.read_bytes);
                    metrics.max_write_bytes = metrics.max_write_bytes.max(sample.write_bytes);

                    if profile_emit_samples() {
                        emit_profile_event(json!({
                            "event": "process_sample",
                            "test": test,
                            "phase": phase,
                            "root_pid": root_pid,
                            "sample_elapsed_ms": started.elapsed().as_millis(),
                            "processes": sample.processes,
                            "threads": sample.threads,
                            "open_fds": sample.open_fds,
                            "rss_kb": sample.rss_kb,
                            "read_bytes": sample.read_bytes,
                            "write_bytes": sample.write_bytes,
                        }));
                    }
                }

                let stop = thread_stop.0.lock().expect("process sampler mutex poisoned");
                let (stop, _) = thread_stop
                    .1
                    .wait_timeout_while(stop, Duration::from_millis(sample_ms), |stop| !*stop)
                    .expect("process sampler condvar poisoned");
                if *stop {
                    break;
                }
            }
            metrics
        });

        Some(Self { stop, handle })
    }

    fn finish(self) -> ProcessMetrics {
        *self.stop.0.lock().expect("process sampler mutex poisoned") = true;
        self.stop.1.notify_one();
        self.handle.join().expect("process sampler panicked")
    }
}

#[derive(Default)]
struct ProcessSample {
    processes: usize,
    threads: u64,
    open_fds: u64,
    rss_kb: u64,
    read_bytes: u64,
    write_bytes: u64,
}

#[cfg(target_os = "linux")]
fn collect_process_sample(root_pid: u32) -> Option<ProcessSample> {
    let mut parents = std::collections::HashMap::new();
    for entry in fs::read_dir("/proc").ok()? {
        let Ok(entry) = entry else { continue };
        let Some(pid) = entry.file_name().to_str().and_then(|name| name.parse::<u32>().ok()) else {
            continue;
        };
        if let Some(ppid) = read_proc_ppid(pid) {
            parents.insert(pid, ppid);
        }
    }

    if !parents.contains_key(&root_pid) {
        return None;
    }

    let mut sample = ProcessSample::default();
    for &pid in parents.keys() {
        if !is_descendant(pid, root_pid, &parents) {
            continue;
        }
        sample.processes += 1;
        if let Some(status) = read_proc_status(pid) {
            sample.rss_kb += status.rss_kb;
            sample.threads += status.threads;
        }
        sample.open_fds += fs::read_dir(format!("/proc/{pid}/fd"))
            .map(|entries| entries.count() as u64)
            .unwrap_or(0);
        if let Some(io) = read_proc_io(pid) {
            sample.read_bytes += io.0;
            sample.write_bytes += io.1;
        }
    }

    Some(sample)
}

#[cfg(not(target_os = "linux"))]
fn collect_process_sample(_root_pid: u32) -> Option<ProcessSample> {
    None
}

#[cfg(target_os = "linux")]
fn read_proc_ppid(pid: u32) -> Option<u32> {
    let stat = fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
    let (_, fields) = stat.rsplit_once(") ")?;
    fields.split_whitespace().nth(1)?.parse().ok()
}

#[cfg(target_os = "linux")]
fn is_descendant(
    mut pid: u32,
    root_pid: u32,
    parents: &std::collections::HashMap<u32, u32>,
) -> bool {
    loop {
        if pid == root_pid {
            return true;
        }
        let Some(&ppid) = parents.get(&pid) else { return false };
        if ppid == 0 || ppid == pid {
            return false;
        }
        pid = ppid;
    }
}

#[cfg(target_os = "linux")]
struct ProcStatus {
    rss_kb: u64,
    threads: u64,
}

#[cfg(target_os = "linux")]
fn read_proc_status(pid: u32) -> Option<ProcStatus> {
    let status = fs::read_to_string(format!("/proc/{pid}/status")).ok()?;
    let mut proc_status = ProcStatus { rss_kb: 0, threads: 0 };
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            proc_status.rss_kb =
                rest.split_whitespace().next().and_then(|s| s.parse().ok()).unwrap_or(0);
        } else if let Some(rest) = line.strip_prefix("Threads:") {
            proc_status.threads =
                rest.split_whitespace().next().and_then(|s| s.parse().ok()).unwrap_or(0);
        }
    }
    Some(proc_status)
}

#[cfg(target_os = "linux")]
fn read_proc_io(pid: u32) -> Option<(u64, u64)> {
    let io = fs::read_to_string(format!("/proc/{pid}/io")).ok()?;
    let mut read_bytes = 0;
    let mut write_bytes = 0;
    for line in io.lines() {
        if let Some(rest) = line.strip_prefix("read_bytes:") {
            read_bytes = rest.trim().parse().unwrap_or(0);
        } else if let Some(rest) = line.strip_prefix("write_bytes:") {
            write_bytes = rest.trim().parse().unwrap_or(0);
        }
    }
    Some((read_bytes, write_bytes))
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
        profile_step(&test_name, None, "check_source_freshness", || {
            check_source_freshness(&source_dir).map_err(|e| e.to_string())
        })?;

        let target_dir = get_target_dir();
        let temp = profile_step(&test_name, None, "create_sandbox", || {
            fs::create_dir_all(&target_dir)?;
            tempfile::Builder::new().prefix("anneal-test-").tempdir_in(&target_dir)
        })?;

        let sandbox_root = temp.path().join(&test_name);
        let home_dir = temp.path().join("home");
        profile_step(&test_name, None, "copy_fixture_source", || {
            fs::create_dir_all(&home_dir)?;
            copy_dir_contents(&source_dir, &sandbox_root)
        })?;

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

        // Copy extra inputs based on config.
        profile_step(&test_name, None, "copy_extra_inputs", || {
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
            Ok::<_, io::Error>(())
        })?;

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

    fn run_anneal(&self, config: &TestConfig, phase_name: Option<&str>) -> CommandRun {
        let mut cmd = process::Command::new(assert_cmd::cargo::cargo_bin!("cargo-anneal"));
        cmd.env_clear();

        // After clearing the environment to prevent scope leakage, we must
        // manually forward essential host variables required by Cargo and the
        // host toolchain.
        for var in [
            "RUSTUP_HOME",
            "CARGO_HOME",
            "RUSTUP_TOOLCHAIN",
            "LD_LIBRARY_PATH",
            "TMPDIR",
            "TMP",
            "TEMP",
            "USER",
            "USERNAME",
        ] {
            if let Some(val) = std::env::var_os(var) {
                cmd.env(var, val);
            }
        }

        cmd.env("ANNEAL_TOOLCHAIN_DIR", get_toolchain_base_dir());
        cmd.env("HOME", &self.home_dir);

        // Resolve Mocks

        // Re-organizing execution flow:
        // 1. Prepare mocks (if any)
        let mut charon_mock_mode = None;
        let mut aeneas_mock_mode = None;

        profile_step(&self.test_name, phase_name, "prepare_mocks", || {
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

                        let processed_mock = mock_content
                            .replace("[PROJECT_ROOT]", self.sandbox_root.to_str().unwrap());
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
        });

        // Create shims for Charon and Aeneas.
        //
        // Most integration tests run against the already-installed toolchain
        // directly. Only tests that explicitly request mocks or command
        // assertions use PATH shims.
        let use_tool_shims = config.mock.is_some() || !config.command.is_empty();
        let original_path = std::env::var_os("PATH").unwrap_or_default();
        profile_step(&self.test_name, phase_name, "prepare_tool_shims", || {
            if use_tool_shims {
                let toolchain_bin_dir = get_toolchain_bin_dir();
                let shim_dir = self.sandbox_root.join("bin_shim");
                fs::create_dir_all(&shim_dir).unwrap();

                if charon_mock_mode.is_some() || !config.command.is_empty() {
                    let real_charon = toolchain_bin_dir.join("charon");
                    self.create_shim("charon", &real_charon, charon_mock_mode).unwrap();
                }
                if aeneas_mock_mode.is_some() {
                    let real_aeneas = toolchain_bin_dir.join("aeneas");
                    self.create_shim("aeneas", &real_aeneas, aeneas_mock_mode).unwrap();
                }

                let new_path = std::env::join_paths(
                    std::iter::once(shim_dir)
                        .chain(std::iter::once(toolchain_bin_dir))
                        .chain(std::env::split_paths(&original_path)),
                )
                .unwrap();
                cmd.env("PATH", new_path);
                cmd.env("ANNEAL_USE_PATH_FOR_TOOLS", "1");
            } else {
                cmd.env("PATH", original_path);
            }
        });

        cmd.env("ANNEAL_FORCE_TTY", "1");
        cmd.env("FORCE_COLOR", "1");
        cmd.env("RAYON_NUM_THREADS", "1");

        // Ensure deterministic LLBC generation within the integration test
        // sandbox by rebasing the `workspace_root` off the absolute filesystem
        // onto `/dummy`.
        let rustflags = format!("--remap-path-prefix={}=/dummy", self.test_case_root.display());

        cmd.env("CARGO_TARGET_DIR", self.sandbox_root.join("target"));
        cmd.env("RUSTFLAGS", rustflags);

        // Redirect HOME to a persistent directory within the sandbox so
        // user-local Cargo or tool output cannot leak across fixtures.
        cmd.env("HOME", &self.home_dir)
            .env("ANNEAL_TEST_DIR_NAME", "anneal_test_target")
            .env("ANNEAL_HASH_WITH_REMOVED_PREFIX", &self.sandbox_root);

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

        run_command_with_profile(&self.test_name, phase_name, cmd)
            .expect("failed to execute cargo-anneal")
    }
}

fn run_integration_test(path: &Path) -> datatest_stable::Result<()> {
    let path_str = path.to_string_lossy();
    let test_case_root = path.parent().unwrap();
    let test_name = test_case_root.file_name().unwrap().to_string_lossy().to_string();
    let _fixture_scope = ProfileScope::new(&test_name, None, "fixture_total");

    let anneal_toml_content = profile_step(&test_name, None, "read_manifest", || {
        fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("Failed to read {}: {}", path.display(), e))
    });
    let anneal_toml: AnnealToml = profile_step(&test_name, None, "parse_manifest", || {
        toml::from_str(&anneal_toml_content)
            .unwrap_or_else(|e| panic!("Failed to parse {}: {}", path.display(), e))
    });
    assert!(
        !anneal_toml.description.trim().is_empty(),
        "Test {} is missing a non-empty `description` field in anneal.toml",
        test_name
    );

    // Special handling for the "dirty_sandbox" test case.
    if path_str.contains("dirty_sandbox/anneal.toml") {
        return profile_step(&test_name, None, "dirty_sandbox_test", || {
            run_dirty_sandbox_test(path)
        });
    }
    if path_str.contains("archive_lake_cache_reuse/anneal.toml") {
        return profile_step(&test_name, None, "archive_lake_cache_reuse_test", || {
            run_archive_lake_cache_reuse_test(&test_name)
        });
    }
    // Load the test configuration from the associated 'anneal.toml' manifest.
    let config = anneal_toml.test.unwrap_or_default();

    // `path` is `tests/fixtures/<test_case>/anneal.toml`
    let ctx =
        profile_step(&test_name, None, "create_test_context", || TestContext::new(path, &config))?;

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
        profile_step(&ctx.test_name, None, "assert_artifacts", || {
            assert_artifacts_match(&anneal_run_root, &ctx.test_case_root, &config.artifact)
        })?;
    }

    // Verify Commands
    if !config.command.is_empty() {
        profile_step(&ctx.test_name, None, "assert_commands", || {
            let log_file = ctx.sandbox_root.join("tool_args.log");
            if !log_file.exists() {
                panic!("Command log file not found! Was the shim called?");
            }
            let log_content = fs::read_to_string(log_file)?;
            let invocations = parse_command_log(&log_content);
            assert_commands_match(&invocations, &config.command);
            Ok::<_, io::Error>(())
        })?;
    }

    profile_step(&ctx.test_name, None, "assert_no_unmapped_files", || {
        assert_no_unmapped_files(&ctx, &config)
    });

    Ok(())
}

fn assert_no_unmapped_files(ctx: &TestContext, config: &TestConfig) {
    let mut allowed_paths = std::collections::HashSet::new();

    // Always allowed baseline files/directories
    allowed_paths.insert(ctx.test_case_root.join("source"));
    allowed_paths.insert(ctx.test_case_root.join("anneal.toml"));

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
    let phase_name = phase.map(|phase| phase.name.as_str());
    let _phase_scope = ProfileScope::new(&ctx.test_name, phase_name, "phase_total");

    if let Some(phase) = phase
        && let Some(action) = &phase.action
    {
        if action == "touch_stale_file" {
            return profile_step(&ctx.test_name, phase_name, "action_touch_stale_file", || {
                let generated_root =
                    ctx.sandbox_root.join("target/anneal/anneal_test_target/lean/generated");
                if !generated_root.exists() {
                    return Err(format!(
                        "Generated Lean directory not found at {}",
                        generated_root.display()
                    )
                    .into());
                }

                let mut slug_dir = None;
                for entry in fs::read_dir(&generated_root)? {
                    let entry = entry?;
                    if entry.file_type()?.is_dir() {
                        slug_dir = Some(entry.path());
                        break;
                    }
                }
                let slug_dir = slug_dir.ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::NotFound,
                        "No slug directory found in generated root",
                    )
                })?;

                let stale_file = slug_dir.join("Stale.lean");
                std::fs::write(&stale_file, "INVALID LEAN CODE").unwrap();
                assert!(stale_file.exists());

                Ok(())
            });
        } else if action == "delete_lake_dir" {
            return profile_step(&ctx.test_name, phase_name, "action_delete_lake_dir", || {
                // Delete the `.lake` build artifacts directory. This is used in
                // `stale_output` tests to force Lake to regenerate its build
                // artifacts from scratch, ensuring that stale cached data doesn't
                // mask bugs in artifact generation or synchronization.
                let lean_root = ctx.sandbox_root.join("target/anneal/anneal_test_target/lean");
                let lake_dir = lean_root.join(".lake");
                if lake_dir.exists() {
                    fs::remove_dir_all(&lake_dir).expect("Failed to delete .lake directory");
                }
                Ok(())
            });
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

    // `datatest_stable` may schedule fixtures concurrently regardless of
    // `RUST_TEST_THREADS`. Real toolchain runs copy/use the installed Lean
    // dependency tree and can exhaust host-wide file handles if many do that at
    // once. Mock-only tests do not hit that path, so keep those parallel while
    // serializing the resource-heavy command execution.
    let run = if config.mock.is_none() {
        let permit = profile_step(&ctx.test_name, phase_name, "wait_toolchain_run_slot", || {
            acquire_toolchain_run_slot()
        });
        emit_profile_event(json!({
            "event": "toolchain_run_slot_acquired",
            "test": ctx.test_name,
            "phase": phase_name,
            "slot": permit.slot,
            "jobs": permit.jobs,
            "wait_ms": permit.wait.as_millis(),
        }));
        let run = ctx.run_anneal(&config, phase_name);
        emit_profile_event(json!({
            "event": "toolchain_run_slot_released",
            "test": ctx.test_name,
            "phase": phase_name,
            "slot": permit.slot,
            "jobs": permit.jobs,
            "hold_ms": permit.hold_duration().as_millis(),
        }));
        run
    } else {
        ctx.run_anneal(&config, phase_name)
    };
    let assert = run.assert;

    // Verify Exit Status
    let _assert_status_scope = ProfileScope::new(&ctx.test_name, phase_name, "assert_exit_status");
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
    drop(_assert_status_scope);

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
        profile_step(&ctx.test_name, phase_name, "assert_stderr", || {
            assert_output_file(
                &ctx.test_case_root,
                &ctx.sandbox_root,
                &ctx.test_name,
                &ctx.home_dir,
                stderr_file,
                &output.stderr,
                "Stderr",
            )
        });
    }

    if let Some(stdout_file) = &config.stdout_file {
        profile_step(&ctx.test_name, phase_name, "assert_stdout", || {
            assert_output_file(
                &ctx.test_case_root,
                &ctx.sandbox_root,
                &ctx.test_name,
                &ctx.home_dir,
                stdout_file,
                &output.stdout,
                "Stdout",
            )
        });
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
    let target_path_str = target_dir.to_str().unwrap();
    let toolchain_base = get_toolchain_base_dir();
    let toolchain_base_str = toolchain_base.to_str().unwrap();
    let toolchain_install_dir = get_toolchain_install_dir();
    let toolchain_install_dir_str = toolchain_install_dir.to_str().unwrap();
    let toolchain_bin_dir = get_toolchain_bin_dir();
    let toolchain_bin_dir_str = toolchain_bin_dir.to_str().unwrap();
    let home_path_str = home_dir.to_str().unwrap();
    // Replace volatile environment-specific paths with static placeholders.
    //
    // - `replace_path` corresponds to the sandbox root, which varies per
    //   test run.
    // - `toolchain_*` paths correspond to the shared pre-installed toolchain.
    // - `target_path_str` corresponds to the cargo target directory or override.
    // - `home_path_str` corresponds to the user's home directory (redirected in
    //   tests).
    let actual_clean = sanitize_output(
        &actual_str
            .replace(replace_path, "[PROJECT_ROOT]")
            .replace(toolchain_bin_dir_str, "[CACHE_ROOT]")
            .replace(toolchain_install_dir_str, "[CACHE_ROOT]")
            .replace(toolchain_base_str, "[CACHE_ROOT]")
            .replace(home_path_str, "[HOME]")
            .replace(target_path_str, "[TARGET_DIR]"),
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
        }
    }
    invocations
}

fn assert_commands_match(invocations: &[Vec<String>], expectations: &[CommandExpectation]) {
    for exp in expectations {
        let found = invocations.iter().any(|cmd| is_subsequence(cmd, &exp.args));

        if !found {
            panic!(
                "Expected command invocation with args {:?} was not found.\nCaptured Invocations: {:#?}",
                exp.args, invocations
            );
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

        // We match strictly on the PascalCase package/target prefix produced by
        // scanner.rs.
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
                // artifacts might match the package prefix. The expectation
                // passes if any one artifact matches.
                let mut any_matched = false;
                let mut collected_errors = String::new();

                for file_name in matching_items {
                    let actual_path = scan_dir.join(file_name);

                    match artifact_path_matches(&expected_path, &actual_path) {
                        Ok(()) => {
                            any_matched = true;
                            break;
                        }
                        Err(e) => collected_errors
                            .push_str(&format!("Artifact '{}' mismatch:\n{}\n", file_name, e)),
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

fn artifact_path_matches(expected: &Path, actual: &Path) -> Result<(), String> {
    if actual.is_dir() != expected.is_dir() {
        return Err(format!(
            "Type mismatch: expected {:?} (is_dir: {}), actual {:?} (is_dir: {})",
            expected,
            expected.is_dir(),
            actual,
            actual.is_dir()
        ));
    }

    if actual.is_dir() {
        directories_match(expected, actual)
    } else {
        files_match(expected, actual)
    }
}

fn files_match(expected: &Path, actual: &Path) -> Result<(), String> {
    let e_txt = fs::read_to_string(expected)
        .map_err(|e| format!("Failed to read expected file {:?}: {}", expected, e))?
        .replace("\r\n", "\n");
    let a_txt = fs::read_to_string(actual)
        .map_err(|e| format!("Failed to read actual file {:?}: {}", actual, e))?
        .replace("\r\n", "\n");
    if e_txt != a_txt {
        return Err(format!("Mismatch in {:?}:\n{}", expected, diff_text(&e_txt, &a_txt)));
    }
    Ok(())
}

fn directories_match(expected: &Path, actual: &Path) -> Result<(), String> {
    for entry in new_sorted_walkdir(expected) {
        let entry = entry.map_err(|e| e.to_string())?;
        if !entry.file_type().is_file() {
            continue;
        }
        let rel = entry.path().strip_prefix(expected).unwrap();
        let act = actual.join(rel);
        if !act.exists() {
            return Err(format!(
                "Missing file in actual artifact:\nExpected: {:?}\nActual is missing: {:?}",
                entry.path(),
                act
            ));
        }
        if let Err(e) = files_match(entry.path(), &act) {
            return Err(format!("Mismatch in {:?}:\n{}", rel, e));
        }
    }
    // Check for extra files in actual
    for entry in new_sorted_walkdir(actual) {
        let entry = entry.map_err(|e| e.to_string())?;
        if !entry.file_type().is_file() {
            continue;
        }
        let rel = entry.path().strip_prefix(actual).unwrap();
        let exp = expected.join(rel);
        if !exp.exists() {
            return Err(format!(
                "Extra file found in actual artifact that is not in expected:\n{:?}",
                rel
            ));
        }
    }
    Ok(())
}

fn diff_text(expected: &str, actual: &str) -> String {
    use similar::{ChangeTag, TextDiff};
    let diff = TextDiff::from_lines(expected, actual);
    let mut diff_str = String::new();
    for change in diff.iter_all_changes() {
        let sign = match change.tag() {
            ChangeTag::Delete => "-",
            ChangeTag::Insert => "+",
            ChangeTag::Equal => " ",
        };
        diff_str.push_str(&format!("{sign}{change}"));
    }
    diff_str
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
// - Local IP/port combinations used in mock servers (replaced with
//   `127.0.0.1:<PORT>`)
// - Rustup toolchain paths (replaced with `[RUSTUP_TOOLCHAIN]`)
fn sanitize_output(output: &str) -> String {
    let re_thread_id = regex::Regex::new(r"thread '([^']+)' \(\d+\) panicked").unwrap();
    let re_file_lock =
        regex::Regex::new(r"(?m)^.*Blocking waiting for file lock on.*$\n?").unwrap();
    let re_cargo_hash = regex::Regex::new(r"([-=_])([a-f0-9]{5,16})\b").unwrap();

    let re_timing = regex::Regex::new(r"took \d+(\.\d*)?(m?s)").unwrap();
    let re_lake_timing = regex::Regex::new(r"\(\d+(\.\d*)?m?s\)").unwrap();
    let re_aeneas_time = regex::Regex::new(r"Total execution time: \d+\.\d+ seconds").unwrap();
    let re_ip_port = regex::Regex::new(r"127\.0\.0\.1:\d+").unwrap();
    let re_rustup =
        regex::Regex::new(r"[^\s]*/(?:\.rustup|opt/rustup)/toolchains/[^/\s]+").unwrap();
    let re_elan = regex::Regex::new(r"[^\s]*/(?:\.elan|opt/elan)/toolchains/[^/\s]+").unwrap();
    // Lake's build progress indicators are volatile as they depend on the cache hit/miss state. We strip the entire line.
    let re_lake_progress = regex::Regex::new(r"(?m)^.*\[\d+/\d+\].*$\n?").unwrap();

    // Aeneas progress bars contain volatile spinner characters. We strip them.
    let re_applied_prepasses = regex::Regex::new(r"(?m)^.*Applied prepasses:.*$\n?").unwrap();
    // Strip ANSI escape codes.
    let re_ansi_escape = regex::Regex::new(r"\x1B\[[0-9;]*[a-zA-Z]").unwrap();

    let mut clean = output.to_string();

    clean = re_thread_id.replace_all(&clean, "thread '$1' (<ID>) panicked").into_owned();
    clean = re_file_lock.replace_all(&clean, "").into_owned();
    clean = re_cargo_hash.replace_all(&clean, "${1}<HASH>").into_owned();

    clean = re_timing.replace_all(&clean, "took <TIME>").into_owned();
    clean = re_lake_timing.replace_all(&clean, "(<TIME>)").into_owned();
    clean = re_aeneas_time.replace_all(&clean, "Total execution time: <TIME> seconds").into_owned();
    clean = re_ip_port.replace_all(&clean, "127.0.0.1:<PORT>").into_owned();
    clean = re_rustup.replace_all(&clean, "[RUSTUP_TOOLCHAIN]").into_owned();
    clean = re_elan.replace_all(&clean, "[ELAN_TOOLCHAIN]").into_owned();
    clean = re_lake_progress.replace_all(&clean, "").into_owned();
    clean = re_applied_prepasses.replace_all(&clean, "").into_owned();
    clean = re_ansi_escape.replace_all(&clean, "").into_owned();

    clean
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
