// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! OS-level elaborator containment (`ExecSeal`), per-invocation path mapping,
//! wall-clock process-group reaping, and Door 1 output validation.
//!
//! Shared between `cargo-anneal` and `anneal-audit` so both target verification
//! and repository Pass 2 correspondence verification compile from one
//! declarative [`SandboxPolicy`]. See `docs/elaborator-containment-design.md`
//! Section 3 for the threat model and empirical rationale.

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
#[cfg(unix)]
use std::os::unix::io::AsRawFd;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::{Arc, Mutex, MutexGuard, PoisonError},
    thread,
    time::{Duration, Instant},
};

use sha2::{Digest, Sha256};

use crate::core::{digest_to_hex, validate_olean_v2_header};
pub use crate::core::{MAX_OLEAN_BYTES, OLEAN_V2_MAGIC};
use crate::sys_util::{SafeFs, SysSanitizer};
use crate::toolchain::Failure;

/// Default wall-clock timeout for a single sandboxed Lean invocation.
pub const DEFAULT_CHILD_TIMEOUT: Duration = Duration::from_secs(600);

/// Maximum bytes retained in memory from each child stdout or stderr stream
/// (16 MiB); excess bytes are still drained and discarded to avoid pipe
/// deadlocks without allowing a hostile child to OOM the host.
pub const MAX_CHILD_STREAM_BYTES: usize = 16 * 1024 * 1024;

/// Maximum characters of sanitized partial child output attached to a
/// `sandbox-timeout` failure, including the elision marker.
const MAX_TIMEOUT_EXCERPT_CHARS: usize = 6_000;

/// How long a timed-out run waits for reader threads to observe EOF after
/// the child's process group is killed, so bytes still buffered in the pipes
/// reach the excerpt. Bounded because escaped descendants may hold the pipes
/// open indefinitely.
const TIMEOUT_OUTPUT_GRACE: Duration = Duration::from_millis(100);

/// Bytes of each stream's most recent output kept in a rolling buffer once
/// [`MAX_CHILD_STREAM_BYTES`] is reached, so a timeout excerpt still shows
/// the child's final lines.
const MAX_CHILD_STREAM_TAIL_BYTES: usize = 64 * 1024;

/// Default Door 1 size cap for a single inspector `result.json` output
/// (64 MiB).
pub const DEFAULT_MAX_INSPECTOR_RESULT_BYTES: u64 = 64 * 1024 * 1024;

/// Door 1 size cap for a single inspector `result.json` output under default
/// settings (64 MiB).
pub const MAX_INSPECTOR_RESULT_BYTES: u64 = DEFAULT_MAX_INSPECTOR_RESULT_BYTES;

/// Hard upper ceiling for configurable Door 1 inspector output size limits
/// (1 GiB).
pub const MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES: u64 = 1024 * 1024 * 1024;

/// Per-child default `RLIMIT_FSIZE` cap (256 MiB).
pub const RLIMIT_FSIZE_BYTES: u64 = 256 * 1024 * 1024;

/// Validate a caller-supplied Door 1 inspector output size cap in bytes.
///
/// Rejects `0` and values exceeding
/// [`MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES`] (`1 GiB`) so untrusted
/// inspector outputs remain bounded.
pub fn validate_max_inspector_result_bytes(max_bytes: u64) -> Result<u64, String> {
    if max_bytes == 0 {
        return Err("max inspector output byte cap must be at least 1".to_owned());
    }
    if max_bytes > MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES {
        return Err(format!(
            "max inspector output byte cap ({max_bytes} bytes) exceeds hard ceiling of \
             {MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES} bytes (1 GiB)"
        ));
    }
    Ok(max_bytes)
}

/// Per-child `RLIMIT_NOFILE` cap (live-verified on Lean `v4.34.1` & `v4.35.0`).
pub const RLIMIT_NOFILE_LIMIT: u64 = 256;

/// Caller-selected OS containment policy for Lean child processes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SandboxMode {
    /// Repository Pass 2 (`trusted/audit`): strictly requires Tier 1 `bwrap`.
    RequireBwrap,
    /// Target verification (`cargo-anneal` default): Tier 1 `bwrap`, falling
    /// back to Tier 2 Landlock + Seccomp when user namespaces are unavailable.
    PreferBwrapOrLandlock,
    /// Explicit `--allow-unsandboxed-elaboration`: skip OS confinement.
    Unsandboxed,
}

/// Active OS containment backend selected for a verification run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActiveSandbox {
    LinuxBwrap,
    LinuxLandlockSeccomp,
    None,
}

impl ActiveSandbox {
    /// Receipt wire spelling for `"elaboration_sandbox"`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LinuxBwrap => "linux_bwrap",
            Self::LinuxLandlockSeccomp => "linux_landlock_seccomp",
            Self::None => "none",
        }
    }
}

/// A host-to-child mount binding in a declarative [`SandboxPolicy`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MountSpec {
    pub host: PathBuf,
    pub child: PathBuf,
}

/// Declarative per-invocation confinement policy compiled to either Linux
/// backend (`linux_bwrap` or `linux_landlock_seccomp`).
#[derive(Debug, Clone)]
pub struct SandboxPolicy {
    pub exec_bin: PathBuf,
    pub args: Vec<String>,
    pub ro_mounts: Vec<MountSpec>,
    pub rw_out: MountSpec,
    pub rw_tmp: MountSpec,
    /// Optional working directory inside the child (defaults to `rw_tmp`).
    /// Tier 1 `bwrap` uses `child` (for example `/work`); Tier 2 and
    /// unsandboxed modes use `host` (without granting Landlock access to
    /// `host` itself).
    pub child_cwd: Option<MountSpec>,
    pub extra_env: BTreeMap<String, String>,
    pub timeout: Duration,
}

/// Maps host paths inside mounted roots to child-visible paths.
#[derive(Debug, Clone)]
pub struct PathMapper {
    backend: ActiveSandbox,
    mounts: Vec<MountSpec>,
    toolchain_dir: PathBuf,
    exec_host: PathBuf,
    exec_child: PathBuf,
    needs_nix_store: bool,
}

impl PathMapper {
    /// Construct a [`PathMapper`] for a prepared invocation.
    pub fn new(
        runtime: &SandboxRuntime,
        ro_mounts: &[MountSpec],
        rw_out: &MountSpec,
        rw_tmp: &MountSpec,
    ) -> Self {
        let mut mounts = Vec::with_capacity(
            ro_mounts.len()
                + runtime.toolchain_ro_mounts.len()
                + runtime.extra_toolchain_mounts.len()
                + 2,
        );
        mounts.extend(ro_mounts.iter().cloned());
        mounts.extend(runtime.toolchain_ro_mounts.iter().cloned());
        mounts.extend(runtime.extra_toolchain_mounts.iter().cloned());
        mounts.push(rw_out.clone());
        mounts.push(rw_tmp.clone());
        // Sort longest host path first so nested mounts resolve
        // deterministically.
        mounts.sort_by(|a, b| {
            b.host
                .components()
                .count()
                .cmp(&a.host.components().count())
                .then_with(|| a.host.cmp(&b.host))
        });
        Self {
            backend: runtime.backend,
            mounts,
            toolchain_dir: runtime.toolchain_dir.clone(),
            exec_host: runtime.exec_lean.clone(),
            exec_child: runtime.child_exec_path(),
            needs_nix_store: runtime.needs_nix_store,
        }
    }

    fn has_parent_dir(path: &Path) -> bool {
        path.components().any(|c| matches!(c, std::path::Component::ParentDir))
    }

    fn map_bwrap_exact(&self, path: &Path) -> Option<PathBuf> {
        if Self::has_parent_dir(path) {
            return None;
        }
        if path == self.exec_host {
            return Some(self.exec_child.clone());
        }
        for m in &self.mounts {
            if let Ok(rel) = path.strip_prefix(&m.host) {
                return Some(if rel.as_os_str().is_empty() {
                    m.child.clone()
                } else {
                    m.child.join(rel)
                });
            }
        }
        if path == self.toolchain_dir {
            return Some(PathBuf::from("/toolchain"));
        }
        if self.needs_nix_store && path.starts_with("/nix/store") {
            return Some(path.to_path_buf());
        }
        None
    }

    /// Translate a host path into the child-visible path for this backend.
    pub fn map_path(&self, host: &Path) -> Result<PathBuf, Failure> {
        match self.backend {
            ActiveSandbox::None => Ok(host.to_path_buf()),
            ActiveSandbox::LinuxLandlockSeccomp => {
                if self.map_bwrap_exact(host).is_some() {
                    return Ok(host.to_path_buf());
                }
                if let Ok(canon) = fs::canonicalize(host)
                    && canon != host
                    && self.map_bwrap_exact(&canon).is_some()
                {
                    return Ok(canon);
                }
                Err(Failure::operational(
                    "sandbox",
                    format!("path {} is outside all mounted sandbox roots", host.display()),
                ))
            }
            ActiveSandbox::LinuxBwrap => {
                if let Some(mapped) = self.map_bwrap_exact(host) {
                    return Ok(mapped);
                }
                if let Ok(canon) = fs::canonicalize(host)
                    && canon != host
                    && let Some(mapped) = self.map_bwrap_exact(&canon)
                {
                    return Ok(mapped);
                }
                Err(Failure::operational(
                    "sandbox",
                    format!("path {} is outside all mounted sandbox roots", host.display()),
                ))
            }
        }
    }

    /// Translate a host path into a UTF-8 string for JSON/CLI transport.
    pub fn map_str(&self, host: &Path) -> Result<String, Failure> {
        let mapped = self.map_path(host)?;
        mapped
            .to_str()
            .map(str::to_owned)
            .ok_or_else(|| Failure::operational("sandbox", "non-UTF-8 mapped sandbox path"))
    }
}

/// Refuse any dynamic-linker environment variable (`LD_*`, `DYLD_*`) in a
/// [`SandboxPolicy::extra_env`] map before spawning a child process.
pub fn reject_forbidden_loader_env(extra_env: &BTreeMap<String, String>) -> Result<(), Failure> {
    SysSanitizer::reject_forbidden_loader_env(extra_env)
}

/// Optional host system library/loader paths (`ENOENT`-skipped in both tiers).
#[cfg(target_os = "linux")]
const OPTIONAL_SYS_PATHS: &[&str] = &[
    "/lib",
    "/lib64",
    "/usr/lib",
    "/usr/lib64",
    "/etc/ld.so.cache",
    "/etc/ld.so.conf",
    "/etc/ld.so.conf.d",
];

/// Standard host library directory prefixes already mounted read-only under
/// `OPTIONAL_SYS_PATHS` or `/nix/store`.
#[cfg(any(target_os = "linux", test))]
const STANDARD_LOADER_LIB_PREFIXES: &[&str] =
    &["/lib", "/lib64", "/usr/lib", "/usr/lib64", "/nix/store"];

/// Return `true` when `dir` is equal to or nested under one of the standard
/// system library roots (`/lib`, `/lib64`, `/usr/lib`, `/usr/lib64`, or
/// `/nix/store`).
#[cfg(any(target_os = "linux", test))]
fn is_under_standard_loader_prefix(dir: &Path) -> bool {
    STANDARD_LOADER_LIB_PREFIXES.iter().any(|prefix| dir.starts_with(prefix))
}

/// Reserved child-namespace mount roots inside `run_bwrap` that custom
/// `PT_INTERP` directory bindings must never shadow or overlap.
#[cfg(any(target_os = "linux", test))]
const RESERVED_BWRAP_CHILD_ROOTS: &[&str] = &["/work", "/toolchain", "/dev", "/proc", "/etc"];

/// Return `true` when `path` equals or lies under a reserved `bwrap` child
/// mount root.
#[cfg(any(target_os = "linux", test))]
fn is_reserved_bwrap_child_path(path: &Path) -> bool {
    RESERVED_BWRAP_CHILD_ROOTS.iter().any(|root| path.starts_with(root))
}

/// Validate a custom `PT_INTERP` directory path (canonical host source or
/// logical symlink bind destination) against traversal components, reserved
/// `bwrap` child roots, broad host roots, `stage_root`, `$HOME`, and `cwd`.
#[cfg(any(target_os = "linux", test))]
fn validate_pt_interp_dir(
    dir: &Path,
    stage_root: Option<&Path>,
    role: &str,
) -> Result<(), Failure> {
    use std::path::Component;

    if dir.components().any(|c| matches!(c, Component::CurDir | Component::ParentDir)) {
        return Err(Failure::operational(
            "sandbox",
            format!("refusing non-normalized {role} {} for sandbox mount", dir.display()),
        ));
    }
    if is_reserved_bwrap_child_path(dir) {
        return Err(Failure::operational(
            "sandbox",
            format!("refusing reserved sandbox path {} as {role}", dir.display()),
        ));
    }
    validate_toolchain_mount_dir(dir, stage_root, role)
}

/// Derive validated custom read-only loader library directories from an ELF
/// binary's resolved `PT_INTERP` paths.
///
/// Standard system loaders (`/lib64/ld-linux-x86-64.so.2`,
/// `/usr/lib/.../ld-linux-...`, `/nix/store/...`) are already covered by
/// `OPTIONAL_SYS_PATHS` or `/nix/store` and return an empty list. Custom
/// sysroot loaders (such as musl or self-contained glibc sysroots) place their
/// sibling `libc.so.6`/`libm.so.6` alongside `PT_INTERP`; this validates both
/// each canonical parent directory and any distinct logical symlink parent
/// directory through [`validate_pt_interp_dir`] so broad host prefixes (`/`,
/// `/usr`, `/tmp`, `/home`, `$HOME`, `cwd`, `stage_root`) and reserved child
/// roots (`/work`, `/toolchain`, `/dev`, `/proc`, `/etc`) are refused
/// fail-closed while legitimate dedicated sysroot library directories are
/// mounted strictly read-only.
#[cfg(any(target_os = "linux", test))]
pub fn resolve_pt_interp_lib_dirs(
    pt_interp_paths: &[PathBuf],
    stage_root: Option<&Path>,
) -> Result<Vec<PathBuf>, Failure> {
    let mut dirs = BTreeSet::new();
    for interp in pt_interp_paths {
        let Some(parent) = interp.parent() else {
            continue;
        };
        if !parent.is_absolute() || is_under_standard_loader_prefix(parent) {
            continue;
        }
        let canon_parent = fs::canonicalize(parent).map_err(|e| {
            Failure::operational(
                "sandbox",
                format!("cannot canonicalize PT_INTERP parent directory {}: {e}", parent.display()),
            )
        })?;
        if !fs::metadata(&canon_parent).is_ok_and(|m| m.is_dir()) {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "PT_INTERP parent path {} is not a directory",
                    canon_parent.display()
                ),
            ));
        }
        if is_under_standard_loader_prefix(&canon_parent) {
            continue;
        }
        validate_pt_interp_dir(&canon_parent, stage_root, "PT_INTERP loader library directory")?;
        if canon_parent != parent {
            validate_pt_interp_dir(
                parent,
                stage_root,
                "PT_INTERP logical loader library directory",
            )?;
        }
        dirs.insert(canon_parent);
    }
    Ok(dirs.into_iter().collect())
}

/// Build the validated read-only `bwrap` bind mounts for custom `PT_INTERP`
/// library directories and any distinct logical symlink parent directories.
///
/// Every bind destination is validated against [`validate_pt_interp_dir`]
/// before emission so a symlinked `PT_INTERP` parent can never shadow reserved
/// child roots (`/work`, `/toolchain`, `/dev`, `/proc`, `/etc`) or broad host
/// prefixes.
#[cfg(any(target_os = "linux", test))]
fn resolve_pt_interp_bwrap_mounts(
    pt_interp_paths: &[PathBuf],
    pt_interp_lib_dirs: &[PathBuf],
    stage_root: Option<&Path>,
) -> Result<Vec<MountSpec>, Failure> {
    let mut mounts = Vec::new();
    let mut seen = BTreeSet::new();
    for interp_dir in pt_interp_lib_dirs {
        validate_pt_interp_dir(interp_dir, stage_root, "PT_INTERP loader library directory")?;
        let key = (interp_dir.clone(), interp_dir.clone());
        if seen.insert(key) {
            mounts.push(MountSpec { host: interp_dir.clone(), child: interp_dir.clone() });
        }
    }
    for interp in pt_interp_paths {
        let Some(parent) = interp.parent() else {
            continue;
        };
        if !parent.is_absolute() || is_under_standard_loader_prefix(parent) {
            continue;
        }
        let Ok(canon_parent) = fs::canonicalize(parent) else {
            continue;
        };
        if canon_parent != parent && pt_interp_lib_dirs.contains(&canon_parent) {
            validate_pt_interp_dir(
                parent,
                stage_root,
                "PT_INTERP logical loader library directory",
            )?;
            let child = parent.to_path_buf();
            let key = (canon_parent.clone(), child.clone());
            if seen.insert(key) {
                mounts.push(MountSpec { host: canon_parent, child });
            }
        }
    }
    Ok(mounts)
}

/// Forbidden broad host roots that may never be mounted as a toolchain prefix
/// or resolved toolchain library directory under `ExecSeal` (`/` is handled by
/// the `normal_component_count < 2` check below).
const FORBIDDEN_BROAD_HOST_MOUNT_DIRS: &[&str] = &[
    "/bin",
    "/boot",
    "/dev",
    "/etc",
    "/home",
    "/mnt",
    "/media",
    "/opt",
    "/proc",
    "/root",
    "/run",
    "/sbin",
    "/srv",
    "/sys",
    "/tmp",
    "/usr",
    "/usr/bin",
    "/usr/local",
    "/usr/local/bin",
    "/usr/share",
    "/Users",
    "/var",
    "/var/tmp",
];

/// Validate that a canonicalized toolchain prefix or resolved toolchain library
/// directory is strictly dedicated and does not encompass broad host trees,
/// `$HOME`, `cwd`, or `stage_root`.
pub fn validate_toolchain_mount_dir(
    canon_dir: &Path,
    stage_root: Option<&Path>,
    role: &str,
) -> Result<(), Failure> {
    use std::path::Component;
    if !canon_dir.is_absolute() {
        return Err(Failure::operational(
            "sandbox",
            format!("refusing non-absolute {role} {} for sandbox mount", canon_dir.display()),
        ));
    }
    let normal_count = canon_dir.components().filter(|c| matches!(c, Component::Normal(_))).count();
    if normal_count < 2
        || FORBIDDEN_BROAD_HOST_MOUNT_DIRS.iter().any(|bad| canon_dir == Path::new(bad))
    {
        return Err(Failure::operational(
            "sandbox",
            format!("refusing broad host path {} as {role} for sandbox mount", canon_dir.display()),
        ));
    }
    if let Some(stage) = stage_root {
        let canon_stage = fs::canonicalize(stage).unwrap_or_else(|_| stage.to_path_buf());
        if canon_stage.starts_with(canon_dir) || canon_dir.starts_with(&canon_stage) {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing {role} {} overlapping staging directory {}",
                    canon_dir.display(),
                    canon_stage.display()
                ),
            ));
        }
    }
    if let Some(home_os) = std::env::var_os("HOME")
        && !home_os.is_empty()
    {
        let home_raw = PathBuf::from(home_os);
        let canon_home = fs::canonicalize(&home_raw).unwrap_or(home_raw);
        // Note: `canon_home.starts_with(canon_dir)` is true when `canon_dir` is
        // `$HOME` itself or an ancestor such as `/home`, while remaining false
        // for dedicated subdirectories like `$HOME/.elan/toolchains/...`.
        if canon_home.starts_with(canon_dir) {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing {role} {} encompassing HOME directory {}",
                    canon_dir.display(),
                    canon_home.display()
                ),
            ));
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        let canon_cwd = fs::canonicalize(&cwd).unwrap_or(cwd);
        if canon_cwd.starts_with(canon_dir) {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing {role} {} encompassing working directory {}",
                    canon_dir.display(),
                    canon_cwd.display()
                ),
            ));
        }
    }
    Ok(())
}

/// Permitted file suffixes inside a dedicated `<prefix>/lib/lean` tree.
const LEAN_STDLIB_FILE_SUFFIXES: &[&str] = &[
    ".olean",
    ".olean.server",
    ".olean.private",
    ".ilean",
    ".ir",
    ".ir.sig",
    ".trace",
    ".hash",
    ".lean",
    ".c",
    ".h",
    ".a",
    ".so",
    ".dylib",
    ".dll",
    ".cmake",
    ".pc",
];

fn is_lean_stdlib_file_name(name: &str) -> bool {
    LEAN_STDLIB_FILE_SUFFIXES.iter().any(|ext| name.ends_with(ext)) || name.contains(".so.")
}

fn is_lean_module_dir_name(name: &str, top_level: bool) -> bool {
    if matches!(name, "cmake" | "pkgconfig") {
        return true;
    }
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    let valid_first = if top_level {
        first.is_ascii_uppercase()
    } else {
        first.is_ascii_alphabetic() || first == '_'
    };
    valid_first && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn is_toolchain_lib_file_name(name: &str) -> bool {
    name == "libc++.modules.json"
        || (name.starts_with("lib")
            && (name.ends_with(".a")
                || name.ends_with(".so")
                || name.ends_with(".dylib")
                || name.ends_with(".la")
                || name.contains(".so.")))
        || (name.ends_with(".o") && name.contains("crt"))
}

fn symlink_stays_within_dedicated_root(
    canon_root: &Path,
    entry_path: &Path,
) -> Result<bool, Failure> {
    let canon_target = fs::canonicalize(entry_path).map_err(|e| {
        Failure::operational(
            "sandbox",
            format!("cannot canonicalize toolchain symlink {}: {e}", entry_path.display()),
        )
    })?;
    Ok(canon_target.starts_with(canon_root)
        || (canon_root.starts_with("/nix/store") && canon_target.starts_with("/nix/store")))
}

fn walk_dedicated_lean_stdlib_tree(
    canon_lib_lean: &Path,
    dir: &Path,
    top_level: bool,
) -> Result<(), Failure> {
    let entries = fs::read_dir(dir).map_err(|e| {
        Failure::operational(
            "sandbox",
            format!("cannot read toolchain directory {}: {e}", dir.display()),
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|e| {
            Failure::operational(
                "sandbox",
                format!("cannot read toolchain directory {}: {e}", dir.display()),
            )
        })?;
        let raw_name = entry.file_name();
        let Some(name) = raw_name.to_str() else {
            return Err(Failure::operational(
                "sandbox",
                format!("refusing non-UTF-8 entry in toolchain lib/lean {}", dir.display()),
            ));
        };
        if name.is_empty() || name.starts_with('.') {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing hidden entry {name} in non-dedicated toolchain lib/lean {}",
                    canon_lib_lean.display()
                ),
            ));
        }
        let path = entry.path();
        let ft = entry.file_type().map_err(|e| {
            Failure::operational("sandbox", format!("cannot inspect {}: {e}", path.display()))
        })?;
        if ft.is_symlink() && !symlink_stays_within_dedicated_root(canon_lib_lean, &path)? {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing escaping symlink {} inside toolchain lib/lean {}",
                    path.display(),
                    canon_lib_lean.display()
                ),
            ));
        }
        let meta = fs::metadata(&path).map_err(|e| {
            Failure::operational("sandbox", format!("cannot stat {}: {e}", path.display()))
        })?;
        if meta.is_dir() {
            if !is_lean_module_dir_name(name, top_level) {
                return Err(Failure::operational(
                    "sandbox",
                    format!(
                        "refusing non-dedicated toolchain lib/lean {} containing unexpected \
                         directory {name}",
                        canon_lib_lean.display()
                    ),
                ));
            }
            if !ft.is_symlink() {
                walk_dedicated_lean_stdlib_tree(canon_lib_lean, &path, false)?;
            }
        } else if meta.is_file() {
            if !is_lean_stdlib_file_name(name) {
                return Err(Failure::operational(
                    "sandbox",
                    format!(
                        "refusing non-dedicated toolchain lib/lean {} containing unexpected \
                         file {name}",
                        canon_lib_lean.display()
                    ),
                ));
            }
        } else {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing special file {} inside toolchain lib/lean {}",
                    path.display(),
                    canon_lib_lean.display()
                ),
            ));
        }
    }
    Ok(())
}

fn walk_no_escaping_symlinks_or_specials(canon_lib: &Path, dir: &Path) -> Result<(), Failure> {
    let entries = fs::read_dir(dir).map_err(|e| {
        Failure::operational(
            "sandbox",
            format!("cannot read toolchain subdir {}: {e}", dir.display()),
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|e| {
            Failure::operational(
                "sandbox",
                format!("cannot read toolchain subdir {}: {e}", dir.display()),
            )
        })?;
        let path = entry.path();
        let ft = entry.file_type().map_err(|e| {
            Failure::operational("sandbox", format!("cannot inspect {}: {e}", path.display()))
        })?;
        if ft.is_symlink() && !symlink_stays_within_dedicated_root(canon_lib, &path)? {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing escaping symlink {} inside toolchain lib {}",
                    path.display(),
                    canon_lib.display()
                ),
            ));
        }
        let meta = fs::metadata(&path).map_err(|e| {
            Failure::operational("sandbox", format!("cannot stat {}: {e}", path.display()))
        })?;
        if meta.is_dir() {
            if !ft.is_symlink() {
                walk_no_escaping_symlinks_or_specials(canon_lib, &path)?;
            }
        } else if !meta.is_file() {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing special file {} inside toolchain lib {}",
                    path.display(),
                    canon_lib.display()
                ),
            ));
        }
    }
    Ok(())
}

/// Structurally validate that `canon_lib_lean` is a dedicated Lean `lib/lean`
/// standard-library tree (`Init.olean` + `Init/` + exclusively Lean/C module
/// artifacts without escaping symlinks or unrelated host files).
pub fn validate_dedicated_lean_stdlib_dir(
    canon_lib_lean: &Path,
    stage_root: Option<&Path>,
) -> Result<(), Failure> {
    validate_toolchain_mount_dir(canon_lib_lean, stage_root, "toolchain lib/lean directory")?;
    if !fs::metadata(canon_lib_lean.join("Init.olean")).is_ok_and(|m| m.is_file())
        || !fs::metadata(canon_lib_lean.join("Init")).is_ok_and(|m| m.is_dir())
    {
        return Err(Failure::operational(
            "sandbox",
            format!(
                "refusing non-dedicated toolchain lib/lean directory {} (missing Init.olean or \
                 Init/)",
                canon_lib_lean.display()
            ),
        ));
    }
    walk_dedicated_lean_stdlib_tree(canon_lib_lean, canon_lib_lean, true)
}

/// Structurally validate that `canon_lib` is a dedicated Lean toolchain `lib/`
/// directory (`lean/` resolving to a valid Lean stdlib tree plus exclusively
/// Lean/C/C++ runtime libraries and CRT objects, rejecting shared host trees
/// such as `/var/lib`, `/usr/lib`, or `/home/shared`).
pub fn validate_dedicated_toolchain_lib_dir(
    canon_lib: &Path,
    stage_root: Option<&Path>,
) -> Result<(), Failure> {
    validate_toolchain_mount_dir(canon_lib, stage_root, "toolchain lib directory")?;
    let lean_sub = canon_lib.join("lean");
    let canon_lib_lean = fs::canonicalize(&lean_sub).map_err(|e| {
        Failure::operational(
            "sandbox",
            format!(
                "refusing non-dedicated toolchain lib directory {} (missing valid lean/ \
                 subdirectory: {e})",
                canon_lib.display()
            ),
        )
    })?;
    validate_dedicated_lean_stdlib_dir(&canon_lib_lean, stage_root)?;

    let entries = fs::read_dir(canon_lib).map_err(|e| {
        Failure::operational(
            "sandbox",
            format!("cannot read toolchain lib directory {}: {e}", canon_lib.display()),
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|e| {
            Failure::operational(
                "sandbox",
                format!("cannot read toolchain lib directory {}: {e}", canon_lib.display()),
            )
        })?;
        let raw_name = entry.file_name();
        let Some(name) = raw_name.to_str() else {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing non-UTF-8 entry in toolchain lib directory {}",
                    canon_lib.display()
                ),
            ));
        };
        if name.is_empty() || name.starts_with('.') {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing hidden entry {name} in non-dedicated toolchain lib directory {}",
                    canon_lib.display()
                ),
            ));
        }
        let path = entry.path();
        let ft = entry.file_type().map_err(|e| {
            Failure::operational("sandbox", format!("cannot inspect {}: {e}", path.display()))
        })?;
        if name == "lean" {
            continue;
        }
        if ft.is_symlink() && !symlink_stays_within_dedicated_root(canon_lib, &path)? {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing escaping symlink {} in toolchain lib directory {}",
                    path.display(),
                    canon_lib.display()
                ),
            ));
        }
        let meta = fs::metadata(&path).map_err(|e| {
            Failure::operational("sandbox", format!("cannot stat {}: {e}", path.display()))
        })?;
        if meta.is_dir() {
            if !matches!(name, "clang" | "glibc" | "cmake" | "pkgconfig") {
                return Err(Failure::operational(
                    "sandbox",
                    format!(
                        "refusing non-dedicated toolchain lib directory {} containing unexpected \
                         subdirectory {name}",
                        canon_lib.display()
                    ),
                ));
            }
            if !ft.is_symlink() {
                walk_no_escaping_symlinks_or_specials(canon_lib, &path)?;
            }
        } else if meta.is_file() {
            if !is_toolchain_lib_file_name(name) {
                return Err(Failure::operational(
                    "sandbox",
                    format!(
                        "refusing non-dedicated toolchain lib directory {} containing unexpected \
                         file {name}",
                        canon_lib.display()
                    ),
                ));
            }
        } else {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "refusing special file {} in toolchain lib directory {}",
                    path.display(),
                    canon_lib.display()
                ),
            ));
        }
    }
    Ok(())
}

/// Cached probed sandbox runtime state for a [`Checker`](crate::Checker) run.
#[derive(Debug, Clone)]
pub struct SandboxRuntime {
    pub backend: ActiveSandbox,
    pub bwrap_path: Option<PathBuf>,
    /// Whether Tier 1 `bwrap` enforces the seccomp-BPF syscall allowlist via
    /// `--seccomp` (always `true` on `x86_64`/`aarch64` Linux).
    pub bwrap_seccomp_active: bool,
    /// Whether Tier 1 `bwrap` disables nested user namespaces via
    /// `--unshare-user --disable-userns` (probed against the host `bwrap`).
    pub bwrap_disable_userns: bool,
    pub exec_lean: PathBuf,
    pub toolchain_dir: PathBuf,
    pub toolchain_ro_mounts: Vec<MountSpec>,
    pub extra_toolchain_mounts: Vec<MountSpec>,
    pub pt_interp_paths: Vec<PathBuf>,
    /// Validated custom read-only parent directories of `PT_INTERP` outside
    /// standard system library roots and `/nix/store`.
    pub pt_interp_lib_dirs: Vec<PathBuf>,
    pub needs_nix_store: bool,
    pub landlock_abi: i32,
}

impl SandboxRuntime {
    /// Discover the narrow read-only toolchain library mounts (`<prefix>/lib`
    /// -> `/toolchain/lib` and any external symlink targets of `lib` or
    /// `lib/lean`), structurally validating every mounted host directory via
    /// [`validate_dedicated_toolchain_lib_dir`] and
    /// [`validate_dedicated_lean_stdlib_dir`] so neither sibling files under
    /// `toolchain_dir` nor shared host directories are exposed.
    #[cfg(target_os = "linux")]
    fn discover_toolchain_mounts(
        toolchain_dir: &Path,
        stage_root: Option<&Path>,
    ) -> Result<(Vec<MountSpec>, Vec<MountSpec>), Failure> {
        validate_toolchain_mount_dir(toolchain_dir, stage_root, "toolchain prefix")?;
        let mut primary = Vec::new();
        let mut extra = Vec::new();
        let mut seen_extra = BTreeSet::new();

        let lib_candidate = toolchain_dir.join("lib");
        if lib_candidate.symlink_metadata().is_ok() {
            let canon_lib = fs::canonicalize(&lib_candidate).map_err(|e| {
                Failure::operational(
                    "sandbox",
                    format!("cannot canonicalize toolchain lib {}: {e}", lib_candidate.display()),
                )
            })?;
            validate_dedicated_toolchain_lib_dir(&canon_lib, stage_root)?;
            primary.push(MountSpec {
                host: canon_lib.clone(),
                child: PathBuf::from("/toolchain/lib"),
            });
            if !canon_lib.starts_with(toolchain_dir) && seen_extra.insert(canon_lib.clone()) {
                extra.push(MountSpec { host: canon_lib.clone(), child: canon_lib });
            }
        }

        let lib_lean_candidate = toolchain_dir.join("lib/lean");
        if lib_lean_candidate.symlink_metadata().is_ok() {
            let canon_lib_lean = fs::canonicalize(&lib_lean_candidate).map_err(|e| {
                Failure::operational(
                    "sandbox",
                    format!(
                        "cannot canonicalize toolchain lib/lean {}: {e}",
                        lib_lean_candidate.display()
                    ),
                )
            })?;
            validate_dedicated_lean_stdlib_dir(&canon_lib_lean, stage_root)?;
            if primary.is_empty() {
                primary.push(MountSpec {
                    host: canon_lib_lean.clone(),
                    child: PathBuf::from("/toolchain/lib/lean"),
                });
            }
            if !canon_lib_lean.starts_with(toolchain_dir)
                && !primary.iter().any(|m| canon_lib_lean.starts_with(&m.host))
                && seen_extra.insert(canon_lib_lean.clone())
            {
                extra.push(MountSpec { host: canon_lib_lean.clone(), child: canon_lib_lean });
            }
        }

        Ok((primary, extra))
    }

    /// Child-visible path to the Lean executable.
    ///
    /// Binding `exec_lean` inside `/toolchain` (at `/toolchain/<rel>` when
    /// under `toolchain_dir`, or `/toolchain/bin/lean` otherwise) ensures both
    /// ELF `DT_RUNPATH` (`$ORIGIN/../lib:$ORIGIN/../lib/lean`) and Lean's
    /// `findSysroot` (`dirname(dirname(/proc/self/exe))` -> `/toolchain`)
    /// resolve to `/toolchain/lib{,/lean}` without mounting sibling files in
    /// `toolchain_dir` or `exec_lean`'s parent directory.
    pub fn child_exec_path(&self) -> PathBuf {
        if self.backend != ActiveSandbox::LinuxBwrap {
            return self.exec_lean.clone();
        }
        if let Ok(rel) = self.exec_lean.strip_prefix(&self.toolchain_dir) {
            PathBuf::from("/toolchain").join(rel)
        } else {
            PathBuf::from("/toolchain/bin/lean")
        }
    }

    /// Single-file RO bind for `exec_lean` in Tier 1 `bwrap` unless an
    /// existing `toolchain_ro_mounts` entry already maps `exec_lean` to the
    /// exact same child path (`self.child_exec_path()`).
    #[cfg(target_os = "linux")]
    fn extra_exec_bind(&self) -> Option<MountSpec> {
        if self.backend != ActiveSandbox::LinuxBwrap {
            return None;
        }
        let child = self.child_exec_path();
        if self.toolchain_ro_mounts.iter().any(|m| {
            self.exec_lean.strip_prefix(&m.host).is_ok_and(|rel| m.child.join(rel) == child)
        }) {
            None
        } else {
            Some(MountSpec { host: self.exec_lean.clone(), child })
        }
    }

    /// Probe and initialize the containment runtime according to `mode`.
    ///
    /// Runs a real functional compile probe of a trivial Lean module with
    /// `--root` inside the selected backend so silent namespace/Landlock/
    /// seccomp failures surface deterministically before any target code runs.
    pub fn probe(
        mode: SandboxMode,
        exec_lean: &Path,
        toolchain_dir: &Path,
        stage_root: &Path,
    ) -> Result<Self, Failure> {
        let exec_lean = fs::canonicalize(exec_lean).map_err(|e| {
            Failure::operational(
                "sandbox",
                format!("cannot canonicalize Lean binary {}: {e}", exec_lean.display()),
            )
        })?;
        let toolchain_dir = fs::canonicalize(toolchain_dir).map_err(|e| {
            Failure::operational(
                "sandbox",
                format!("cannot canonicalize toolchain prefix {}: {e}", toolchain_dir.display()),
            )
        })?;
        if mode == SandboxMode::Unsandboxed {
            return Ok(Self {
                backend: ActiveSandbox::None,
                bwrap_path: None,
                bwrap_seccomp_active: false,
                bwrap_disable_userns: false,
                exec_lean,
                toolchain_dir,
                toolchain_ro_mounts: Vec::new(),
                extra_toolchain_mounts: Vec::new(),
                pt_interp_paths: Vec::new(),
                pt_interp_lib_dirs: Vec::new(),
                needs_nix_store: false,
                landlock_abi: 0,
            });
        }

        #[cfg(not(target_os = "linux"))]
        {
            let _ = stage_root;
            return Err(Failure::operational(
                "sandbox",
                "OS elaborator containment requires Linux (bwrap or Landlock ABI >= 3 + \
                 seccomp); pass --allow-unsandboxed-elaboration to run unsandboxed on \
                 non-Linux hosts",
            ));
        }

        #[cfg(target_os = "linux")]
        {
            Self::probe_linux(mode, exec_lean, toolchain_dir, stage_root)
        }
    }

    /// Execute a single invocation under this runtime's confinement policy.
    pub fn execute(&self, policy: &SandboxPolicy) -> Result<Output, Failure> {
        self.execute_with_options(policy, None, RLIMIT_FSIZE_BYTES)
    }

    /// Execute a single invocation under this runtime's confinement policy with
    /// an explicit per-child `RLIMIT_FSIZE` cap in bytes.
    pub(crate) fn execute_with_rlimit_fsize(
        &self,
        policy: &SandboxPolicy,
        rlimit_fsize_bytes: u64,
    ) -> Result<Output, Failure> {
        self.execute_with_options(policy, None, rlimit_fsize_bytes)
    }

    /// Execute a single invocation under this runtime's confinement policy,
    /// streaming child stdout directly to a host-owned file bounded by
    /// `max_stdout_bytes`.
    ///
    /// Used by Actions `5a`/`5b` (`leanexport`) so large NDJSON exports never
    /// truncate at [`MAX_CHILD_STREAM_BYTES`] while keeping the child's
    /// writable output mount completely empty.
    pub fn execute_stdout_to_file(
        &self,
        policy: &SandboxPolicy,
        stdout_path: &Path,
        max_stdout_bytes: u64,
    ) -> Result<Output, Failure> {
        self.execute_with_options(
            policy,
            Some((stdout_path.to_path_buf(), max_stdout_bytes)),
            RLIMIT_FSIZE_BYTES,
        )
    }

    fn execute_with_options(
        &self,
        policy: &SandboxPolicy,
        stdout_file: Option<(PathBuf, u64)>,
        rlimit_fsize_bytes: u64,
    ) -> Result<Output, Failure> {
        match self.backend {
            ActiveSandbox::None => run_unsandboxed(policy, stdout_file, rlimit_fsize_bytes),
            #[cfg(target_os = "linux")]
            ActiveSandbox::LinuxBwrap => {
                linux::run_bwrap(self, policy, stdout_file, rlimit_fsize_bytes)
            }
            #[cfg(target_os = "linux")]
            ActiveSandbox::LinuxLandlockSeccomp => {
                linux::run_landlock_seccomp(self, policy, stdout_file, rlimit_fsize_bytes)
            }
            #[cfg(not(target_os = "linux"))]
            ActiveSandbox::LinuxBwrap | ActiveSandbox::LinuxLandlockSeccomp => Err(
                Failure::operational("sandbox", "Linux sandbox backend unavailable on this host"),
            ),
        }
    }

    #[cfg(target_os = "linux")]
    fn probe_linux(
        mode: SandboxMode,
        exec_lean: PathBuf,
        toolchain_dir: PathBuf,
        stage_root: &Path,
    ) -> Result<Self, Failure> {
        let pt_interp_paths = resolve_pt_interp_paths(&exec_lean).unwrap_or_default();
        let pt_interp_lib_dirs = resolve_pt_interp_lib_dirs(&pt_interp_paths, Some(stage_root))?;
        let needs_nix_store = exec_lean.starts_with("/nix/store")
            || pt_interp_paths.iter().any(|p| p.starts_with("/nix/store"));
        let (toolchain_ro_mounts, extra_toolchain_mounts) =
            Self::discover_toolchain_mounts(&toolchain_dir, Some(stage_root))?;

        let bwrap_err = match find_bwrap_binary() {
            Some(bwrap_path) => {
                // Prefer `--unshare-user --disable-userns` to block nested
                // user namespaces inside Tier 1, falling back to `false` only
                // if the host `bwrap`/kernel does not support `--disable-userns`
                // while still keeping `--seccomp` enforced on x86_64/aarch64.
                let seccomp_supported = cfg!(any(target_arch = "x86_64", target_arch = "aarch64"));
                let mut last_err = String::new();
                for disable_userns in [true, false] {
                    let candidate = Self {
                        backend: ActiveSandbox::LinuxBwrap,
                        bwrap_path: Some(bwrap_path.clone()),
                        bwrap_seccomp_active: seccomp_supported,
                        bwrap_disable_userns: disable_userns,
                        exec_lean: exec_lean.clone(),
                        toolchain_dir: toolchain_dir.clone(),
                        toolchain_ro_mounts: toolchain_ro_mounts.clone(),
                        extra_toolchain_mounts: extra_toolchain_mounts.clone(),
                        pt_interp_paths: pt_interp_paths.clone(),
                        pt_interp_lib_dirs: pt_interp_lib_dirs.clone(),
                        needs_nix_store,
                        landlock_abi: 0,
                    };
                    match run_functional_lean_probe(&candidate, stage_root) {
                        Ok(()) => return Ok(candidate),
                        Err(err) => {
                            last_err = format!(
                                "linux_bwrap probe failed (disable_userns={disable_userns}): {}",
                                err.message
                            );
                        }
                    }
                }
                last_err
            }
            None => {
                "linux_bwrap unavailable: neither /usr/bin/bwrap nor /bin/bwrap exists".to_string()
            }
        };

        if mode == SandboxMode::RequireBwrap {
            return Err(Failure::operational(
                "sandbox",
                format!("RequireBwrap containment failed: {bwrap_err}"),
            ));
        }

        let landlock_err = match linux::check_tier2_preconditions(&exec_lean) {
            Ok((abi, interps)) => {
                let nix = exec_lean.starts_with("/nix/store")
                    || interps.iter().any(|p| p.starts_with("/nix/store"));
                let interp_lib_dirs =
                    match resolve_pt_interp_lib_dirs(&interps, Some(stage_root)) {
                        Ok(dirs) => dirs,
                        Err(err) => {
                            return Err(Failure::operational(
                                "sandbox",
                                format!(
                                    "elaborator containment unavailable; pass \
                                     --allow-unsandboxed-elaboration to opt out (tainted). \
                                     Tier 1: {bwrap_err}; Tier 2: {}",
                                    err.message
                                ),
                            ));
                        }
                    };
                let candidate = Self {
                    backend: ActiveSandbox::LinuxLandlockSeccomp,
                    bwrap_path: None,
                    bwrap_seccomp_active: false,
                    bwrap_disable_userns: false,
                    exec_lean,
                    toolchain_dir,
                    toolchain_ro_mounts,
                    extra_toolchain_mounts,
                    pt_interp_paths: interps,
                    pt_interp_lib_dirs: interp_lib_dirs,
                    needs_nix_store: nix,
                    landlock_abi: abi,
                };
                match run_functional_lean_probe(&candidate, stage_root) {
                    Ok(()) => return Ok(candidate),
                    Err(err) => format!("linux_landlock_seccomp probe failed: {}", err.message),
                }
            }
            Err(err) => format!("linux_landlock_seccomp unavailable: {err}"),
        };

        Err(Failure::operational(
            "sandbox",
            format!(
                "elaborator containment unavailable; pass --allow-unsandboxed-elaboration \
                 to opt out (tainted). Tier 1: {bwrap_err}; Tier 2: {landlock_err}"
            ),
        ))
    }
}

/// Functional startup probe compiling a trivial Lean module with `--root` to
/// verify the selected sandbox backend end-to-end before target execution.
#[cfg(target_os = "linux")]
fn run_functional_lean_probe(runtime: &SandboxRuntime, stage_root: &Path) -> Result<(), Failure> {
    let probe_dir =
        stage_root.join(format!("sandbox-probe-{}", runtime.backend.as_str().replace('_', "-")));
    let in_dir = probe_dir.join("in");
    let out_dir = probe_dir.join("out");
    let tmp_dir = probe_dir.join("tmp");
    let _ = fs::remove_dir_all(&probe_dir);
    create_dir_mode(&probe_dir, 0o700)?;
    create_dir_mode(&in_dir, 0o700)?;
    create_dir_mode(&out_dir, 0o700)?;
    create_dir_mode(&tmp_dir, 0o700)?;

    let src_host = in_dir.join("Probe.lean");
    fs::write(&src_host, b"prelude\ninductive AnnealProbeOk where\n  | ok\n")
        .map_err(|e| Failure::operational("sandbox-probe", e.to_string()))?;
    set_mode(&src_host, 0o444)?;
    set_mode(&in_dir, 0o500)?;

    let ro_mounts = vec![MountSpec { host: in_dir.clone(), child: PathBuf::from("/work/in") }];
    let rw_out = MountSpec { host: out_dir.clone(), child: PathBuf::from("/work/out") };
    let rw_tmp = MountSpec { host: tmp_dir.clone(), child: PathBuf::from("/work/tmp") };
    let mapper = PathMapper::new(runtime, &ro_mounts, &rw_out, &rw_tmp);
    let out_olean = out_dir.join("Probe.olean");
    let policy = SandboxPolicy {
        exec_bin: runtime.exec_lean.clone(),
        args: vec![
            "-j1".to_string(),
            "-M512".to_string(),
            "-t0".to_string(),
            "-R".to_string(),
            mapper.map_str(&in_dir)?,
            "-o".to_string(),
            mapper.map_str(&out_olean)?,
            mapper.map_str(&src_host)?,
        ],
        ro_mounts,
        rw_out,
        rw_tmp,
        child_cwd: None,
        extra_env: BTreeMap::new(),
        timeout: Duration::from_secs(60),
    };
    let exec_res = runtime.execute(&policy);
    let check_res = exec_res.and_then(|output| {
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            return Err(Failure::operational(
                "sandbox-probe",
                format!(
                    "probe exited {:?}: stdout={} stderr={}",
                    output.status.code(),
                    stdout.trim(),
                    stderr.trim()
                ),
            ));
        }
        let promoted = probe_dir.join("promoted.olean");
        validate_and_promote_olean(&out_dir, "Probe.olean", &promoted)?;
        Ok(())
    });
    let _ = set_mode(&in_dir, 0o700);
    let _ = fs::remove_dir_all(&probe_dir);
    check_res
}

/// Locate bubblewrap strictly at canonical system paths (`/usr/bin/bwrap` or
/// `/bin/bwrap`), never via ambient `PATH`.
#[cfg(target_os = "linux")]
pub fn find_bwrap_binary() -> Option<PathBuf> {
    for candidate in ["/usr/bin/bwrap", "/bin/bwrap"] {
        let path = Path::new(candidate);
        if let Ok(meta) = fs::metadata(path)
            && meta.is_file()
            && (meta.permissions().mode() & 0o111) != 0
        {
            return Some(path.to_path_buf());
        }
    }
    None
}

/// Create a directory (and parents if needed) with an explicit Unix mode.
pub fn create_dir_mode(path: &Path, mode: u32) -> Result<(), Failure> {
    SafeFs::create_dir_mode(path, mode, "stage")
}

/// Restore owner write/execute permissions recursively across `root` (without
/// following symlinks) so read-only `0o500`/`0o444` staging subtrees can be
/// deleted cleanly during `reset_stage()` and `Drop`.
pub fn make_tree_writable(root: &Path) {
    SafeFs::make_tree_writable(root);
}

/// Set Unix file or directory mode bits; no-op on non-Unix targets.
pub fn set_mode(path: &Path, mode: u32) -> Result<(), Failure> {
    SafeFs::set_mode(path, mode, "stage")
}

/// Physically copy a regular file (never hardlinking) and mark the copy
/// read-only (`0o444`).
pub fn copy_readonly_file(src: &Path, dest: &Path, phase: &str) -> Result<(), Failure> {
    SafeFs::copy_readonly_file(src, dest, phase)
}

/// Door 1 validator for target module compilation (`"isModule": false`):
/// scans `out_dir` non-recursively, requires an exact singleton regular file
/// named `expected_filename` with `st_nlink == 1`, zero subdirectories, zero
/// symlinks, a valid `v2` `.olean` header (`b"olean\x02"`), and size
/// `<= MAX_OLEAN_BYTES`, marks it `0o444`, atomically renames it to
/// `dest_path`, and returns its SHA-256 hex digest.
pub fn validate_and_promote_olean(
    out_dir: &Path,
    expected_filename: &str,
    dest_path: &Path,
) -> Result<String, Failure> {
    let entries = collect_out_entries(out_dir, "door1")?;
    if entries.len() != 1 || entries[0].0 != expected_filename {
        let names: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();
        return Err(Failure::operational(
            "door1",
            format!(
                "unexpected compiler outputs in {}: expected [{expected_filename}], found {names:?}",
                out_dir.display()
            ),
        ));
    }
    let src = &entries[0].1;
    let mut file = open_validated_out_file(src, MAX_OLEAN_BYTES, "door1")?;
    let sha = validate_olean_v2_and_sha256(&mut file, MAX_OLEAN_BYTES, src, "door1")?;
    set_file_mode_readonly(&file, src, "door1")?;
    drop(file);
    if let Some(parent) = dest_path.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            Failure::operational("door1", format!("cannot create {}: {e}", parent.display()))
        })?;
    }
    fs::rename(src, dest_path).map_err(|e| {
        Failure::operational(
            "door1",
            format!("cannot promote {} to {}: {e}", src.display(), dest_path.display()),
        )
    })?;
    Ok(sha)
}

/// Door 1 validator for Lean `module` compilation where a module may emit
/// declared `.olean.server` / `.olean.private` sidecars (promoted) and
/// `.ir` / `.ir.sig` outputs (validated and discarded) alongside
/// `<stem>.olean`. Rejects any undeclared file, subdirectory, symlink,
/// hardlink, or oversized file before hashing, marking `0o444`, and atomically
/// renaming each promoted file into `dest_dir`.
///
/// Returns a map from promoted destination paths to their lowercase hex SHA-256
/// digests so callers can register every promoted `.olean*` file in the
/// artifact ledger.
pub fn validate_and_promote_olean_set_with_digests(
    out_dir: &Path,
    allowed_promote: &BTreeSet<String>,
    allowed_discard: &BTreeSet<String>,
    required_filename: &str,
    dest_dir: &Path,
) -> Result<BTreeMap<PathBuf, String>, Failure> {
    let entries = collect_out_entries(out_dir, "door1")?;
    let mut saw_required = false;
    let mut opened: Vec<(String, PathBuf, fs::File, Option<String>)> =
        Vec::with_capacity(entries.len());
    for (name, path) in entries {
        if !allowed_promote.contains(&name) && !allowed_discard.contains(&name) {
            return Err(Failure::operational(
                "door1",
                format!(
                    "unexpected compiler output {name} in {} (allowed promote: {allowed_promote:?}, discard: {allowed_discard:?})",
                    out_dir.display()
                ),
            ));
        }
        let mut file = open_validated_out_file(&path, MAX_OLEAN_BYTES, "door1")?;
        let sha = if allowed_promote.contains(&name) {
            Some(validate_olean_v2_and_sha256(
                &mut file,
                MAX_OLEAN_BYTES,
                &path,
                "door1",
            )?)
        } else {
            None
        };
        if name == required_filename {
            saw_required = true;
        }
        opened.push((name, path, file, sha));
    }
    if !saw_required {
        return Err(Failure::operational(
            "door1",
            format!(
                "compiler omitted required output {required_filename} in {}",
                out_dir.display()
            ),
        ));
    }
    fs::create_dir_all(dest_dir).map_err(|e| {
        Failure::operational("door1", format!("cannot create {}: {e}", dest_dir.display()))
    })?;
    let mut promoted = BTreeMap::new();
    for (name, path, file, sha) in opened {
        if let Some(sha) = sha {
            set_file_mode_readonly(&file, &path, "door1")?;
            drop(file);
            let dest = dest_dir.join(&name);
            fs::rename(&path, &dest).map_err(|e| {
                Failure::operational(
                    "door1",
                    format!("cannot promote {} to {}: {e}", path.display(), dest.display()),
                )
            })?;
            promoted.insert(dest, sha);
        } else {
            drop(file);
            let _ = fs::remove_file(&path);
        }
    }
    Ok(promoted)
}

/// Door 1 validator for Pass 2 module compilation where Lean `module` files
/// may emit declared `.olean.server` / `.olean.private` sidecars (promoted)
/// and `.ir` / `.ir.sig` outputs (validated and discarded) alongside
/// `<stem>.olean`. Rejects any undeclared file, subdirectory, symlink,
/// hardlink, or oversized file before promoting each promoted file to
/// `dest_dir`.
pub fn validate_and_promote_olean_set(
    out_dir: &Path,
    allowed_promote: &BTreeSet<String>,
    allowed_discard: &BTreeSet<String>,
    required_filename: &str,
    dest_dir: &Path,
) -> Result<(), Failure> {
    validate_and_promote_olean_set_with_digests(
        out_dir,
        allowed_promote,
        allowed_discard,
        required_filename,
        dest_dir,
    )?;
    Ok(())
}

/// Door 1 validator for `TrustedBoundary.lean` inspector invocations using
/// [`DEFAULT_MAX_INSPECTOR_RESULT_BYTES`] (64 MiB).
///
/// Must be called on **both** exit `0` and exit `1`. Returns `Ok(None)` if
/// `out_dir` is empty (for instance if Lean aborted before writing the result),
/// `Ok(Some(bytes))` if `out_dir` contains strictly `expected_filename` as a
/// regular non-hardlinked file `<= DEFAULT_MAX_INSPECTOR_RESULT_BYTES`, and
/// fails closed on any extra file, subdirectory, symlink, hardlink, or oversize
/// file.
pub fn validate_inspector_result(
    out_dir: &Path,
    expected_filename: &str,
) -> Result<Option<Vec<u8>>, Failure> {
    validate_inspector_result_with_cap(
        out_dir,
        expected_filename,
        DEFAULT_MAX_INSPECTOR_RESULT_BYTES,
    )
}

/// Door 1 validator for `TrustedBoundary.lean` / `SpecPreflight.lean` inspector
/// invocations enforcing an explicit `max_bytes` upper bound
/// (`1..=`[`MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES`]).
pub fn validate_inspector_result_with_cap(
    out_dir: &Path,
    expected_filename: &str,
    max_bytes: u64,
) -> Result<Option<Vec<u8>>, Failure> {
    let max_bytes = validate_max_inspector_result_bytes(max_bytes)
        .map_err(|msg| Failure::operational("door1", msg))?;
    let entries = collect_out_entries(out_dir, "door1")?;
    if entries.is_empty() {
        return Ok(None);
    }
    if entries.len() != 1 || entries[0].0 != expected_filename {
        let names: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();
        return Err(Failure::operational(
            "door1",
            format!(
                "unexpected inspector outputs in {}: expected [{expected_filename}], found {names:?}",
                out_dir.display()
            ),
        ));
    }
    let path = &entries[0].1;
    let mut file = open_validated_out_file(path, max_bytes, "door1")?;
    let mut bytes = Vec::new();
    let mut limited = (&mut file).take(max_bytes.saturating_add(1));
    limited.read_to_end(&mut bytes).map_err(|e| {
        Failure::operational(
            "door1",
            format!("cannot read inspector output {}: {e}", path.display()),
        )
    })?;
    if (bytes.len() as u64) > max_bytes {
        return Err(Failure::operational(
            "door1",
            format!("sandbox output {} exceeds size cap ({max_bytes} bytes)", path.display()),
        ));
    }
    Ok(Some(bytes))
}

fn collect_out_entries(out_dir: &Path, phase: &str) -> Result<Vec<(String, PathBuf)>, Failure> {
    let mut entries = Vec::new();
    let rd = fs::read_dir(out_dir).map_err(|e| {
        Failure::operational(phase, format!("cannot scan {}: {e}", out_dir.display()))
    })?;
    for entry in rd {
        let entry = entry.map_err(|e| Failure::operational(phase, e.to_string()))?;
        let name = entry
            .file_name()
            .into_string()
            .map_err(|_| Failure::operational(phase, "non-UTF-8 filename in sandbox out dir"))?;
        entries.push((name, entry.path()));
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(entries)
}

/// Open a sandbox output file without following symlinks or blocking on FIFOs,
/// then `fstat` the opened descriptor to verify regular-file type, single link
/// count, and size cap (eliminating path-based `lstat` -> `open` TOCTOU).
fn open_validated_out_file(path: &Path, max_bytes: u64, phase: &str) -> Result<fs::File, Failure> {
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    opts.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
    let file = opts.open(path).map_err(|e| {
        Failure::operational(
            phase,
            format!("sandbox output {} rejected on open: {e}", path.display()),
        )
    })?;
    let meta = file.metadata().map_err(|e| {
        Failure::operational(phase, format!("cannot fstat {}: {e}", path.display()))
    })?;
    if !meta.file_type().is_file() {
        return Err(Failure::operational(
            phase,
            format!("sandbox output {} is not a regular file", path.display()),
        ));
    }
    #[cfg(unix)]
    if meta.nlink() != 1 {
        return Err(Failure::operational(
            phase,
            format!(
                "sandbox output {} has hardlink count {} (expected 1)",
                path.display(),
                meta.nlink()
            ),
        ));
    }
    if meta.len() > max_bytes {
        return Err(Failure::operational(
            phase,
            format!(
                "sandbox output {} exceeds size cap ({} > {} bytes)",
                path.display(),
                meta.len(),
                max_bytes
            ),
        ));
    }
    Ok(file)
}

/// Validate the `v2` `.olean` header and compute the SHA-256 digest of the
/// complete file in a single bounded pass over the already-opened descriptor.
fn validate_olean_v2_and_sha256(
    file: &mut fs::File,
    max_bytes: u64,
    path: &Path,
    phase: &str,
) -> Result<String, Failure> {
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 64 * 1024];
    let mut total = 0u64;
    let mut prefix = [0u8; 6];
    let mut prefix_len = 0usize;
    loop {
        let n = file.read(&mut buf).map_err(|e| {
            Failure::operational(phase, format!("cannot read {}: {e}", path.display()))
        })?;
        if n == 0 {
            break;
        }
        total = total.saturating_add(n as u64);
        if total > max_bytes {
            return Err(Failure::operational(
                phase,
                format!(
                    "sandbox output {} grew past size cap ({} bytes)",
                    path.display(),
                    max_bytes
                ),
            ));
        }
        if prefix_len < prefix.len() {
            let take = (prefix.len() - prefix_len).min(n);
            prefix[prefix_len..prefix_len + take].copy_from_slice(&buf[..take]);
            prefix_len += take;
        }
        hasher.update(&buf[..n]);
    }
    validate_olean_v2_header(&prefix[..prefix_len], &path.display().to_string(), phase)?;
    let digest = hasher.finalize();
    Ok(digest_to_hex(digest.as_ref()))
}

fn set_file_mode_readonly(file: &fs::File, path: &Path, phase: &str) -> Result<(), Failure> {
    #[cfg(unix)]
    {
        // SAFETY: `file.as_raw_fd()` is a valid open regular-file descriptor.
        if unsafe { libc::fchmod(file.as_raw_fd(), 0o444) } != 0 {
            let err = std::io::Error::last_os_error();
            return Err(Failure::operational(
                phase,
                format!("cannot fchmod 0444 on {}: {err}", path.display()),
            ));
        }
    }
    #[cfg(not(unix))]
    {
        let _ = (file, path, phase);
    }
    Ok(())
}

/// Parse an ELF64 little-endian binary's `PT_INTERP` dynamic linker path with
/// zero external crates. Returns `Ok(None)` for static ELF64 binaries (no
/// `PT_INTERP` program header) and `Err` for non-ELF or malformed binaries.
pub fn parse_elf64_pt_interp(path: &Path) -> Result<Option<PathBuf>, String> {
    SysSanitizer::parse_elf64_pt_interp(path)
}

/// Resolve both the declared `PT_INTERP` path and its canonicalized target (for
/// example `/lib64/ld-linux-x86-64.so.2` and `/usr/lib/.../ld-linux-...`).
pub fn resolve_pt_interp_paths(exec_bin: &Path) -> Result<Vec<PathBuf>, String> {
    SysSanitizer::resolve_pt_interp_paths(exec_bin)
}

#[cfg(target_os = "linux")]
fn child_exited_unreaped(child_pid: u32) -> std::io::Result<bool> {
    loop {
        // SAFETY: `siginfo_t` is plain old data; zero-initializing `si_signo`
        // lets `waitid(..., WNOHANG | WNOWAIT)` distinguish "still running"
        // (`si_signo == 0`) from "exited zombie" (`si_signo != 0`) without
        // reaping `child_pid`, keeping its PID/PGID kernel-pinned.
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        let rc = unsafe {
            libc::waitid(
                libc::P_PID,
                child_pid as libc::id_t,
                &mut info,
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        };
        if rc == 0 {
            return Ok(info.si_signo != 0);
        }
        let err = std::io::Error::last_os_error();
        if err.kind() != std::io::ErrorKind::Interrupted {
            return Err(err);
        }
    }
}

/// Spawn `cmd`, drain stdout and stderr concurrently on dedicated threads so
/// pipe buffers never deadlock, terminate the child process group upon leader
/// exit or timeout before reaping `child`, and enforce the wall-clock deadline
/// across pipe draining so forked descendants inheriting stdout/stderr cannot
/// hang verification.
fn spawn_and_wait_with_timeout(
    mut cmd: Command,
    timeout: Duration,
    label: &str,
    stdout_file: Option<(PathBuf, u64)>,
) -> Result<Output, Failure> {
    cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = cmd
        .spawn()
        .map_err(|e| Failure::operational(label, format!("failed to spawn child: {e}")))?;
    #[cfg(unix)]
    let child_pid = child.id();
    let stdout_pipe = child
        .stdout
        .take()
        .ok_or_else(|| Failure::operational(label, "missing child stdout pipe"))?;
    let stderr_pipe = child
        .stderr
        .take()
        .ok_or_else(|| Failure::operational(label, "missing child stderr pipe"))?;

    // Readers append to shared buffers incrementally rather than handing
    // back a `Vec` at EOF, so a timeout can snapshot whatever has been
    // captured without waiting on pipes an escaped descendant still holds.
    // Each reader reports its drain result once; only a file-backed stdout
    // sink can fail.
    let stdout_buf = Arc::new(Mutex::new(StreamCapture::default()));
    let stderr_buf = Arc::new(Mutex::new(StreamCapture::default()));
    let spawn_reader = |drain: Box<dyn FnOnce() -> Result<(), Failure> + Send>| {
        let (tx, rx) = std::sync::mpsc::sync_channel(1);
        thread::spawn(move || {
            let _ = tx.send(drain());
        });
        rx
    };
    let stdout_rx = {
        let buf = Arc::clone(&stdout_buf);
        let label_owned = label.to_owned();
        spawn_reader(Box::new(move || match stdout_file {
            Some((path, max_bytes)) => {
                drain_to_bounded_file(stdout_pipe, &path, max_bytes, &label_owned)
            }
            None => {
                drain_bounded_into(
                    stdout_pipe,
                    MAX_CHILD_STREAM_BYTES,
                    MAX_CHILD_STREAM_TAIL_BYTES,
                    &buf,
                );
                Ok(())
            }
        }))
    };
    let stderr_rx = {
        let buf = Arc::clone(&stderr_buf);
        spawn_reader(Box::new(move || {
            drain_bounded_into(
                stderr_pipe,
                MAX_CHILD_STREAM_BYTES,
                MAX_CHILD_STREAM_TAIL_BYTES,
                &buf,
            );
            Ok(())
        }))
    };

    let on_timeout = || timeout_failure(timeout, &stdout_buf, &stderr_buf);
    let deadline = Instant::now() + timeout;
    let mut stdout_done: Option<Result<(), Failure>> = None;
    let mut stderr_done: Option<Result<(), Failure>> = None;
    let mut poll_ms = 1u64;
    let status = loop {
        poll_reader(&mut stdout_done, &stdout_rx);
        poll_reader(&mut stderr_done, &stderr_rx);
        #[cfg(target_os = "linux")]
        {
            match child_exited_unreaped(child_pid) {
                Ok(true) => {
                    // SAFETY: `child_pid` was started in its own process group
                    // (`setpgid(0, 0)` / `setsid()`), and `WNOWAIT` has not yet
                    // reaped it, so its PID/PGID cannot be recycled. Killing
                    // the process group before `child.wait()` closes pipes
                    // inherited by forked descendants in the same group.
                    unsafe {
                        let _ = libc::kill(-(child_pid as libc::pid_t), libc::SIGKILL);
                    }
                    break child
                        .wait()
                        .map_err(|e| Failure::operational(label, format!("wait failed: {e}")));
                }
                Ok(false) => {}
                Err(e) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    break Err(Failure::operational(label, format!("wait failed: {e}")));
                }
            }
        }
        #[cfg(not(target_os = "linux"))]
        if stdout_done.is_some() && stderr_done.is_some() {
            match child.try_wait() {
                Ok(Some(status)) => break Ok(status),
                Ok(None) => {}
                Err(e) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    break Err(Failure::operational(label, format!("wait failed: {e}")));
                }
            }
        }
        if Instant::now() >= deadline {
            #[cfg(unix)]
            {
                // SAFETY: `child_pid` was started in its own process group and
                // has not yet been reaped, so its PID/PGID cannot be recycled.
                unsafe {
                    let _ = libc::kill(-(child_pid as libc::pid_t), libc::SIGKILL);
                }
            }
            let _ = child.kill();
            let _ = child.wait();
            // Give the readers a bounded moment to drain bytes still in the
            // pipes, without waiting on pipes an escaped descendant holds.
            let grace_deadline = Instant::now() + TIMEOUT_OUTPUT_GRACE;
            for (done, rx) in [(&stdout_done, &stdout_rx), (&stderr_done, &stderr_rx)] {
                if done.is_none() {
                    let remaining = grace_deadline.saturating_duration_since(Instant::now());
                    let _ = rx.recv_timeout(remaining);
                }
            }
            break Err(on_timeout());
        }
        thread::sleep(Duration::from_millis(poll_ms));
        poll_ms = (poll_ms * 2).min(25);
    };
    let status = status?;
    let wait_until_deadline =
        |done: Option<Result<(), Failure>>, rx: &std::sync::mpsc::Receiver<Result<(), Failure>>| {
            if let Some(res) = done {
                return res;
            }
            let remaining = deadline.saturating_duration_since(Instant::now());
            match rx.recv_timeout(remaining) {
                Ok(res) => res,
                Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => Ok(()),
                Err(std::sync::mpsc::RecvTimeoutError::Timeout) => Err(on_timeout()),
            }
        };
    wait_until_deadline(stdout_done, &stdout_rx)?;
    wait_until_deadline(stderr_done, &stderr_rx)?;
    // A completed run reports only the bounded head, as before; the rolling
    // tail exists for timeout diagnostics.
    let stdout = std::mem::take(&mut lock_capture(&stdout_buf).head);
    let stderr = std::mem::take(&mut lock_capture(&stderr_buf).head);
    Ok(Output { status, stdout, stderr })
}

/// Record a reader's drain result once it arrives; a reader that exited
/// without reporting counts as a clean finish.
fn poll_reader(
    slot: &mut Option<Result<(), Failure>>,
    rx: &std::sync::mpsc::Receiver<Result<(), Failure>>,
) {
    if slot.is_none() {
        match rx.try_recv() {
            Ok(res) => *slot = Some(res),
            Err(std::sync::mpsc::TryRecvError::Disconnected) => *slot = Some(Ok(())),
            Err(std::sync::mpsc::TryRecvError::Empty) => {}
        }
    }
}

fn drain_to_bounded_file(
    mut reader: impl Read,
    path: &Path,
    max_bytes: u64,
    label: &str,
) -> Result<(), Failure> {
    use std::io::Write as _;
    let mut opts = fs::OpenOptions::new();
    opts.write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        opts.mode(0o600).custom_flags(libc::O_NOFOLLOW);
    }
    let mut file = opts.open(path).map_err(|e| {
        Failure::operational(label, format!("cannot create stdout sink {}: {e}", path.display()))
    })?;
    let mut chunk = [0u8; 64 * 1024];
    let mut total = 0u64;
    let mut overflowed = false;
    let mut write_err: Option<std::io::Error> = None;
    loop {
        match reader.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => {
                if !overflowed && write_err.is_none() {
                    let next = total.saturating_add(n as u64);
                    if next > max_bytes {
                        overflowed = true;
                    } else if let Err(e) = file.write_all(&chunk[..n]) {
                        write_err = Some(e);
                    } else {
                        total = next;
                    }
                }
            }
            Err(e) => {
                write_err.get_or_insert(e);
                break;
            }
        }
    }
    if overflowed {
        let _ = fs::remove_file(path);
        return Err(Failure::operational(
            label,
            format!("sandboxed stdout exceeded cap of {max_bytes} bytes"),
        ));
    }
    if let Some(e) = write_err {
        let _ = fs::remove_file(path);
        return Err(Failure::operational(
            label,
            format!("error writing stdout sink {}: {e}", path.display()),
        ));
    }
    file.flush().map_err(|e| {
        Failure::operational(label, format!("cannot flush stdout sink {}: {e}", path.display()))
    })
}

/// Holds one child stream: the first `limit` bytes, then a rolling window of
/// the most recent bytes once `limit` is reached.
#[derive(Default)]
struct StreamCapture {
    head: Vec<u8>,
    tail: std::collections::VecDeque<u8>,
    /// Counts bytes read past `head` that are no longer in `tail`.
    dropped: usize,
}

impl StreamCapture {
    fn push(&mut self, bytes: &[u8], limit: usize, tail_limit: usize) {
        let take = limit.saturating_sub(self.head.len()).min(bytes.len());
        self.head.extend_from_slice(&bytes[..take]);
        let rest = &bytes[take..];
        let keep = &rest[rest.len().saturating_sub(tail_limit)..];
        self.dropped = self.dropped.saturating_add(rest.len() - keep.len());
        let overflow = (self.tail.len() + keep.len()).saturating_sub(tail_limit);
        self.tail.drain(..overflow);
        self.dropped = self.dropped.saturating_add(overflow);
        self.tail.extend(keep);
    }

    /// Render the stream for a diagnostic: sanitized head, then the
    /// sanitized rolling tail, separated by a gap marker only when bytes
    /// between them were discarded.
    fn render(&self) -> String {
        let mut text = sanitize_child_output(&String::from_utf8_lossy(&self.head));
        if self.dropped > 0 {
            text.push_str(&format!("\n… [{} bytes not captured] …\n", self.dropped));
        }
        if !self.tail.is_empty() {
            let tail: Vec<u8> = self.tail.iter().copied().collect();
            text.push_str(&sanitize_child_output(&String::from_utf8_lossy(&tail)));
        }
        text
    }
}

fn lock_capture<T>(buf: &Mutex<T>) -> MutexGuard<'_, T> {
    // Readers only append bytes, so a poisoned buffer is still coherent.
    buf.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Build the `sandbox-timeout` failure, appending a sanitized, middle-elided
/// excerpt of the output captured so far. The tail is kept because a stuck
/// elaboration's last lines (e.g. the goal it was working on) are usually
/// the most useful clue.
fn timeout_failure(
    timeout: Duration,
    stdout: &Mutex<StreamCapture>,
    stderr: &Mutex<StreamCapture>,
) -> Failure {
    let mut detail =
        format!("sandboxed child exceeded wall-clock timeout of {}s", timeout.as_secs());
    // Sanitize each stream before deciding whether it has anything to show,
    // so escape-only output neither adds an empty `[stderr]` header nor
    // hides the "no partial output" note.
    let mut combined = lock_capture(stdout).render();
    let stderr = lock_capture(stderr).render();
    if !stderr.trim().is_empty() {
        if !combined.trim().is_empty() {
            combined.push('\n');
        }
        combined.push_str("[stderr]\n");
        combined.push_str(&stderr);
    }
    let excerpt = elide_middle(&combined, MAX_TIMEOUT_EXCERPT_CHARS);
    if excerpt.trim().is_empty() {
        detail.push_str("; no partial output captured");
    } else {
        detail.push_str("; partial output (stdout+stderr, middle-elided):\n");
        detail.push_str(&excerpt);
    }
    Failure::operational("sandbox-timeout", detail)
}

/// Strip terminal escape sequences and control characters (keeping `\n` and
/// `\t`) so untrusted child output cannot restyle or rewrite the terminal
/// when a diagnostic is printed. Bidirectional-override characters are also
/// dropped so they cannot visually reorder the excerpt.
fn sanitize_child_output(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\n' | '\t' => out.push(c),
            '\u{1b}' => match chars.peek() {
                Some('[') => {
                    chars.next();
                    skip_csi(&mut chars);
                }
                Some(']' | 'P' | 'X' | '^' | '_') => {
                    chars.next();
                    skip_control_string(&mut chars);
                }
                _ => {
                    // Two-byte or `nF` escapes: intermediates, then a final.
                    while chars.next_if(|c| ('\u{20}'..='\u{2f}').contains(c)).is_some() {}
                    let _ = chars.next_if(|c| ('\u{30}'..='\u{7e}').contains(c));
                }
            },
            '\u{9b}' => skip_csi(&mut chars),
            '\u{90}' | '\u{9d}' | '\u{98}' | '\u{9e}' | '\u{9f}' => skip_control_string(&mut chars),
            // Every Unicode `Bidi_Control` code point.
            '\u{061c}'
            | '\u{200e}'
            | '\u{200f}'
            | '\u{202a}'..='\u{202e}'
            | '\u{2066}'..='\u{2069}' => {}
            c if c.is_control() => {}
            c => out.push(c),
        }
    }
    out
}

/// Skip CSI parameter/intermediate bytes and the final byte, stopping early
/// (without consuming) at anything that cannot belong to the sequence.
fn skip_csi(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while chars.next_if(|c| ('\u{20}'..='\u{3f}').contains(c)).is_some() {}
    let _ = chars.next_if(|c| ('\u{40}'..='\u{7e}').contains(c));
}

/// Skip an OSC/DCS-style string through its BEL or ST terminator. A newline
/// also ends it (unconsumed) so an unterminated string cannot swallow the
/// rest of the output.
fn skip_control_string(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while let Some(c) = chars.next_if(|c| *c != '\n') {
        match c {
            '\u{07}' | '\u{9c}' => return,
            '\u{1b}' if chars.next_if_eq(&'\\').is_some() => return,
            _ => {}
        }
    }
}

/// Keep at most `max_chars` characters of `text`: if it is longer, keep the
/// first two thirds and last third of the budget left after an explicit
/// elision marker. Splits only on `char` boundaries.
fn elide_middle(text: &str, max_chars: usize) -> String {
    let marker = |elided: usize| format!("\n… [{elided} chars elided] …\n");
    let total = text.chars().count();
    if total <= max_chars {
        return text.to_owned();
    }
    // Size the marker for the largest possible elided count so the final
    // (possibly shorter) marker can never push the result past `max_chars`.
    let budget = max_chars.saturating_sub(marker(total).chars().count());
    if budget == 0 {
        return text.chars().take(max_chars).collect();
    }
    let head = budget * 2 / 3;
    let tail = budget - head;
    let byte_at = |idx: usize| text.char_indices().nth(idx).map_or(text.len(), |(i, _)| i);
    let head_end = byte_at(head);
    let tail_start = byte_at(total - tail);
    format!("{}{}{}", &text[..head_end], marker(total - head - tail), &text[tail_start..])
}

/// Drain `reader` to EOF, appending at most `limit` bytes to `sink` as each
/// chunk arrives and discarding the excess so the writer never blocks.
fn drain_bounded_into(
    mut reader: impl Read,
    limit: usize,
    tail_limit: usize,
    sink: &Mutex<StreamCapture>,
) {
    let mut chunk = [0u8; 8192];
    loop {
        match reader.read(&mut chunk) {
            Ok(0) | Err(_) => break,
            Ok(n) => lock_capture(sink).push(&chunk[..n], limit, tail_limit),
        }
    }
}

fn run_unsandboxed(
    policy: &SandboxPolicy,
    stdout_file: Option<(PathBuf, u64)>,
    rlimit_fsize_bytes: u64,
) -> Result<Output, Failure> {
    reject_forbidden_loader_env(&policy.extra_env)?;
    let cwd = policy.child_cwd.as_ref().map_or(policy.rw_tmp.host.as_path(), |m| m.host.as_path());
    let mut cmd = Command::new(&policy.exec_bin);
    cmd.args(&policy.args)
        .current_dir(cwd)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("HOME", &policy.rw_tmp.host)
        .env("TMPDIR", &policy.rw_tmp.host);
    for (k, v) in &policy.extra_env {
        cmd.env(k, v);
    }
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::process::CommandExt;
        let parent_pid = unsafe { libc::getpid() };
        // SAFETY: `apply_process_hygiene` calls only async-signal-safe libc
        // routines (`setpgid`, `prctl`, `getppid`, `close_range`/`fcntl`,
        // `getrlimit`/`setrlimit`) before `exec`.
        unsafe {
            cmd.pre_exec(move || {
                linux::apply_process_hygiene(parent_pid, false, rlimit_fsize_bytes)
            });
        }
    }
    #[cfg(all(unix, not(target_os = "linux")))]
    {
        let _ = rlimit_fsize_bytes;
        use std::os::unix::process::CommandExt;
        // SAFETY: `setpgid(0, 0)` is async-signal-safe and isolates the child
        // process group for deterministic timeout reaping.
        unsafe {
            cmd.pre_exec(|| {
                let _ = libc::setpgid(0, 0);
                Ok(())
            });
        }
    }
    #[cfg(not(unix))]
    {
        let _ = rlimit_fsize_bytes;
    }
    spawn_and_wait_with_timeout(cmd, policy.timeout, "unsandboxed-lean", stdout_file)
}

#[cfg(target_os = "linux")]
mod linux {
    use std::{
        ffi::CString,
        fs,
        io::{self, Read},
        os::unix::{ffi::OsStrExt, io::AsRawFd, process::CommandExt},
        path::{Path, PathBuf},
        process::{Command, Output},
    };

    use super::{
        MountSpec, OPTIONAL_SYS_PATHS, PathMapper, RLIMIT_NOFILE_LIMIT,
        SandboxPolicy, SandboxRuntime, make_tree_writable, reject_forbidden_loader_env,
        resolve_pt_interp_lib_dirs, resolve_pt_interp_paths, set_mode,
        spawn_and_wait_with_timeout,
    };
    use crate::toolchain::Failure;

    // -----------------------------------------------------------------------
    // Linux Landlock UAPI constants (pinned `libc = 0.2.191` exposes syscall
    // numbers `SYS_landlock_*` and `SYS_close_range` but omits these UAPI
    // constants and structs; values are part of the stable Linux UAPI ABI in
    // `include/uapi/linux/landlock.h`).
    // -----------------------------------------------------------------------
    const LANDLOCK_CREATE_RULESET_VERSION: u32 = 1 << 0;
    const LANDLOCK_RULE_PATH_BENEATH: u32 = 1;
    const CLOSE_RANGE_CLOEXEC: u32 = 1 << 2;

    const LL_FS_EXECUTE: u64 = 1 << 0;
    const LL_FS_WRITE_FILE: u64 = 1 << 1;
    const LL_FS_READ_FILE: u64 = 1 << 2;
    const LL_FS_READ_DIR: u64 = 1 << 3;
    const LL_FS_REMOVE_DIR: u64 = 1 << 4;
    const LL_FS_REMOVE_FILE: u64 = 1 << 5;
    const LL_FS_MAKE_CHAR: u64 = 1 << 6;
    const LL_FS_MAKE_DIR: u64 = 1 << 7;
    const LL_FS_MAKE_REG: u64 = 1 << 8;
    const LL_FS_MAKE_SOCK: u64 = 1 << 9;
    const LL_FS_MAKE_FIFO: u64 = 1 << 10;
    const LL_FS_MAKE_BLOCK: u64 = 1 << 11;
    const LL_FS_MAKE_SYM: u64 = 1 << 12;
    const LL_FS_REFER: u64 = 1 << 13;
    const LL_FS_TRUNCATE: u64 = 1 << 14;
    const LL_FS_IOCTL_DEV: u64 = 1 << 15;

    const LL_FS_ALL_V3: u64 = LL_FS_EXECUTE
        | LL_FS_WRITE_FILE
        | LL_FS_READ_FILE
        | LL_FS_READ_DIR
        | LL_FS_REMOVE_DIR
        | LL_FS_REMOVE_FILE
        | LL_FS_MAKE_CHAR
        | LL_FS_MAKE_DIR
        | LL_FS_MAKE_REG
        | LL_FS_MAKE_SOCK
        | LL_FS_MAKE_FIFO
        | LL_FS_MAKE_BLOCK
        | LL_FS_MAKE_SYM
        | LL_FS_REFER
        | LL_FS_TRUNCATE;

    const LL_FS_ALL_V5: u64 = LL_FS_ALL_V3 | LL_FS_IOCTL_DEV;

    const LL_NET_BIND_TCP: u64 = 1 << 0;
    const LL_NET_CONNECT_TCP: u64 = 1 << 1;

    const LL_SCOPE_ABSTRACT_UNIX_SOCKET: u64 = 1 << 0;
    const LL_SCOPE_SIGNAL: u64 = 1 << 1;

    const LL_RO_FILE: u64 = LL_FS_READ_FILE;
    const LL_RO_DIR: u64 = LL_FS_READ_FILE | LL_FS_READ_DIR;
    const LL_EXEC_FILE: u64 = LL_FS_READ_FILE | LL_FS_EXECUTE;
    const LL_RW_DEV_NULL: u64 = LL_FS_READ_FILE | LL_FS_WRITE_FILE;
    const LL_RW_SCRATCH_DIR: u64 = LL_FS_READ_FILE
        | LL_FS_READ_DIR
        | LL_FS_WRITE_FILE
        | LL_FS_TRUNCATE
        | LL_FS_MAKE_REG
        | LL_FS_MAKE_DIR
        | LL_FS_REMOVE_FILE
        | LL_FS_REMOVE_DIR;

    #[repr(C)]
    struct LandlockRulesetAttr {
        handled_access_fs: u64,
        handled_access_net: u64,
        scoped: u64,
    }

    #[repr(C, packed)]
    struct LandlockPathBeneathAttr {
        allowed_access: u64,
        parent_fd: i32,
    }

    /// Owned Landlock ruleset file descriptor closed automatically on drop.
    struct RulesetFd(libc::c_int);

    impl Drop for RulesetFd {
        fn drop(&mut self) {
            if self.0 >= 0 {
                // SAFETY: `self.0` is an owned file descriptor returned by
                // `SYS_landlock_create_ruleset`.
                unsafe {
                    let _ = libc::close(self.0);
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Linux classic BPF & seccomp UAPI constants (`uapi/linux/filter.h`,
    // `uapi/linux/seccomp.h`, `uapi/linux/audit.h`).
    // -----------------------------------------------------------------------
    const BPF_LD: u16 = 0x00;
    const BPF_JMP: u16 = 0x05;
    const BPF_RET: u16 = 0x06;
    const BPF_W: u16 = 0x00;
    const BPF_ABS: u16 = 0x20;
    const BPF_JEQ: u16 = 0x10;
    const BPF_JSET: u16 = 0x40;
    const BPF_JA: u16 = 0x00;
    const BPF_K: u16 = 0x00;

    const SECCOMP_SET_MODE_FILTER: libc::c_uint = 1;
    const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
    const SECCOMP_RET_ERRNO: u32 = 0x0005_0000;
    const SECCOMP_RET_ALLOW: u32 = 0x7fff_0000;

    const OFFSET_NR: u32 = 0;
    const OFFSET_ARCH: u32 = 4;
    const fn offset_arg_lo(idx: u32) -> u32 {
        16 + idx * 8
    }
    const fn offset_arg_hi(idx: u32) -> u32 {
        16 + idx * 8 + 4
    }

    #[cfg(target_arch = "x86_64")]
    const EXPECTED_AUDIT_ARCH: u32 = 0xC000_003E;
    #[cfg(target_arch = "aarch64")]
    const EXPECTED_AUDIT_ARCH: u32 = 0xC000_00B7;

    #[repr(C)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) struct SockFilter {
        pub code: u16,
        pub jt: u8,
        pub jf: u8,
        pub k: u32,
    }

    #[repr(C)]
    struct SockFprog {
        len: u16,
        filter: *const SockFilter,
    }

    /// Symbolic classic-BPF builder that resolves named labels into relative
    /// jumps and fails closed if any conditional branch exceeds `u8::MAX`
    /// (`255`).
    pub(crate) struct BpfBuilder {
        insns: Vec<BpfOp>,
        labels: std::collections::BTreeMap<&'static str, usize>,
    }

    enum BpfOp {
        Raw(SockFilter),
        JumpIfEq { k: u32, jt: &'static str, jf: Option<&'static str> },
        JumpIfSet { k: u32, jt: &'static str, jf: Option<&'static str> },
        JumpAlways(&'static str),
    }

    pub(crate) struct CompiledBpf {
        pub filter: Vec<SockFilter>,
        pub kill_pid_idx: usize,
        pub tgkill_pid_idx: usize,
    }

    impl BpfBuilder {
        fn new() -> Self {
            Self { insns: Vec::with_capacity(192), labels: std::collections::BTreeMap::new() }
        }

        fn label(&mut self, name: &'static str) {
            let prev = self.labels.insert(name, self.insns.len());
            assert!(prev.is_none(), "duplicate BPF label {name}");
        }

        fn load_abs(&mut self, offset: u32) {
            self.insns.push(BpfOp::Raw(SockFilter {
                code: BPF_LD | BPF_W | BPF_ABS,
                jt: 0,
                jf: 0,
                k: offset,
            }));
        }

        fn ret(&mut self, val: u32) {
            self.insns.push(BpfOp::Raw(SockFilter { code: BPF_RET | BPF_K, jt: 0, jf: 0, k: val }));
        }

        fn jeq(&mut self, k: u32, jt: &'static str) -> usize {
            let idx = self.insns.len();
            self.insns.push(BpfOp::JumpIfEq { k, jt, jf: None });
            idx
        }

        fn jeq_else(&mut self, k: u32, jt: &'static str, jf: &'static str) -> usize {
            let idx = self.insns.len();
            self.insns.push(BpfOp::JumpIfEq { k, jt, jf: Some(jf) });
            idx
        }

        fn jset_else(&mut self, k: u32, jt: &'static str, jf: &'static str) {
            self.insns.push(BpfOp::JumpIfSet { k, jt, jf: Some(jf) });
        }

        fn jmp(&mut self, target: &'static str) {
            self.insns.push(BpfOp::JumpAlways(target));
        }

        fn finish(self) -> Vec<SockFilter> {
            let mut out = Vec::with_capacity(self.insns.len());
            for (idx, op) in self.insns.into_iter().enumerate() {
                let next_pc = idx + 1;
                let rel = |lbl: &'static str| -> u8 {
                    let target =
                        *self.labels.get(lbl).unwrap_or_else(|| panic!("unknown BPF label {lbl}"));
                    assert!(target >= next_pc, "BPF backward jump from {idx} to {lbl} ({target})");
                    let delta = target - next_pc;
                    assert!(
                        delta <= 255,
                        "BPF conditional jump from {idx} to {lbl} exceeds 255 ({delta})"
                    );
                    delta as u8
                };
                match op {
                    BpfOp::Raw(f) => out.push(f),
                    BpfOp::JumpIfEq { k, jt, jf } => out.push(SockFilter {
                        code: BPF_JMP | BPF_JEQ | BPF_K,
                        jt: rel(jt),
                        jf: jf.map_or(0, rel),
                        k,
                    }),
                    BpfOp::JumpIfSet { k, jt, jf } => out.push(SockFilter {
                        code: BPF_JMP | BPF_JSET | BPF_K,
                        jt: rel(jt),
                        jf: jf.map_or(0, rel),
                        k,
                    }),
                    BpfOp::JumpAlways(target_lbl) => {
                        let target = *self
                            .labels
                            .get(target_lbl)
                            .unwrap_or_else(|| panic!("unknown BPF label {target_lbl}"));
                        assert!(target >= next_pc, "BPF backward JA");
                        let delta = (target - next_pc) as u32;
                        out.push(SockFilter { code: BPF_JMP | BPF_JA, jt: 0, jf: 0, k: delta });
                    }
                }
            }
            assert!(out.len() <= 4096, "BPF program exceeds Linux 4096-insn cap");
            out
        }
    }

    /// Construct the fail-closed dual-arch seccomp-BPF allowlist pre-fork.
    ///
    /// Returns the compiled instruction buffer together with the two exact
    /// indices (`kill_pid_idx`, `tgkill_pid_idx`) patched in-place with
    /// `libc::getpid()` inside `pre_exec` (zero heap allocation post-fork).
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    pub(crate) fn build_seccomp_bpf() -> CompiledBpf {
        let mut b = BpfBuilder::new();
        // 1. Authenticate syscall ABI architecture.
        b.load_abs(OFFSET_ARCH);
        b.jeq_else(EXPECTED_AUDIT_ARCH, "arch_ok", "kill");
        b.label("arch_ok");

        // 2. Load syscall number; reject x32 ABI (`nr & 0x4000_0000 != 0`).
        b.load_abs(OFFSET_NR);
        #[cfg(target_arch = "x86_64")]
        {
            b.jset_else(0x4000_0000, "kill", "nr_ok");
            b.label("nr_ok");
        }

        // 3. Six argument-guarded syscalls (`ioctl` dropped completely).
        b.jeq(libc::SYS_clone3 as u32, "ret_enosys");
        b.jeq(libc::SYS_clone as u32, "guard_clone");
        b.jeq(libc::SYS_prlimit64 as u32, "guard_prlimit64");
        b.jeq(libc::SYS_kill as u32, "guard_kill");
        b.jeq(libc::SYS_tgkill as u32, "guard_tgkill");
        b.jeq(libc::SYS_fcntl as u32, "guard_fcntl");

        // 4. Unconditionally allowed pure / Landlock-confined syscalls.
        //    Every symbol comes directly from pinned `libc` (no magic numbers).
        const COMMON_ALLOWED: &[libc::c_long] = &[
            // Process/thread lifecycle & sync
            libc::SYS_exit,
            libc::SYS_exit_group,
            libc::SYS_futex,
            libc::SYS_set_robust_list,
            libc::SYS_set_tid_address,
            libc::SYS_rseq,
            libc::SYS_sched_yield,
            libc::SYS_sched_getaffinity,
            libc::SYS_getpid,
            libc::SYS_gettid,
            libc::SYS_getppid,
            libc::SYS_getuid,
            libc::SYS_geteuid,
            libc::SYS_getgid,
            libc::SYS_getegid,
            libc::SYS_sigaltstack,
            libc::SYS_rt_sigaction,
            libc::SYS_rt_sigprocmask,
            libc::SYS_rt_sigreturn,
            libc::SYS_restart_syscall,
            libc::SYS_execve,
            // Memory
            libc::SYS_brk,
            libc::SYS_mmap,
            libc::SYS_munmap,
            libc::SYS_mprotect,
            libc::SYS_mremap,
            libc::SYS_madvise,
            // Landlock-confined file/dir I/O & event loop
            libc::SYS_read,
            libc::SYS_write,
            libc::SYS_readv,
            libc::SYS_writev,
            libc::SYS_pread64,
            libc::SYS_pwrite64,
            libc::SYS_lseek,
            libc::SYS_openat,
            libc::SYS_close,
            libc::SYS_close_range,
            libc::SYS_dup,
            libc::SYS_dup3,
            libc::SYS_fstat,
            libc::SYS_newfstatat,
            libc::SYS_statx,
            libc::SYS_faccessat,
            libc::SYS_faccessat2,
            libc::SYS_readlinkat,
            libc::SYS_getcwd,
            libc::SYS_getdents64,
            libc::SYS_ftruncate,
            libc::SYS_mkdirat,
            libc::SYS_unlinkat,
            libc::SYS_renameat,
            libc::SYS_renameat2,
            libc::SYS_fsync,
            libc::SYS_fdatasync,
            libc::SYS_pipe2,
            libc::SYS_epoll_create1,
            libc::SYS_epoll_ctl,
            libc::SYS_epoll_pwait,
            libc::SYS_ppoll,
            libc::SYS_pselect6,
            libc::SYS_eventfd2,
            libc::SYS_umask,
            // Time, entropy, and self-accounting (Lean `-M` uses `getrusage`)
            libc::SYS_clock_gettime,
            libc::SYS_clock_getres,
            libc::SYS_clock_nanosleep,
            libc::SYS_nanosleep,
            libc::SYS_gettimeofday,
            libc::SYS_getrandom,
            libc::SYS_getcpu,
            libc::SYS_getrusage,
            libc::SYS_uname,
            libc::SYS_sysinfo,
        ];
        for &nr in COMMON_ALLOWED {
            b.jeq(nr as u32, "allow");
        }

        #[cfg(target_arch = "x86_64")]
        {
            const X86_64_ONLY_ALLOWED: &[libc::c_long] = &[
                libc::SYS_arch_prctl,
                libc::SYS_open,
                libc::SYS_dup2,
                libc::SYS_access,
                libc::SYS_stat,
                libc::SYS_lstat,
                libc::SYS_readlink,
                libc::SYS_rename,
                libc::SYS_unlink,
                libc::SYS_mkdir,
                libc::SYS_pipe,
                libc::SYS_poll,
                libc::SYS_select,
                libc::SYS_epoll_wait,
                libc::SYS_eventfd,
                libc::SYS_getrlimit,
                libc::SYS_time,
            ];
            for &nr in X86_64_ONLY_ALLOWED {
                b.jeq(nr as u32, "allow");
            }
        }

        // Default fail-closed action for all unlisted syscalls.
        b.jmp("deny");

        // --- Guard 1: `clone` allowed strictly with `CLONE_THREAD` set. ---
        b.label("guard_clone");
        b.load_abs(offset_arg_hi(0));
        b.jeq_else(0, "guard_clone_lo", "deny");
        b.label("guard_clone_lo");
        b.load_abs(offset_arg_lo(0));
        b.jset_else(libc::CLONE_THREAD as u32, "allow", "deny");

        // --- Guard 2: `prlimit64` allowed strictly for read-only self
        // (`pid == 0 && new_limit == NULL`). ---
        b.label("guard_prlimit64");
        b.load_abs(offset_arg_hi(0));
        b.jeq_else(0, "guard_prlimit64_pid_lo", "deny");
        b.label("guard_prlimit64_pid_lo");
        b.load_abs(offset_arg_lo(0));
        b.jeq_else(0, "guard_prlimit64_new_hi", "deny");
        b.label("guard_prlimit64_new_hi");
        b.load_abs(offset_arg_hi(2));
        b.jeq_else(0, "guard_prlimit64_new_lo", "deny");
        b.label("guard_prlimit64_new_lo");
        b.load_abs(offset_arg_lo(2));
        b.jeq_else(0, "allow", "deny");

        // --- Guard 3: `kill` allowed strictly targeting `child_pid`. ---
        b.label("guard_kill");
        b.load_abs(offset_arg_hi(0));
        b.jeq_else(0, "guard_kill_lo", "deny");
        b.label("guard_kill_lo");
        b.load_abs(offset_arg_lo(0));
        let kill_pid_idx = b.jeq_else(0, "allow", "deny");

        // --- Guard 4: `tgkill` allowed strictly targeting `child_pid`. ---
        b.label("guard_tgkill");
        b.load_abs(offset_arg_hi(0));
        b.jeq_else(0, "guard_tgkill_lo", "deny");
        b.label("guard_tgkill_lo");
        b.load_abs(offset_arg_lo(0));
        let tgkill_pid_idx = b.jeq_else(0, "allow", "deny");

        // --- Guard 5: `fcntl` restricted to closed FD/flag manipulation. ---
        b.label("guard_fcntl");
        b.load_abs(offset_arg_hi(1));
        b.jeq_else(0, "guard_fcntl_lo", "deny");
        b.label("guard_fcntl_lo");
        b.load_abs(offset_arg_lo(1));
        for cmd in [
            libc::F_GETFD,
            libc::F_SETFD,
            libc::F_GETFL,
            libc::F_SETFL,
            libc::F_DUPFD,
            libc::F_DUPFD_CLOEXEC,
        ] {
            b.jeq(cmd as u32, "allow");
        }
        b.jmp("deny");

        // Terminal return blocks.
        b.label("allow");
        b.ret(SECCOMP_RET_ALLOW);
        b.label("ret_enosys");
        b.ret(SECCOMP_RET_ERRNO | (libc::ENOSYS as u32));
        b.label("deny");
        b.ret(SECCOMP_RET_ERRNO | (libc::EPERM as u32));
        b.label("kill");
        b.ret(SECCOMP_RET_KILL_PROCESS);

        let filter = b.finish();
        CompiledBpf { filter, kill_pid_idx, tgkill_pid_idx }
    }

    /// Query Landlock ABI version and check Tier 2 hard preconditions.
    pub(super) fn check_tier2_preconditions(
        exec_bin: &Path,
    ) -> Result<(i32, Vec<PathBuf>), String> {
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        {
            let _ = exec_bin;
            return Err("Tier 2 seccomp-BPF allowlist supports x86_64 and aarch64 only".into());
        }
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        {
            // SAFETY: `geteuid()` has no preconditions.
            if unsafe { libc::geteuid() } == 0 {
                return Err("refusing Tier 2 Landlock + seccomp under root (euid == 0)".into());
            }
            // SAFETY: Querying Landlock ABI version with NULL attr and size 0
            // is the documented `userspace-api/landlock.rst` kernel interface.
            let abi = unsafe {
                libc::syscall(
                    libc::SYS_landlock_create_ruleset,
                    std::ptr::null::<LandlockRulesetAttr>(),
                    0usize,
                    LANDLOCK_CREATE_RULESET_VERSION,
                )
            } as i32;
            if abi < 3 {
                return Err(format!(
                    "kernel Landlock ABI {abi} < 3 (ABI >= 3 required for mandatory TRUNCATE)"
                ));
            }
            let interps = resolve_pt_interp_paths(exec_bin)?;
            Ok((abi, interps))
        }
    }

    fn landlock_add_path(
        ruleset_fd: libc::c_int,
        path: &Path,
        access: u64,
        optional: bool,
    ) -> Result<(), Failure> {
        let cpath = CString::new(path.as_os_str().as_bytes()).map_err(|_| {
            Failure::operational("sandbox", format!("NUL byte in path {}", path.display()))
        })?;
        // SAFETY: `cpath` is a valid NUL-terminated string; `O_PATH|O_CLOEXEC`
        // opens a path-only descriptor without executing or opening FIFOs.
        let fd = unsafe { libc::open(cpath.as_ptr(), libc::O_PATH | libc::O_CLOEXEC) };
        if fd < 0 {
            let err = io::Error::last_os_error();
            if optional && err.raw_os_error() == Some(libc::ENOENT) {
                return Ok(());
            }
            return Err(Failure::operational(
                "sandbox",
                format!("landlock open({}) failed: {err}", path.display()),
            ));
        }
        let rule = LandlockPathBeneathAttr { allowed_access: access, parent_fd: fd };
        // SAFETY: `ruleset_fd` and `fd` are valid descriptors and `rule` is a
        // valid `#[repr(C, packed)]` `landlock_path_beneath_attr`.
        let rc = unsafe {
            libc::syscall(
                libc::SYS_landlock_add_rule,
                ruleset_fd,
                LANDLOCK_RULE_PATH_BENEATH,
                &rule as *const LandlockPathBeneathAttr,
                0u32,
            )
        };
        let add_err = if rc != 0 { Some(io::Error::last_os_error()) } else { None };
        // SAFETY: `fd` is an owned file descriptor returned by `libc::open`.
        unsafe {
            let _ = libc::close(fd);
        }
        if let Some(err) = add_err {
            return Err(Failure::operational(
                "sandbox",
                format!("landlock_add_rule({}, 0x{:x}) failed: {err}", path.display(), access),
            ));
        }
        Ok(())
    }

    fn build_landlock_ruleset(
        runtime: &SandboxRuntime,
        policy: &SandboxPolicy,
    ) -> Result<RulesetFd, Failure> {
        let abi = runtime.landlock_abi;
        let (attr, size) = if abi >= 6 {
            (
                LandlockRulesetAttr {
                    handled_access_fs: LL_FS_ALL_V5,
                    handled_access_net: LL_NET_BIND_TCP | LL_NET_CONNECT_TCP,
                    scoped: LL_SCOPE_ABSTRACT_UNIX_SOCKET | LL_SCOPE_SIGNAL,
                },
                24usize,
            )
        } else if abi == 5 {
            (
                LandlockRulesetAttr {
                    handled_access_fs: LL_FS_ALL_V5,
                    handled_access_net: LL_NET_BIND_TCP | LL_NET_CONNECT_TCP,
                    scoped: 0,
                },
                16usize,
            )
        } else if abi == 4 {
            (
                LandlockRulesetAttr {
                    handled_access_fs: LL_FS_ALL_V3,
                    handled_access_net: LL_NET_BIND_TCP | LL_NET_CONNECT_TCP,
                    scoped: 0,
                },
                16usize,
            )
        } else {
            (
                LandlockRulesetAttr {
                    handled_access_fs: LL_FS_ALL_V3,
                    handled_access_net: 0,
                    scoped: 0,
                },
                8usize,
            )
        };

        // SAFETY: `attr` is initialized for at least `size` bytes matching the
        // queried kernel ABI (`8` for v3, `16` for v4-v5, `24` for v6+).
        let fd = unsafe {
            libc::syscall(
                libc::SYS_landlock_create_ruleset,
                &attr as *const LandlockRulesetAttr,
                size,
                0u32,
            )
        } as libc::c_int;
        if fd < 0 {
            return Err(Failure::operational(
                "sandbox",
                format!(
                    "landlock_create_ruleset(abi={abi}, size={size}) failed: {}",
                    io::Error::last_os_error()
                ),
            ));
        }
        // Mark `ruleset_fd` close-on-exec so it never leaks past `execve`.
        // SAFETY: `fd` is a valid open file descriptor.
        unsafe {
            let _ = libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
        }
        let ruleset = RulesetFd(fd);

        // 1. Executable regular files ONLY (`exec_bin` + `PT_INTERP`).
        landlock_add_path(ruleset.0, &policy.exec_bin, LL_EXEC_FILE, false)?;
        for interp in &runtime.pt_interp_paths {
            landlock_add_path(ruleset.0, interp, LL_EXEC_FILE, false)?;
        }

        // 2. Explicit 3-device surface.
        landlock_add_path(ruleset.0, Path::new("/dev/null"), LL_RW_DEV_NULL, false)?;
        landlock_add_path(ruleset.0, Path::new("/dev/zero"), LL_RO_FILE, false)?;
        landlock_add_path(ruleset.0, Path::new("/dev/urandom"), LL_RO_FILE, false)?;

        // 3. Optional system loader/shared-library paths (`ENOENT`-skipped).
        for raw in OPTIONAL_SYS_PATHS {
            let p = Path::new(raw);
            match fs::metadata(p) {
                Ok(meta) => {
                    let mask = if meta.is_dir() { LL_RO_DIR } else { LL_RO_FILE };
                    landlock_add_path(ruleset.0, p, mask, true)?;
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => {
                    return Err(Failure::operational(
                        "sandbox",
                        format!("cannot inspect system path {raw}: {e}"),
                    ));
                }
            }
        }
        if runtime.needs_nix_store && fs::metadata("/nix/store").is_ok() {
            landlock_add_path(ruleset.0, Path::new("/nix/store"), LL_RO_DIR, true)?;
        }
        for interp_dir in &runtime.pt_interp_lib_dirs {
            landlock_add_path(ruleset.0, interp_dir, LL_RO_DIR, false)?;
        }

        // 4. Read-only mounts (strictly separating file vs dir masks).
        for MountSpec { host, .. } in policy
            .ro_mounts
            .iter()
            .chain(runtime.toolchain_ro_mounts.iter())
            .chain(runtime.extra_toolchain_mounts.iter())
        {
            let meta = fs::metadata(host).map_err(|e| {
                Failure::operational("sandbox", format!("cannot stat {}: {e}", host.display()))
            })?;
            let mask = if meta.is_dir() { LL_RO_DIR } else { LL_RO_FILE };
            landlock_add_path(ruleset.0, host, mask, false)?;
        }

        // 5. Writable per-invocation scratch & output dirs (`RW_SCRATCH_DIR`).
        landlock_add_path(ruleset.0, &policy.rw_out.host, LL_RW_SCRATCH_DIR, false)?;
        landlock_add_path(ruleset.0, &policy.rw_tmp.host, LL_RW_SCRATCH_DIR, false)?;

        Ok(ruleset)
    }

    /// Async-signal-safe FD hygiene: set `FD_CLOEXEC` on all descriptors `>= 3`
    /// using `close_range`, falling back to bounded `fcntl(F_GETFD / F_SETFD)`
    /// iteration up to `RLIMIT_NOFILE.min(65536)` when `SYS_close_range` is
    /// unavailable.
    ///
    /// SAFETY: Must be called only inside `pre_exec` (single-threaded child).
    unsafe fn close_inherited_fds_cloexec() -> io::Result<()> {
        // SAFETY: `SYS_close_range` with `CLOSE_RANGE_CLOEXEC` is
        // async-signal-safe and keeps Rust's exec-error pipe open until exec.
        let rc =
            unsafe { libc::syscall(libc::SYS_close_range, 3u32, u32::MAX, CLOSE_RANGE_CLOEXEC) };
        if rc == 0 {
            return Ok(());
        }
        let err = io::Error::last_os_error();
        if err.raw_os_error() != Some(libc::ENOSYS) && err.raw_os_error() != Some(libc::EINVAL) {
            return Err(err);
        }
        // Fallback: iterate `3..max_fd` (bounded by soft `RLIMIT_NOFILE`),
        // setting `FD_CLOEXEC` via `fcntl` (async-signal-safe, zero allocs).
        let mut rlim = libc::rlimit { rlim_cur: 1024, rlim_max: 1024 };
        let _ = unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut rlim) };
        let upper = rlim.rlim_cur.min(65536) as libc::c_int;
        for fd in 3..upper {
            let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
            if flags >= 0 && (flags & libc::FD_CLOEXEC) == 0 {
                let _ = unsafe { libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) };
            }
        }
        Ok(())
    }

    /// Async-signal-safe shared process hygiene run inside `pre_exec`.
    ///
    /// SAFETY: Must be called only inside `CommandExt::pre_exec`.
    pub(super) unsafe fn apply_process_hygiene(
        parent_pid: libc::pid_t,
        use_setsid: bool,
        rlimit_fsize_bytes: u64,
    ) -> io::Result<()> {
        if use_setsid {
            if unsafe { libc::setsid() } < 0 {
                return Err(io::Error::last_os_error());
            }
        } else if unsafe { libc::setpgid(0, 0) } < 0 {
            return Err(io::Error::last_os_error());
        }
        // Register parent-death signal, then close the fork-to-prctl race by
        // confirming the parent is still alive.
        if unsafe { libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL as libc::c_ulong, 0, 0, 0) }
            != 0
        {
            return Err(io::Error::last_os_error());
        }
        if unsafe { libc::getppid() } != parent_pid {
            unsafe { libc::_exit(127) };
        }
        unsafe { close_inherited_fds_cloexec()? };
        // Clamp each resource cap against the inherited hard limit so tight
        // container limits never cause `setrlimit` to fail with `EPERM`.
        macro_rules! set_clamped_rlimit {
            ($resource:expr, $desired:expr) => {{
                let mut cur = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
                let capped = if unsafe { libc::getrlimit($resource, &mut cur) } == 0
                    && cur.rlim_max != libc::RLIM_INFINITY
                {
                    ($desired).min(cur.rlim_max)
                } else {
                    $desired
                };
                let lim = libc::rlimit { rlim_cur: capped, rlim_max: capped };
                if unsafe { libc::setrlimit($resource, &lim) } != 0 {
                    return Err(io::Error::last_os_error());
                }
            }};
        }
        set_clamped_rlimit!(libc::RLIMIT_CORE, 0);
        set_clamped_rlimit!(libc::RLIMIT_FSIZE, rlimit_fsize_bytes);
        set_clamped_rlimit!(libc::RLIMIT_NOFILE, RLIMIT_NOFILE_LIMIT);
        Ok(())
    }

    /// Per-invocation `0o400` backing files for Tier 1's read-only `/dev/zero`
    /// and `/dev/urandom` mounts.
    ///
    /// On Linux, `bwrap --ro-bind` and `--remount-ro` set `MS_NODEV`, which
    /// causes VFS `may_open` to reject even `O_RDONLY` on character devices
    /// (`EACCES`, breaking `libc++`'s `std::random_device("/dev/urandom")` at
    /// Lean startup), whereas `MS_RDONLY` without `MS_NODEV` leaves `0666`
    /// `S_IFCHR` nodes writable (`fs/namei.c:may_open` skips `mnt_want_write`
    /// for character devices). Binding per-invocation `0o400` regular files
    /// seeded from `/dev/urandom` and NUL bytes via `--ro-bind` keeps both
    /// paths read-only (`EROFS` on write or truncate) without exposing host
    /// character devices.
    struct BwrapRoDevices {
        dir: tempfile::TempDir,
        zero: PathBuf,
        urandom: PathBuf,
    }

    impl BwrapRoDevices {
        const SEED_LEN: usize = 64 * 1024;

        fn create(out_host: &Path) -> Result<Self, Failure> {
            let mut builder = tempfile::Builder::new();
            builder.prefix("anneal-bwrap-dev-");
            let dir = match out_host.parent() {
                Some(parent) => builder.tempdir_in(parent),
                None => builder.tempdir(),
            }
            .map_err(|e| {
                Failure::operational("sandbox", format!("create bwrap device staging dir: {e}"))
            })?;
            set_mode(dir.path(), 0o700)?;

            let zero = dir.path().join("zero");
            fs::write(&zero, vec![0u8; Self::SEED_LEN]).map_err(|e| {
                Failure::operational("sandbox", format!("stage bwrap /dev/zero backing file: {e}"))
            })?;
            set_mode(&zero, 0o400)?;

            let mut rand_bytes = vec![0u8; Self::SEED_LEN];
            let mut urandom_src = fs::File::open("/dev/urandom").map_err(|e| {
                Failure::operational("sandbox", format!("open host /dev/urandom: {e}"))
            })?;
            urandom_src.read_exact(&mut rand_bytes).map_err(|e| {
                Failure::operational("sandbox", format!("read host /dev/urandom: {e}"))
            })?;
            let urandom = dir.path().join("urandom");
            fs::write(&urandom, &rand_bytes).map_err(|e| {
                Failure::operational(
                    "sandbox",
                    format!("stage bwrap /dev/urandom backing file: {e}"),
                )
            })?;
            set_mode(&urandom, 0o400)?;

            Ok(Self { dir, zero, urandom })
        }
    }

    impl Drop for BwrapRoDevices {
        fn drop(&mut self) {
            make_tree_writable(self.dir.path());
        }
    }

    /// Build a pipe pre-loaded with the compiled Tier 2 seccomp-BPF allowlist
    /// for `bwrap --seccomp <fd>` and return its read end.
    ///
    /// Under `bwrap --unshare-all --as-pid-1`, the confined executable runs as
    /// PID 1 inside its isolated PID namespace, so self-targeted `kill`/`tgkill`
    /// guards are patched to PID `1`. The entire BPF program is ~1 KiB, well
    /// below Linux's minimum 64 KiB pipe buffer, so writing the program and
    /// closing the write end before `spawn` never blocks.
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    pub(crate) fn prepare_bwrap_seccomp_pipe() -> Result<std::os::unix::io::OwnedFd, Failure> {
        use std::io::Write as _;
        use std::os::unix::io::{FromRawFd, OwnedFd};

        let mut compiled = build_seccomp_bpf();
        compiled.filter[compiled.kill_pid_idx].k = 1;
        compiled.filter[compiled.tgkill_pid_idx].k = 1;

        let mut fds = [0 as libc::c_int; 2];
        // SAFETY: `fds` is a valid writable 2-element `c_int` array.
        if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
            let err = io::Error::last_os_error();
            return Err(Failure::operational(
                "sandbox",
                format!("pipe2 for bwrap seccomp filter failed: {err}"),
            ));
        }
        // SAFETY: `pipe2` succeeded and returned two freshly opened unique FDs.
        let read_fd = unsafe { OwnedFd::from_raw_fd(fds[0]) };
        let mut write_file = unsafe { fs::File::from_raw_fd(fds[1]) };

        let byte_len = std::mem::size_of_val(compiled.filter.as_slice());
        // SAFETY: `SockFilter` is `#[repr(C)]` plain-old-data (`u16, u8, u8, u32`)
        // with no padding bytes; `compiled.filter` stays alive across `write_all`.
        let bytes = unsafe {
            std::slice::from_raw_parts(compiled.filter.as_ptr().cast::<u8>(), byte_len)
        };
        write_file.write_all(bytes).map_err(|e| {
            Failure::operational("sandbox", format!("writing bwrap seccomp BPF failed: {e}"))
        })?;
        drop(write_file);
        Ok(read_fd)
    }

    /// Probe whether `bwrap_path --help` advertises `--disable-userns`.
    pub(super) fn bwrap_help_supports_disable_userns(bwrap_path: &Path) -> bool {
        Command::new(bwrap_path)
            .arg("--help")
            .env_clear()
            .output()
            .is_ok_and(|out| {
                String::from_utf8_lossy(&out.stdout).contains("--disable-userns")
                    || String::from_utf8_lossy(&out.stderr).contains("--disable-userns")
            })
    }

    /// Execute `policy` under Tier 1 (`linux_bwrap`).
    pub(super) fn run_bwrap(
        runtime: &SandboxRuntime,
        policy: &SandboxPolicy,
        stdout_file: Option<(PathBuf, u64)>,
        rlimit_fsize_bytes: u64,
    ) -> Result<Output, Failure> {
        reject_forbidden_loader_env(&policy.extra_env)?;
        let bwrap = runtime.bwrap_path.as_ref().ok_or_else(|| {
            Failure::operational("sandbox", "missing bwrap binary path for LinuxBwrap")
        })?;
        let ro_devs = BwrapRoDevices::create(&policy.rw_out.host)?;
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        let seccomp_read_fd = if runtime.bwrap_seccomp_active {
            Some(prepare_bwrap_seccomp_pipe()?)
        } else {
            None
        };
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        let seccomp_read_fd: Option<std::os::unix::io::OwnedFd> = None;

        let mut cmd = Command::new(bwrap);
        cmd.env_clear().env("PATH", "/usr/bin:/bin");
        // Note: `run_bwrap` calls `setsid()` in `pre_exec` (below) rather than
        // passing `--new-session` to `bwrap`. Detaching the controlling
        // terminal before `exec` gives the same TIOCSTI protection while
        // keeping both outer `bwrap` and inner PID 1 in `PGID = bwrap_pid` so
        // `kill(-bwrap_pid, SIGKILL)` atomically tears down the entire PID
        // namespace on wall-clock timeout without relying on
        // `--die-with-parent` alone.
        cmd.arg("--unshare-all");
        if runtime.bwrap_disable_userns {
            // `bwrap` requires explicit `--unshare-user` alongside
            // `--disable-userns` even when `--unshare-all` is set.
            cmd.args(["--unshare-user", "--disable-userns"]);
        }
        cmd.args([
            "--as-pid-1",
            "--cap-drop",
            "ALL",
            "--die-with-parent",
            "--clearenv",
            "--size",
            "16777216",
            "--tmpfs",
            "/",
            "--size",
            "65536",
            "--tmpfs",
            "/dev",
            "--dev-bind",
            "/dev/null",
            "/dev/null",
        ]);
        if let Some(fd) = &seccomp_read_fd {
            cmd.arg("--seccomp").arg(fd.as_raw_fd().to_string());
        }
        cmd.arg("--ro-bind").arg(&ro_devs.zero).arg("/dev/zero");
        cmd.arg("--ro-bind").arg(&ro_devs.urandom).arg("/dev/urandom");
        cmd.args(["--proc", "/proc"]);
        for sys in OPTIONAL_SYS_PATHS {
            cmd.args(["--ro-bind-try", sys, sys]);
        }
        if runtime.needs_nix_store {
            cmd.args(["--ro-bind-try", "/nix/store", "/nix/store"]);
        }
        for MountSpec { host, child } in super::resolve_pt_interp_bwrap_mounts(
            &runtime.pt_interp_paths,
            &runtime.pt_interp_lib_dirs,
            None,
        )? {
            cmd.arg("--ro-bind").arg(host).arg(child);
        }
        for MountSpec { host, child } in policy
            .ro_mounts
            .iter()
            .chain(runtime.toolchain_ro_mounts.iter())
            .chain(runtime.extra_toolchain_mounts.iter())
        {
            cmd.arg("--ro-bind").arg(host).arg(child);
        }
        if let Some(MountSpec { host, child }) = runtime.extra_exec_bind() {
            cmd.arg("--ro-bind").arg(host).arg(child);
        }
        cmd.arg("--bind").arg(&policy.rw_out.host).arg(&policy.rw_out.child);
        let bwrap_cwd =
            policy.child_cwd.as_ref().map_or(Path::new("/work/tmp"), |m| m.child.as_path());
        cmd.args([
            "--size",
            "1073741824",
            "--tmpfs",
            "/work/tmp",
            "--setenv",
            "PATH",
            "/usr/bin:/bin",
            "--setenv",
            "HOME",
            "/work/tmp",
            "--setenv",
            "TMPDIR",
            "/work/tmp",
        ]);
        cmd.arg("--chdir").arg(bwrap_cwd);
        for (k, v) in &policy.extra_env {
            cmd.arg("--setenv").arg(k).arg(v);
        }
        let mapper = PathMapper::new(runtime, &policy.ro_mounts, &policy.rw_out, &policy.rw_tmp);
        let child_exec = mapper.map_path(&policy.exec_bin)?;
        cmd.arg("--").arg(child_exec).args(&policy.args);

        // SAFETY: `getpid()` has no preconditions.
        let parent_pid = unsafe { libc::getpid() };
        let preserve_seccomp_fd = seccomp_read_fd.as_ref().map(AsRawFd::as_raw_fd);
        // SAFETY: `apply_process_hygiene` and `fcntl(F_SETFD, 0)` invoke
        // strictly async-signal-safe libc syscalls with zero allocations or
        // locks. Clearing `FD_CLOEXEC` strictly on `preserve_seccomp_fd` after
        // `close_inherited_fds_cloexec` lets `bwrap --seccomp <fd>` read the
        // BPF program while every other descriptor `>= 3` closes on `exec`.
        unsafe {
            cmd.pre_exec(move || {
                apply_process_hygiene(parent_pid, true, rlimit_fsize_bytes)?;
                if let Some(fd) = preserve_seccomp_fd
                    && libc::fcntl(fd, libc::F_SETFD, 0) < 0
                {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let result = spawn_and_wait_with_timeout(cmd, policy.timeout, "sandbox-bwrap", stdout_file);
        drop(seccomp_read_fd);
        result
    }

    /// Execute `policy` under Tier 2 (`linux_landlock_seccomp`).
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    pub(super) fn run_landlock_seccomp(
        runtime: &SandboxRuntime,
        policy: &SandboxPolicy,
        stdout_file: Option<(PathBuf, u64)>,
        rlimit_fsize_bytes: u64,
    ) -> Result<Output, Failure> {
        reject_forbidden_loader_env(&policy.extra_env)?;
        let ruleset = build_landlock_ruleset(runtime, policy)?;
        let ruleset_fd = ruleset.0;
        let mut compiled = build_seccomp_bpf();
        let kill_idx = compiled.kill_pid_idx;
        let tgkill_idx = compiled.tgkill_pid_idx;

        let cwd =
            policy.child_cwd.as_ref().map_or(policy.rw_tmp.host.as_path(), |m| m.host.as_path());
        let mut cmd = Command::new(&policy.exec_bin);
        cmd.args(&policy.args)
            .current_dir(cwd)
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("HOME", &policy.rw_tmp.host)
            .env("TMPDIR", &policy.rw_tmp.host);
        for (k, v) in &policy.extra_env {
            cmd.env(k, v);
        }

        // SAFETY: `getpid()` has no preconditions.
        let parent_pid = unsafe { libc::getpid() };
        // SAFETY: `ruleset_fd` stays alive in parent until after `spawn()`
        // returns (`drop(ruleset)` below); `compiled.filter` is pre-allocated
        // before `fork()`, so the closure performs strictly async-signal-safe
        // syscalls and two in-place `u32` writes with zero heap allocation.
        unsafe {
            cmd.pre_exec(move || {
                apply_process_hygiene(parent_pid, true, rlimit_fsize_bytes)?;
                // Lean's `-M` memory limit reads `/proc/self/statm` alongside
                // `getrusage`. Grant read-only Landlock access strictly to this
                // child's own `/proc/<child_pid>/statm` inode (`O_PATH` inside
                // the forked child) without opening any other `/proc` path.
                const PROC_SELF_STATM: &[u8] = b"/proc/self/statm\0";
                let statm_fd = libc::open(
                    PROC_SELF_STATM.as_ptr().cast::<libc::c_char>(),
                    libc::O_PATH | libc::O_CLOEXEC,
                );
                if statm_fd >= 0 {
                    let statm_rule =
                        LandlockPathBeneathAttr { allowed_access: LL_RO_FILE, parent_fd: statm_fd };
                    let _ = libc::syscall(
                        libc::SYS_landlock_add_rule,
                        ruleset_fd,
                        LANDLOCK_RULE_PATH_BENEATH,
                        &statm_rule as *const LandlockPathBeneathAttr,
                        0u32,
                    );
                    let _ = libc::close(statm_fd);
                }
                if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 {
                    return Err(io::Error::last_os_error());
                }
                let rc_ll = libc::syscall(libc::SYS_landlock_restrict_self, ruleset_fd, 0u32);
                let ll_err = if rc_ll != 0 { Some(io::Error::last_os_error()) } else { None };
                let _ = libc::close(ruleset_fd);
                if let Some(err) = ll_err {
                    return Err(err);
                }
                let child_pid = libc::getpid() as u32;
                compiled.filter[kill_idx].k = child_pid;
                compiled.filter[tgkill_idx].k = child_pid;
                let prog = SockFprog {
                    len: compiled.filter.len() as u16,
                    filter: compiled.filter.as_ptr(),
                };
                let rc_sc = libc::syscall(
                    libc::SYS_seccomp,
                    SECCOMP_SET_MODE_FILTER,
                    0u32,
                    &prog as *const SockFprog,
                );
                if rc_sc != 0 {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let res = spawn_and_wait_with_timeout(
            cmd,
            policy.timeout,
            "sandbox-landlock-seccomp",
            stdout_file,
        );
        drop(ruleset);
        res
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub(super) fn run_landlock_seccomp(
        _runtime: &SandboxRuntime,
        _policy: &SandboxPolicy,
        _stdout_file: Option<(PathBuf, u64)>,
        _rlimit_fsize_bytes: u64,
    ) -> Result<Output, Failure> {
        Err(Failure::operational(
            "sandbox",
            "Tier 2 Landlock + seccomp is only supported on Linux x86_64 and aarch64",
        ))
    }

    /// Expose Tier 2 ruleset+seccomp execution directly to integration escape
    /// tests (even on hosts where Tier 1 `bwrap` is also available).
    #[doc(hidden)]
    pub fn force_tier2_runtime(
        exec_bin: &Path,
        toolchain_dir: &Path,
    ) -> Result<SandboxRuntime, Failure> {
        let exec_bin = fs::canonicalize(exec_bin)
            .map_err(|e| Failure::operational("sandbox", format!("canonicalize exec_bin: {e}")))?;
        let toolchain_dir = fs::canonicalize(toolchain_dir).map_err(|e| {
            Failure::operational("sandbox", format!("canonicalize toolchain_dir: {e}"))
        })?;
        let (abi, interps) =
            check_tier2_preconditions(&exec_bin).map_err(|e| Failure::operational("sandbox", e))?;
        let pt_interp_lib_dirs = resolve_pt_interp_lib_dirs(&interps, None)?;
        let needs_nix_store = exec_bin.starts_with("/nix/store")
            || interps.iter().any(|p| p.starts_with("/nix/store"));
        let (toolchain_ro_mounts, extra_toolchain_mounts) =
            SandboxRuntime::discover_toolchain_mounts(&toolchain_dir, None)?;
        Ok(SandboxRuntime {
            backend: super::ActiveSandbox::LinuxLandlockSeccomp,
            bwrap_path: None,
            bwrap_seccomp_active: false,
            bwrap_disable_userns: false,
            exec_lean: exec_bin,
            toolchain_dir,
            toolchain_ro_mounts,
            extra_toolchain_mounts,
            pt_interp_paths: interps,
            pt_interp_lib_dirs,
            needs_nix_store,
            landlock_abi: abi,
        })
    }

    /// Expose Tier 1 `bwrap` runtime construction directly to integration
    /// escape tests.
    #[doc(hidden)]
    pub fn force_tier1_runtime(
        exec_bin: &Path,
        toolchain_dir: &Path,
    ) -> Result<SandboxRuntime, Failure> {
        let bwrap_path = super::find_bwrap_binary()
            .ok_or_else(|| Failure::operational("sandbox", "bwrap binary not found"))?;
        let exec_bin = fs::canonicalize(exec_bin)
            .map_err(|e| Failure::operational("sandbox", format!("canonicalize exec_bin: {e}")))?;
        let toolchain_dir = fs::canonicalize(toolchain_dir).map_err(|e| {
            Failure::operational("sandbox", format!("canonicalize toolchain_dir: {e}"))
        })?;
        let interps = resolve_pt_interp_paths(&exec_bin).unwrap_or_default();
        let pt_interp_lib_dirs = resolve_pt_interp_lib_dirs(&interps, None)?;
        let needs_nix_store = exec_bin.starts_with("/nix/store")
            || interps.iter().any(|p| p.starts_with("/nix/store"));
        let (toolchain_ro_mounts, extra_toolchain_mounts) =
            SandboxRuntime::discover_toolchain_mounts(&toolchain_dir, None)?;
        let bwrap_disable_userns = bwrap_help_supports_disable_userns(&bwrap_path);
        Ok(SandboxRuntime {
            backend: super::ActiveSandbox::LinuxBwrap,
            bwrap_path: Some(bwrap_path),
            bwrap_seccomp_active: cfg!(any(target_arch = "x86_64", target_arch = "aarch64")),
            bwrap_disable_userns,
            exec_lean: exec_bin,
            toolchain_dir,
            toolchain_ro_mounts,
            extra_toolchain_mounts,
            pt_interp_paths: interps,
            pt_interp_lib_dirs,
            needs_nix_store,
            landlock_abi: 0,
        })
    }
}

#[cfg(target_os = "linux")]
#[doc(hidden)]
pub use linux::{force_tier1_runtime, force_tier2_runtime};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn elf64_pt_interp_parses_current_test_binary() {
        #[cfg(target_os = "linux")]
        {
            let exe = std::env::current_exe().unwrap();
            let interp = parse_elf64_pt_interp(&exe).unwrap();
            if let Some(p) = interp {
                assert!(p.is_absolute(), "expected absolute PT_INTERP path, got {}", p.display());
                assert!(p.exists(), "expected PT_INTERP {} to exist on host", p.display());
            }
        }
    }

    #[test]
    fn elf64_pt_interp_rejects_non_elf_and_truncated_files() {
        let dir = tempfile::tempdir().unwrap();
        let non_elf = dir.path().join("script.sh");
        fs::write(&non_elf, b"#!/bin/sh\necho hi\n").unwrap();
        assert!(parse_elf64_pt_interp(&non_elf).is_err());

        let tiny = dir.path().join("tiny");
        fs::write(&tiny, b"\x7fELF").unwrap();
        assert!(parse_elf64_pt_interp(&tiny).is_err());
    }

    #[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")))]
    #[test]
    fn seccomp_bpf_compiles_within_jump_and_instruction_limits() {
        let compiled = linux::build_seccomp_bpf();
        assert!(compiled.filter.len() > 80);
        assert!(compiled.filter.len() < 4096);
        assert!(compiled.kill_pid_idx < compiled.filter.len());
        assert!(compiled.tgkill_pid_idx < compiled.filter.len());
        assert_ne!(compiled.kill_pid_idx, compiled.tgkill_pid_idx);
        assert_eq!(compiled.filter[compiled.kill_pid_idx].k, 0);
        assert_eq!(compiled.filter[compiled.tgkill_pid_idx].k, 0);
    }

    #[test]
    fn path_mapper_maps_bwrap_roots_and_rejects_unmounted_paths() {
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let real_lib = base.join("real-prefix/lib");
        fs::create_dir_all(real_lib.join("lean")).unwrap();
        let real_init = real_lib.join("lean/Init.olean");
        fs::write(&real_init, b"olean").unwrap();
        let escaped_target = base.join("outside-secret.olean");
        fs::write(&escaped_target, b"secret").unwrap();

        let custom_prefix = base.join("custom-prefix");
        fs::create_dir_all(&custom_prefix).unwrap();
        let sibling_secret = custom_prefix.join("sibling_secret.txt");
        fs::write(&sibling_secret, b"sibling").unwrap();
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(&real_lib, custom_prefix.join("lib")).unwrap();
            std::os::unix::fs::symlink(&escaped_target, real_lib.join("lean/Escape.olean"))
                .unwrap();
        }

        let ro = vec![MountSpec {
            host: PathBuf::from("/tmp/stage/runs/1/in"),
            child: PathBuf::from("/work/in"),
        }];
        let rw_out = MountSpec {
            host: PathBuf::from("/tmp/stage/runs/1/out"),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: PathBuf::from("/tmp/stage/runs/1/tmp"),
            child: PathBuf::from("/work/tmp"),
        };

        for backend in [ActiveSandbox::LinuxBwrap, ActiveSandbox::LinuxLandlockSeccomp] {
            let rt = SandboxRuntime {
                backend,
                bwrap_path: Some(PathBuf::from("/usr/bin/bwrap")),
                bwrap_seccomp_active: true,
                bwrap_disable_userns: true,
                exec_lean: PathBuf::from("/opt/lean/bin/lean"),
                toolchain_dir: custom_prefix.clone(),
                toolchain_ro_mounts: vec![MountSpec {
                    host: real_lib.clone(),
                    child: PathBuf::from("/toolchain/lib"),
                }],
                extra_toolchain_mounts: Vec::new(),
                pt_interp_paths: Vec::new(),
                pt_interp_lib_dirs: Vec::new(),
                needs_nix_store: false,
                landlock_abi: 3,
            };
            let mapper = PathMapper::new(&rt, &ro, &rw_out, &rw_tmp);
            let expected_init = if backend == ActiveSandbox::LinuxBwrap {
                PathBuf::from("/toolchain/lib/lean/Init.olean")
            } else {
                real_init.clone()
            };
            assert_eq!(mapper.map_path(&real_init).unwrap(), expected_init);
            #[cfg(unix)]
            {
                assert_eq!(
                    mapper.map_path(&custom_prefix.join("lib/lean/Init.olean")).unwrap(),
                    expected_init
                );
                assert!(
                    mapper.map_path(&custom_prefix.join("lib/lean/Escape.olean")).is_err(),
                    "symlink escaping mounted lib root must fail closed under {backend:?}"
                );
            }
            let expected_out = if backend == ActiveSandbox::LinuxBwrap {
                PathBuf::from("/work/out/Foo.olean")
            } else {
                PathBuf::from("/tmp/stage/runs/1/out/Foo.olean")
            };
            assert_eq!(
                mapper.map_path(Path::new("/tmp/stage/runs/1/out/Foo.olean")).unwrap(),
                expected_out
            );
            for rejected in [
                Path::new("/etc/passwd"),
                sibling_secret.as_path(),
                Path::new("/tmp/stage/runs/1/in/../../secret"),
            ] {
                assert!(
                    mapper.map_path(rejected).is_err(),
                    "expected {} to fail closed under {backend:?}",
                    rejected.display()
                );
            }
        }
    }

    #[test]
    fn door1_rejects_sidecars_symlinks_hardlinks_subdirs_and_extra_files() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("out");
        let dest = dir.path().join("lib/Foo.olean");
        fs::create_dir_all(&out).unwrap();

        // 1. Forged companion `.olean.private` rejected.
        fs::write(out.join("Foo.olean"), b"ok").unwrap();
        fs::write(out.join("Foo.olean.private"), b"smuggled").unwrap();
        assert!(validate_and_promote_olean(&out, "Foo.olean", &dest).is_err());
        fs::remove_file(out.join("Foo.olean.private")).unwrap();

        // 2. Subdirectory rejected.
        fs::create_dir_all(out.join("sub")).unwrap();
        assert!(validate_and_promote_olean(&out, "Foo.olean", &dest).is_err());
        fs::remove_dir(out.join("sub")).unwrap();

        // 3. Hardlink (`st_nlink > 1`) rejected.
        #[cfg(unix)]
        {
            let link = dir.path().join("outside_link");
            fs::hard_link(out.join("Foo.olean"), &link).unwrap();
            assert!(validate_and_promote_olean(&out, "Foo.olean", &dest).is_err());
            fs::remove_file(&link).unwrap();
        }

        // 4. Symlink rejected.
        #[cfg(unix)]
        {
            fs::remove_file(out.join("Foo.olean")).unwrap();
            let outside = dir.path().join("outside");
            fs::write(&outside, b"outside").unwrap();
            std::os::unix::fs::symlink(&outside, out.join("Foo.olean")).unwrap();
            assert!(validate_and_promote_olean(&out, "Foo.olean", &dest).is_err());
            fs::remove_file(out.join("Foo.olean")).unwrap();
        }

        // 5. Clean singleton regular file with v2 header succeeds and becomes 0o444.
        fs::write(out.join("Foo.olean"), b"olean\x02clean-olean").unwrap();
        let sha = validate_and_promote_olean(&out, "Foo.olean", &dest).unwrap();
        assert_eq!(sha.len(), 64);
        assert!(dest.is_file());
        #[cfg(unix)]
        assert_eq!(fs::metadata(&dest).unwrap().permissions().mode() & 0o777, 0o444);
    }

    #[test]
    fn door1_rejects_non_v2_olean_headers() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("out");
        let dest = dir.path().join("lib/Foo.olean");
        fs::create_dir_all(&out).unwrap();

        for (label, bytes) in [
            ("v3-closure-header", b"olean\x03\x014.34.1\x00".as_slice()),
            ("v1-header", b"olean\x01payload".as_slice()),
            ("truncated-header", b"olean".as_slice()),
            ("empty-file", b"".as_slice()),
            ("arbitrary-bytes", b"not-an-olean".as_slice()),
        ] {
            fs::write(out.join("Foo.olean"), bytes).unwrap();
            let err = validate_and_promote_olean(&out, "Foo.olean", &dest)
                .expect_err(&format!("Door 1 must reject {label}"));
            assert_eq!(err.phase, "door1");
            assert!(!dest.exists(), "rejected {label} must not be promoted");
        }

        // Also verify `validate_and_promote_olean_set` rejects a v3 sidecar.
        let set_out = dir.path().join("set_out");
        let set_dest = dir.path().join("set_lib");
        fs::create_dir_all(&set_out).unwrap();
        fs::write(set_out.join("Mod.olean"), b"olean\x02ok").unwrap();
        fs::write(set_out.join("Mod.olean.server"), b"olean\x03bad").unwrap();
        let promote = BTreeSet::from(["Mod.olean".to_string(), "Mod.olean.server".to_string()]);
        let discard = BTreeSet::new();
        let err =
            validate_and_promote_olean_set(&set_out, &promote, &discard, "Mod.olean", &set_dest)
                .expect_err("Door 1 set must reject v3 sidecar");
        assert_eq!(err.phase, "door1");
        assert!(!set_dest.join("Mod.olean").exists());
    }

    #[test]
    fn door1_inspector_result_handles_empty_valid_and_extra_files() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("out");
        fs::create_dir_all(&out).unwrap();
        assert_eq!(validate_inspector_result(&out, "result.json").unwrap(), None);

        fs::write(out.join("result.json"), b"{\"ok\":true}").unwrap();
        fs::write(out.join("extra.txt"), b"nope").unwrap();
        assert!(validate_inspector_result(&out, "result.json").is_err());
        fs::remove_file(out.join("extra.txt")).unwrap();

        let bytes = validate_inspector_result(&out, "result.json").unwrap().unwrap();
        assert_eq!(bytes, b"{\"ok\":true}");
    }

    #[test]
    fn door1_inspector_result_cap_enforces_default_and_configurable_bounds() {
        assert!(validate_max_inspector_result_bytes(0).unwrap_err().contains("at least 1"));
        assert!(
            validate_max_inspector_result_bytes(MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES + 1)
                .unwrap_err()
                .contains("hard ceiling")
        );
        assert_eq!(validate_max_inspector_result_bytes(1).unwrap(), 1);
        assert_eq!(
            validate_max_inspector_result_bytes(DEFAULT_MAX_INSPECTOR_RESULT_BYTES).unwrap(),
            DEFAULT_MAX_INSPECTOR_RESULT_BYTES
        );
        assert_eq!(
            validate_max_inspector_result_bytes(MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES).unwrap(),
            MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES
        );

        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("out");
        fs::create_dir_all(&out).unwrap();
        let res_path = out.join("result.json");
        fs::write(&res_path, b"{\"ok\":true}").unwrap();

        // Invalid bounds fail closed before opening or reading.
        let err_zero = validate_inspector_result_with_cap(&out, "result.json", 0).unwrap_err();
        assert_eq!(err_zero.phase, "door1");
        assert!(err_zero.message.contains("at least 1"), "{err_zero}");

        let err_ceiling = validate_inspector_result_with_cap(
            &out,
            "result.json",
            MAX_CONFIGURABLE_INSPECTOR_RESULT_BYTES + 1,
        )
        .unwrap_err();
        assert_eq!(err_ceiling.phase, "door1");
        assert!(err_ceiling.message.contains("hard ceiling"), "{err_ceiling}");

        // Small explicit cap rejects larger payload and accepts exact match.
        let err_small = validate_inspector_result_with_cap(&out, "result.json", 10).unwrap_err();
        assert_eq!(err_small.phase, "door1");
        assert!(err_small.message.contains("exceeds size cap"), "{err_small}");
        let exact = validate_inspector_result_with_cap(&out, "result.json", 11).unwrap().unwrap();
        assert_eq!(exact, b"{\"ok\":true}");

        // Sparse 64 MiB + 1 file fails default 64 MiB cap and passes raised
        // 256 MiB cap.
        let f =
            fs::OpenOptions::new().write(true).create(true).truncate(true).open(&res_path).unwrap();
        f.set_len(DEFAULT_MAX_INSPECTOR_RESULT_BYTES + 1).unwrap();
        drop(f);
        let default_err = validate_inspector_result(&out, "result.json").unwrap_err();
        assert_eq!(default_err.phase, "door1");
        assert!(default_err.message.contains("exceeds size cap"), "{default_err}");

        let raised = validate_inspector_result_with_cap(&out, "result.json", 256 * 1024 * 1024)
            .unwrap()
            .unwrap();
        assert_eq!(raised.len() as u64, DEFAULT_MAX_INSPECTOR_RESULT_BYTES + 1);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn execute_with_rlimit_fsize_propagates_custom_limit_to_child() {
        const MODE_ENV: &str = "ANNEAL_SANDBOX_RLIMIT_FSIZE_PROBE";
        if std::env::var_os(MODE_ENV).is_some() {
            let mut rlim = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
            // SAFETY: `rlim` is a valid mutable `libc::rlimit`.
            assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_FSIZE, &mut rlim) }, 0);
            println!("RLIMIT_FSIZE_CUR={}", rlim.rlim_cur);
            return;
        }

        let dir = tempfile::tempdir().unwrap();
        let out_dir = dir.path().join("out");
        let tmp_dir = dir.path().join("tmp");
        fs::create_dir_all(&out_dir).unwrap();
        fs::create_dir_all(&tmp_dir).unwrap();

        let exe = std::env::current_exe().unwrap();
        let rt = SandboxRuntime {
            backend: ActiveSandbox::None,
            bwrap_path: None,
            bwrap_seccomp_active: false,
            bwrap_disable_userns: false,
            exec_lean: exe.clone(),
            toolchain_dir: dir.path().to_path_buf(),
            toolchain_ro_mounts: Vec::new(),
            extra_toolchain_mounts: Vec::new(),
            pt_interp_paths: Vec::new(),
            pt_interp_lib_dirs: Vec::new(),
            needs_nix_store: false,
            landlock_abi: 0,
        };
        let policy = SandboxPolicy {
            exec_bin: exe,
            args: vec![
                "--exact".to_owned(),
                "sandbox::tests::execute_with_rlimit_fsize_propagates_custom_limit_to_child"
                    .to_owned(),
                "--nocapture".to_owned(),
            ],
            ro_mounts: Vec::new(),
            rw_out: MountSpec { host: out_dir, child: PathBuf::from("/work/out") },
            rw_tmp: MountSpec { host: tmp_dir, child: PathBuf::from("/work/tmp") },
            child_cwd: None,
            extra_env: BTreeMap::from([(MODE_ENV.to_owned(), "1".to_owned())]),
            timeout: Duration::from_secs(10),
        };

        let mut host_lim = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
        // SAFETY: `host_lim` is a valid mutable `libc::rlimit`.
        assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_FSIZE, &mut host_lim) }, 0);
        let desired = 128 * 1024u64;
        let expected = if host_lim.rlim_max == libc::RLIM_INFINITY {
            desired
        } else {
            desired.min(host_lim.rlim_max)
        };

        let out = rt.execute_with_rlimit_fsize(&policy, desired).unwrap();
        assert!(out.status.success(), "{out:?}");
        let stdout = String::from_utf8(out.stdout).unwrap();
        let reported: u64 = stdout
            .lines()
            .find_map(|line| {
                line.split_once("RLIMIT_FSIZE_CUR=")
                    .and_then(|(_, rest)| rest.trim().parse::<u64>().ok())
            })
            .unwrap_or_else(|| panic!("missing RLIMIT_FSIZE_CUR marker in stdout: {stdout:?}"));
        assert_eq!(reported, expected);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn rlimit_fsize_headroom_leaves_over_cap_result_above_door1_cap() {
        const OUT_ENV: &str = "ANNEAL_SANDBOX_RLIMIT_HEADROOM_OUT";
        if let Some(dest) = std::env::var_os(OUT_ENV) {
            let mut f = fs::File::create(dest).unwrap();
            let buf = [b'x'; 8192];
            let _ = std::io::Write::write_all(&mut f, &buf);
            return;
        }

        let cap = 4096u64;
        let mut host_lim = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
        // SAFETY: `host_lim` is a valid mutable `libc::rlimit`.
        assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_FSIZE, &mut host_lim) }, 0);
        if host_lim.rlim_max != libc::RLIM_INFINITY && host_lim.rlim_max <= cap {
            return;
        }

        let dir = tempfile::tempdir().unwrap();
        let out_dir = dir.path().join("out");
        let tmp_dir = dir.path().join("tmp");
        fs::create_dir_all(&out_dir).unwrap();
        fs::create_dir_all(&tmp_dir).unwrap();
        let result_path = out_dir.join("result.json");

        let exe = std::env::current_exe().unwrap();
        let rt = SandboxRuntime {
            backend: ActiveSandbox::None,
            bwrap_path: None,
            bwrap_seccomp_active: false,
            bwrap_disable_userns: false,
            exec_lean: exe.clone(),
            toolchain_dir: dir.path().to_path_buf(),
            toolchain_ro_mounts: Vec::new(),
            extra_toolchain_mounts: Vec::new(),
            pt_interp_paths: Vec::new(),
            pt_interp_lib_dirs: Vec::new(),
            needs_nix_store: false,
            landlock_abi: 0,
        };
        let policy = SandboxPolicy {
            exec_bin: exe,
            args: vec![
                "--exact".to_owned(),
                "sandbox::tests::rlimit_fsize_headroom_leaves_over_cap_result_above_door1_cap"
                    .to_owned(),
                "--nocapture".to_owned(),
            ],
            ro_mounts: Vec::new(),
            rw_out: MountSpec { host: out_dir.clone(), child: PathBuf::from("/work/out") },
            rw_tmp: MountSpec { host: tmp_dir, child: PathBuf::from("/work/tmp") },
            child_cwd: None,
            extra_env: BTreeMap::from([(
                OUT_ENV.to_owned(),
                result_path.to_str().unwrap().to_owned(),
            )]),
            timeout: Duration::from_secs(10),
        };

        let out = rt.execute_with_rlimit_fsize(&policy, cap + 1).unwrap();
        assert!(!out.status.success(), "over-cap write should hit RLIMIT_FSIZE: {out:?}");
        let err = validate_inspector_result_with_cap(&out_dir, "result.json", cap).unwrap_err();
        assert_eq!(err.phase, "door1");
        assert!(err.message.contains("exceeds size cap"), "{err}");
    }

    #[test]
    fn door1_olean_set_promotes_allowed_and_discards_ir() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("out");
        let dest_dir = dir.path().join("lib");
        fs::create_dir_all(&out).unwrap();
        fs::write(out.join("Mod.olean"), b"olean\x02mod").unwrap();
        fs::write(out.join("Mod.olean.server"), b"olean\x02server").unwrap();
        fs::write(out.join("Mod.ir"), b"ir").unwrap();
        fs::write(out.join("Mod.ir.sig"), b"irsig").unwrap();
        let promote = BTreeSet::from(["Mod.olean".to_string(), "Mod.olean.server".to_string()]);
        let discard = BTreeSet::from(["Mod.ir".to_string(), "Mod.ir.sig".to_string()]);
        validate_and_promote_olean_set(&out, &promote, &discard, "Mod.olean", &dest_dir).unwrap();
        assert!(dest_dir.join("Mod.olean").is_file());
        assert!(dest_dir.join("Mod.olean.server").is_file());
        assert!(!dest_dir.join("Mod.ir").exists());
        assert!(!dest_dir.join("Mod.ir.sig").exists());
        assert!(!out.join("Mod.ir").exists());
    }

    #[test]
    fn drain_bounded_caps_retained_bytes_and_drains_reader() {
        let payload = vec![b'x'; 20_000];
        let mut cursor = std::io::Cursor::new(payload);
        let sink = Mutex::new(StreamCapture::default());
        drain_bounded_into(&mut cursor, 4096, 100, &sink);
        let capture = sink.into_inner().unwrap();
        assert_eq!(capture.head.len(), 4096);
        assert_eq!(capture.tail.len(), 100);
        assert_eq!(capture.dropped, 20_000 - 4096 - 100);
        assert_eq!(cursor.position(), 20_000);
    }

    #[test]
    fn stream_capture_keeps_true_tail_after_overflow() {
        // Feed in odd-sized pieces so the rolling window crosses chunks.
        let mut text = String::from("head_marker\n");
        for i in 0..2_000 {
            text.push_str(&format!("noise-{i:05}\n"));
        }
        text.push_str("\u{22a2} final_goal\n");
        let mut capture = StreamCapture::default();
        for piece in text.as_bytes().chunks(37) {
            capture.push(piece, 64, 32);
        }
        assert_eq!(capture.head.len(), 64);
        assert_eq!(capture.tail.len(), 32);
        assert_eq!(capture.head.len() + capture.dropped + capture.tail.len(), text.len());
        let rendered = capture.render();
        assert!(rendered.starts_with("head_marker\n"), "{rendered}");
        assert!(rendered.ends_with("\u{22a2} final_goal\n"), "{rendered}");
        assert!(rendered.contains(" bytes not captured] "), "{rendered}");

        // The timeout diagnostic keeps that final tail.
        let msg = timeout_failure(
            Duration::from_secs(1),
            &Mutex::new(capture),
            &Mutex::new(StreamCapture::default()),
        )
        .message;
        assert!(msg.contains("head_marker") && msg.ends_with("\u{22a2} final_goal\n"), "{msg}");

        // Overflow that discards nothing joins head and tail without a gap
        // marker.
        let mut contiguous = StreamCapture::default();
        contiguous.push(b"0123456789", 6, 32);
        assert_eq!((contiguous.dropped, contiguous.tail.len()), (0, 4));
        assert_eq!(contiguous.render(), "0123456789");

        // Without overflow, rendering is just the sanitized head.
        let mut small = StreamCapture::default();
        small.push(b"ok\x1b[0m\n", 64, 32);
        assert_eq!(small.render(), "ok\n");
    }

    #[test]
    fn elide_middle_bounds_length_and_keeps_head_and_tail() {
        // At or under the cap the text is returned unchanged.
        let exact = "x".repeat(60);
        assert_eq!(elide_middle(&exact, 60), exact);
        assert_eq!(elide_middle("", 60), "");

        // One char over the cap elides, staying within the cap.
        let text: String = (0..1000).map(|i| char::from(b'a' + (i % 26) as u8)).collect();
        for max in [61, 100, 999] {
            let out = elide_middle(&text[..max + 1], max);
            assert!(out.chars().count() <= max, "{max}: {out:?}");
            assert!(out.contains(" chars elided] "), "{out:?}");
        }

        // Head is two thirds and tail one third of the post-marker budget,
        // and the reported elided count accounts for every dropped char.
        let out = elide_middle(&text, 100);
        let (head, rest) = out.split_once("\n… [").unwrap();
        let (count, tail) = rest.split_once(" chars elided] …\n").unwrap();
        let elided: usize = count.parse().unwrap();
        assert_eq!(head.len() + elided + tail.len(), text.len());
        assert!(text.starts_with(head) && text.ends_with(tail));
        let budget = head.len() + tail.len();
        assert_eq!(head.len(), budget * 2 / 3);
        assert!(out.chars().count() <= 100);

        // Multibyte characters are never split.
        let multi: String = "⊢é漢🦀".repeat(500);
        let out = elide_middle(&multi, 77);
        assert!(out.chars().count() <= 77);
        assert!(out.starts_with('⊢') && out.ends_with('🦀'), "{out:?}");

        // A cap smaller than the marker degrades to a plain prefix.
        assert_eq!(elide_middle(&multi, 3), "⊢é漢");
    }

    #[test]
    fn sanitize_child_output_strips_escapes_and_controls() {
        let raw = "a\u{1b}[31mb\u{1b}[0m\tc\r\nd\u{7}e\u{1b}]0;title\u{7}f\u{202e}g\
                   \u{9b}1mh\u{1b}(Bi\u{1b}]8;;x\u{1b}\\j\u{0}⊢ k";
        assert_eq!(sanitize_child_output(raw), "ab\tc\ndefghij⊢ k");
        // An unterminated OSC string ends at the next newline.
        assert_eq!(sanitize_child_output("x\u{1b}]bad\ny"), "x\ny");
        // A lone trailing ESC or truncated CSI is dropped without panicking.
        assert_eq!(sanitize_child_output("z\u{1b}"), "z");
        assert_eq!(sanitize_child_output("z\u{1b}[12"), "z");
        // Implicit directional marks (LRM, RLM, ALM) are dropped too.
        assert_eq!(sanitize_child_output("a\u{200e}b\u{200f}c\u{061c}d\u{2067}e"), "abcde");
    }

    #[test]
    fn timeout_failure_omits_streams_with_nothing_visible() {
        let capture = |bytes: &[u8]| {
            let mut capture = StreamCapture::default();
            capture.push(bytes, usize::MAX, 0);
            Mutex::new(capture)
        };
        let detail = |stdout: &[u8], stderr: &[u8]| {
            timeout_failure(Duration::from_secs(1), &capture(stdout), &capture(stderr)).message
        };
        let none = "sandboxed child exceeded wall-clock timeout of 1s; no partial output captured";
        assert_eq!(detail(b"", b""), none);
        assert_eq!(detail(b"", b"\x1b[31m\x1b[0m \r\n"), none);
        assert_eq!(detail(b"\x1b[2J", b"\x07"), none);

        let stderr_only = detail(b"\x1b[0m", b"oops\n");
        assert!(stderr_only.ends_with("middle-elided):\n[stderr]\noops\n"), "{stderr_only}");
        let stdout_only = detail(b"out\n", b"\x1b[31m");
        assert!(stdout_only.ends_with("middle-elided):\nout\n"), "{stdout_only}");
        assert!(!stdout_only.contains("[stderr]"), "{stdout_only}");
        let both = detail(b"out", b"err");
        assert!(both.ends_with("middle-elided):\nout\n[stderr]\nerr"), "{both}");
    }

    #[cfg(unix)]
    #[test]
    fn spawn_and_wait_with_timeout_attaches_sanitized_partial_output() {
        use std::os::unix::process::CommandExt;

        let mut cmd = Command::new("/bin/sh");
        cmd.arg("-c").arg(concat!(
            "printf 'head_marker\\n'; ",
            "printf '\\033[31mred_text\\033[0m\\n'; ",
            "printf 'stderr_marker\\n' >&2; ",
            "i=0; while [ $i -lt 400 ]; do ",
            "printf 'middle-noise-line-%04d\\n' $i; i=$((i+1)); done; ",
            // U+22A2 (`⊢`) as UTF-8 octal escapes.
            "printf '\\342\\212\\242 goal_marker\\n'; ",
            "exec sleep 30",
        ));
        // SAFETY: `setpgid(0, 0)` is async-signal-safe.
        unsafe {
            cmd.pre_exec(|| {
                if libc::setpgid(0, 0) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }

        // The child prints everything within milliseconds and then sleeps,
        // so a 2s limit leaves ample margin on a loaded machine while still
        // proving that the timeout fires long before the 30s sleep ends.
        let start = Instant::now();
        let err = spawn_and_wait_with_timeout(cmd, Duration::from_secs(2), "test", None)
            .expect_err("sleeping child must time out");
        let elapsed = start.elapsed();
        assert!(elapsed < Duration::from_secs(20), "timeout not prompt: {elapsed:?}");
        assert_eq!(err.phase, "sandbox-timeout");
        let msg = &err.message;
        assert!(msg.starts_with("sandboxed child exceeded wall-clock timeout of 2s"), "{msg}");
        for needle in ["head_marker", "red_text", "stderr_marker", "⊢ goal_marker", "chars elided"]
        {
            assert!(msg.contains(needle), "missing {needle:?} in {msg}");
        }
        assert!(!msg.contains('\u{1b}') && !msg.contains("[31m"), "{msg}");
        assert!(msg.chars().count() <= MAX_TIMEOUT_EXCERPT_CHARS + 200, "{}", msg.len());
    }

    #[cfg(unix)]
    #[test]
    fn spawn_and_wait_with_timeout_bounds_inherited_pipe_descendants() {
        use std::{io::Write, os::unix::process::CommandExt};

        const MODE_ENV: &str = "ANNEAL_SANDBOX_PIPE_DESCENDANT_CHILD";
        if let Ok(mode) = std::env::var(MODE_ENV) {
            let escape_session = mode == "setsid";
            let _ = std::io::stdout().write_all(b"leader-out");
            let _ = std::io::stdout().flush();
            let mut sync_pipe = [-1; 2];
            // SAFETY: Helper branch runs async-signal-safe libc calls across
            // `fork()` (`pipe`, `fork`, `setsid`, `close`, `read`, `sleep`,
            // `_exit`), keeping inherited stdout/stderr open in the grandchild
            // until the leader receives `sync_pipe` EOF strictly after any
            // `setsid()`, so the parent cannot `SIGKILL` the leader's process
            // group before `setsid()` runs.
            unsafe {
                if libc::pipe(sync_pipe.as_mut_ptr()) != 0 {
                    libc::_exit(1);
                }
                let pid = libc::fork();
                if pid < 0 {
                    libc::_exit(1);
                }
                if pid == 0 {
                    if escape_session && libc::setsid() < 0 {
                        libc::_exit(1);
                    }
                    let _ = libc::close(sync_pipe[0]);
                    let _ = libc::close(sync_pipe[1]);
                    for fd in 3..256 {
                        let _ = libc::close(fd);
                    }
                    let _ = libc::sleep(if escape_session { 6 } else { 10 });
                    libc::_exit(0);
                }
                let _ = libc::close(sync_pipe[1]);
                let mut byte = [0u8; 1];
                let _ = libc::read(sync_pipe[0], byte.as_mut_ptr().cast(), 1);
                let _ = libc::close(sync_pipe[0]);
                libc::_exit(0);
            }
        }

        let exe = std::env::current_exe().unwrap();
        let make_cmd = |mode: &str| {
            let mut cmd = Command::new(&exe);
            cmd.arg("--exact")
                .arg(
                    "sandbox::tests::spawn_and_wait_with_timeout_bounds_inherited_pipe_descendants",
                )
                .arg("--nocapture")
                .env(MODE_ENV, mode);
            unsafe {
                cmd.pre_exec(|| {
                    if libc::setpgid(0, 0) < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                    Ok(())
                });
            }
            cmd
        };

        // 1. Descendant in the child's process group: leader exit terminates
        //    the process group (or hits the short timeout on non-Linux) and
        //    returns without blocking for 60s.
        let start = Instant::now();
        let out = spawn_and_wait_with_timeout(
            make_cmd("same_pgid"),
            Duration::from_secs(3),
            "test",
            None,
        )
        .expect("same-pgid descendant should be reaped cleanly");
        assert!(out.status.success());
        assert!(
            String::from_utf8_lossy(&out.stdout).contains("leader-out"),
            "missing leader stdout: {:?}",
            String::from_utf8_lossy(&out.stdout)
        );
        assert!(
            start.elapsed() < Duration::from_secs(10),
            "pipe drain hung beyond timeout: {:?}",
            start.elapsed()
        );

        // 2. Descendant that escapes into a new session (`setsid()`) while
        //    holding stdout/stderr open: deadline-bounded pipe draining returns
        //    `sandbox-timeout` rather than hanging indefinitely.
        let start_esc = Instant::now();
        let err =
            spawn_and_wait_with_timeout(make_cmd("setsid"), Duration::from_secs(1), "test", None)
                .expect_err("setsid pipe-holding descendant must time out");
        assert_eq!(err.phase, "sandbox-timeout");
        assert!(
            start_esc.elapsed() < Duration::from_secs(10),
            "escaped pipe drain hung beyond timeout: {:?}",
            start_esc.elapsed()
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn child_exec_path_and_extra_exec_bind_stay_synchronized_across_layouts() {
        let cases = [
            // Standard self-contained installation (`/opt/lean`).
            ("/opt/lean/bin/lean", "/opt/lean", "/opt/lean/lib", false, "/toolchain/bin/lean"),
            // Nix store package where `exec_lean` lives inside `toolchain_dir`.
            (
                "/nix/store/abc-lean-4.34.1/bin/lean",
                "/nix/store/abc-lean-4.34.1",
                "/nix/store/abc-lean-4.34.1/lib",
                true,
                "/toolchain/bin/lean",
            ),
            // Nix `symlinkJoin` wrapper where `exec_lean` resolves to a sibling
            // unwrapped `/nix/store/.../bin/lean` outside `toolchain_dir`.
            (
                "/nix/store/xyz-lean-unwrapped/bin/lean",
                "/nix/store/abc-lean-joined",
                "/nix/store/abc-lean-joined/lib",
                true,
                "/toolchain/bin/lean",
            ),
            // Custom prefix whose `lib` symlink resolves to `/real` (covering
            // `/real/bin/lean` on the host, but mounted at `/toolchain/lib` in
            // the child rather than `/toolchain`).
            ("/real/bin/lean", "/custom/prefix", "/real", false, "/toolchain/bin/lean"),
        ];
        for (exec, prefix, lib_host, nix, expected_child) in cases {
            let rt = SandboxRuntime {
                backend: ActiveSandbox::LinuxBwrap,
                bwrap_path: Some(PathBuf::from("/usr/bin/bwrap")),
                bwrap_seccomp_active: true,
                bwrap_disable_userns: true,
                exec_lean: PathBuf::from(exec),
                toolchain_dir: PathBuf::from(prefix),
                toolchain_ro_mounts: vec![MountSpec {
                    host: PathBuf::from(lib_host),
                    child: PathBuf::from("/toolchain/lib"),
                }],
                extra_toolchain_mounts: Vec::new(),
                pt_interp_paths: Vec::new(),
                pt_interp_lib_dirs: Vec::new(),
                needs_nix_store: nix,
                landlock_abi: 0,
            };
            assert_eq!(rt.child_exec_path(), PathBuf::from(expected_child));
            let bind = rt.extra_exec_bind().expect("expected single-file exec bind");
            assert_eq!(bind.host, PathBuf::from(exec));
            assert_eq!(bind.child, rt.child_exec_path());
        }
    }

    #[test]
    fn reject_forbidden_loader_env_blocks_ld_and_dyld_overrides() {
        let clean = BTreeMap::from([
            ("LEAN_PATH".to_string(), "/work/lib".to_string()),
            ("LANG".to_string(), "C".to_string()),
        ]);
        assert!(reject_forbidden_loader_env(&clean).is_ok());

        for key in [
            "LD_LIBRARY_PATH",
            "LD_PRELOAD",
            "LD_AUDIT",
            "DYLD_LIBRARY_PATH",
            "DYLD_INSERT_LIBRARIES",
        ] {
            let dirty = BTreeMap::from([(key.to_string(), "/evil".to_string())]);
            let err = reject_forbidden_loader_env(&dirty).unwrap_err();
            assert!(err.message.contains(key), "{key}: {err:?}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn resolve_pt_interp_lib_dirs_skips_standard_allows_custom_sysroot_and_rejects_broad_roots() {
        // 1. Standard system paths and `/nix/store` need no extra custom mount.
        let standard = vec![
            PathBuf::from("/lib64/ld-linux-x86-64.so.2"),
            PathBuf::from("/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"),
            PathBuf::from("/nix/store/abc-glibc-2.39/lib/ld-linux-x86-64.so.2"),
        ];
        assert!(resolve_pt_interp_lib_dirs(&standard, None).unwrap().is_empty());

        // 2. A dedicated custom sysroot loader directory outside standard roots
        //    is validated and returned canonically.
        let dir = tempfile::tempdir().unwrap();
        let custom_lib = dir.path().join("custom-sysroot/lib64");
        fs::create_dir_all(&custom_lib).unwrap();
        let custom_loader = custom_lib.join("ld-linux-x86-64.so.2");
        fs::write(&custom_loader, b"loader").unwrap();
        let stage = dir.path().join("stage");
        fs::create_dir_all(&stage).unwrap();

        let resolved =
            resolve_pt_interp_lib_dirs(&[custom_loader], Some(&stage)).unwrap();
        assert_eq!(resolved, vec![fs::canonicalize(&custom_lib).unwrap()]);

        // 3. Broad host roots and stage-overlapping directories must fail closed.
        let stage_loader = stage.join("ld-linux-x86-64.so.2");
        fs::write(&stage_loader, b"loader").unwrap();
        for bad in [
            PathBuf::from("/tmp/ld-linux-x86-64.so.2"),
            PathBuf::from("/usr/ld-linux-x86-64.so.2"),
            stage_loader,
        ] {
            assert!(
                resolve_pt_interp_lib_dirs(std::slice::from_ref(&bad), Some(&stage)).is_err(),
                "expected {} to fail closed",
                bad.display()
            );
        }

        // 4. Symlinked logical `PT_INTERP` parent directories must be validated
        //    just like their canonical targets: valid dedicated symlinked dirs
        //    bind both canonical and logical paths, while symlinks overlapping
        //    `stage_root`, containing `..`, or targeting reserved bwrap roots
        //    (`/work`, `/toolchain`, `/dev`, `/proc`, `/etc`) fail closed.
        let canon_custom_lib = fs::canonicalize(&custom_lib).unwrap();
        let valid_link_dir = dir.path().join("linked-sysroot/lib64");
        fs::create_dir_all(valid_link_dir.parent().unwrap()).unwrap();
        std::os::unix::fs::symlink(&custom_lib, &valid_link_dir).unwrap();
        let valid_link_loader = valid_link_dir.join("ld-linux-x86-64.so.2");
        let resolved_link_dirs =
            resolve_pt_interp_lib_dirs(std::slice::from_ref(&valid_link_loader), Some(&stage))
                .unwrap();
        assert_eq!(resolved_link_dirs, vec![canon_custom_lib.clone()]);
        let bwrap_mounts = resolve_pt_interp_bwrap_mounts(
            std::slice::from_ref(&valid_link_loader),
            &resolved_link_dirs,
            Some(&stage),
        )
        .unwrap();
        assert_eq!(
            bwrap_mounts,
            vec![
                MountSpec { host: canon_custom_lib.clone(), child: canon_custom_lib.clone() },
                MountSpec { host: canon_custom_lib.clone(), child: valid_link_dir },
            ]
        );

        // Symlink inside `stage_root` pointing to valid `custom_lib`: canonical
        // target is outside `stage_root`, so both `resolve_pt_interp_lib_dirs`
        // and `resolve_pt_interp_bwrap_mounts` must still reject the logical
        // parent path.
        let stage_symlink_dir = stage.join("linked-lib64");
        std::os::unix::fs::symlink(&custom_lib, &stage_symlink_dir).unwrap();
        let stage_symlink_loader = stage_symlink_dir.join("ld-linux-x86-64.so.2");
        assert!(
            resolve_pt_interp_lib_dirs(std::slice::from_ref(&stage_symlink_loader), Some(&stage))
                .is_err(),
            "expected symlinked PT_INTERP parent under stage_root to fail closed"
        );
        assert!(
            resolve_pt_interp_bwrap_mounts(
                std::slice::from_ref(&stage_symlink_loader),
                &resolved_link_dirs,
                Some(&stage),
            )
            .is_err(),
            "expected bwrap mount builder to reject symlinked parent under stage_root"
        );

        // Non-normalized `..` path and reserved bwrap child roots must fail closed.
        let traversal_loader =
            dir.path().join("linked-sysroot/sub/../lib64/ld-linux-x86-64.so.2");
        fs::create_dir_all(dir.path().join("linked-sysroot/sub")).unwrap();
        assert!(
            resolve_pt_interp_lib_dirs(std::slice::from_ref(&traversal_loader), Some(&stage))
                .is_err()
        );
        assert!(
            resolve_pt_interp_bwrap_mounts(
                std::slice::from_ref(&traversal_loader),
                &resolved_link_dirs,
                Some(&stage),
            )
            .is_err()
        );
        for reserved in [
            "/work",
            "/work/custom/lib",
            "/toolchain",
            "/toolchain/custom/lib",
            "/dev",
            "/dev/custom/lib",
            "/proc",
            "/proc/custom/lib",
            "/etc",
            "/etc/custom/lib",
        ] {
            let path = PathBuf::from(reserved);
            assert!(
                validate_pt_interp_dir(&path, None, "test").is_err(),
                "expected reserved bwrap root {reserved} to fail closed"
            );
            assert!(
                resolve_pt_interp_bwrap_mounts(&[], std::slice::from_ref(&path), None).is_err(),
                "expected bwrap mount builder to reject reserved root {reserved}"
            );
        }
    }

    #[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")))]
    #[test]
    fn bwrap_seccomp_pipe_contains_complete_pid1_bpf_program() {
        let mut expected = linux::build_seccomp_bpf();
        expected.filter[expected.kill_pid_idx].k = 1;
        expected.filter[expected.tgkill_pid_idx].k = 1;

        let read_fd = linux::prepare_bwrap_seccomp_pipe().unwrap();
        let mut file = fs::File::from(read_fd);
        let mut raw = Vec::new();
        file.read_to_end(&mut raw).unwrap();
        let expected_len = std::mem::size_of_val(expected.filter.as_slice());
        assert_eq!(raw.len(), expected_len);
        assert!(!raw.is_empty() && raw.len() % 8 == 0);
    }
}
