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
    fmt::Write as _,
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    thread,
    time::{Duration, Instant},
};

use sha2::{Digest, Sha256};

use crate::toolchain::Failure;

/// Default wall-clock timeout for a single sandboxed Lean invocation.
pub const DEFAULT_CHILD_TIMEOUT: Duration = Duration::from_secs(600);

/// Maximum bytes retained in memory from each child stdout or stderr stream
/// (16 MiB); excess bytes are still drained and discarded to avoid pipe
/// deadlocks without allowing a hostile child to OOM the host.
pub const MAX_CHILD_STREAM_BYTES: usize = 16 * 1024 * 1024;

/// Door 1 size cap for a single compiled `.olean` output (256 MiB).
pub const MAX_OLEAN_BYTES: u64 = 256 * 1024 * 1024;

/// Required 6-byte magic prefix for standard Lean 4 module `.olean` artifacts
/// (`v2` compacted region without closure relocation).
///
/// Lean 4's extended `v3` format (`b"olean\x03"`) carries relocated function
/// pointers (`allowClosures := true`) intended only for identical-process
/// serialization, never for standard `.olean` compilation outputs. Rejecting
/// non-`v2` headers at Door 1 fails closed before any promoted `.olean` can
/// reach downstream artifact inspection.
pub const OLEAN_V2_MAGIC: &[u8; 6] = b"olean\x02";

/// Door 1 size cap for a single inspector `result.json` output (64 MiB).
pub const MAX_INSPECTOR_RESULT_BYTES: u64 = 64 * 1024 * 1024;

/// Per-child `RLIMIT_FSIZE` cap (256 MiB).
pub const RLIMIT_FSIZE_BYTES: u64 = 256 * 1024 * 1024;

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

/// Dynamic-linker environment variable prefixes forbidden inside sandboxed
/// child `extra_env` maps.
const FORBIDDEN_LOADER_ENV_PREFIXES: &[&str] = &["LD_", "DYLD_"];

/// Refuse any dynamic-linker environment variable (`LD_*`, `DYLD_*`) in a
/// [`SandboxPolicy::extra_env`] map before spawning a child process.
pub fn reject_forbidden_loader_env(extra_env: &BTreeMap<String, String>) -> Result<(), Failure> {
    for key in extra_env.keys() {
        if FORBIDDEN_LOADER_ENV_PREFIXES.iter().any(|prefix| key.starts_with(prefix)) {
            return Err(Failure::operational(
                "sandbox",
                format!("refusing dynamic linker environment variable {key} in sandbox extra_env"),
            ));
        }
    }
    Ok(())
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

/// Derive validated custom read-only loader library directories from an ELF
/// binary's resolved `PT_INTERP` paths.
///
/// Standard system loaders (`/lib64/ld-linux-x86-64.so.2`,
/// `/usr/lib/.../ld-linux-...`, `/nix/store/...`) are already covered by
/// `OPTIONAL_SYS_PATHS` or `/nix/store` and return an empty list. Custom
/// sysroot loaders (such as musl or self-contained glibc sysroots) place their
/// sibling `libc.so.6`/`libm.so.6` alongside `PT_INTERP`; this validates each
/// custom parent directory through [`validate_toolchain_mount_dir`] so broad
/// host prefixes (`/`, `/usr`, `/tmp`, `/home`, `$HOME`, `cwd`, `stage_root`)
/// are refused fail-closed while legitimate dedicated sysroot library
/// directories are mounted strictly read-only.
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
        validate_toolchain_mount_dir(&canon_parent, stage_root, "PT_INTERP loader library directory")?;
        dirs.insert(canon_parent);
    }
    Ok(dirs.into_iter().collect())
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
        match self.backend {
            ActiveSandbox::None => run_unsandboxed(policy),
            #[cfg(target_os = "linux")]
            ActiveSandbox::LinuxBwrap => linux::run_bwrap(self, policy),
            #[cfg(target_os = "linux")]
            ActiveSandbox::LinuxLandlockSeccomp => linux::run_landlock_seccomp(self, policy),
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
                let candidate = Self {
                    backend: ActiveSandbox::LinuxBwrap,
                    bwrap_path: Some(bwrap_path),
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
                    Err(err) => format!("linux_bwrap probe failed: {}", err.message),
                }
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
    fs::create_dir_all(path).map_err(|e| {
        Failure::operational("stage", format!("cannot create {}: {e}", path.display()))
    })?;
    set_mode(path, mode)
}

/// Restore owner write/execute permissions recursively across `root` (without
/// following symlinks) so `fs::remove_dir_all` can delete read-only `0o500`/
/// `0o444` staging subtrees cleanly during `reset_stage()` and `Drop`.
pub fn make_tree_writable(root: &Path) {
    #[cfg(unix)]
    {
        for entry in walkdir::WalkDir::new(root).follow_links(false).into_iter().flatten() {
            let ft = entry.file_type();
            if ft.is_symlink() {
                continue;
            }
            let mode = if ft.is_dir() { 0o700 } else { 0o600 };
            let _ = fs::set_permissions(entry.path(), fs::Permissions::from_mode(mode));
        }
    }
    #[cfg(not(unix))]
    {
        let _ = root;
    }
}

/// Set Unix file or directory mode bits; no-op on non-Unix targets.
pub fn set_mode(path: &Path, mode: u32) -> Result<(), Failure> {
    #[cfg(unix)]
    {
        fs::set_permissions(path, fs::Permissions::from_mode(mode)).map_err(|e| {
            Failure::operational(
                "stage",
                format!("cannot set mode {:o} on {}: {e}", mode, path.display()),
            )
        })?;
    }
    #[cfg(not(unix))]
    {
        let _ = (path, mode);
    }
    Ok(())
}

/// Physically copy a regular file (never hardlinking) and mark the copy
/// read-only (`0o444`).
pub fn copy_readonly_file(src: &Path, dest: &Path, phase: &str) -> Result<(), Failure> {
    if let Some(parent) = dest.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            Failure::operational(phase, format!("cannot create {}: {e}", parent.display()))
        })?;
    }
    let bytes = fs::read(src)
        .map_err(|e| Failure::operational(phase, format!("cannot read {}: {e}", src.display())))?;
    fs::write(dest, bytes).map_err(|e| {
        Failure::operational(phase, format!("cannot write {}: {e}", dest.display()))
    })?;
    set_mode(dest, 0o444)
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
    let entries = collect_out_entries(out_dir, "door1")?;
    let mut saw_required = false;
    let mut opened: Vec<(String, PathBuf, fs::File)> = Vec::with_capacity(entries.len());
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
        if allowed_promote.contains(&name) {
            validate_olean_v2_header(&mut file, &path, "door1")?;
        }
        if name == required_filename {
            saw_required = true;
        }
        opened.push((name, path, file));
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
    for (name, path, file) in opened {
        if allowed_promote.contains(&name) {
            set_file_mode_readonly(&file, &path, "door1")?;
            drop(file);
            let dest = dest_dir.join(&name);
            fs::rename(&path, &dest).map_err(|e| {
                Failure::operational(
                    "door1",
                    format!("cannot promote {} to {}: {e}", path.display(), dest.display()),
                )
            })?;
        } else {
            drop(file);
            let _ = fs::remove_file(&path);
        }
    }
    Ok(())
}

/// Door 1 validator for `TrustedBoundary.lean` inspector invocations.
///
/// Must be called on **both** exit `0` and exit `1`. Returns `Ok(None)` if
/// `out_dir` is empty (for instance if Lean aborted before writing the result),
/// `Ok(Some(bytes))` if `out_dir` contains strictly `expected_filename` as a
/// regular non-hardlinked file `<= MAX_INSPECTOR_RESULT_BYTES`, and fails
/// closed on any extra file, subdirectory, symlink, hardlink, or oversize file.
pub fn validate_inspector_result(
    out_dir: &Path,
    expected_filename: &str,
) -> Result<Option<Vec<u8>>, Failure> {
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
    let mut file = open_validated_out_file(path, MAX_INSPECTOR_RESULT_BYTES, "door1")?;
    let mut bytes = Vec::new();
    let mut limited = (&mut file).take(MAX_INSPECTOR_RESULT_BYTES + 1);
    limited.read_to_end(&mut bytes).map_err(|e| {
        Failure::operational(
            "door1",
            format!("cannot read inspector output {}: {e}", path.display()),
        )
    })?;
    if (bytes.len() as u64) > MAX_INSPECTOR_RESULT_BYTES {
        return Err(Failure::operational(
            "door1",
            format!(
                "sandbox output {} exceeds size cap ({} bytes)",
                path.display(),
                MAX_INSPECTOR_RESULT_BYTES
            ),
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

/// Verify that an opened `.olean` descriptor starts with [`OLEAN_V2_MAGIC`].
///
/// Reading directly from the already-opened `O_NOFOLLOW` descriptor avoids
/// path-based TOCTOU between validation and promotion.
fn validate_olean_v2_header(file: &mut fs::File, path: &Path, phase: &str) -> Result<(), Failure> {
    let mut header = [0u8; 6];
    let mut filled = 0usize;
    while filled < header.len() {
        let n = file.read(&mut header[filled..]).map_err(|e| {
            Failure::operational(phase, format!("cannot read header of {}: {e}", path.display()))
        })?;
        if n == 0 {
            return Err(Failure::operational(
                phase,
                format!(
                    "malformed .olean artifact {}: truncated header ({filled} bytes, expected v2 magic)",
                    path.display()
                ),
            ));
        }
        filled += n;
    }
    if &header != OLEAN_V2_MAGIC {
        return Err(Failure::operational(
            phase,
            format!(
                "unsupported or malformed .olean header in {}: expected v2 magic {:02x?}, got {:02x?}",
                path.display(),
                OLEAN_V2_MAGIC,
                header
            ),
        ));
    }
    Ok(())
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
    if prefix_len < prefix.len() {
        return Err(Failure::operational(
            phase,
            format!(
                "malformed .olean artifact {}: truncated header ({prefix_len} bytes, expected v2 magic)",
                path.display()
            ),
        ));
    }
    if &prefix != OLEAN_V2_MAGIC {
        return Err(Failure::operational(
            phase,
            format!(
                "unsupported or malformed .olean header in {}: expected v2 magic {:02x?}, got {:02x?}",
                path.display(),
                OLEAN_V2_MAGIC,
                prefix
            ),
        ));
    }
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(&mut hex, "{b:02x}");
    }
    Ok(hex)
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
    let mut file = fs::File::open(path).map_err(|e| format!("open {}: {e}", path.display()))?;
    let file_len = file.metadata().map_err(|e| format!("stat {}: {e}", path.display()))?.len();
    if file_len < 64 {
        return Err(format!("{} is smaller than an ELF64 header", path.display()));
    }
    let mut ehdr = [0u8; 64];
    file.read_exact(&mut ehdr).map_err(|e| format!("read ELF header {}: {e}", path.display()))?;
    if &ehdr[0..4] != b"\x7fELF" {
        return Err(format!("{} is not an ELF binary", path.display()));
    }
    if ehdr[4] != 2 || ehdr[5] != 1 {
        return Err(format!(
            "{} is not little-endian ELF64 (class={}, data={})",
            path.display(),
            ehdr[4],
            ehdr[5]
        ));
    }
    let e_phoff = u64::from_le_bytes(ehdr[32..40].try_into().unwrap());
    let e_phentsize = u16::from_le_bytes(ehdr[54..56].try_into().unwrap()) as u64;
    let e_phnum = u16::from_le_bytes(ehdr[56..58].try_into().unwrap()) as u64;
    if e_phnum == 0 {
        return Ok(None);
    }
    if e_phentsize < 56 {
        return Err(format!("invalid ELF64 e_phentsize {e_phentsize} in {}", path.display()));
    }
    let ph_table_bytes = e_phentsize
        .checked_mul(e_phnum)
        .ok_or_else(|| "ELF64 program header table size overflow".to_string())?;
    let ph_end = e_phoff
        .checked_add(ph_table_bytes)
        .ok_or_else(|| "ELF64 program header table end overflow".to_string())?;
    if ph_end > file_len || ph_table_bytes > 4 * 1024 * 1024 {
        return Err(format!("ELF64 program header table out of bounds in {}", path.display()));
    }
    use std::io::{Seek, SeekFrom};
    file.seek(SeekFrom::Start(e_phoff)).map_err(|e| format!("seek phdr table: {e}"))?;
    let mut table = vec![0u8; ph_table_bytes as usize];
    file.read_exact(&mut table).map_err(|e| format!("read phdr table: {e}"))?;
    const PT_INTERP: u32 = 3;
    for i in 0..(e_phnum as usize) {
        let base = i * (e_phentsize as usize);
        let p_type = u32::from_le_bytes(table[base..base + 4].try_into().unwrap());
        if p_type == PT_INTERP {
            let p_offset = u64::from_le_bytes(table[base + 8..base + 16].try_into().unwrap());
            let p_filesz = u64::from_le_bytes(table[base + 32..base + 40].try_into().unwrap());
            if p_filesz == 0 || p_filesz > 4096 {
                return Err(format!("invalid PT_INTERP size {p_filesz}"));
            }
            let end = p_offset
                .checked_add(p_filesz)
                .ok_or_else(|| "PT_INTERP offset overflow".to_string())?;
            if end > file_len {
                return Err("PT_INTERP extends past EOF".to_string());
            }
            file.seek(SeekFrom::Start(p_offset)).map_err(|e| format!("seek PT_INTERP: {e}"))?;
            let mut raw = vec![0u8; p_filesz as usize];
            file.read_exact(&mut raw).map_err(|e| format!("read PT_INTERP: {e}"))?;
            let nul_pos = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
            let s = std::str::from_utf8(&raw[..nul_pos])
                .map_err(|e| format!("non-UTF-8 PT_INTERP: {e}"))?;
            if s.is_empty() {
                return Err("empty PT_INTERP".to_string());
            }
            return Ok(Some(PathBuf::from(s)));
        }
    }
    Ok(None)
}

/// Resolve both the declared `PT_INTERP` path and its canonicalized target (for
/// example `/lib64/ld-linux-x86-64.so.2` and `/usr/lib/.../ld-linux-...`).
pub fn resolve_pt_interp_paths(exec_bin: &Path) -> Result<Vec<PathBuf>, String> {
    let Some(interp) = parse_elf64_pt_interp(exec_bin)? else {
        return Ok(Vec::new());
    };
    let mut paths = vec![interp.clone()];
    if let Ok(canon) = fs::canonicalize(&interp)
        && canon != interp
    {
        paths.push(canon);
    }
    Ok(paths)
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
) -> Result<Output, Failure> {
    cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = cmd
        .spawn()
        .map_err(|e| Failure::operational(label, format!("failed to spawn child: {e}")))?;
    let child_pid = child.id();
    let stdout_pipe = child
        .stdout
        .take()
        .ok_or_else(|| Failure::operational(label, "missing child stdout pipe"))?;
    let stderr_pipe = child
        .stderr
        .take()
        .ok_or_else(|| Failure::operational(label, "missing child stderr pipe"))?;

    let (stdout_tx, stdout_rx) = std::sync::mpsc::sync_channel(1);
    let (stderr_tx, stderr_rx) = std::sync::mpsc::sync_channel(1);
    thread::spawn(move || {
        let _ = stdout_tx.send(drain_bounded(stdout_pipe, MAX_CHILD_STREAM_BYTES));
    });
    thread::spawn(move || {
        let _ = stderr_tx.send(drain_bounded(stderr_pipe, MAX_CHILD_STREAM_BYTES));
    });

    let timeout_failure = || {
        Failure::operational(
            "sandbox-timeout",
            format!("sandboxed child exceeded wall-clock timeout of {}s", timeout.as_secs()),
        )
    };
    let deadline = Instant::now() + timeout;
    let mut stdout_done: Option<Vec<u8>> = None;
    let mut stderr_done: Option<Vec<u8>> = None;
    let mut poll_ms = 1u64;
    let status = loop {
        if stdout_done.is_none()
            && let Ok(bytes) = stdout_rx.try_recv()
        {
            stdout_done = Some(bytes);
        }
        if stderr_done.is_none()
            && let Ok(bytes) = stderr_rx.try_recv()
        {
            stderr_done = Some(bytes);
        }
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
            break Err(timeout_failure());
        }
        thread::sleep(Duration::from_millis(poll_ms));
        poll_ms = (poll_ms * 2).min(25);
    };
    let status = status?;
    let recv_until_deadline = |rx: std::sync::mpsc::Receiver<Vec<u8>>| -> Result<Vec<u8>, Failure> {
        let remaining = deadline.saturating_duration_since(Instant::now());
        match rx.recv_timeout(remaining) {
            Ok(bytes) => Ok(bytes),
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => Ok(Vec::new()),
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => Err(timeout_failure()),
        }
    };
    let stdout = match stdout_done {
        Some(bytes) => bytes,
        None => recv_until_deadline(stdout_rx)?,
    };
    let stderr = match stderr_done {
        Some(bytes) => bytes,
        None => recv_until_deadline(stderr_rx)?,
    };
    Ok(Output { status, stdout, stderr })
}

fn drain_bounded(mut reader: impl Read, limit: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        match reader.read(&mut chunk) {
            Ok(0) | Err(_) => break,
            Ok(n) => {
                if out.len() < limit {
                    let take = (limit - out.len()).min(n);
                    out.extend_from_slice(&chunk[..take]);
                }
            }
        }
    }
    out
}

fn run_unsandboxed(policy: &SandboxPolicy) -> Result<Output, Failure> {
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
            cmd.pre_exec(move || linux::apply_process_hygiene(parent_pid, false));
        }
    }
    #[cfg(all(unix, not(target_os = "linux")))]
    {
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
    spawn_and_wait_with_timeout(cmd, policy.timeout, "unsandboxed-lean")
}

#[cfg(target_os = "linux")]
mod linux {
    use std::{
        ffi::CString,
        fs,
        io::{self, Read},
        os::unix::{ffi::OsStrExt, process::CommandExt},
        path::{Path, PathBuf},
        process::{Command, Output},
    };

    use super::{
        MountSpec, OPTIONAL_SYS_PATHS, PathMapper, RLIMIT_FSIZE_BYTES, RLIMIT_NOFILE_LIMIT,
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
        set_clamped_rlimit!(libc::RLIMIT_FSIZE, RLIMIT_FSIZE_BYTES);
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

    /// Execute `policy` under Tier 1 (`linux_bwrap`).
    pub(super) fn run_bwrap(
        runtime: &SandboxRuntime,
        policy: &SandboxPolicy,
    ) -> Result<Output, Failure> {
        reject_forbidden_loader_env(&policy.extra_env)?;
        let bwrap = runtime.bwrap_path.as_ref().ok_or_else(|| {
            Failure::operational("sandbox", "missing bwrap binary path for LinuxBwrap")
        })?;
        let ro_devs = BwrapRoDevices::create(&policy.rw_out.host)?;
        let mut cmd = Command::new(bwrap);
        cmd.env_clear().env("PATH", "/usr/bin:/bin");
        // Note: `run_bwrap` calls `setsid()` in `pre_exec` (below) rather than
        // passing `--new-session` to `bwrap`. Detaching the controlling
        // terminal before `exec` gives the same TIOCSTI protection while
        // keeping both outer `bwrap` and inner PID 1 in `PGID = bwrap_pid` so
        // `kill(-bwrap_pid, SIGKILL)` atomically tears down the entire PID
        // namespace on wall-clock timeout without relying on
        // `--die-with-parent` alone.
        cmd.args([
            "--unshare-all",
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
        cmd.arg("--ro-bind").arg(&ro_devs.zero).arg("/dev/zero");
        cmd.arg("--ro-bind").arg(&ro_devs.urandom).arg("/dev/urandom");
        cmd.args(["--proc", "/proc"]);
        for sys in OPTIONAL_SYS_PATHS {
            cmd.args(["--ro-bind-try", sys, sys]);
        }
        if runtime.needs_nix_store {
            cmd.args(["--ro-bind-try", "/nix/store", "/nix/store"]);
        }
        for interp_dir in &runtime.pt_interp_lib_dirs {
            cmd.arg("--ro-bind").arg(interp_dir).arg(interp_dir);
        }
        for interp in &runtime.pt_interp_paths {
            if let Some(parent) = interp.parent()
                && parent.is_absolute()
                && !super::is_under_standard_loader_prefix(parent)
                && let Ok(canon_parent) = fs::canonicalize(parent)
                && canon_parent != parent
                && runtime.pt_interp_lib_dirs.contains(&canon_parent)
            {
                cmd.arg("--ro-bind").arg(&canon_parent).arg(parent);
            }
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
        // SAFETY: `apply_process_hygiene` invokes strictly async-signal-safe
        // libc syscalls (`setsid`, `prctl`, `getppid`, `close_range`,
        // `setrlimit`) with zero allocations or locks.
        unsafe {
            cmd.pre_exec(move || apply_process_hygiene(parent_pid, true));
        }
        spawn_and_wait_with_timeout(cmd, policy.timeout, "sandbox-bwrap")
    }

    /// Execute `policy` under Tier 2 (`linux_landlock_seccomp`).
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    pub(super) fn run_landlock_seccomp(
        runtime: &SandboxRuntime,
        policy: &SandboxPolicy,
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
                apply_process_hygiene(parent_pid, true)?;
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
        let res = spawn_and_wait_with_timeout(cmd, policy.timeout, "sandbox-landlock-seccomp");
        drop(ruleset);
        res
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub(super) fn run_landlock_seccomp(
        _runtime: &SandboxRuntime,
        _policy: &SandboxPolicy,
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
        Ok(SandboxRuntime {
            backend: super::ActiveSandbox::LinuxBwrap,
            bwrap_path: Some(bwrap_path),
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
        let retained = drain_bounded(&mut cursor, 4096);
        assert_eq!(retained.len(), 4096);
        assert_eq!(cursor.position(), 20_000);
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
        let out =
            spawn_and_wait_with_timeout(make_cmd("same_pgid"), Duration::from_secs(3), "test")
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
        let err = spawn_and_wait_with_timeout(make_cmd("setsid"), Duration::from_secs(1), "test")
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
    }
}
