// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Toolchain installation and bundle layout via `exocrate`
//! (`cargo anneal setup`).
//!
//! Manages the versioned omnibus archive containing:
//! - `bin/anneal-rustc-capture`, the standalone MIR capture driver;
//! - `lean/`, the pinned Lean toolchain;
//! - `rust/`, the pinned Rust toolchain (`rustc`, `rust-std`, and `rustc-dev`);
//!   and
//! - `share/anneal/`, the `trusted/lean/` foundation metadata.

use std::{
    fs,
    io::{self, IsTerminal as _},
    path::{Path, PathBuf},
};

mod install_dir;
mod lease;
mod prune;
mod reinstall;
#[cfg(test)]
mod tests;

use self::install_dir::resolve_installation_dir;
use self::lease::{AcquireLeaseError, acquire_bundle_lease};
use self::prune::{PruneMode, PruneReport, prompt_stdin_stdout, prune_old_toolchains_with};
use self::reinstall::{install_local, install_remote, resolve_complete_existing};
#[cfg(test)]
use self::install_dir::{
    open_exclusive_lock, remove_temp_dir_best_effort_with, resolve_installation_dir_with,
    sibling_lock_path,
};
#[cfg(test)]
use self::lease::SEED_TAR_ZST;
#[cfg(test)]
use self::prune::{
    RemoveOldOutcome, TryLockOutcome, open_try_exclusive_lock, prompt_on_streams,
    try_remove_old_toolchain,
};
#[cfg(test)]
use self::reinstall::{install_from_source, install_local_with_seed_hook, reinstall_existing};

exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: ["anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
    };
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
exocrate::parse_remote_archive! {
    const REMOTE_ARCHIVE: RemoteArchive = "Cargo.toml";
}

fn remote_archive() -> Result<exocrate::RemoteArchive, String> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
    {
        if REMOTE_ARCHIVE.sha256 == [0; 32] {
            return Err(
                "the alpha archive has not been pinned; use --local-archive <path> \
                 (e.g., build with `nix build .#omnibus-archive` and run \
                 `cargo anneal setup --local-archive result`), or pass --capture, \
                 --sysroot, and --lean directly to `cargo anneal verify`"
                    .into(),
            );
        }
        Ok(REMOTE_ARCHIVE)
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
    Err("the downloadable alpha toolchain requires x86-64 Linux with glibc".into())
}

/// Directory layout of an unpacked Anneal omnibus toolchain bundle.
///
/// When acquired through [`installed_bundle_at`] or an install helper, holds a
/// shared flock on `<slug>.lock` so concurrent `cargo anneal setup` reinstalls
/// and cross-version `--clear-old` pruning treat this toolchain as in use until
/// the caller drops the handle.
#[derive(Debug)]
pub(crate) struct Bundle {
    root: PathBuf,
    _lock: Option<fs::File>,
}

impl Bundle {
    #[cfg(test)]
    fn new(root: PathBuf) -> Self {
        Self { root, _lock: None }
    }

    fn capture(&self) -> PathBuf {
        self.root.join("bin/anneal-rustc-capture")
    }

    fn sysroot(&self) -> PathBuf {
        self.root.join("rust")
    }

    fn lean(&self) -> PathBuf {
        self.root.join("lean/bin/lean")
    }

    pub(crate) fn prebuilt_dir(&self) -> PathBuf {
        self.root.join("share/anneal/prebuilt")
    }
}

/// Installs or resolves the Anneal toolchain archive in the user-global cache
/// and optionally clears older cached toolchain directories.
///
/// Reuses an installed toolchain when `local_archive` is `None` (installing
/// the pinned remote archive when absent and configured). When
/// `local_archive` is `Some(path)`, extracts and atomically installs `path`,
/// replacing an existing installation for this version only after extraction
/// succeeds.
///
/// After resolving the current installation, scans its parent cache directory
/// for older toolchain directories:
/// - When `clear_old` is `true`, removes unlocked old directories immediately
///   without prompting and reports removed paths on stderr.
/// - When `clear_old` is `false` and both stdin and stdout are terminals,
///   lists the old directories on stdout and prompts `[y/N]` before removing.
/// - Otherwise (non-interactive), leaves old directories untouched and prints
///   a note on stderr suggesting `cargo anneal setup --clear-old`.
///
/// Busy locks or cleanup errors on obsolete directories emit warnings on
/// stderr without failing the returned current installation path.
pub fn install(local_archive: Option<PathBuf>, clear_old: bool) -> Result<PathBuf, String> {
    install_with_quiet(local_archive, clear_old, false)
}

/// Like [`install`], suppressing the non-interactive old-toolchain `note:` on
/// `stderr` when `quiet` is `true` (while still emitting operational warnings).
pub fn install_with_quiet(
    local_archive: Option<PathBuf>,
    clear_old: bool,
    quiet: bool,
) -> Result<PathBuf, String> {
    let mode = if clear_old {
        PruneMode::ClearOld
    } else if io::stdin().is_terminal() && io::stdout().is_terminal() {
        PruneMode::Interactive
    } else if quiet {
        PruneMode::NonInteractiveQuiet
    } else {
        PruneMode::NonInteractive
    };
    let (root, _report) = install_at_with_prune(
        local_archive,
        exocrate::Location::UserGlobal,
        mode,
        prompt_stdin_stdout,
        &mut io::stderr(),
    )?;
    Ok(root)
}

/// Installs or resolves the archive at an explicit exocrate location.
///
/// Unit and smoke tests use a fresh `Custom` location for each synthetic local
/// archive. Production setup uses [`install`] -> [`install_at_with_prune`].
#[doc(hidden)]
pub fn install_at(
    local_archive: Option<PathBuf>,
    location: exocrate::Location,
) -> Result<PathBuf, String> {
    install_at_bundle(local_archive, location, remote_archive).map(|bundle| bundle.root)
}

/// Installs or resolves the archive at an explicit exocrate location, then
/// prunes older sibling toolchain directories according to `mode` while
/// holding a shared `<current>.lock` lease on the current installation root.
///
/// Obsolete-directory pruning warnings or busy locks never fail returning the
/// valid current installation root.
pub(crate) fn install_at_with_prune(
    local_archive: Option<PathBuf>,
    location: exocrate::Location,
    mode: PruneMode,
    prompt: impl FnOnce(&Path, &[PathBuf]) -> io::Result<bool>,
    status_out: &mut impl io::Write,
) -> Result<(PathBuf, PruneReport), String> {
    let bundle = install_at_bundle(local_archive, location, remote_archive)?;
    // Keep the shared `<current>.lock` lease alive across the entire pruning
    // pass (including any interactive prompt) so concurrent `setup --clear-old`
    // runs from other `cargo-anneal` versions see this root as busy.
    let report = prune_old_toolchains_with(&bundle.root, mode, prompt, status_out);
    let Bundle { root, _lock } = bundle;
    drop(_lock);
    Ok((root, report))
}

#[cfg(test)]
fn install_at_with_remote(
    local_archive: Option<PathBuf>,
    location: exocrate::Location,
    get_remote: impl Fn() -> Result<exocrate::RemoteArchive, String>,
) -> Result<PathBuf, String> {
    install_at_bundle(local_archive, location, get_remote).map(|bundle| bundle.root)
}

fn install_at_bundle(
    local_archive: Option<PathBuf>,
    location: exocrate::Location,
    get_remote: impl Fn() -> Result<exocrate::RemoteArchive, String>,
) -> Result<Bundle, String> {
    match local_archive {
        Some(path) => install_local(path, location)
            .map_err(|e| format!("failed to install Anneal toolchain: {e}")),
        None => match get_remote() {
            Ok(_) => install_remote(get_remote, location),
            Err(reason) => resolve_complete_existing(location, reason),
        },
    }
}

/// Explicit tool overrides passed to [`resolve_tools`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ToolOverrides {
    pub(crate) capture: Option<PathBuf>,
    pub(crate) sysroot: Option<PathBuf>,
    pub(crate) lean: Option<PathBuf>,
}

/// Resolved capture, sysroot, and Lean locations from [`resolve_tools`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResolvedTools {
    pub(crate) capture: PathBuf,
    pub(crate) sysroot: Option<PathBuf>,
    pub(crate) lean: Option<PathBuf>,
}

/// Resolves capture, Rust sysroot, and Lean paths in one precedence order:
/// explicit override, then `installed` (using bundle `lean/bin/lean` only when
/// it is an existing file), then fallback (`anneal-rustc-capture` beside the
/// running executable for capture; `None` for sysroot and Lean so callers fall
/// back to `default_lean_path` or `rustup`).
///
/// `current_exe` is the result of [`std::env::current_exe`]. Only the capture
/// fallback reads it, and that fallback returns an error when the executable
/// path is unknown or relative.
pub(crate) fn resolve_tools(
    overrides: ToolOverrides,
    installed: Option<&Bundle>,
    current_exe: io::Result<PathBuf>,
) -> Result<ResolvedTools, String> {
    let capture = match overrides.capture.or_else(|| installed.map(Bundle::capture)) {
        Some(capture) => capture,
        None => sibling_capture(current_exe)?,
    };
    Ok(ResolvedTools {
        capture,
        sysroot: overrides.sysroot.or_else(|| installed.map(Bundle::sysroot)),
        lean: overrides
            .lean
            .or_else(|| installed.map(Bundle::lean).filter(|p| p.is_file())),
    })
}

/// Returns the `anneal-rustc-capture` path beside the running executable.
///
/// The sibling of an empty or relative path is itself relative. It would
/// resolve against the working directory, which can be the checkout under
/// verification, and a file there must not run as the trusted capture driver.
fn sibling_capture(current_exe: io::Result<PathBuf>) -> Result<PathBuf, String> {
    let cli = current_exe.map_err(|e| {
        format!("cannot find anneal-rustc-capture beside cargo-anneal: {e}; pass --capture")
    })?;
    if !cli.is_absolute() {
        return Err(format!(
            "cannot find anneal-rustc-capture beside cargo-anneal: executable path {cli:?} is not \
             absolute; pass --capture"
        ));
    }
    Ok(cli.with_file_name("anneal-rustc-capture"))
}

/// Resolves an already installed bundle at `location`, holding a shared flock
/// on `<slug>.lock` for the lifetime of the returned [`Bundle`].
///
/// Returns `Ok(None)` without creating files or directories when no bundle is
/// installed or no user cache base is configured. Fails closed if the resolved
/// path is a symlink or non-directory, or if `<slug>.lock` cannot be opened
/// read-only and shared-locked.
pub(crate) fn installed_bundle_at(location: exocrate::Location) -> Result<Option<Bundle>, String> {
    // Verification discovery must not turn a missing installation into an
    // implicit download or installation. None lets the caller use its explicit
    // development tool or sibling executable instead.
    let dir = match resolve_installation_dir(&location) {
        Ok(dir) => dir,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(err) => {
            return Err(format!("cannot inspect installed Anneal toolchain: {err}"));
        }
    };
    acquire_bundle_lease(&dir)
        .map(Some)
        .map_err(AcquireLeaseError::into_message)
}

/// Resolves an already installed user-global bundle without downloading it.
pub(crate) fn installed_bundle() -> Result<Option<Bundle>, String> {
    installed_bundle_at(exocrate::Location::UserGlobal)
}
