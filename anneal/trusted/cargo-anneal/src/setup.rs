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

use std::io;
use std::path::PathBuf;

exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: ["anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
    };
}

exocrate::parse_remote_archive! {
    const REMOTE_ARCHIVE: RemoteArchive = "Cargo.toml";
}

/// Directory layout of an unpacked Anneal omnibus toolchain bundle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Bundle(PathBuf);

impl Bundle {
    fn new(root: PathBuf) -> Self {
        Self(root)
    }

    fn capture(&self) -> PathBuf {
        self.0.join("bin/anneal-rustc-capture")
    }

    fn sysroot(&self) -> PathBuf {
        self.0.join("rust")
    }

    fn lean(&self) -> PathBuf {
        self.0.join("lean/bin/lean")
    }
}

/// Installs or resolves the Anneal toolchain archive in the user-global cache.
///
/// Uses `local_archive` when set, falling back to the remote archive recorded
/// in `[[package.metadata.exocrate]]` for the current platform.
pub(crate) fn install(local_archive: Option<PathBuf>) -> Result<PathBuf, String> {
    install_at(local_archive, exocrate::Location::UserGlobal)
}

/// Installs or resolves the archive at an explicit exocrate location.
///
/// Unit tests use a fresh `Custom` location for each synthetic local archive.
/// Production setup uses the user-global cache above.
pub(crate) fn install_at(
    local_archive: Option<PathBuf>,
    location: exocrate::Location,
) -> Result<PathBuf, String> {
    let source = match local_archive {
        Some(path) => exocrate::Source::Local(path),
        None => exocrate::Source::Remote(REMOTE_ARCHIVE),
    };
    CONFIG
        .resolve_installation_dir_or_install(location, source)
        .map(|(dir, _)| dir)
        .map_err(|e| format!("failed to install Anneal toolchain: {e}"))
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

/// Resolves an already installed bundle without downloading or executing it.
pub(crate) fn installed_bundle() -> Option<Bundle> {
    // Verification discovery must not turn a missing installation into an
    // implicit download or installation. None lets the caller use its
    // explicit development tool or sibling executable instead.
    CONFIG
        .resolve_installation_dir(exocrate::Location::UserGlobal)
        .ok()
        .map(Bundle::new)
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::io;
    use std::path::{Path, PathBuf};

    use super::{Bundle, ToolOverrides, install_at, resolve_tools, sibling_capture};

    /// Return a successful `current_exe` result for a workspace-built CLI.
    fn cli() -> io::Result<PathBuf> {
        Ok(PathBuf::from("/workspace/target/debug/cargo-anneal"))
    }

    /// Return a failed `current_exe` result.
    fn unknown_cli() -> io::Result<PathBuf> {
        Err(io::Error::other("executable path unavailable"))
    }

    fn write_archive(path: &Path) {
        let file = fs::File::create(path).expect("create archive");
        let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
        let mut archive = tar::Builder::new(encoder);
        let contents = b"archive under test";
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(0o644);
        header.set_cksum();
        archive
            .append_data(&mut header, "marker.txt", contents.as_slice())
            .expect("write archive marker");
        archive
            .into_inner()
            .expect("finish tar archive")
            .finish()
            .expect("finish compressed archive");
    }

    #[test]
    fn bundle_paths_follow_omnibus_archive_layout() {
        let bundle = Bundle::new(PathBuf::from("/opt/anneal-bundle"));
        assert_eq!(
            bundle.capture(),
            Path::new("/opt/anneal-bundle/bin/anneal-rustc-capture")
        );
        assert_eq!(bundle.sysroot(), Path::new("/opt/anneal-bundle/rust"));
        assert_eq!(bundle.lean(), Path::new("/opt/anneal-bundle/lean/bin/lean"));
    }

    #[test]
    fn resolve_tools_prefers_explicit_then_installed_then_sibling() {
        let bundle_dir = tempfile::tempdir().expect("create synthetic bundle");
        let installed = Bundle::new(bundle_dir.path().to_path_buf());
        fs::create_dir_all(installed.lean().parent().unwrap()).expect("create lean bin dir");
        fs::write(installed.lean(), b"lean").expect("write synthetic lean binary");

        let explicit = resolve_tools(
            ToolOverrides {
                capture: Some(PathBuf::from("/explicit/capture")),
                sysroot: Some(PathBuf::from("/explicit/sysroot")),
                lean: Some(PathBuf::from("/explicit/lean")),
            },
            Some(&installed),
            cli(),
        )
        .expect("resolve explicit tools");
        assert_eq!(explicit.capture, Path::new("/explicit/capture"));
        assert_eq!(
            explicit.sysroot.as_deref(),
            Some(Path::new("/explicit/sysroot"))
        );
        assert_eq!(explicit.lean.as_deref(), Some(Path::new("/explicit/lean")));

        let from_installed = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
            .expect("resolve installed tools");
        assert_eq!(from_installed.capture, installed.capture());
        assert_eq!(from_installed.sysroot, Some(installed.sysroot()));
        assert_eq!(from_installed.lean, Some(installed.lean()));

        let fallback =
            resolve_tools(ToolOverrides::default(), None, cli()).expect("resolve sibling capture");
        assert_eq!(
            fallback.capture,
            Path::new("/workspace/target/debug/anneal-rustc-capture")
        );
        assert_eq!(fallback.sysroot, None);
        assert_eq!(fallback.lean, None);
    }

    #[test]
    fn resolve_tools_falls_back_when_installed_bundle_lacks_lean() {
        let bundle_dir = tempfile::tempdir().expect("create bundle without lean");
        let installed = Bundle::new(bundle_dir.path().to_path_buf());

        let without_lean = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
            .expect("resolve installed tools");
        assert_eq!(without_lean.capture, installed.capture());
        assert_eq!(without_lean.sysroot, Some(installed.sysroot()));
        assert_eq!(without_lean.lean, None);

        let with_override = resolve_tools(
            ToolOverrides {
                lean: Some(PathBuf::from("/explicit/lean")),
                ..ToolOverrides::default()
            },
            Some(&installed),
            cli(),
        )
        .expect("resolve explicit Lean");
        assert_eq!(
            with_override.lean.as_deref(),
            Some(Path::new("/explicit/lean"))
        );

        fs::create_dir_all(installed.lean().parent().unwrap()).expect("create lean bin dir");
        fs::write(installed.lean(), b"lean").expect("write synthetic lean binary");
        let with_lean = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
            .expect("resolve installed Lean");
        assert_eq!(with_lean.lean, Some(installed.lean()));
    }

    #[test]
    fn sibling_capture_requires_an_absolute_executable_path() {
        let unknown = sibling_capture(unknown_cli())
            .expect_err("an unknown executable must not select a capture driver");
        assert!(
            unknown.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
            "{unknown}"
        );
        assert!(unknown.contains("executable path unavailable"), "{unknown}");

        // Each sibling would be a relative path resolved in the working
        // directory, where the checkout under verification may provide it.
        for relative in [
            "",
            "cargo-anneal",
            "./cargo-anneal",
            "target/debug/cargo-anneal",
        ] {
            let failure = sibling_capture(Ok(PathBuf::from(relative)))
                .expect_err("a relative executable must not select a capture driver");
            assert!(
                failure.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
                "{relative:?}: {failure}"
            );
            assert!(
                failure.contains("is not absolute"),
                "{relative:?}: {failure}"
            );
        }

        assert_eq!(
            sibling_capture(cli()),
            Ok(PathBuf::from(
                "/workspace/target/debug/anneal-rustc-capture"
            ))
        );
    }

    #[test]
    fn resolve_tools_needs_the_executable_path_only_for_the_sibling() {
        let explicit = resolve_tools(
            ToolOverrides {
                capture: Some(PathBuf::from("/explicit/capture")),
                ..ToolOverrides::default()
            },
            None,
            unknown_cli(),
        )
        .expect("an explicit capture driver needs no executable path");
        assert_eq!(explicit.capture, Path::new("/explicit/capture"));

        let bundle_dir = tempfile::tempdir().expect("create synthetic bundle");
        let installed = Bundle::new(bundle_dir.path().to_path_buf());
        let from_installed =
            resolve_tools(ToolOverrides::default(), Some(&installed), unknown_cli())
                .expect("an installed capture driver needs no executable path");
        assert_eq!(from_installed.capture, installed.capture());

        for current_exe in [
            unknown_cli(),
            Ok(PathBuf::new()),
            Ok(PathBuf::from("cargo-anneal")),
        ] {
            let failure = resolve_tools(ToolOverrides::default(), None, current_exe)
                .expect_err("the sibling fallback must fail closed");
            assert!(
                failure.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
                "{failure}"
            );
        }
    }

    #[test]
    fn custom_locations_install_only_the_requested_archive() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let archive = temp.path().join("current-run.tar.zst");
        write_archive(&archive);
        let ordinary = temp.path().join("ordinary-cache");
        let root = install_at(Some(archive), exocrate::Location::Custom(ordinary.clone()))
            .expect("install requested local archive");
        assert!(root.starts_with(&ordinary), "{}", root.display());
        assert_eq!(
            fs::read(root.join("marker.txt")).expect("read installed marker"),
            b"archive under test"
        );

        for (name, contents) in [("missing", None), ("broken", Some(b"bad"))] {
            let archive = temp.path().join(format!("{name}.tar.zst"));
            if let Some(contents) = contents {
                fs::write(&archive, contents).expect("write broken archive");
            }
            let fresh = temp.path().join(format!("{name}-cache"));
            let error = install_at(Some(archive), exocrate::Location::Custom(fresh))
                .expect_err("another location's installation must not satisfy setup");
            assert!(error.contains("failed to install Anneal toolchain"));
        }

        assert_eq!(
            fs::read(root.join("marker.txt")).expect("ordinary cache survives"),
            b"archive under test"
        );
    }
}
