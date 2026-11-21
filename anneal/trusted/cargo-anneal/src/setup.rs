// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Toolchain installation via `exocrate` (`cargo anneal setup`).
//!
//! Manages the versioned omnibus archive containing:
//! - `bin/anneal-rustc-capture`, the standalone MIR capture driver;
//! - `lean/`, the pinned Lean toolchain;
//! - `rust/`, the pinned Rust toolchain (`rustc`, `rust-std`, and `rustc-dev`);
//!   and
//! - `share/anneal/`, the `trusted/lean/` foundation metadata.

use std::path::PathBuf;

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
            return Err("the alpha archive has not been pinned; use --local-archive".into());
        }
        Ok(REMOTE_ARCHIVE)
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
    Err("the downloadable alpha toolchain requires x86-64 Linux with glibc".into())
}

pub(crate) struct InstalledTools {
    pub(crate) capture: PathBuf,
    pub(crate) sysroot: PathBuf,
    pub(crate) lean: PathBuf,
}

/// Resolves the installed toolchain without downloading anything or consulting
/// the working directory for tool paths.
pub(crate) fn installed_tools() -> Result<InstalledTools, String> {
    let root = CONFIG
        .resolve_installation_dir(exocrate::Location::UserGlobal)
        .map_err(|e| format!("toolchain unavailable; run cargo anneal setup: {e}"))?;
    Ok(InstalledTools {
        capture: root.join("bin/anneal-rustc-capture"),
        sysroot: root.join("rust"),
        lean: root.join("lean/bin/lean"),
    })
}

/// Installs or resolves the Anneal toolchain archive in the user-global cache.
///
/// Reuses an installed toolchain for this version. A new installation uses
/// `local_archive` when set or the remote archive recorded in
/// `[[package.metadata.exocrate]]` for the current platform.
pub fn install(local_archive: Option<PathBuf>) -> Result<PathBuf, String> {
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
        None => match remote_archive() {
            Ok(archive) => exocrate::Source::Remote(archive),
            Err(reason) => return CONFIG.resolve_installation_dir(location).map_err(|_| reason),
        },
    };
    CONFIG
        .resolve_installation_dir_or_install(location, source)
        .map(|(dir, _)| dir)
        .map_err(|e| format!("failed to install Anneal toolchain: {e}"))
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

    use super::*;

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

    #[test]
    fn setup_reuses_a_locally_installed_toolchain() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let archive = temp.path().join("toolchain.tar.zst");
        write_archive(&archive);
        let cache = temp.path().join("cache");
        let installed =
            install_at(Some(archive.clone()), exocrate::Location::Custom(cache.clone()))
                .expect("install local archive");
        fs::remove_file(archive).expect("remove original archive");

        assert_eq!(
            install_at(None, exocrate::Location::Custom(cache))
                .expect("reuse the installed toolchain"),
            installed
        );
        if let Err(reason) = remote_archive() {
            let fresh = exocrate::Location::Custom(temp.path().join("fresh-cache"));
            assert_eq!(install_at(None, fresh), Err(reason));
        }
    }
}
