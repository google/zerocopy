// SPDX-License-Identifier: Apache-2.0 OR MIT

// https://doc.rust-lang.org/nightly/cargo/reference/config.html#hierarchical-structure
//
// > Cargo allows local configuration for a particular package as well as global
// > configuration. It looks for configuration files in the current directory
// > and all parent directories. If, for example, Cargo were invoked in
// > `/projects/foo/bar/baz`, then the following configuration files would be
// > probed for and unified in this order:
// >
// > - `/projects/foo/bar/baz/.cargo/config.toml`
// > - `/projects/foo/bar/.cargo/config.toml`
// > - `/projects/foo/.cargo/config.toml`
// > - `/projects/.cargo/config.toml`
// > - `/.cargo/config.toml`
// > - `$CARGO_HOME/config.toml` which defaults to:
// >   - Windows: `%USERPROFILE%\.cargo\config.toml`
// >   - Unix: `$HOME/.cargo/config.toml`

use core::ops;
use std::path::{Path, PathBuf};

fn config_path(path: &Path) -> Option<PathBuf> {
    // https://doc.rust-lang.org/nightly/cargo/reference/config.html#hierarchical-structure
    //
    // > Cargo also reads config files without the `.toml` extension,
    // > such as `.cargo/config`. Support for the `.toml` extension was
    // > added in version 1.39 and is the preferred form. If both files
    // > exist, Cargo will use the file without the extension.
    let config = path.join("config");
    if config.exists() {
        return Some(config);
    }
    let config = path.join("config.toml");
    if config.exists() {
        return Some(config);
    }
    None
}

// Do not use std::env::home_dir only on Windows which std::env::home_dir is not correct.
// https://github.com/rust-lang/cargo/blob/0.80.0/crates/home/src/lib.rs#L65-L72
// Do not use home crate since it is no longer a crate for ecosystem use.
// https://github.com/rust-lang/cargo/pull/14600
// This is needed until MSRV become Rust 1.85: https://github.com/rust-lang/rust/pull/132515
#[cfg(windows)]
pub fn home_dir() -> Option<PathBuf> {
    // Adapted from https://github.com/rust-lang/cargo/blob/0.83.0/crates/home/src/windows.rs.
    use std::{
        env,
        ffi::{OsString, c_void},
        os::windows::ffi::OsStringExt as _,
        ptr, slice,
    };

    use windows_sys::Win32::{
        Foundation::S_OK,
        System::Com::CoTaskMemFree,
        UI::Shell::{FOLDERID_Profile, KF_FLAG_DONT_VERIFY, SHGetKnownFolderPath},
    };

    #[cfg(not(target_vendor = "uwp"))]
    fn home_dir_crt() -> Option<PathBuf> {
        unsafe {
            let mut path = ptr::null_mut();
            match SHGetKnownFolderPath(
                &FOLDERID_Profile,
                KF_FLAG_DONT_VERIFY as u32,
                ptr::null_mut(),
                &mut path,
            ) {
                S_OK => {
                    let path_slice = slice::from_raw_parts(path, wcslen(path));
                    let s = OsString::from_wide(&path_slice);
                    CoTaskMemFree(path.cast::<c_void>());
                    Some(PathBuf::from(s))
                }
                _ => {
                    // Free any allocated memory even on failure. A null ptr is a no-op for `CoTaskMemFree`.
                    CoTaskMemFree(path.cast::<c_void>());
                    None
                }
            }
        }
    }
    #[cfg(target_vendor = "uwp")]
    fn home_dir_crt() -> Option<PathBuf> {
        None
    }
    extern "C" {
        fn wcslen(buf: *const u16) -> usize;
    }

    env::var_os("USERPROFILE").filter(|s| !s.is_empty()).map(PathBuf::from).or_else(home_dir_crt)
}
#[cfg(not(windows))]
pub fn home_dir() -> Option<PathBuf> {
    #[allow(deprecated)]
    std::env::home_dir()
}
pub fn cargo_home_with_cwd(cwd: &Path) -> Option<PathBuf> {
    // Follow the cargo's behavior.
    // https://github.com/rust-lang/cargo/blob/0.80.0/crates/home/src/lib.rs#L77-L86
    // https://github.com/rust-lang/cargo/blob/0.80.0/crates/home/src/env.rs#L63-L77
    match std::env::var_os("CARGO_HOME").filter(|h| !h.is_empty()).map(PathBuf::from) {
        Some(home) => {
            if home.is_absolute() {
                Some(home)
            } else {
                Some(cwd.join(home))
            }
        }
        _ => Some(home_dir()?.join(".cargo")),
    }
}
pub fn rustup_home_with_cwd(cwd: &Path) -> Option<PathBuf> {
    // Follow the cargo's behavior.
    // https://github.com/rust-lang/cargo/blob/0.80.0/crates/home/src/lib.rs#L114-L123
    // https://github.com/rust-lang/cargo/blob/0.80.0/crates/home/src/env.rs#L92-L106
    match std::env::var_os("RUSTUP_HOME").filter(|h| !h.is_empty()).map(PathBuf::from) {
        Some(home) => {
            if home.is_absolute() {
                Some(home)
            } else {
                Some(cwd.join(home))
            }
        }
        _ => Some(home_dir()?.join(".rustup")),
    }
}

/// An iterator over Cargo configuration file paths.
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub(crate) struct WalkInner<'a, P> {
    ancestors: std::path::Ancestors<'a>,
    cargo_home: Option<P>,
}

impl<'a, P: ops::Deref<Target = Path>> WalkInner<'a, P> {
    /// Creates an iterator over Cargo configuration file paths from the given path
    /// and `CARGO_HOME` path.
    pub(crate) fn with_cargo_home(current_dir: &'a Path, cargo_home: Option<P>) -> Self {
        Self { ancestors: current_dir.ancestors(), cargo_home }
    }
}

impl<P: ops::Deref<Target = Path>> Iterator for WalkInner<'_, P> {
    type Item = PathBuf;
    fn next(&mut self) -> Option<Self::Item> {
        for p in self.ancestors.by_ref() {
            let p = p.join(".cargo");
            // dedup CARGO_HOME
            if self.cargo_home.as_deref() == Some(&p) {
                self.cargo_home = None;
            }
            if let Some(p) = config_path(&p) {
                return Some(p);
            }
        }
        config_path(&self.cargo_home.take()?)
    }
}

// TODO: Remove in next breaking release? (if no one using this)
/// An iterator over Cargo configuration file paths.
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Walk<'a>(WalkInner<'a, PathBuf>);

impl<'a> Walk<'a> {
    /// Creates an iterator over Cargo configuration file paths from the given path.
    pub fn new(current_dir: &'a Path) -> Self {
        Self::with_cargo_home(current_dir, cargo_home_with_cwd(current_dir))
    }

    /// Creates an iterator over Cargo configuration file paths from the given path
    /// and `CARGO_HOME` path.
    pub fn with_cargo_home(current_dir: &'a Path, cargo_home: Option<PathBuf>) -> Self {
        Self(WalkInner::with_cargo_home(current_dir, cargo_home))
    }
}

impl Iterator for Walk<'_> {
    type Item = PathBuf;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

#[cfg(test)]
mod tests {
    use fs_err as fs;

    use super::*;

    #[test]
    fn walk() {
        let tmp = tempfile::tempdir().unwrap();
        let p = tmp.path();
        let home = &p.join("a/.cargo");
        let cwd = &p.join("a/b/c");
        fs::create_dir_all(home).unwrap();
        fs::write(p.join("a/.cargo/config"), "").unwrap();
        fs::create_dir_all(p.join("a/b/.cargo")).unwrap();
        fs::write(p.join("a/b/.cargo/config"), "").unwrap();
        fs::write(p.join("a/b/.cargo/config.toml"), "").unwrap();
        fs::create_dir_all(p.join("a/b/c/.cargo")).unwrap();
        fs::write(p.join("a/b/c/.cargo/config.toml"), "").unwrap();
        let mut w = Walk::with_cargo_home(cwd, Some(home.clone()));
        assert_eq!(w.next(), Some(p.join("a/b/c/.cargo/config.toml")));
        assert_eq!(w.next(), Some(p.join("a/b/.cargo/config")));
        assert_eq!(w.next(), Some(p.join("a/.cargo/config")));
        assert_eq!(w.next(), None);
    }
}
