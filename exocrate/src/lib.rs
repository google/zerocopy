// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exocrate: An exoskeleton for your crate.
//!
//! Exocrate is a manager for crate dependencies which are not managed by Cargo
//! itself such as external toolchains, large binary files, etc.
//!
//! Exocrate *assumes*:
//!
//! - An external mechanism that packages external dependencies into a single archive.
//!
//! Exocrate *supports*:
//!
//! - Remote archives loaded by URL and verified by checksum;
//! - Local archives designated by file path.
//!
//! Exocrate *provides* mechanisms to:
//!
//! - Install external dependencies:
//!   - Download and extract an archive;
//!   - Fix up archive artifacts that depend on the installed environment (e.g., rewriting absolute
//!     paths in dependency files);
//!   - Install archive contents in a versioned filesystem location.
//! - Access extracted external dependencies:
//!   - Resolve current installation location.
//!
//! # How exocrate installations are versioned
//!
//! ## Platform + versioned files list
//!
//! The simplest way to auto-version your installations is using macros that tie your installation
//! platform (i.e., `std::env::consts::OS` and `std::env::consts::ARCH` values) and versioning
//! files that will change anytime your external dependencies might. A tool can construct these
//! values directly, or derive them from the macros exported by `exocrate`:
//!
//! ```rust,no_run
//! const CONFIG: exocrate::Config = exocrate::Config {
//!     // Path components that are joined to establish the base directory for all exocrate
//!     // installations.
//!     //
//!     // For `my-tool` developers: `<my-tool-root>/target/.my-tool/exocrate/<version>`
//!     // For `my-tool` users: `~/.my-tool/exocrate/<version>`
//!     rel_dir_path: &[".my-tool", "exocrate"],
//!     version_slug: "example-version",
//! };
//!
//! const REMOTE: exocrate::RemoteArchive = exocrate::RemoteArchive {
//!     sha256: [0xaa; 32],
//!     url: "https://example.com/linux-x86_64.tar.zst",
//! };
//!
//! // FIXME: Detect whether running in tool-installed or tool-development environment. The typical
//! // pattern would be:
//! // - tool-installed => use `exocrate::Location::UserGlobal`,
//! // - tool-development => use `exocrate::Location::LocalDev`.
//! let location: exocrate::Location = exocrate::Location::LocalDev;
//!
//! // FIXME: Use environment detection here too. The typical pattern would be:
//! // - tool-installed => use `exocrate::Source::Remote(REMOTE)`,
//! // - tool-development => use
//! //       `exocrate::Source::Local("/path/to/dep-archive-builder-output.tar.zst".into())`.
//! let source: exocrate::Source = if std::env::var_os("MY_TOOL_DEV").is_some() {
//!     exocrate::Source::Local("tests/my-tool-deps.tar.zst".into())
//! } else {
//!     exocrate::Source::Remote(REMOTE)
//! };
//!
//! // Check whether `source` archive is already installed at `location`, and if not, install it.
//! let (installed_exocrate_dir, _) = CONFIG.resolve_installation_dir_or_install(location, source)
//!     .expect("failed to resolve or install my-tool's exocrate");
//!
//! // Invoke tool installed from `tests/my-tool-deps.tar.zst` extracted to versioned exocrate
//! // directory.
//! let tool_status = std::process::Command::new(installed_exocrate_dir.join("bin").join("tool"))
//!     .status()
//!     .expect("failed to start external dependency located at `bin/tool`");
//! assert!(tool_status.success());
//! ```
//!
//! And in your `Cargo.toml`:
//!
//! ```toml
//! #
//! # Prepares `REMOTE = exocrate::RemoteArchive { sha256, url }` according to compile-time machine
//! # `std::env::consts::OS . std::env::consts::ARCH` listed as supported in your invocation of
//! # `exocrate::parse_remote_archive`.
//! #
//! [package.metadata.exocrate.linux.x86_64]
//! # FIXME: Replace `sha256` with actual linux-x86_64.tar.zst checksum.
//! sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
//! url = "https://example.com/linux-x86_64.tar.zst"
//!
//! [package.metadata.exocrate.macos.x86_64]
//! # FIXME: Replace `sha256` with actual macos-x86_64.tar.zst checksum.
//! sha256 = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
//! url = "https://example.com/macos-x86_64.tar.zst"
//!
//! [package.metadata.exocrate.linux.aarch64]
//! # FIXME: Replace `sha256` with actual linux-aarch64.tar.zst checksum.
//! sha256 = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
//! url = "https://example.com/linux-aarch64.tar.zst"
//!
//! [package.metadata.exocrate.macos.aarch64]
//! # FIXME: Replace `sha256` with actual macos-aarch64.tar.zst checksum.
//! sha256 = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
//! url = "https://example.com/macos-aarch64.tar.zst"
//! ```
//!
//! ### Limitations
//!
//! This versioning strategy does not distinguish between changes to `package.metadata.exocrate` and
//! other changes to `Cargo.toml`. This can result in proliferation of distinct exocrate versions
//! that developers need to clear out if your exocrate is particularly large. This cleanup can be
//! achieved using `cargo clean`.
//!
//! ## Custom versioning
//!
//! Manually constructing an [`Config`] offers you full control over the base directory (relative
//! to one or another [`Location`] for installation) and version string that is used to construct
//! this `Config`'s version of the exocrate. By using this pattern, you takeresponsbility for
//! determining what version of your exocrate corresponds with the code consuming the `exocrate`
//! library.
//!
//! # Limitations
//!
//! Exocrate does not currently support any helpers for cleaning up old versions of your exocrate
//! installations. All installed versions will be stored somewhere inside the directories designated
//! by one of the [`Location`] variants, but there are no other guarantees about how these
//! directory trees are managed at this time.

mod sync;

use std::{
    io::{Read, Result as IoResult},
    path::{Path, PathBuf},
};

use sha2::Digest as _;
use sync::ManagedDirName;

pub struct RemoteArchive {
    pub url: &'static str,
    /// The SHA-256 hash of the file at `url`.
    pub sha256: [u8; 32],
}

pub struct Config {
    /// The relative path of the directory containing dependencies, stored as a
    /// sequence of path components for cross-platform compatibility.
    ///
    /// Dependencies are stored in `<rel_dir_path>`. In production use, this is
    /// relative to the user cache directory. In development, this is relative
    /// to Cargo's `target` directory if it can be resolved, and otherwise relative
    /// relative to the current working directory.
    //
    // FIXME(#3408): Make this non-`pub` and validate at construction that each
    // item is valid for the OS.
    pub rel_dir_path: &'static [&'static str],
    /// A unique identifier for this version of the dependencies.
    pub version_slug: &'static str,
}

/// The location to install dependencies.
pub enum Location {
    /// A location in the user's cache directory.
    UserGlobal,
    /// A location in the Cargo `target` directory if it can be resolved, and
    /// otherwise in the current working directory.
    LocalDev,
    /// A caller-provided base directory.
    Custom(PathBuf),
}

/// The source from which to install dependencies
pub enum Source {
    /// Download the dependencies from the internet.
    Remote(RemoteArchive),
    /// Use a locally available archive.
    Local(PathBuf),
}

/// Whether an installation was resolved or newly installed.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ResolvedOrInstalled {
    /// An existing installation was resolved.
    ResolvedExisting,
    /// A new installation was installed.
    NewlyInstalled,
}

impl Config {
    /// Resolves the dependency directory, failing if it doesn't exist.
    pub fn resolve_installation_dir(&self, location: Location) -> IoResult<PathBuf> {
        let dir_path = self.dir_path(location)?;
        let _ = ManagedDirName::new(&dir_path).check_exists()?;
        Ok(dir_path)
    }

    /// Resolves the dependency directory, installing it if needed.
    pub fn resolve_installation_dir_or_install(
        &self,
        location: Location,
        source: Source,
    ) -> IoResult<(PathBuf, ResolvedOrInstalled)> {
        let dir_path = self.dir_path(location)?;
        if ManagedDirName::new(&dir_path).check_exists().is_ok() {
            return Ok((dir_path, ResolvedOrInstalled::ResolvedExisting));
        }
        let (reader, expected_sha) = self.open_source(source)?;
        install(reader, &dir_path, expected_sha)?;
        Ok((dir_path, ResolvedOrInstalled::NewlyInstalled))
    }

    /// Opens the given source.
    ///
    /// For `Source::Download`, returns the SHA-256 hash which should be used to
    /// validate the downloaded contents.
    fn open_source(&self, source: Source) -> IoResult<(impl Read, Option<[u8; 32]>)> {
        enum SourceReader<D, L> {
            Download(D),
            Local(L),
        }

        impl<D: Read, L: Read> Read for SourceReader<D, L> {
            fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
                match self {
                    Self::Download(r) => r.read(buf),
                    Self::Local(r) => r.read(buf),
                }
            }
        }

        match source {
            Source::Remote(RemoteArchive { url, sha256 }) => {
                let resp = ureq::get(url).call().map_err(std::io::Error::other)?;
                let reader = resp.into_body().into_reader();
                Ok((SourceReader::Download(reader), Some(sha256)))
            }
            Source::Local(path) => {
                let file = std::fs::File::open(path)?;
                Ok((SourceReader::Local(file), None))
            }
        }
    }

    /// Calculates the directory path:
    /// - The parent is the user cache directory for `UserGlobal`,
    ///   `CARGO_MANIFEST_DIR/target` for
    ///   `Local` (or `./target` if `CARGO_MANIFEST_DIR` is not set), and the
    ///   supplied path for `Custom`.
    /// - The remainder is `{self.rel_dir_path}/{self.version_slug}`.
    fn dir_path(&self, location: Location) -> IoResult<PathBuf> {
        let mut parts = match location {
            Location::UserGlobal => dirs::cache_dir().ok_or_else(|| {
                std::io::Error::new(std::io::ErrorKind::NotFound, "cache dir not found")
            })?,
            Location::LocalDev => {
                std::env::var("CARGO_MANIFEST_DIR")
                    .map(PathBuf::from)
                    // Fall back to current directory if `CARGO_MANIFEST_DIR` is
                    // not set, which can happen if the binary is executed
                    // directly rather than via `cargo run`.
                    .unwrap_or_else(|_| std::env::current_dir().unwrap())
                    .join("target")
            }
            Location::Custom(path) => path,
        };

        parts.extend(self.rel_dir_path);
        Ok(parts.join(self.version_slug))
    }
}

/// Extracts the `.tar.zst` from `reader` and installs it at `dst`, optionally
/// validating its hash.
fn install(mut reader: impl Read, dst: &Path, expected_sha256: Option<[u8; 32]>) -> IoResult<()> {
    struct HashingReader<R> {
        reader: R,
        hasher: sha2::Sha256,
    }

    impl<R: std::io::Read> std::io::Read for HashingReader<R> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            let n = self.reader.read(buf)?;
            sha2::Digest::update(&mut self.hasher, &buf[..n]);
            Ok(n)
        }
    }

    sync::ManagedDirName::new(dst)
        .check_exists_or_create(|target_dir| {
            if let Some(expected) = expected_sha256 {
                let mut hash_reader = HashingReader { reader, hasher: sha2::Sha256::new() };
                {
                    let decoder = zstd::stream::read::Decoder::new(&mut hash_reader)?;
                    let mut archive = tar::Archive::new(decoder);
                    archive.unpack(target_dir)?;
                }

                // Ensure any remaining trailing bytes in the stream are read
                // and hashed. Zstd may skip trailing data which isn't necessary
                // to decompress, but we need to account for it in the hash, or
                // else a valid archive could fail to hash properly if that
                // archive contains trailing data which isn't required for
                // decompression.
                std::io::copy(&mut hash_reader, &mut std::io::sink())?;

                let hash: [u8; 32] = sha2::Digest::finalize(hash_reader.hasher).into();
                if hash != expected {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "SHA-256 hash mismatch",
                    ));
                }
            } else {
                let decoder = zstd::stream::read::Decoder::new(&mut reader)?;
                let mut archive = tar::Archive::new(decoder);
                archive.unpack(target_dir)?;
            }
            Ok(())
        })
        .map(|_| ())
}

/// Parses a [`RemoteArchive`] from the `Cargo.toml` at `$cargo_toml_path`.
///
/// The `Cargo.toml` is expected to have content of the form:
///
/// ```toml
/// [package.metadata.exocrate.linux.x86_64]
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/linux-x86_64.tar.zst"
///
/// [package.metadata.exocrate.macos.x86_64]
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/macos-x86_64.tar.zst"
///
/// [package.metadata.exocrate.linux.aarch64]
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/linux-aarch64.tar.zst"
///
/// [package.metadata.exocrate.macos.aarch64]
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/macos-aarch64.tar.zst"
///
/// Example Usage:
/// parse_remote_archive! {
///     const REMOTE: RemoteArchive;
/// }
/// ```
///
#[macro_export]
macro_rules! parse_remote_archive {
    ($vis:vis const $name:ident: RemoteArchive;) => {
        $vis const $name: $crate::RemoteArchive = {
            // Read the calling crate's `Cargo.toml`. `CARGO_MANIFEST_DIR` is expanded
            // at the invocation site, so this always refers to the manifest of the crate
            // using `parse_remote_archive!`, not the crate defining the macro.
            const MANIFEST: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml"));
            const PREFIX: &str = "[package.metadata.exocrate.";

            let Some(header) = $crate::macro_util::find_line(
                MANIFEST,
                ::std::env::consts::OS,
                ::std::env::consts::ARCH,
                PREFIX,
            ) else {
                panic!("unsupported platform")
            };
            let bytes = MANIFEST.as_bytes();
            let mut body_start = header;
            while body_start < bytes.len() && bytes[body_start] != b'\n' {
                body_start += 1;
            }
            if body_start < bytes.len() {
                body_start += 1;
            }

            let Some(url) = $crate::macro_util::find_field(MANIFEST, body_start, "url") else {
                panic!("missing `url` field")
            };
            let Some(sha256_str) =
                $crate::macro_util::find_field(MANIFEST, body_start, "sha256")
            else {
                panic!("missing `sha256` field")
            };
            let Some(sha256) = $crate::macro_util::decode_hex(sha256_str) else {
                panic!("invalid sha256")
            };

            $crate::RemoteArchive { sha256, url }
        };
    };
}

/// Defines a versioned exocrate configuration (a [`Config`])
///
/// This macro must refer to a source of truth that changes whenever the exocrate might change.
/// The recommended pattern for this is to specify your exocrate versioning information inside
/// `Cargo.toml`, and point the config at `Cargo.toml` and `Cargo.lock`.
///
/// ```rust
/// exocrate::config! {
///     const CONFIG: Config = Config {
///         // Path components that are joined to establish the base directory for all exocrate
///         // installations.
///         //
///         // For `my-tool` developers: `<my-tool-root>/target/.my-tool/exocrate/<version>`
///         // For `my-tool` users: `~/.my-tool/exocrate/<version>`
///         rel_dir_path: [".my-tool", "exocrate"],
///         // Since the definition of platform-specific exocrate releases for `my-tool` will be
///         // specified in its `Cargo.toml` file (see below), we use `Cargo.toml` and `Cargo.lock`
///         //  as a "change detector" to change the version.
///         //
///         // This is an over-approximation: unrelated changes to `Cargo.toml` or `Cargo.lock`
///         // (e.g., patch-level version bumps of cargo-managed dependencies, changes in listed
///         // crate dependencies, shipping an exocrate release for some other platform, etc.) will
///         // also change the exocrate version. This is generally not a problem because only
///         // developers of `my-tool` itself need to deal with noisy exocrate version changes;
///         // users will only install versions associated with less frequent releases of
///         // `my-tool`.
///         versioned_files: &["../Cargo.toml", "../Cargo.lock"],
///     };
/// }
/// ```
#[macro_export]
macro_rules! config {
    ($vis:vis const $name:ident: Config = Config {
        rel_dir_path: $rel_dir_path:expr,
        versioned_files: &[ $($path:literal),* $(,)? ] $(,)?
    };) => {
        #[allow(long_running_const_eval)]
        $vis const $name: $crate::Config = {
            $crate::Config {
                rel_dir_path: &$rel_dir_path,
                version_slug: {
                    #[allow(long_running_const_eval)]
                    const HEX: [u8; 64] = {
                        // FIXME(#3411): Pick a reasonably-collision-resistant
                        // hash function that is cheaper to evaluate at const
                        // time and eliminate
                        // `#[allow(long_running_const_eval)]` above.
                        let mut hasher = $crate::macro_util::Sha256::new();
                        $(
                            hasher = hasher.update($path.as_bytes());
                            hasher = hasher.update(include_bytes!($path));
                        )*
                        let hash = hasher
                            .update(std::env::consts::OS.as_bytes())
                            .update(std::env::consts::ARCH.as_bytes())
                            .finalize();
                        $crate::macro_util::encode_hex::<{ 32 }, { 64 }>(&hash)
                    };

                    let Ok(s) = str::from_utf8(&HEX) else {
                        unreachable!()
                    };
                    s
                }
            }
        };
    };
}

#[doc(hidden)]
pub mod macro_util {
    pub use sha2_const::Sha256;

    /// Packs the bytes of `s` into a `u128`.
    ///
    /// # Panics
    ///
    /// Panics if `s.as_bytes().len() > 16`.
    pub const fn pack(s: &str) -> u128 {
        let b = s.as_bytes();
        assert!(b.len() <= 16, "slice too large to pack into u128");

        let mut res = 0u128;
        let mut i = 0;
        while i < b.len() {
            res |= (b[i] as u128) << (i * 8);
            i += 1;
        }
        res
    }

    /// Decodes a hexadecimal string into its byte representation.
    pub const fn decode_hex(s: &str) -> Option<[u8; 32]> {
        let bytes = s.as_bytes();
        if bytes.len() != 64 {
            return None;
        }
        let mut res = [0u8; 32];
        let mut i = 0;
        while i < 32 {
            let (h, l) = (bytes[i * 2], bytes[i * 2 + 1]);
            let h_nib = match decode_nibble(h) {
                Some(n) => n,
                None => return None,
            };
            let l_nib = match decode_nibble(l) {
                Some(n) => n,
                None => return None,
            };
            res[i] = (h_nib << 4) | l_nib;
            i += 1;
        }
        Some(res)
    }

    const fn decode_nibble(c: u8) -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    }

    pub const fn encode_hex<const N: usize, const M: usize>(bytes: &[u8; N]) -> [u8; M] {
        assert!(M == N * 2, "Output buffer must be exactly twice the input length");

        let mut res = [0u8; M];
        const HEX_TABLE: &[u8; 16] = b"0123456789abcdef";

        let mut i = 0;
        while i < N {
            res[i * 2] = HEX_TABLE[(bytes[i] >> 4) as usize];
            res[i * 2 + 1] = HEX_TABLE[(bytes[i] & 0x0f) as usize];
            i += 1;
        }
        res
    }

    #[doc(hidden)]
    pub struct ParsedRemoteArchive<'a> {
        pub url: &'a str,
        pub sha256: &'a str,
    }

    /// Returns `true` if the bytes in `data` starting at `offset` exactly match
    /// `to_search`.
    ///
    /// If `offset + to_search.len()` would exceed the bounds of `data`, this
    /// function returns `false`.
    pub const fn bytes_eq_at(data: &[u8], offset: usize, to_search: &[u8]) -> bool {
        if offset + to_search.len() > data.len() {
            return false;
        }

        let mut i = 0;
        while i < to_search.len() {
            if data[offset + i] != to_search[i] {
                return false;
            }
            i += 1;
        }

        true
    }

    /// Searches `manifest` for a metadata section whose header matches
    /// `prefix`, `os`, and `arch`.
    /// The expected format is `[metadata.exocrate.manifest.{os}.{arch}]`
    pub const fn find_line(manifest: &str, os: &str, arch: &str, prefix: &str) -> Option<usize> {
        let bytes = manifest.as_bytes();
        let os = os.as_bytes();
        let arch = arch.as_bytes();
        let prefix = prefix.as_bytes();

        let mut i = 0;

        while i < bytes.len() {
            // Only consider the beginning of lines.
            if i != 0 && bytes[i - 1] != b'\n' {
                i += 1;
                continue;
            }

            if !bytes_eq_at(bytes, i, prefix) {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                if i < bytes.len() {
                    i += 1;
                }
                continue;
            }

            let mut pos = i + prefix.len();

            if !bytes_eq_at(bytes, pos, os) {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                if i < bytes.len() {
                    i += 1;
                }
                continue;
            }
            pos += os.len();

            if pos >= bytes.len() || bytes[pos] != b'.' {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                if i < bytes.len() {
                    i += 1;
                }
                continue;
            }
            pos += 1;

            if !bytes_eq_at(bytes, pos, arch) {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                if i < bytes.len() {
                    i += 1;
                }
                continue;
            }
            pos += arch.len();

            if pos < bytes.len() && bytes[pos] == b']' {
                return Some(i);
            }

            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            if i < bytes.len() {
                i += 1;
            }
        }

        None
    }

    /// This function finds the `value` for a passed `key` in the passed
    /// `manifest` after starting at `start` offset. It  returns a `None`
    /// variant if it hits a `[` or an `EOF` before finding the key.
    ///
    /// Note: Expected format for key/value pair is:
    /// `Key = "Value"` do mind the spaces otherwise it will return `None`.
    pub const fn find_field<'a>(manifest: &'a str, start: usize, key: &str) -> Option<&'a str> {
        let bytes = manifest.as_bytes();
        let key = key.as_bytes();
        let mut i = start;
        while i < bytes.len() {
            if bytes[i] == b'[' {
                return None;
            }
            if bytes_eq_at(bytes, i, key) {
                let mut pos = i + key.len();
                // expect exactly " = \"" (space, equals, space, quote)
                if pos + 4 <= bytes.len()
                    && bytes[pos] == b' '
                    && bytes[pos + 1] == b'='
                    && bytes[pos + 2] == b' '
                    && bytes[pos + 3] == b'"'
                {
                    pos += 4;
                    let value_start = pos;
                    let mut value_end = value_start;
                    while value_end < bytes.len() && bytes[value_end] != b'"' {
                        value_end += 1;
                    }
                    if value_end < bytes.len() {
                        let (_, rest) = manifest.split_at(value_start);
                        let (value, _) = rest.split_at(value_end - value_start);
                        return Some(value);
                    }
                }
            }
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            if i < bytes.len() {
                i += 1;
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    fn create_dummy_tar_zst(files: &[(&str, &[u8])]) -> Vec<u8> {
        let mut zstd_enc = zstd::stream::write::Encoder::new(Vec::new(), 0).unwrap();
        {
            let mut tar_builder = tar::Builder::new(&mut zstd_enc);
            for (name, content) in files {
                let mut header = tar::Header::new_gnu();
                header.set_size(content.len() as u64);
                header.set_mode(0o644);
                header.set_cksum();
                tar_builder.append_data(&mut header, name, *content).unwrap();
            }
            tar_builder.finish().unwrap();
        }
        zstd_enc.finish().unwrap()
    }

    fn compute_sha256(data: &[u8]) -> [u8; 32] {
        let mut hasher = sha2::Sha256::new();
        hasher.update(data);
        hasher.finalize().into()
    }

    fn dummy_config(rel_dir_path: &'static [&'static str]) -> Config {
        Config { rel_dir_path, version_slug: "slug" }
    }

    #[allow(dead_code)]
    fn dummy_remote() -> RemoteArchive {
        RemoteArchive {
            url: "https://example.com/dummy.tar.zst",
            sha256: compute_sha256(b"dummy content"),
        }
    }

    #[test]
    fn test_install_new() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let tar_zst = create_dummy_tar_zst(&[
            ("hello.txt", b"hello world"),
            ("nested/dir/data.bin", b"\x01\x02\x03"),
        ]);
        let expected_hash = compute_sha256(&tar_zst);

        install(tar_zst.as_slice(), &dst, Some(expected_hash)).unwrap();

        assert!(dst.is_dir());
        assert_eq!(fs::read_to_string(dst.join("hello.txt")).unwrap(), "hello world");
        assert_eq!(fs::read(dst.join("nested/dir/data.bin")).unwrap(), b"\x01\x02\x03");
    }

    #[test]
    fn test_install_without_hash_validation() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let tar_zst = create_dummy_tar_zst(&[("hello.txt", b"hello world")]);

        install(tar_zst.as_slice(), &dst, None).unwrap();

        assert!(dst.is_dir());
        assert_eq!(fs::read_to_string(dst.join("hello.txt")).unwrap(), "hello world");
    }

    #[test]
    fn test_install_invalid_archive() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");

        let invalid_data = b"definitely not a valid zstd or tar";

        let result = install(&invalid_data[..], &dst, None);
        assert!(result.is_err());

        assert!(!dst.exists());
        let entries: Vec<_> = fs::read_dir(temp.path())
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n != "install_target.lock")
            .collect();
        assert!(entries.is_empty());
    }

    #[test]
    fn test_install_already_exists() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        fs::create_dir_all(&dst).unwrap();
        fs::write(dst.join("existing.txt"), "existing content").unwrap();

        // Since dst already exists as a managed directory, install returns early
        // without reading the invalid archive or validating the hash.
        let bad_data = b"invalid archive data";
        let bad_hash = [0u8; 32];
        install(&bad_data[..], &dst, Some(bad_hash)).unwrap();

        assert!(dst.is_dir());
        assert_eq!(fs::read_to_string(dst.join("existing.txt")).unwrap(), "existing content");
    }

    #[test]
    fn test_install_hash_mismatch() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let tar_zst = create_dummy_tar_zst(&[("hello.txt", b"hello world")]);

        let bad_hash = [0u8; 32];

        let result = install(tar_zst.as_slice(), &dst, Some(bad_hash));
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().kind(), std::io::ErrorKind::InvalidData);

        assert!(!dst.exists());
        let entries: Vec<_> = fs::read_dir(temp.path())
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n != "install_target.lock")
            .collect();
        assert!(entries.is_empty());
    }

    #[test]
    fn test_install_trailing_garbage_hash_mismatch() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let valid_tar_zst = create_dummy_tar_zst(&[("hello.txt", b"hello world")]);
        let expected_hash = compute_sha256(&valid_tar_zst);

        // Append trailing garbage to the archive
        let mut corrupted_archive = valid_tar_zst.clone();
        corrupted_archive.extend_from_slice(b"trailing garbage data");

        // Even though the archive unpacks successfully, the trailing bytes should be
        // read and hashed, causing a hash mismatch.
        let result = install(corrupted_archive.as_slice(), &dst, Some(expected_hash));
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().kind(), std::io::ErrorKind::InvalidData);
    }

    #[test]
    fn test_macro_util_encode_hex() {
        let res1 = macro_util::encode_hex::<0, 0>(b"");
        assert_eq!(std::str::from_utf8(&res1).unwrap(), "");

        let res2 = macro_util::encode_hex::<6, 12>(b"\x00\x01\x0a\x0f\x10\xff");
        assert_eq!(std::str::from_utf8(&res2).unwrap(), "00010a0f10ff");
    }

    #[test]
    fn test_macro_util_pack() {
        assert_eq!(macro_util::pack("a"), 0x61);
        assert_eq!(macro_util::pack("ab"), 0x6261);
        assert_eq!(macro_util::pack("linux"), 0x78756e696c);
    }

    #[test]
    #[should_panic(expected = "slice too large to pack into u128")]
    fn test_macro_util_pack_too_large() {
        let _ = macro_util::pack("this_identifier_is_way_too_long");
    }

    #[test]
    fn test_macro_util_decode_hex() {
        let valid_hex = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
        let decoded = macro_util::decode_hex(valid_hex).unwrap();
        assert_eq!(decoded.len(), 32);
        assert_eq!(decoded[0], 0xba);
        assert_eq!(decoded[1], 0x78);
        assert_eq!(decoded[31], 0xad);

        assert!(macro_util::decode_hex("ba78").is_none());
        let invalid_hex = "ga7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
        assert!(macro_util::decode_hex(invalid_hex).is_none());
    }

    #[test]
    fn test_config_dir_path() {
        let config = dummy_config(&["test_dir_path"]);
        let prod_path = config.dir_path(Location::UserGlobal).unwrap();
        assert!(prod_path.starts_with(dirs::cache_dir().unwrap()));
        assert!(prod_path.ends_with(PathBuf::from_iter(["test_dir_path", "slug"])));

        let dev_path = config.dir_path(Location::LocalDev).unwrap();
        assert!(
            dev_path.starts_with(
                std::env::var("CARGO_MANIFEST_DIR")
                    .map(PathBuf::from)
                    .unwrap_or_else(|_| std::env::current_dir().unwrap())
                    .join("target")
            )
        );
        assert!(dev_path.ends_with(PathBuf::from_iter(["test_dir_path", "slug"])));
    }

    #[test]
    fn test_config_resolve_installation_dir() {
        let config = dummy_config(&["test_dir_resolve"]);
        assert!(config.resolve_installation_dir(Location::LocalDev).is_err());

        let dev_path = config.dir_path(Location::LocalDev).unwrap();
        fs::create_dir_all(&dev_path).unwrap();

        let resolved = config.resolve_installation_dir(Location::LocalDev).unwrap();
        assert_eq!(resolved, dev_path);

        fs::remove_dir_all(&dev_path).unwrap();
    }

    #[test]
    fn test_config_resolve_installation_dir_or_install_local() {
        let temp = tempfile::tempdir().unwrap();
        let archive_path = temp.path().join("archive.tar.zst");
        let dummy_tar = create_dummy_tar_zst(&[("bin/compiler", b"binary data")]);
        fs::write(&archive_path, &dummy_tar).unwrap();

        let config = Config { rel_dir_path: &["test_dir_install"], version_slug: "slug" };

        let dev_path = config.dir_path(Location::LocalDev).unwrap();
        let _ = fs::remove_dir_all(&dev_path);

        let (resolved, status) = config
            .resolve_installation_dir_or_install(Location::LocalDev, Source::Local(archive_path))
            .unwrap();
        assert_eq!(resolved, dev_path);
        assert_eq!(status, ResolvedOrInstalled::NewlyInstalled);
        assert!(dev_path.join("bin/compiler").exists());

        let (resolved2, status2) = config
            .resolve_installation_dir_or_install(
                Location::LocalDev,
                Source::Local(PathBuf::from("/nonexistent/path/should/not/be/accessed")),
            )
            .unwrap();
        assert_eq!(resolved2, dev_path);
        assert_eq!(status2, ResolvedOrInstalled::ResolvedExisting);

        fs::remove_dir_all(&dev_path).unwrap();
    }

    #[test]
    fn test_config_open_source_not_found() {
        let config = dummy_config(&["test_open_source"]);
        let res =
            config.open_source(Source::Local(PathBuf::from("/nonexistent/path/file.missing")));
        assert!(res.is_err());
    }

    #[test]
    fn test_config_macro() {
        config! {
            const CONFIG: Config = Config {
                rel_dir_path: ["test", "project"],
                versioned_files: &["../Cargo.toml"],
            };
        }

        assert_eq!(CONFIG.rel_dir_path, &["test", "project"]);
        assert_eq!(CONFIG.version_slug.len(), 64);
    }
}
