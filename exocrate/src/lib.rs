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
//! - Remote archives loaded by URL and verified by SHA-256 checksum;
//! - Offline/pre-fetched local archives designated by file path and verified by
//!   SHA-256 checksum (`Source::VerifiedLocal`);
//! - Unverified local development archives designated by file path
//!   (`Source::Local`).
//!
//! Fetching and installing archives requires the default `host-fetch` feature.
//! Without it, only the pure-Rust verification core is available.
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
//! const CONFIG: exocrate::Config = exocrate::Config::new (
//!     // Path components that are joined to establish the base directory for all exocrate
//!     // installations.
//!     //
//!     // For `my-tool` developers: `<my-tool-root>/target/.my-tool/exocrate/<version>`
//!     // For `my-tool` users: `~/.my-tool/exocrate/<version>`
//!     &[".my-tool", "exocrate"],
//!     "example-version",
//! );
//!
//! const REMOTE: exocrate::RemoteArchive = exocrate::RemoteArchive {
//!     sha256: [0xaa; 32],
//!     url: "https://example.com/linux-x86_64.tar.zst",
//! };
//!
//! # #[cfg(feature = "host-fetch")] {
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
//! # }
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
//!
//! [[package.metadata.exocrate]]
//! os = "linux"
//! arch = "x86_64"
//! sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
//! url = "https://example.com/linux-x86_64.tar.zst"
//!
//! [[package.metadata.exocrate]]
//! os = "macos"
//! arch = "x86_64"
//! sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
//! url = "https://example.com/macos-x86_64.tar.zst"
//!
//! [[package.metadata.exocrate]]
//! os = "linux"
//! arch = "aarch64"
//! sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
//! url = "https://example.com/linux-aarch64.tar.zst"
//!
//! [[package.metadata.exocrate]]
//! os = "macos"
//! arch = "aarch64"
//! sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
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
//! to one or another `Location` for installation) and version string that is used to construct
//! this `Config`'s version of the exocrate. By using this pattern, you takeresponsbility for
//! determining what version of your exocrate corresponds with the code consuming the `exocrate`
//! library.
//!
//! # Limitations
//!
//! Exocrate does not currently support any helpers for cleaning up old versions of your exocrate
//! installations. All installed versions will be stored somewhere inside the directories designated
//! by one of the `Location` variants, but there are no other guarantees about how these
//! directory trees are managed at this time.

#[cfg(feature = "host-fetch")]
mod sync;

use std::{
    collections::HashSet,
    io::{Read, Result as IoResult},
};
#[cfg(feature = "host-fetch")]
use std::{
    ffi::OsString,
    io::Seek as _,
    path::{Path, PathBuf},
};

use sha2::Digest as _;
#[cfg(feature = "host-fetch")]
use sync::ManagedDirName;

pub struct RemoteArchive {
    pub url: &'static str,
    /// The SHA-256 hash of the file at `url`.
    pub sha256: [u8; 32],
}

/// A local archive path paired with the expected SHA-256 digest of its
/// compressed bytes, enabling airgapped or mirror-backed installation with the
/// same pre-decompression integrity check as [`RemoteArchive`].
#[cfg(feature = "host-fetch")]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedLocalArchive {
    pub path: PathBuf,
    /// The expected SHA-256 hash of the archive at `path`.
    pub sha256: [u8; 32],
}

pub struct Config {
    rel_dir_path: &'static [&'static str],
    version_slug: &'static str,
}

/// Runtime-constructed counterpart to [`Config`] for archive installations
/// whose cache directory components or version slug are resolved dynamically
/// from manifests or content digests rather than compile-time constants.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DynamicConfig {
    rel_dir_path: Vec<String>,
    version_slug: String,
}

/// The location to install dependencies.
#[cfg(feature = "host-fetch")]
pub enum Location {
    /// A location in the user's cache directory.
    UserGlobal,
    /// A location in the Cargo `target` directory if it can be resolved, and
    /// otherwise in the current working directory.
    LocalDev,
    /// A caller-provided base directory.
    Custom(PathBuf),
}

/// The source from which to install dependencies.
#[cfg(feature = "host-fetch")]
pub enum Source {
    /// Download the dependencies from the internet and verify their SHA-256.
    Remote(RemoteArchive),
    /// Install from a locally available archive after verifying its SHA-256
    /// before decompression (for offline mirrors, vendored CIPD/Nix archives,
    /// or pre-fetched toolchains).
    VerifiedLocal(VerifiedLocalArchive),
    /// Use a locally available archive without a pinned digest check (for
    /// local development builds).
    Local(PathBuf),
}

#[cfg(feature = "host-fetch")]
impl Source {
    /// Resolves a [`RemoteArchive`] against an optional local offline mirror
    /// directory before falling back to network download.
    ///
    /// When `mirror_dir` is `Some(dir)`, extracts the trailing archive file
    /// name from `remote.url`, validates that it is a single cross-platform
    /// path component, and returns [`Source::VerifiedLocal`] bound to
    /// `remote.sha256` with zero network I/O.
    pub fn from_remote_or_mirror(
        remote: RemoteArchive,
        mirror_dir: Option<&Path>,
    ) -> IoResult<Self> {
        let Some(dir) = mirror_dir else {
            return Ok(Self::Remote(remote));
        };
        let url_without_query = remote.url.split(['?', '#']).next().unwrap_or(remote.url);
        // The file name is the last segment of the URL's path, never its
        // authority (`https://example.com` has no file name).
        let after_scheme =
            url_without_query.split_once("://").map_or(url_without_query, |(_, rest)| rest);
        let Some((_authority, path)) = after_scheme.split_once('/') else {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "remote archive URL has no path to name a mirrored file",
            ));
        };
        let file_name = path.rsplit('/').next().unwrap_or("");
        if let Err(reason) = check_path_component(file_name) {
            return Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, reason));
        }
        Ok(Self::VerifiedLocal(VerifiedLocalArchive {
            path: dir.join(file_name),
            sha256: remote.sha256,
        }))
    }
}

/// Whether an installation was resolved or newly installed.
#[cfg(feature = "host-fetch")]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ResolvedOrInstalled {
    /// An existing installation was resolved.
    ResolvedExisting,
    /// A new installation was installed.
    NewlyInstalled,
}

impl Config {
    /// Resolves the dependency directory, failing if it doesn't exist.
    #[cfg(feature = "host-fetch")]
    pub fn resolve_installation_dir(&self, location: Location) -> IoResult<PathBuf> {
        let dir_path = self.dir_path(location)?;
        let _ = ManagedDirName::new(&dir_path).check_exists()?;
        Ok(dir_path)
    }

    /// Resolves the dependency directory, installing it if needed.
    #[cfg(feature = "host-fetch")]
    pub fn resolve_installation_dir_or_install(
        &self,
        location: Location,
        source: Source,
    ) -> IoResult<(PathBuf, ResolvedOrInstalled)> {
        let dir_path = self.dir_path(location)?;
        let state = install_if_missing(&dir_path, source)?;
        Ok((dir_path, state))
    }

    /// Opens the given source.
    ///
    /// For [`Source::Remote`] and [`Source::VerifiedLocal`], returns the
    /// SHA-256 digest that must be verified before decompressing the archive.
    #[cfg(all(test, feature = "host-fetch"))]
    fn open_source(&self, source: Source) -> IoResult<(impl Read, Option<[u8; 32]>)> {
        open_archive_source(source)
    }

    /// Calculates the directory path:
    /// - The parent is the user cache directory for `UserGlobal`,
    ///   `CARGO_MANIFEST_DIR/target` for
    ///   `Local` (or `./target` if `CARGO_MANIFEST_DIR` is not set), and the
    ///   supplied path for `Custom`.
    /// - The remainder is `{self.rel_dir_path}/{self.version_slug}`.
    #[cfg(feature = "host-fetch")]
    fn dir_path(&self, location: Location) -> IoResult<PathBuf> {
        resolve_base_dir(location, self.rel_dir_path.iter().copied(), self.version_slug)
    }

    /// Returns the validated relative path components for this configuration.
    pub const fn rel_dir_path(&self) -> &'static [&'static str] {
        self.rel_dir_path
    }

    /// Returns the validated version slug for this configuration.
    pub const fn version_slug(&self) -> &'static str {
        self.version_slug
    }

    /// Creates a new `Config` after validating `rel_dir_path` and
    /// `version_slug`.
    ///
    /// `rel_dir_path` is the relative path of the directory
    /// containing the dependencies, stored as a sequence of path
    /// components for cross-platform compatibility.
    ///
    /// Dependencies are stored in `<rel_dir_path>`. In production
    /// use, this is relative to the user cache directory. In
    /// development, this is relative to Cargo's `target` directory
    /// if it can be resolved, and otherwise relative to the current
    /// working directory.
    ///
    /// `version_slug` is a unique identifier for this version of
    /// the dependencies.
    pub const fn new(rel_dir_path: &'static [&'static str], version_slug: &'static str) -> Self {
        let mut i = 0;
        while i < rel_dir_path.len() {
            validate_path(rel_dir_path[i]);
            i += 1;
        }
        // `version_slug` is joined onto the path in `dir_path` exactly like a
        // `rel_dir_path` component, so it needs the same validation.
        validate_path(version_slug);

        Self { rel_dir_path, version_slug }
    }
}

impl DynamicConfig {
    /// Creates a runtime [`DynamicConfig`] after validating every component of
    /// `rel_dir_path` and `version_slug` against the cross-platform path rules.
    pub fn try_new<I, S>(rel_dir_path: I, version_slug: impl Into<String>) -> IoResult<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut validated_dirs = Vec::new();
        for component in rel_dir_path {
            let component = component.into();
            if let Err(reason) = check_path_component(&component) {
                return Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, reason));
            }
            validated_dirs.push(component);
        }
        let version_slug = version_slug.into();
        if let Err(reason) = check_path_component(&version_slug) {
            return Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, reason));
        }
        Ok(Self { rel_dir_path: validated_dirs, version_slug })
    }

    /// Returns the validated relative path components for this configuration.
    pub fn rel_dir_path(&self) -> &[String] {
        &self.rel_dir_path
    }

    /// Returns the validated version slug for this configuration.
    pub fn version_slug(&self) -> &str {
        &self.version_slug
    }

    /// Resolves the dependency directory, failing if it does not exist.
    #[cfg(feature = "host-fetch")]
    pub fn resolve_installation_dir(&self, location: Location) -> IoResult<PathBuf> {
        let dir_path = self.dir_path(location)?;
        let _ = ManagedDirName::new(&dir_path).check_exists()?;
        Ok(dir_path)
    }

    /// Resolves the dependency directory, installing it if needed.
    #[cfg(feature = "host-fetch")]
    pub fn resolve_installation_dir_or_install(
        &self,
        location: Location,
        source: Source,
    ) -> IoResult<(PathBuf, ResolvedOrInstalled)> {
        let dir_path = self.dir_path(location)?;
        let state = install_if_missing(&dir_path, source)?;
        Ok((dir_path, state))
    }

    #[cfg(feature = "host-fetch")]
    fn dir_path(&self, location: Location) -> IoResult<PathBuf> {
        resolve_base_dir(location, self.rel_dir_path.iter().map(String::as_str), &self.version_slug)
    }
}

#[cfg(feature = "host-fetch")]
fn install_if_missing(dir_path: &Path, source: Source) -> IoResult<ResolvedOrInstalled> {
    if ManagedDirName::new(dir_path).check_ready_or_absent()?.is_some() {
        return Ok(ResolvedOrInstalled::ResolvedExisting);
    }
    let (reader, expected_sha) = open_archive_source(source)?;
    install(reader, dir_path, expected_sha)?;
    Ok(ResolvedOrInstalled::NewlyInstalled)
}

#[cfg(feature = "host-fetch")]
fn resolve_local_dev_root(
    manifest_dir: Option<OsString>,
    cwd: impl FnOnce() -> IoResult<PathBuf>,
) -> IoResult<PathBuf> {
    match manifest_dir {
        Some(dir) if !dir.is_empty() => Ok(PathBuf::from(dir)),
        // Fall back to the current directory if `CARGO_MANIFEST_DIR` is unset
        // or empty, which can happen if the binary is executed directly rather
        // than via Cargo.
        Some(_) | None => cwd(),
    }
}

#[cfg(feature = "host-fetch")]
fn resolve_base_dir<'a>(
    location: Location,
    rel_dir_path: impl IntoIterator<Item = &'a str>,
    version_slug: &str,
) -> IoResult<PathBuf> {
    let mut parts = match location {
        Location::UserGlobal => dirs::cache_dir().ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::NotFound, "cache dir not found")
        })?,
        Location::LocalDev => {
            resolve_local_dev_root(std::env::var_os("CARGO_MANIFEST_DIR"), std::env::current_dir)?
                .join("target")
        }
        Location::Custom(path) => path,
    };
    parts.extend(rel_dir_path);
    Ok(parts.join(version_slug))
}

#[cfg(feature = "host-fetch")]
fn open_archive_source(source: Source) -> IoResult<(impl Read, Option<[u8; 32]>)> {
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
        Source::VerifiedLocal(VerifiedLocalArchive { path, sha256 }) => {
            let file = open_regular_local_archive(&path)?;
            Ok((SourceReader::Local(file), Some(sha256)))
        }
        Source::Local(path) => {
            let file = open_regular_local_archive(&path)?;
            Ok((SourceReader::Local(file), None))
        }
    }
}

/// Checks a single path component without panicking, returning the static
/// diagnostic reason when invalid.
pub const fn check_path_component(part: &str) -> Result<(), &'static str> {
    let bytes = part.as_bytes();

    if bytes.len() > 255 {
        return Err("Error: each `rel_dir_path` component must not exceed 255 bytes.");
    }
    if bytes.is_empty() {
        return Err("rel_dir_path component must not be empty");
    }
    if bytes.len() == 1 && bytes[0] == b'.' {
        return Err("Error: `rel_dir_path` component must not be '.'");
    }
    if bytes.len() == 2 && bytes[0] == b'.' && bytes[1] == b'.' {
        return Err("Error: `rel_dir_path` component must not be '..'");
    }
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'/' || b == b'\\' {
            return Err(
                "Error: `rel_dir_path` component must not contain a path separator ('/' or '\\')",
            );
        }
        if b == b'\0'
            || b == b'<'
            || b == b'>'
            || b == b':'
            || b == b'"'
            || b == b'|'
            || b == b'?'
            || b == b'*'
        {
            return Err(
                "Error: `rel_dir_path` component must not contain a character reserved on Windows: < > : \" | ? *",
            );
        }
        if b < 0x20 || b == 0x7f {
            return Err(
                "Error: `rel_dir_path` component must not contain an ASCII control character",
            );
        }
        i += 1;
    }
    // Windows strips trailing dots and spaces, so `a.` and `a ` alias `a`.
    let last = bytes[bytes.len() - 1];
    if last == b'.' || last == b' ' {
        return Err("Error: `rel_dir_path` component must not end with '.' or ' '");
    }

    // Device names reserved by Windows, including the superscript-digit
    // `COM`/`LPT` forms (encoded here as UTF-8).
    let reserved_names: &[&[u8]] = &[
        b"CON",
        b"PRN",
        b"AUX",
        b"NUL",
        b"COM0",
        b"COM1",
        b"COM2",
        b"COM3",
        b"COM4",
        b"COM5",
        b"COM6",
        b"COM7",
        b"COM8",
        b"COM9",
        b"LPT0",
        b"LPT1",
        b"LPT2",
        b"LPT3",
        b"LPT4",
        b"LPT5",
        b"LPT6",
        b"LPT7",
        b"LPT8",
        b"LPT9",
        b"COM\xC2\xB9",
        b"COM\xC2\xB2",
        b"COM\xC2\xB3",
        b"LPT\xC2\xB9",
        b"LPT\xC2\xB2",
        b"LPT\xC2\xB3",
    ];

    // Length of the component up to (not including) the first '.', minus any
    // spaces before it. If there is no '.', then this is the whole component.
    // Windows reserves device names matched by their stem, i.e., "CON.abc" and
    // "CON .abc" are reserved the same as "CON".
    let mut len = 0;
    while len < bytes.len() && bytes[len] != b'.' {
        len += 1;
    }
    while len > 0 && bytes[len - 1] == b' ' {
        len -= 1;
    }
    let mut r = 0;
    while r < reserved_names.len() {
        let name = reserved_names[r];
        if len == name.len() {
            let mut is_reserved = true;
            let mut j = 0;
            while j < len {
                if bytes[j].to_ascii_uppercase() != name[j] {
                    is_reserved = false;
                    break;
                }
                j += 1;
            }
            if is_reserved {
                return Err(
                    "Error: `rel_dir_path` component must not be a Windows-reserved device name.",
                );
            }
        }
        r += 1;
    }
    Ok(())
}

/// Validates a single path component.
///
/// This function intentionally accepts only a small cross-platform subset
/// of path component names. Thus, it ignores platform-specific behavior
/// and ensures that the same logical path is valid on Windows, macOS
/// and Unix-like systems.
///
/// # Panics
///
/// Panics if the component:
/// - is empty
/// - is `.` or `..`
/// - contains a path separator
/// - contains a character reserved on Windows
/// - ends with `.` or a space, which Windows strips
/// - is a Windows-reserved device name (matched by its stem)
/// - contains a null byte
const fn validate_path(part: &str) {
    if let Err(msg) = check_path_component(part) {
        panic!("{}", msg);
    }
}

/// An in-memory regular file entry from a verified `.tar.zst` archive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedArchiveEntry {
    /// Normalized relative Unix-style path using `/` separators.
    pub path: String,
    /// Uncompressed file contents.
    pub bytes: Vec<u8>,
}

/// Verifies that `bytes` matches `expected_sha256` in pure Rust without I/O.
pub fn verify_sha256_bytes(bytes: &[u8], expected_sha256: &[u8; 32]) -> IoResult<()> {
    let actual: [u8; 32] = sha2::Sha256::digest(bytes).into();
    if &actual != expected_sha256 {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "SHA-256 hash mismatch"));
    }
    Ok(())
}

fn normalize_tar_entry_path(raw: &str) -> IoResult<Option<String>> {
    if raw.contains('\0') || raw.contains('\\') {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("invalid archive path character in {raw:?}"),
        ));
    }
    let mut parts = Vec::new();
    for seg in raw.split('/') {
        if seg.is_empty() || seg == "." {
            continue;
        }
        if let Err(reason) = check_path_component(seg) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("unsafe archive path component in {raw:?}: {reason}"),
            ));
        }
        parts.push(seg);
    }
    if parts.is_empty() { Ok(None) } else { Ok(Some(parts.join("/"))) }
}

/// Returns a key under which two normalized ASCII archive paths collide if
/// they may name the same file on a case-insensitive file system (Windows or
/// default macOS). Callers reject non-ASCII paths first, because Unicode case
/// folding and normalization differ across file systems.
fn path_collision_key(path: &str) -> String {
    debug_assert!(path.is_ascii());
    path.to_ascii_lowercase()
}

#[derive(Copy, Clone)]
enum ArchiveEntryKind {
    File,
    Directory,
}

/// Records an archive entry at collision key `key` in `files` and `dirs`,
/// returning `false` if it would collide with an earlier entry (duplicate file,
/// file-vs-directory collision at the same path, or entry placed below an
/// earlier file).
fn record_archive_entry(
    kind: ArchiveEntryKind,
    key: String,
    files: &mut HashSet<String>,
    dirs: &mut HashSet<String>,
) -> bool {
    let collides_with_self = match kind {
        ArchiveEntryKind::File => files.contains(&key) || dirs.contains(&key),
        ArchiveEntryKind::Directory => files.contains(&key),
    };
    if collides_with_self {
        return false;
    }
    let ancestors: Vec<String> = key.match_indices('/').map(|(i, _)| key[..i].to_owned()).collect();
    if ancestors.iter().any(|a| files.contains(a)) {
        return false;
    }
    dirs.extend(ancestors);
    match kind {
        ArchiveEntryKind::File => {
            files.insert(key);
        }
        ArchiveEntryKind::Directory => {
            dirs.insert(key);
        }
    }
    true
}

/// Verifies (when `expected_sha256` is `Some`) and decodes a `.tar.zst` archive
/// purely in Rust, rejecting symlinks, hardlinks, special files, path
/// traversal, duplicate or colliding paths, and corrupt Zstd/tar streams.
///
/// Entry paths must be ASCII. Two entries collide if their normalized paths
/// are equal after ASCII case folding (except repeated directory entries),
/// or if a regular file shares a (case-folded) path with a directory entry
/// or an ancestor directory of another entry. Path components that Windows
/// would alias (trailing `.` or ` `, or reserved device names) are rejected.
///
/// The archive must be exactly one Zstd frame: bytes after its end, including
/// further frames, are rejected. If the frame carries a content checksum, it
/// is verified.
///
/// When `expected_sha256` is `Some`, the compressed byte stream's SHA-256
/// digest is checked before any byte reaches the Zstd or tar decoders.
pub fn verify_and_read_tar_zst_entries<R: Read>(
    mut reader: R,
    expected_sha256: Option<[u8; 32]>,
) -> IoResult<Vec<VerifiedArchiveEntry>> {
    let mut compressed = Vec::new();
    reader.read_to_end(&mut compressed)?;
    if let Some(expected) = expected_sha256 {
        verify_sha256_bytes(&compressed, &expected)?;
    }
    if compressed.is_empty() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "empty compressed archive",
        ));
    }

    let mut decoder = ruzstd::decoding::StreamingDecoder::new(compressed.as_slice())
        .map_err(|err| std::io::Error::new(std::io::ErrorKind::InvalidData, err))?;
    let mut out = Vec::new();
    let mut seen_files = HashSet::new();
    let mut seen_dirs = HashSet::new();
    {
        let mut archive = tar::Archive::new(&mut decoder);
        for entry_res in archive.entries()? {
            let mut entry = entry_res?;
            let entry_type = entry.header().entry_type();
            let raw_path = std::str::from_utf8(entry.path_bytes().as_ref())
                .map_err(|err| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!("non-UTF-8 archive entry path: {err}"),
                    )
                })?
                .to_owned();
            if raw_path.starts_with('/') {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("absolute archive entry path rejected: {raw_path:?}"),
                ));
            }
            let normalized = normalize_tar_entry_path(&raw_path)?;
            let kind = if entry_type.is_dir() {
                ArchiveEntryKind::Directory
            } else if entry_type.is_file() {
                ArchiveEntryKind::File
            } else {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("non-regular archive entry {raw_path:?} ({entry_type:?}) rejected"),
                ));
            };
            let path = match (kind, normalized) {
                (ArchiveEntryKind::Directory, None) => continue,
                (ArchiveEntryKind::File, None) => {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!("empty archive file path for {raw_path:?}"),
                    ));
                }
                (_, Some(path)) => path,
            };
            if !path.is_ascii() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("non-ASCII archive entry path rejected: {path:?}"),
                ));
            }
            if !record_archive_entry(
                kind,
                path_collision_key(&path),
                &mut seen_files,
                &mut seen_dirs,
            ) {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "duplicate archive entry path (case-insensitively, or as a file and a \
                         directory): {path}"
                    ),
                ));
            }
            if matches!(kind, ArchiveEntryKind::Directory) {
                continue;
            }
            let mut bytes = Vec::new();
            entry.read_to_end(&mut bytes)?;
            out.push(VerifiedArchiveEntry { path, bytes });
        }
    }
    // Drain the remainder of the tar stream so truncated or trailing corrupt
    // Zstd blocks after the tar EOF marker are still detected.
    std::io::copy(&mut decoder, &mut std::io::sink())?;
    // `StreamingDecoder` stops at the end of the first frame and never reads
    // past it, so any input left over was not decoded.
    let trailing = decoder.get_ref().len();
    if trailing != 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("{trailing} unexpected bytes after the Zstd frame"),
        ));
    }
    // `StreamingDecoder` reads the optional content checksum but does not
    // compare it against the decoded bytes.
    let frame = decoder.into_frame_decoder();
    if let Some(stored) = frame.get_checksum_from_data()
        && frame.get_calculated_checksum() != Some(stored)
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Zstd content checksum mismatch",
        ));
    }
    Ok(out)
}

#[cfg(feature = "host-fetch")]
fn not_regular_file_error(path: &Path) -> std::io::Error {
    std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        format!("local archive path is not a regular file: {}", path.display()),
    )
}

/// Opens a local archive path after checking via `stat` (without opening
/// FIFOs/devices) and `fstat` on the open descriptor that it refers to the
/// same regular file.
///
/// On Unix, symlinks are resolved up front and the final open neither follows
/// a symlink nor blocks, so a FIFO or symlink swapped in after the `stat` is
/// rejected by the `fstat` check (or fails to open) instead of hanging.
#[cfg(feature = "host-fetch")]
fn open_regular_local_archive(path: &Path) -> IoResult<std::fs::File> {
    #[cfg(unix)]
    {
        let resolved = std::fs::canonicalize(path)?;
        let pre_meta = std::fs::symlink_metadata(&resolved)?;
        if !pre_meta.is_file() {
            return Err(not_regular_file_error(path));
        }
        open_expected_regular_file(&resolved, &pre_meta)
    }
    #[cfg(not(unix))]
    {
        if !std::fs::metadata(path)?.is_file() {
            return Err(not_regular_file_error(path));
        }
        let file = std::fs::File::open(path)?;
        if !file.metadata()?.is_file() {
            return Err(not_regular_file_error(path));
        }
        Ok(file)
    }
}

/// Opens `path` for reading iff it is (still) the regular file that
/// `expected` describes.
#[cfg(all(feature = "host-fetch", unix))]
fn open_expected_regular_file(
    path: &Path,
    expected: &std::fs::Metadata,
) -> IoResult<std::fs::File> {
    use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};

    // `O_NONBLOCK` keeps the open from waiting for a writer if `path` is now a
    // FIFO; `O_NOFOLLOW` refuses a symlink (e.g. to a device node).
    let file = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(not_regular_file_error(path));
    }
    if (meta.dev(), meta.ino()) != (expected.dev(), expected.ino()) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("local archive inode changed during open: {}", path.display()),
        ));
    }
    // `O_NONBLOCK` is left set: POSIX ignores it for reads of regular files,
    // which is all `file` can be after the check above.
    Ok(file)
}

/// Extracts the `.tar.zst` from `reader` and installs it at `dst`.
///
/// When `expected_sha256` is `Some`, buffers and verifies the SHA-256 digest of
/// the entire compressed stream before invoking `zstd` or `tar` extraction.
#[cfg(feature = "host-fetch")]
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

    fn unpack_tar_zst(reader: impl Read, target_dir: &Path) -> IoResult<()> {
        let decoder = zstd::stream::read::Decoder::new(reader)?;
        let mut archive = tar::Archive::new(decoder);
        archive.unpack(target_dir)
    }

    sync::ManagedDirName::new(dst)
        .check_exists_or_create(|target_dir| {
            if let Some(expected) = expected_sha256 {
                // Stream and verify the compressed archive inside a private
                // temporary file on the cache filesystem before passing any
                // untrusted bytes to `zstd` or `tar`.
                let mut tmp = tempfile::tempfile_in(sync::staging_parent(dst))?;
                let mut hash_reader = HashingReader { reader, hasher: sha2::Sha256::new() };
                std::io::copy(&mut hash_reader, &mut tmp)?;

                let hash: [u8; 32] = sha2::Digest::finalize(hash_reader.hasher).into();
                if hash != expected {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "SHA-256 hash mismatch",
                    ));
                }

                tmp.rewind()?;
                unpack_tar_zst(tmp, target_dir)
            } else {
                unpack_tar_zst(&mut reader, target_dir)
            }
        })
        .map(|_| ())
}

/// Parses a [`RemoteArchive`] from the `Cargo.toml` at `$cargo_toml_path`.
///
/// The `Cargo.toml` is expected to have content of the form:
///
/// ```toml
///
/// [[package.metadata.exocrate]]
/// os = "linux"
/// arch = "x86_64"
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/linux-x86_64.tar.zst"
///
/// [[package.metadata.exocrate]]
/// os = "macos"
/// arch = "x86_64"
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/macos-x86_64.tar.zst"
///
/// [[package.metadata.exocrate]]
/// os = "linux"
/// arch = "aarch64"
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/linux-aarch64.tar.zst"
///
/// [[package.metadata.exocrate]]
/// os = "macos"
/// arch = "aarch64"
/// sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// url = "https://example.com/macos-aarch64.tar.zst"
/// ```
#[macro_export]
macro_rules! parse_remote_archive {
    ($vis:vis const $name:ident: RemoteArchive = $cargo_toml_path:literal;) => {
        $vis const $name: $crate::RemoteArchive = {
            $crate::macro_util::toml_const::toml_const!{
                const MANIFEST: $cargo_toml_path;
            }
            use std::env::consts::*;
            use $crate::macro_util::pack;

            let entries = MANIFEST.package.metadata.exocrate;
            let mut i = 0;
            let config = loop {

                if i == entries.len() {
                    panic!("Unsupported Platform");
                }
                let entry = &entries[i];

                // NOTE: Rust doesn't support checking `&str`s for equality in a
                // `const` context. We work around that limitation by packing
                // their bytes into `u128`s, which can be compared.
                if pack(entry.os) == pack(OS) && pack(entry.arch) == pack(ARCH) {
                    break entry;
                }
                i+=1;
            };

            let Some(sha256) = $crate::macro_util::decode_hex(config.sha256) else {
                panic!("invalid sha256")
            };
            $crate::RemoteArchive {
                sha256,
                url: config.url,
            }
        };
    }
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
        $vis const $name: $crate::Config = $crate::Config::new(
            &$rel_dir_path,
            {
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

                let Ok(s) = ::core::str::from_utf8(&HEX) else {
                    unreachable!()
                };
                s
            },
        );
    };
}

#[doc(hidden)]
pub mod macro_util {
    pub use sha2_const::Sha256;
    pub use toml_const;

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
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "host-fetch")]
    use std::fs;

    use super::*;

    fn wrap_raw_zstd_frame(payload: &[u8]) -> Vec<u8> {
        const MAX_RAW_BLOCK: usize = 128 * 1024;
        let mut out = Vec::new();
        // Zstandard frame magic + single-segment FHD with 4-byte FCS.
        out.extend_from_slice(&0xFD2F_B528u32.to_le_bytes());
        out.push(0xA0);
        out.extend_from_slice(&(payload.len() as u32).to_le_bytes());
        if payload.is_empty() {
            out.extend_from_slice(&1u32.to_le_bytes()[..3]);
            return out;
        }
        let mut offset = 0;
        while offset < payload.len() {
            let end = (offset + MAX_RAW_BLOCK).min(payload.len());
            let chunk = &payload[offset..end];
            let is_last = end == payload.len();
            let header = ((chunk.len() as u32) << 3) | u32::from(is_last);
            out.extend_from_slice(&header.to_le_bytes()[..3]);
            out.extend_from_slice(chunk);
            offset = end;
        }
        out
    }

    fn build_raw_tar_zst_bytes(entries: &[(&str, tar::EntryType, &[u8])]) -> Vec<u8> {
        let mut tar_bytes = Vec::new();
        {
            let mut builder = tar::Builder::new(&mut tar_bytes);
            for &(name, entry_type, content) in entries {
                let mut header = tar::Header::new_gnu();
                header.set_entry_type(entry_type);
                header.set_mode(if entry_type.is_dir() { 0o755 } else { 0o644 });
                header.set_size(if entry_type.is_file() { content.len() as u64 } else { 0 });
                if entry_type == tar::EntryType::Symlink {
                    header.set_link_name("target").unwrap();
                }
                header.set_path(name).unwrap();
                header.set_cksum();
                builder.append(&header, content).unwrap();
            }
            builder.finish().unwrap();
        }
        wrap_raw_zstd_frame(&tar_bytes)
    }

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
    fn dummy_config(rel_dir_path: &'static [&'static str]) -> Config {
        Config::new(rel_dir_path, "slug")
    }

    #[allow(dead_code)]
    fn dummy_remote() -> RemoteArchive {
        RemoteArchive {
            url: "https://example.com/dummy.tar.zst",
            sha256: compute_sha256(b"dummy content"),
        }
    }

    #[test]
    fn test_dynamic_config_validation() {
        let cfg = DynamicConfig::try_new(["anneal", "evidence"], "0.1.0-zerocopy").unwrap();
        assert_eq!(cfg.rel_dir_path(), &["anneal".to_string(), "evidence".to_string()]);
        assert_eq!(cfg.version_slug(), "0.1.0-zerocopy");
        assert!(DynamicConfig::try_new(["../escape"], "v1").is_err());
        assert!(DynamicConfig::try_new(["ok"], "CON.txt").is_err());
    }

    #[test]
    fn test_pure_tar_zst_verification_and_safety() {
        let valid = build_raw_tar_zst_bytes(&[
            ("specs/", tar::EntryType::Directory, b""),
            ("./specs/Spec.lean", tar::EntryType::Regular, b"theorem ok : True := trivial\n"),
        ]);
        let digest = compute_sha256(&valid);
        let entries = verify_and_read_tar_zst_entries(valid.as_slice(), Some(digest)).unwrap();
        assert_eq!(
            entries,
            vec![VerifiedArchiveEntry {
                path: "specs/Spec.lean".to_string(),
                bytes: b"theorem ok : True := trivial\n".to_vec(),
            }]
        );

        // Digest mismatch must fail before passing non-zstd bytes to decode.
        let err = verify_and_read_tar_zst_entries(&b"not zstd"[..], Some(digest)).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(err.to_string(), "SHA-256 hash mismatch");

        // Reject symlinks and duplicate entry paths.
        let with_symlink = build_raw_tar_zst_bytes(&[("specs/link", tar::EntryType::Symlink, b"")]);
        let err = verify_and_read_tar_zst_entries(with_symlink.as_slice(), None).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);

        let with_dup = build_raw_tar_zst_bytes(&[
            ("specs/a.txt", tar::EntryType::Regular, b"one"),
            ("specs/a.txt", tar::EntryType::Regular, b"two"),
        ]);
        let err = verify_and_read_tar_zst_entries(with_dup.as_slice(), None).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);

        let build_ustar_bytes = |name: &[u8]| -> Vec<u8> {
            let mut raw = vec![0u8; 512];
            raw[..name.len()].copy_from_slice(name);
            raw[100..107].copy_from_slice(b"000644 ");
            raw[108..115].copy_from_slice(b"000000 ");
            raw[116..123].copy_from_slice(b"000000 ");
            raw[124..135].copy_from_slice(b"00000000000");
            raw[136..147].copy_from_slice(b"00000000000");
            raw[148..156].fill(b' ');
            raw[156] = b'0';
            raw[257..263].copy_from_slice(b"ustar ");
            let cksum: u32 = raw[..512].iter().map(|&b| u32::from(b)).sum();
            let cksum_str = format!("{cksum:06o}\0 ");
            raw[148..156].copy_from_slice(cksum_str.as_bytes());
            raw.extend_from_slice(&[0u8; 1024]);
            wrap_raw_zstd_frame(&raw)
        };

        // Reject parent-dir traversal even inside manual raw tar header bytes.
        let bad_zst = build_ustar_bytes(b"specs/../escape.txt");
        let err = verify_and_read_tar_zst_entries(bad_zst.as_slice(), None).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);

        // Non-UTF-8 archive paths must fail closed rather than using U+FFFD.
        let non_utf8_zst = build_ustar_bytes(b"specs/\xff.txt");
        let err = verify_and_read_tar_zst_entries(non_utf8_zst.as_slice(), None).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
    }

    #[test]
    fn test_archive_rejects_case_folded_duplicates_and_windows_aliases() {
        let read = |entries: &[(&str, &[u8])]| {
            let entries: Vec<_> =
                entries.iter().map(|&(p, b)| (p, tar::EntryType::Regular, b)).collect();
            verify_and_read_tar_zst_entries(build_raw_tar_zst_bytes(&entries).as_slice(), None)
        };

        // Paths that name the same file on a case-insensitive file system, or
        // that would need one name to be both a file and a directory.
        for (a, b) in [
            ("bin/Tool", "bin/tool"),
            ("BIN/tool", "bin/tool"),
            ("bin", "bin/tool"),
            ("bin/tool", "bin"),
            ("BIN", "bin/tool"),
            ("bin/tool", "Bin"),
            ("a/b", "A/B/c"),
        ] {
            let err = read(&[(a, b"one"), (b, b"two")]).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{a:?} vs {b:?}");
            assert!(err.to_string().contains("duplicate"), "{a:?} vs {b:?}: {err}");
        }

        // Non-ASCII paths are rejected outright: file systems disagree on
        // Unicode case folding (`\u{1e9e}` vs `\u{df}`, KELVIN SIGN vs `k`)
        // and normalization (NFC vs NFD).
        for name in ["specs/\u{c9}t\u{e9}.lean", "bin/\u{212a}", "bin/\u{1e9e}", "bin/e\u{301}"] {
            let err = read(&[(name, b"x")]).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{name:?}");
            assert!(err.to_string().contains("non-ASCII"), "{name:?}: {err}");
        }

        // Components that Windows strips or maps to a device.
        for name in [
            "bin/tool.",
            "bin/tool ",
            "bin./tool",
            "bin/NUL",
            "bin/nul.txt",
            "bin/Com1.tar.gz",
            "bin/LPT9",
            "bin/con .txt",
            "bin/COM\u{b9}",
        ] {
            let err = read(&[(name, b"x")]).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{name:?}");
        }

        // Similar but non-aliasing paths are accepted.
        let entries = read(&[
            ("bin/tool", b"1"),
            ("bin/tool.v2", b"2"),
            ("bin/console", b"3"),
            ("bin/sub/tool", b"4"),
            ("binary", b"5"),
        ])
        .unwrap();
        assert_eq!(entries.len(), 5);
    }

    #[test]
    fn test_archive_directory_validation_and_file_collisions() {
        let read_mixed = |entries: &[(&str, tar::EntryType, &[u8])]| {
            verify_and_read_tar_zst_entries(build_raw_tar_zst_bytes(entries).as_slice(), None)
        };

        // Valid real-world tar directories: root `./`, parent dir before file,
        // repeated dir entries, and non-colliding sibling dirs.
        let valid = read_mixed(&[
            ("./", tar::EntryType::Directory, b""),
            ("a/", tar::EntryType::Directory, b""),
            ("a/", tar::EntryType::Directory, b""),
            ("a/b.txt", tar::EntryType::Regular, b"hello"),
            ("bin/", tar::EntryType::Directory, b""),
            ("binary", tar::EntryType::Regular, b"world"),
        ])
        .unwrap();
        assert_eq!(
            valid,
            vec![
                VerifiedArchiveEntry { path: "a/b.txt".to_string(), bytes: b"hello".to_vec() },
                VerifiedArchiveEntry { path: "binary".to_string(), bytes: b"world".to_vec() },
            ]
        );

        // Non-ASCII directory entries must be rejected just like file entries.
        for dir in ["specs/\u{e9}/", "bin/\u{212a}/", "dir/\u{1e9e}/"] {
            let err = read_mixed(&[(dir, tar::EntryType::Directory, b"")]).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{dir:?}");
            assert!(err.to_string().contains("non-ASCII"), "{dir:?}: {err}");
        }

        // Collisions between directory entries and regular files in either
        // order (including case-folded and ancestor/descendant collisions).
        for (first, second) in [
            (("foo/", tar::EntryType::Directory), ("foo", tar::EntryType::Regular)),
            (("FOO/", tar::EntryType::Directory), ("foo", tar::EntryType::Regular)),
            (("a/b/", tar::EntryType::Directory), ("A", tar::EntryType::Regular)),
            (("foo", tar::EntryType::Regular), ("foo/", tar::EntryType::Directory)),
            (("foo", tar::EntryType::Regular), ("FOO/", tar::EntryType::Directory)),
            (("a", tar::EntryType::Regular), ("A/b/", tar::EntryType::Directory)),
        ] {
            let err =
                read_mixed(&[(first.0, first.1, b""), (second.0, second.1, b"")]).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{first:?} vs {second:?}");
            assert!(err.to_string().contains("duplicate"), "{first:?} vs {second:?}: {err}");
        }
    }

    #[test]
    fn test_archive_rejects_bytes_after_first_zstd_frame() {
        let first = build_raw_tar_zst_bytes(&[("a.txt", tar::EntryType::Regular, b"one")]);
        assert_eq!(verify_and_read_tar_zst_entries(first.as_slice(), None).unwrap().len(), 1);

        let second = build_raw_tar_zst_bytes(&[("b.txt", tar::EntryType::Regular, b"two")]);
        // Zstandard skippable frame with an empty payload.
        let mut skippable = 0x184D_2A50u32.to_le_bytes().to_vec();
        skippable.extend_from_slice(&0u32.to_le_bytes());
        for suffix in [&b"\0"[..], b"garbage", &second, &skippable] {
            let input = [first.as_slice(), suffix].concat();
            let err = verify_and_read_tar_zst_entries(input.as_slice(), None).unwrap_err();
            assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
            let expected = format!("{} unexpected bytes after the Zstd frame", suffix.len());
            assert_eq!(err.to_string(), expected);
        }
    }

    #[test]
    fn test_archive_rejects_zstd_content_checksum_mismatch() {
        let mut frame = build_raw_tar_zst_bytes(&[("a.txt", tar::EntryType::Regular, b"one")]);
        // Set the frame header's Content_Checksum_flag and append a checksum
        // that does not match the content.
        frame[4] |= 0x04;
        frame.extend_from_slice(&0u32.to_le_bytes());
        let err = verify_and_read_tar_zst_entries(frame.as_slice(), None).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(err.to_string(), "Zstd content checksum mismatch");
    }

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_archive_accepts_valid_zstd_content_checksum() {
        let mut enc = zstd::stream::write::Encoder::new(Vec::new(), 0).unwrap();
        enc.include_checksum(true).unwrap();
        {
            let mut builder = tar::Builder::new(&mut enc);
            let mut header = tar::Header::new_gnu();
            header.set_size(3);
            header.set_mode(0o644);
            builder.append_data(&mut header, "a.txt", &b"one"[..]).unwrap();
            builder.finish().unwrap();
        }
        let mut bytes = enc.finish().unwrap();
        let entries = verify_and_read_tar_zst_entries(bytes.as_slice(), None).unwrap();
        assert_eq!(entries[0].bytes, b"one");

        *bytes.last_mut().unwrap() ^= 1;
        let err = verify_and_read_tar_zst_entries(bytes.as_slice(), None).unwrap_err();
        assert_eq!(err.to_string(), "Zstd content checksum mismatch");
    }

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_install_without_hash_validation() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let tar_zst = create_dummy_tar_zst(&[("hello.txt", b"hello world")]);

        install(tar_zst.as_slice(), &dst, None).unwrap();

        assert!(dst.is_dir());
        assert_eq!(fs::read_to_string(dst.join("hello.txt")).unwrap(), "hello world");
    }

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_resolve_local_dev_root() {
        let mut cwd_called = false;
        let resolved = resolve_local_dev_root(Some(OsString::from("/manifest/root")), || {
            cwd_called = true;
            Ok(PathBuf::from("/fallback/cwd"))
        })
        .unwrap();
        assert!(!cwd_called);
        assert_eq!(resolved, PathBuf::from("/manifest/root"));

        // Unset `CARGO_MANIFEST_DIR` falls back to `cwd`.
        let resolved = resolve_local_dev_root(None, || Ok(PathBuf::from("/fallback/cwd"))).unwrap();
        assert_eq!(resolved, PathBuf::from("/fallback/cwd"));

        // Empty `CARGO_MANIFEST_DIR` is treated as unset.
        let resolved =
            resolve_local_dev_root(Some(OsString::new()), || Ok(PathBuf::from("/empty/fallback")))
                .unwrap();
        assert_eq!(resolved, PathBuf::from("/empty/fallback"));

        // `current_dir()` failures are propagated instead of panicking.
        let err = resolve_local_dev_root(Some(OsString::new()), || {
            Err(std::io::Error::new(std::io::ErrorKind::NotFound, "cwd missing"))
        })
        .unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::NotFound);

        // Non-UTF-8 `CARGO_MANIFEST_DIR` values are preserved verbatim.
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStringExt as _;
            let raw = OsString::from_vec(vec![b'/', b'm', 0xff, b'd']);
            let expected = PathBuf::from(raw.clone());
            let mut unix_cwd_called = false;
            let resolved = resolve_local_dev_root(Some(raw), || {
                unix_cwd_called = true;
                Ok(PathBuf::from("/unused"))
            })
            .unwrap();
            assert!(!unix_cwd_called);
            assert_eq!(resolved, expected);
        }
    }

    #[cfg(all(feature = "host-fetch", unix))]
    #[test]
    fn test_install_or_resolve_dangling_symlink_fails_before_opening_source() {
        let temp = tempfile::tempdir().unwrap();
        let config = Config::new(&["tool"], "v1");
        let tool_dir = temp.path().join("tool");
        fs::create_dir_all(&tool_dir).unwrap();
        std::os::unix::fs::symlink(temp.path().join("missing"), tool_dir.join("v1")).unwrap();

        // Unreachable port: preflight check must reject the dangling symlink
        // before attempting any HTTP request.
        let err = config
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().to_path_buf()),
                Source::Remote(RemoteArchive {
                    url: "http://127.0.0.1:1/archive.tar.zst",
                    sha256: [0u8; 32],
                }),
            )
            .unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::AlreadyExists);

        // Same when an intermediate destination ancestor is a dangling symlink.
        let anc_config = Config::new(&["dangling_tool"], "v1");
        std::os::unix::fs::symlink(
            temp.path().join("missing_anc"),
            temp.path().join("dangling_tool"),
        )
        .unwrap();
        let err = anc_config
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().to_path_buf()),
                Source::Remote(RemoteArchive {
                    url: "http://127.0.0.1:1/archive.tar.zst",
                    sha256: [0u8; 32],
                }),
            )
            .unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::AlreadyExists);
    }

    #[cfg(feature = "host-fetch")]
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

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_config_resolve_installation_dir_or_install_local() {
        let temp = tempfile::tempdir().unwrap();
        let archive_path = temp.path().join("archive.tar.zst");
        let dummy_tar = create_dummy_tar_zst(&[("bin/compiler", b"binary data")]);
        fs::write(&archive_path, &dummy_tar).unwrap();

        let config = Config::new(&["test_dir_install"], "slug");
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

    #[cfg(feature = "host-fetch")]
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
    #[test]
    fn test_valid_rel_dir_path() {
        let config = Config::new(&["tool", "deps"], "v1");

        assert_eq!(config.rel_dir_path, &["tool", "deps"]);
        assert_eq!(config.version_slug, "v1");
    }

    #[test]
    #[should_panic(expected = "must not contain a path separator")]
    fn test_config_new_invalid_rel_dir_path() {
        let _ = Config::new(&["foo/bar"], "v1");
    }

    #[test]
    #[should_panic(expected = "must not contain a path separator")]
    fn test_config_new_invalid_version_slug() {
        let _ = Config::new(&["tool"], "v1/bar");
    }
    #[test]
    fn test_config_new_similar_but_not_reserved_name() {
        // "console" starts with "con" but has a different stem length,
        // so it must not be treated as reserved.
        let config = Config::new(&["console"], "v1");
        assert_eq!(config.rel_dir_path, &["console"]);
    }
    #[test]
    #[should_panic(expected = "must not be a Windows-reserved device name")]
    fn test_config_new_windows_reserved_name() {
        // Reserved names are matched case-insensitively.
        let _ = Config::new(&["con"], "v1");
    }

    #[test]
    #[should_panic(expected = "must not be a Windows-reserved device name")]
    fn test_config_new_windows_reserved_name_with_extension() {
        // "COM1.txt" is reserved the same as "COM1" since Windows
        // matches device names by their stem, not the full name.
        let _ = Config::new(&["COM1.txt"], "v1");
    }

    #[cfg(feature = "host-fetch")]
    #[cfg(unix)]
    fn create_tar_zst_with_modes(files: &[(&str, &[u8], u32)], dirs: &[(&str, u32)]) -> Vec<u8> {
        let mut zstd_enc = zstd::stream::write::Encoder::new(Vec::new(), 0).unwrap();
        {
            let mut tar_builder = tar::Builder::new(&mut zstd_enc);
            for (name, content, mode) in files {
                let mut header = tar::Header::new_gnu();
                header.set_size(content.len() as u64);
                header.set_mode(*mode);
                header.set_cksum();
                tar_builder.append_data(&mut header, name, *content).unwrap();
            }
            for (dir_name, mode) in dirs {
                let mut dir = tar::Header::new_gnu();
                dir.set_entry_type(tar::EntryType::Directory);
                dir.set_size(0);
                dir.set_mode(*mode);
                dir.set_cksum();
                tar_builder.append_data(&mut dir, dir_name, std::io::empty()).unwrap();
            }
            tar_builder.finish().unwrap();
        }
        zstd_enc.finish().unwrap()
    }

    #[cfg(feature = "host-fetch")]
    #[cfg(unix)]
    fn serve_archives_once(
        archives: Vec<Vec<u8>>,
    ) -> (std::net::SocketAddr, std::thread::JoinHandle<()>) {
        use std::{io::Write as _, net::TcpListener, time::Duration};

        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let handle = std::thread::spawn(move || {
            for archive in archives {
                let (mut socket, _) = listener.accept().unwrap();
                socket.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
                let mut request = Vec::new();
                let mut byte = [0];
                while !request.ends_with(b"\r\n\r\n") {
                    socket.read_exact(&mut byte).unwrap();
                    request.push(byte[0]);
                    assert!(request.len() < 8192);
                }
                write!(
                    socket,
                    "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                    archive.len()
                )
                .unwrap();
                socket.write_all(&archive).unwrap();
            }
        });
        (addr, handle)
    }

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_install_verifies_hash_before_decompression() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");

        // Not valid zstd or tar; a wrong hash must fail at hash verification
        // rather than surfacing a decompression/unpack error.
        let garbage = b"not a zstd or tar payload";
        let wrong_hash = compute_sha256(b"authentic payload");

        let err = install(garbage.as_slice(), &dst, Some(wrong_hash)).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(err.to_string(), "SHA-256 hash mismatch");
        assert!(!dst.exists());

        let entries: Vec<_> = fs::read_dir(temp.path())
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n != "install_target.lock")
            .collect();
        assert!(entries.is_empty());
    }

    #[cfg(feature = "host-fetch")]
    #[cfg(unix)]
    #[test]
    fn test_rejected_0555_archive_does_not_contaminate_remote_install() {
        let temp = tempfile::tempdir().unwrap();
        let _restore = sync::tests::UnixRestorePermissions { root: temp.path() };

        let malicious = create_tar_zst_with_modes(
            &[("unexpected/marker.txt", b"UNVERIFIED REMOTE MARKER", 0o600)],
            &[("unexpected", 0o555)],
        );
        let valid = create_tar_zst_with_modes(
            &[("official.txt", b"authenticated expected contents", 0o644)],
            &[],
        );
        let expected_sha256 = compute_sha256(&valid);

        let (addr, server) = serve_archives_once(vec![malicious, valid]);
        let url: &'static str =
            Box::leak(format!("http://{addr}/archive.tar.zst").into_boxed_str());
        let config = Config::new(&["tool"], "v1");
        let tool_parent = temp.path().join("tool");

        let first = config.resolve_installation_dir_or_install(
            Location::Custom(temp.path().to_path_buf()),
            Source::Remote(RemoteArchive { url, sha256: expected_sha256 }),
        );
        let err = first.unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(err.to_string(), "SHA-256 hash mismatch");
        assert!(!tool_parent.join("v1").exists());
        let leftover: Vec<_> = fs::read_dir(&tool_parent)
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n != "v1.lock")
            .collect();
        assert!(leftover.is_empty(), "unexpected leftover entries: {leftover:?}");

        let (installed, status) = config
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().to_path_buf()),
                Source::Remote(RemoteArchive { url, sha256: expected_sha256 }),
            )
            .unwrap();
        server.join().unwrap();

        assert_eq!(status, ResolvedOrInstalled::NewlyInstalled);
        assert_eq!(
            fs::read_to_string(installed.join("official.txt")).unwrap(),
            "authenticated expected contents"
        );
        assert!(!installed.join("unexpected").exists());
        assert!(!installed.join("unexpected/marker.txt").exists());
    }

    #[cfg(feature = "host-fetch")]
    #[cfg(unix)]
    #[test]
    fn test_rejected_0000_dir_archive_does_not_block_remote_install() {
        let temp = tempfile::tempdir().unwrap();
        let _restore = sync::tests::UnixRestorePermissions { root: temp.path() };

        let malicious =
            create_tar_zst_with_modes(&[("bin/poison", b"UNVERIFIED", 0o600)], &[("bin", 0o000)]);
        let valid = create_tar_zst_with_modes(&[("bin/tool", b"ok", 0o755)], &[]);
        let expected_sha256 = compute_sha256(&valid);

        let (addr, server) = serve_archives_once(vec![malicious, valid]);
        let url: &'static str =
            Box::leak(format!("http://{addr}/archive.tar.zst").into_boxed_str());
        let config = Config::new(&["tool"], "v1");

        let first = config.resolve_installation_dir_or_install(
            Location::Custom(temp.path().to_path_buf()),
            Source::Remote(RemoteArchive { url, sha256: expected_sha256 }),
        );
        let err = first.unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(err.to_string(), "SHA-256 hash mismatch");

        let (installed, status) = config
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().to_path_buf()),
                Source::Remote(RemoteArchive { url, sha256: expected_sha256 }),
            )
            .unwrap();
        server.join().unwrap();

        assert_eq!(status, ResolvedOrInstalled::NewlyInstalled);
        assert_eq!(fs::read(installed.join("bin/tool")).unwrap(), b"ok");
        assert!(!installed.join("bin/poison").exists());
    }

    #[cfg(feature = "host-fetch")]
    #[cfg(unix)]
    #[test]
    fn test_preexisting_unwritable_staging_residue_does_not_poison_or_block() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().unwrap();
        let _restore = sync::tests::UnixRestorePermissions { root: temp.path() };
        let dst = temp.path().join("install_target");

        // Pre-populate both a legacy `<dst>.staging` tree with a mode-0555
        // directory and a sibling `.staging-*` leftover containing a mode-0000
        // directory.
        let legacy_unexpected = temp.path().join("install_target.staging/unexpected");
        fs::create_dir_all(&legacy_unexpected).unwrap();
        fs::write(legacy_unexpected.join("marker.txt"), b"POISON").unwrap();
        fs::set_permissions(&legacy_unexpected, fs::Permissions::from_mode(0o555)).unwrap();
        fs::set_permissions(
            temp.path().join("install_target.staging"),
            fs::Permissions::from_mode(0o555),
        )
        .unwrap();

        let orphaned_bin = temp.path().join(".staging-install_target.orphaned.staging/bin");
        fs::create_dir_all(&orphaned_bin).unwrap();
        fs::set_permissions(&orphaned_bin, fs::Permissions::from_mode(0o000)).unwrap();

        let valid = create_tar_zst_with_modes(&[("official.txt", b"clean", 0o644)], &[]);
        let expected_sha256 = compute_sha256(&valid);

        install(valid.as_slice(), &dst, Some(expected_sha256)).unwrap();

        assert!(dst.is_dir());
        assert_eq!(fs::read_to_string(dst.join("official.txt")).unwrap(), "clean");
        assert!(!dst.join("unexpected").exists());
        assert!(!dst.join("bin").exists());
    }

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_verified_local_archive_succeeds_and_rejects_hash_mismatch_before_unpack() {
        let temp = tempfile::tempdir().unwrap();
        let valid_bytes = create_dummy_tar_zst(&[("bin/tool", b"verified-offline")]);
        let expected_sha256 = compute_sha256(&valid_bytes);

        let bad_archive_path = temp.path().join("tampered.tar.zst");
        fs::write(&bad_archive_path, b"not even valid zstd").unwrap();

        let config = Config::new(&["offline_tool"], "v1");
        let err = config
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().to_path_buf()),
                Source::VerifiedLocal(VerifiedLocalArchive {
                    path: bad_archive_path,
                    sha256: expected_sha256,
                }),
            )
            .unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(err.to_string(), "SHA-256 hash mismatch");
        assert!(!temp.path().join("offline_tool/v1").exists());

        let good_archive_path = temp.path().join("good.tar.zst");
        fs::write(&good_archive_path, &valid_bytes).unwrap();
        let (installed, status) = config
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().to_path_buf()),
                Source::VerifiedLocal(VerifiedLocalArchive {
                    path: good_archive_path,
                    sha256: expected_sha256,
                }),
            )
            .unwrap();
        assert_eq!(status, ResolvedOrInstalled::NewlyInstalled);
        assert_eq!(fs::read(installed.join("bin/tool")).unwrap(), b"verified-offline");
    }

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_local_archive_rejects_directory_source() {
        let temp = tempfile::tempdir().unwrap();
        let dir_source = temp.path().join("not_a_file_dir");
        fs::create_dir_all(&dir_source).unwrap();

        let config = Config::new(&["dir_reject"], "v1");
        let err = config
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().to_path_buf()),
                Source::Local(dir_source),
            )
            .unwrap_err();
        // The regular-file check rejects the directory up front, before
        // anything (such as a lock file) is created under the location.
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput, "{err:?}");
        let entries: Vec<_> =
            fs::read_dir(temp.path()).unwrap().map(|e| e.unwrap().file_name()).collect();
        assert_eq!(entries, [std::ffi::OsString::from("not_a_file_dir")]);
    }

    #[cfg(feature = "host-fetch")]
    #[test]
    fn test_dynamic_config_and_offline_mirror_resolution() {
        let temp = tempfile::tempdir().unwrap();
        let mirror_dir = temp.path().join("mirror");
        fs::create_dir_all(&mirror_dir).unwrap();

        let archive_bytes = create_dummy_tar_zst(&[("anneal-evidence.json", b"{}")]);
        let sha256 = compute_sha256(&archive_bytes);
        fs::write(mirror_dir.join("zerocopy-evidence-v0.8.64.tar.zst"), &archive_bytes).unwrap();

        let remote = RemoteArchive {
            // Unreachable port; mirror resolution must skip network I/O.
            url: "http://127.0.0.1:1/releases/zerocopy-evidence-v0.8.64.tar.zst?download=1",
            sha256,
        };
        let source = Source::from_remote_or_mirror(remote, Some(&mirror_dir)).unwrap();
        assert!(matches!(source, Source::VerifiedLocal(_)));

        let dyn_cfg = DynamicConfig::try_new(["anneal", "evidence"], "0.1.0-zerocopy-0.8.64")
            .expect("valid dynamic config");
        let (installed, status) = dyn_cfg
            .resolve_installation_dir_or_install(
                Location::Custom(temp.path().join("cache")),
                source,
            )
            .unwrap();
        assert_eq!(status, ResolvedOrInstalled::NewlyInstalled);
        assert_eq!(fs::read(installed.join("anneal-evidence.json")).unwrap(), b"{}");

        // Reject invalid path components at runtime without panicking.
        assert!(DynamicConfig::try_new(["../escape"], "v1").is_err());
        assert!(DynamicConfig::try_new(["ok"], "CON.txt").is_err());
        for url in ["https://example.com/", "https://example.com", "https://example.com?download=1"]
        {
            let bad_remote = RemoteArchive { url, sha256 };
            assert!(Source::from_remote_or_mirror(bad_remote, Some(&mirror_dir)).is_err(), "{url}");
        }
    }

    #[cfg(all(feature = "host-fetch", unix))]
    #[test]
    fn test_local_archive_open_rejects_swapped_fifo_and_symlink() {
        use std::{ffi::CString, os::unix::ffi::OsStrExt as _, sync::mpsc, time::Duration};

        let temp = tempfile::tempdir().unwrap();
        let regular = temp.path().join("archive.tar.zst");
        fs::write(&regular, b"archive").unwrap();
        let expected = fs::symlink_metadata(&regular).unwrap();

        // Simulate a FIFO swapped in after the `stat`: the open must neither
        // wait for a writer nor hand back the FIFO.
        let fifo = temp.path().join("fifo");
        let c_fifo = CString::new(fifo.as_os_str().as_bytes()).unwrap();
        // SAFETY: `c_fifo` is a valid NUL-terminated path.
        assert_eq!(unsafe { libc::mkfifo(c_fifo.as_ptr(), 0o600) }, 0);
        let (tx, rx) = mpsc::channel();
        let (fifo_clone, expected_clone) = (fifo.clone(), expected.clone());
        std::thread::spawn(move || {
            let res = open_expected_regular_file(&fifo_clone, &expected_clone);
            let _ = tx.send(res.map(drop));
        });
        match rx.recv_timeout(Duration::from_secs(10)) {
            Ok(res) => assert_eq!(res.unwrap_err().kind(), std::io::ErrorKind::InvalidInput),
            Err(_) => {
                // Unblock the stuck reader before failing.
                let _writer = fs::OpenOptions::new().write(true).open(&fifo);
                panic!("opening a swapped-in FIFO blocked");
            }
        }

        // A symlink swapped in, even to the expected file, is not followed.
        let link = temp.path().join("link");
        std::os::unix::fs::symlink(&regular, &link).unwrap();
        assert!(open_expected_regular_file(&link, &expected).is_err());

        // A different regular file fails the inode check.
        let other = temp.path().join("other");
        fs::write(&other, b"archive").unwrap();
        let err = open_expected_regular_file(&other, &expected).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);

        // The expected file opens and reads in full.
        let mut file = open_expected_regular_file(&regular, &expected).unwrap();
        let mut contents = Vec::new();
        file.read_to_end(&mut contents).unwrap();
        assert_eq!(contents, b"archive");

        // Through the public path, a FIFO is rejected up front and a symlink
        // to a regular archive is resolved before opening.
        let err = open_regular_local_archive(&fifo).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput);
        let mut contents = Vec::new();
        open_regular_local_archive(&link).unwrap().read_to_end(&mut contents).unwrap();
        assert_eq!(contents, b"archive");
    }
}
