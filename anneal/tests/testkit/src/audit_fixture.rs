// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared Lean audit temporary fixture staging and cross-process `OleanCache`
//! helpers for `anneal-audit-tests` and `cargo-anneal-tests`.

use std::{
    fs,
    path::{Component, Path, PathBuf},
};

use crate::{
    TestResult,
    digest::sha256_hex,
    process::{Invocation, reject_symlink_components, write_regular_file},
    toolchain::ToolchainEnv,
};

/// Default vetted `Trusted.lean` header used by synthetic Lean audit fixtures.
pub const DEFAULT_VETTED_HEADER: &str =
    "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\n";

/// Controls whether a [`LeanAuditFixture`] binds its `Checker` environment to
/// an isolated per-fixture cache directory or to a persistent target-dir
/// [`SharedOleanCache`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OleanCachePolicy {
    /// Allocate a fresh empty cache root private to this fixture and remove it
    /// on drop (safe default for cache-tamper, cold-compile, and hostile-env
    /// regression tests).
    #[default]
    Isolated,
    /// Opt in to sharing a persistent cache root inside `CARGO_TARGET_DIR`
    /// (`$CARGO_TARGET_DIR/anneal-test-olean-cache`, or
    /// `<anneal_root>/target/anneal-test-olean-cache` when unset). Relies on
    /// `cargo-anneal`'s per-key `flock` and atomic rename so `cargo-nextest`
    /// test processes reuse compiled `TrustedBoundary` and bundled `.olean`
    /// artifacts without copying ambient `~/.cache` or leaking `/tmp`.
    Shared,
}

enum CacheRoot {
    /// Persistent workspace/target-dir root shared across test processes.
    Persistent,
    /// Ephemeral per-fixture or test-owned root removed automatically on drop.
    Ephemeral { _dir: tempfile::TempDir },
}

/// `.olean` cache root matching `OleanCache`'s XDG/macOS layout
/// (`<home>/.cache/anneal/olean-cache` on Linux,
/// `<home>/Library/Caches/anneal/olean-cache` on macOS).
///
/// Supports both:
/// - **Persistent shared roots** ([`Self::shared`],
///   [`Self::in_persistent_dir`]) backed by
///   `$CARGO_TARGET_DIR/anneal-test-olean-cache` (never `/tmp`, never copying
///   ambient `~/.cache`) for lock-safe reuse across `cargo-nextest` processes.
/// - **Ephemeral isolated or pre-seeded roots** ([`Self::isolated`],
///   [`Self::from_seed_dir`]) owned by a `TempDir` that restores permissions
///   and deletes itself cleanly on [`Drop`].
pub struct SharedOleanCache {
    root: CacheRoot,
    home_dir: PathBuf,
    xdg_cache_home: PathBuf,
    olean_cache_dir: PathBuf,
    seeded_entries: usize,
    readonly_root: bool,
}

impl Drop for SharedOleanCache {
    fn drop(&mut self) {
        // Restore write permissions only on ephemeral tempdirs so
        // `TempDir::drop` cleans up frozen entries without EACCES while
        // leaving persistent target-dir caches untouched.
        if matches!(self.root, CacheRoot::Ephemeral { .. }) {
            make_tree_writable_best_effort(&self.home_dir);
        }
    }
}

impl SharedOleanCache {
    /// Open or initialize the persistent shared cache root inside
    /// `CARGO_TARGET_DIR` (or `ANNEAL_TEST_OLEAN_CACHE_DIR` when explicitly
    /// overridden, falling back to
    /// `<anneal_root>/target/anneal-test-olean-cache`).
    ///
    /// Never copies ambient `~/.cache` and never allocates static `TempDir`s in
    /// `/tmp`. Safe across concurrent `cargo-nextest` processes because
    /// `cargo-anneal`'s `OleanCache` serializes entry writes with per-key
    /// `flock` and atomic directory renames.
    pub fn shared() -> TestResult<Self> {
        let root = resolve_persistent_cache_root(|k| std::env::var_os(k))?;
        Self::in_persistent_dir(root)
    }

    /// Open or initialize a persistent shared cache at `home_root`.
    pub fn in_persistent_dir(home_root: PathBuf) -> TestResult<Self> {
        create_private_dir_all(&home_root)?;
        let home_dir = fs::canonicalize(&home_root).unwrap_or(home_root);
        let (xdg_cache_home, olean_cache_dir) = initialize_cache_layout(&home_dir)?;
        Ok(Self {
            root: CacheRoot::Persistent,
            home_dir,
            xdg_cache_home,
            olean_cache_dir,
            seeded_entries: 0,
            readonly_root: false,
        })
    }

    /// Allocate a fresh empty ephemeral cache directory that is removed when
    /// dropped.
    pub fn isolated() -> TestResult<Self> {
        Self::from_seed_dir(None, false)
    }

    /// Allocate an ephemeral cache directory optionally seeded from
    /// `seed_olean_cache_dir` (when `Some` and pointing to a non-symlink
    /// directory containing `v2/`).
    ///
    /// Seeded `v2/<key>` entries are copied without following symlinks and
    /// frozen read-only (`0o500` dirs / `0o444` files on Unix). When
    /// `readonly_root` is `true`, `olean-cache` and `v2/` are also frozen
    /// `0o500`. All permissions are restored before deletion on [`Drop`].
    pub fn from_seed_dir(
        seed_olean_cache_dir: Option<&Path>,
        readonly_root: bool,
    ) -> TestResult<Self> {
        let mut builder = tempfile::Builder::new();
        builder.prefix("anneal-isolated-olean-cache-");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            builder.permissions(fs::Permissions::from_mode(0o700));
        }
        let dir = builder
            .tempdir()
            .map_err(|error| format!("create isolated olean cache tempdir: {error}"))?;
        let home_dir = fs::canonicalize(dir.path()).unwrap_or_else(|_| dir.path().to_path_buf());
        let (xdg_cache_home, olean_cache_dir) = initialize_cache_layout(&home_dir)?;
        let v2_dir = olean_cache_dir.join("v2");

        let mut seeded_entries = 0usize;
        if let Some(seed) = seed_olean_cache_dir {
            seeded_entries = copy_v2_entries_readonly(seed, &v2_dir)?;
        }

        if readonly_root {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(&v2_dir, fs::Permissions::from_mode(0o500))
                    .map_err(|error| format!("freeze {}: {error}", v2_dir.display()))?;
                fs::set_permissions(&olean_cache_dir, fs::Permissions::from_mode(0o500))
                    .map_err(|error| format!("freeze {}: {error}", olean_cache_dir.display()))?;
            }
        }

        Ok(Self {
            root: CacheRoot::Ephemeral { _dir: dir },
            home_dir,
            xdg_cache_home,
            olean_cache_dir,
            seeded_entries,
            readonly_root,
        })
    }

    /// Synthetic `HOME` directory whose default cache root is
    /// [`Self::olean_cache_dir`].
    pub fn home_dir(&self) -> &Path {
        &self.home_dir
    }

    /// `XDG_CACHE_HOME` directory containing `anneal/olean-cache`.
    pub fn xdg_cache_home(&self) -> &Path {
        &self.xdg_cache_home
    }

    /// Full path to `<cache>/anneal/olean-cache`.
    pub fn olean_cache_dir(&self) -> &Path {
        &self.olean_cache_dir
    }

    /// Number of pre-existing `v2/<key>` entries copied during seeding.
    pub fn seeded_entries(&self) -> usize {
        self.seeded_entries
    }

    /// Whether the `olean-cache` root itself was frozen read-only.
    pub fn is_readonly_root(&self) -> bool {
        self.readonly_root
    }

    /// Whether this handle points to a persistent shared directory rather than
    /// an ephemeral `TempDir`.
    pub fn is_persistent(&self) -> bool {
        matches!(self.root, CacheRoot::Persistent)
    }

    /// Build a clean `Checker::new_with_env`-compatible environment vector
    /// binding `HOME` (and `TMPDIR`, `LANG`, `LC_ALL` when present in the
    /// current process) plus `XDG_CACHE_HOME` to this cache.
    pub fn checker_env(&self) -> TestResult<Vec<(String, String)>> {
        let home = path_to_utf8(&self.home_dir, "HOME")?;
        let xdg = path_to_utf8(&self.xdg_cache_home, "XDG_CACHE_HOME")?;
        let mut env = vec![("HOME".to_string(), home), ("XDG_CACHE_HOME".to_string(), xdg)];
        for key in ["TMPDIR", "LANG", "LC_ALL"] {
            if let Some(val) = std::env::var_os(key)
                && let Ok(s) = val.into_string()
            {
                env.push((key.to_string(), s));
            }
        }
        Ok(env)
    }

    /// Apply `HOME` and `XDG_CACHE_HOME` to an [`Invocation`].
    pub fn apply_to_invocation(&self, invocation: &mut Invocation) {
        invocation.environment.insert("HOME".into(), self.home_dir.as_os_str().to_os_string());
        invocation
            .environment
            .insert("XDG_CACHE_HOME".into(), self.xdg_cache_home.as_os_str().to_os_string());
    }
}

/// Isolated temporary Anneal checkout seeded with Lean toolchain locks,
/// `TrustedBoundary.lean`, and `trusted/lean/Trusted.lean`, plus optional
/// [`SharedOleanCache`] environment helpers.
pub struct LeanAuditFixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
    cache_policy: OleanCachePolicy,
    cache: SharedOleanCache,
}

impl LeanAuditFixture {
    /// Create a temporary Lean audit fixture seeded from `checkout` using the
    /// default [`OleanCachePolicy::Isolated`].
    ///
    /// Copies `trusted/lean/lean-toolchain`,
    /// `trusted/lean/foundation-lock.json`,
    /// `trusted/audit/TrustedBoundary.lean`, and (when `with_library_lock` is
    /// `true`) `trusted/audit/library-lock.json`, then writes
    /// `trusted/lean/Trusted.lean` with `trusted_source` (or
    /// [`DEFAULT_VETTED_HEADER`] when `None`).
    pub fn new(
        checkout: &Path,
        prefix: &str,
        trusted_source: Option<&str>,
        with_library_lock: bool,
    ) -> TestResult<Self> {
        Self::with_cache_policy(
            checkout,
            prefix,
            trusted_source,
            with_library_lock,
            OleanCachePolicy::default(),
        )
    }

    /// Create a temporary Lean audit fixture with an explicit
    /// [`OleanCachePolicy`].
    pub fn with_cache_policy(
        checkout: &Path,
        prefix: &str,
        trusted_source: Option<&str>,
        with_library_lock: bool,
        cache_policy: OleanCachePolicy,
    ) -> TestResult<Self> {
        let cache = match cache_policy {
            OleanCachePolicy::Isolated => SharedOleanCache::isolated()?,
            OleanCachePolicy::Shared => SharedOleanCache::shared()?,
        };
        Self::with_cache(checkout, prefix, trusted_source, with_library_lock, cache_policy, cache)
    }

    /// Create a temporary Lean audit fixture backed by a caller-supplied
    /// [`SharedOleanCache`].
    pub fn with_cache(
        checkout: &Path,
        prefix: &str,
        trusted_source: Option<&str>,
        with_library_lock: bool,
        cache_policy: OleanCachePolicy,
        cache: SharedOleanCache,
    ) -> TestResult<Self> {
        Self::with_cache_in_temp(
            &std::env::temp_dir(),
            checkout,
            prefix,
            trusted_source,
            with_library_lock,
            cache_policy,
            cache,
        )
    }

    fn with_cache_in_temp(
        temp_parent: &Path,
        checkout: &Path,
        prefix: &str,
        trusted_source: Option<&str>,
        with_library_lock: bool,
        cache_policy: OleanCachePolicy,
        cache: SharedOleanCache,
    ) -> TestResult<Self> {
        let dir = tempfile::Builder::new()
            .prefix(prefix)
            .tempdir_in(temp_parent)
            .map_err(|error| format!("create Lean audit fixture dir: {error}"))?;
        // Canonicalize `dir.path()` so symlinked `TMPDIR` roots (e.g. macOS
        // `/var -> /private/var`) never trip `reject_symlink_components`.
        let root = fs::canonicalize(dir.path()).map_err(|error| {
            format!("canonicalize Lean audit fixture root {}: {error}", dir.path().display())
        })?;

        let mut locks = vec![
            "trusted/lean/lean-toolchain",
            "trusted/lean/foundation-lock.json",
            "trusted/audit/TrustedBoundary.lean",
        ];
        if with_library_lock {
            locks.push("trusted/audit/library-lock.json");
        }
        for rel in locks {
            let dst = root.join(rel);
            if let Some(parent) = dst.parent() {
                fs::create_dir_all(parent)
                    .map_err(|error| format!("create {}: {error}", parent.display()))?;
            }
            fs::copy(checkout.join(rel), &dst)
                .map_err(|error| format!("copy {rel} into fixture: {error}"))?;
        }

        write_regular_file(
            &root.join("trusted/lean/Trusted.lean"),
            trusted_source.unwrap_or(DEFAULT_VETTED_HEADER).as_bytes(),
        )?;

        Ok(Self { _dir: dir, root, cache_policy, cache })
    }

    /// Root path of the temporary checkout.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Active cache-sharing policy for this fixture.
    pub fn cache_policy(&self) -> OleanCachePolicy {
        self.cache_policy
    }

    /// Borrow the [`SharedOleanCache`] handle owned by this fixture.
    pub fn olean_cache(&self) -> &SharedOleanCache {
        &self.cache
    }

    /// Build a `Checker::new_with_env`-compatible environment vector backed by
    /// this fixture's [`SharedOleanCache`].
    pub fn checker_env(&self) -> TestResult<Vec<(String, String)>> {
        self.cache.checker_env()
    }

    /// Build a `Checker::new_with_env` environment vector combining this
    /// fixture's cache environment with caller-supplied hostile/override
    /// entries.
    pub fn checker_env_with<I>(&self, extra: I) -> TestResult<Vec<(String, String)>>
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let mut env = self.checker_env()?;
        env.extend(extra);
        Ok(env)
    }

    /// Write `bytes` to `<root>/<rel>`, creating parent directories as needed.
    ///
    /// Rejects empty paths, absolute paths, `.`, `..`, and any symlink
    /// component so fixture writes can never escape [`Self::root`].
    pub fn write_rel(&self, rel: impl AsRef<Path>, bytes: &[u8]) -> TestResult<PathBuf> {
        let rel = rel.as_ref();
        if rel.as_os_str().is_empty()
            || !rel.components().all(|c| matches!(c, Component::Normal(_)))
        {
            return Err(format!(
                "expected a fixture-relative path with normal components only: {}",
                rel.display()
            ));
        }
        let dest = self.root.join(rel);
        reject_symlink_components(&dest)?;
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
        write_regular_file(&dest, bytes)?;
        Ok(dest)
    }

    /// Write `<root>/inputs/<name>.lean` and return `(path, sha256_hex)`.
    ///
    /// Rejects empty, absolute, `.`, or `..` names before joining onto
    /// `inputs/`.
    pub fn write_input_lean(&self, name: &str, source: &str) -> TestResult<(PathBuf, String)> {
        let name_path = Path::new(name);
        if name.is_empty() || !name_path.components().all(|c| matches!(c, Component::Normal(_))) {
            return Err(format!("expected a fixture-relative Lean input name: {name:?}"));
        }
        let path =
            self.write_rel(Path::new("inputs").join(format!("{name}.lean")), source.as_bytes())?;
        Ok((path, sha256_hex(source.as_bytes())))
    }
}

fn resolve_persistent_cache_root(
    get_env: impl Fn(&str) -> Option<std::ffi::OsString>,
) -> TestResult<PathBuf> {
    if let Some(explicit) = get_env("ANNEAL_TEST_OLEAN_CACHE_DIR").filter(|v| !v.is_empty()) {
        return Ok(PathBuf::from(explicit));
    }
    if let Some(target_dir) = get_env("CARGO_TARGET_DIR").filter(|v| !v.is_empty()) {
        return Ok(PathBuf::from(target_dir).join("anneal-test-olean-cache"));
    }
    let repo_root = ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))?;
    Ok(repo_root.join("target/anneal-test-olean-cache"))
}

fn initialize_cache_layout(home_dir: &Path) -> TestResult<(PathBuf, PathBuf)> {
    let xdg_cache_home = if cfg!(target_os = "macos") {
        home_dir.join("Library/Caches")
    } else {
        home_dir.join(".cache")
    };
    let olean_cache_dir = xdg_cache_home.join("anneal/olean-cache");
    let v2_dir = olean_cache_dir.join("v2");
    create_private_dir_all(&v2_dir)?;
    Ok((xdg_cache_home, olean_cache_dir))
}

fn create_private_dir_all(path: &Path) -> TestResult {
    fs::create_dir_all(path).map_err(|error| format!("create {}: {error}", path.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o700));
    }
    Ok(())
}

fn strip_trailing_separators(path: &Path) -> PathBuf {
    #[cfg(unix)]
    {
        use std::{ffi::OsStr, os::unix::ffi::OsStrExt};
        let bytes = path.as_os_str().as_bytes();
        let mut end = bytes.len();
        while end > 1 && bytes[end - 1] == b'/' {
            end -= 1;
        }
        PathBuf::from(OsStr::from_bytes(&bytes[..end]))
    }
    #[cfg(not(unix))]
    {
        path.components().collect()
    }
}

fn copy_v2_entries_readonly(seed_olean_cache_dir: &Path, dest_v2_dir: &Path) -> TestResult<usize> {
    // Inspect `seed_olean_cache_dir` itself (with trailing `/` stripped so
    // POSIX `lstat` does not dereference a symlinked root) before joining
    // `"v2"`, rejecting symlinked roots and returning `Ok(0)` on missing or
    // regular-file paths without hitting `ENOTDIR`.
    let seed_root = strip_trailing_separators(seed_olean_cache_dir);
    let root_meta = match fs::symlink_metadata(&seed_root) {
        Ok(meta) => meta,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(0);
        }
        Err(error) => {
            return Err(format!("inspect {}: {error}", seed_root.display()));
        }
    };
    if root_meta.file_type().is_symlink() || !root_meta.is_dir() {
        return Ok(0);
    }

    let seed_v2 = seed_root.join("v2");
    let meta = match fs::symlink_metadata(&seed_v2) {
        Ok(meta) => meta,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(0);
        }
        Err(error) => {
            return Err(format!("inspect {}: {error}", seed_v2.display()));
        }
    };
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Ok(0);
    }

    let mut copied = 0usize;
    let entries =
        fs::read_dir(&seed_v2).map_err(|error| format!("list {}: {error}", seed_v2.display()))?;
    for entry in entries {
        let Ok(entry) = entry else {
            continue;
        };
        let name = entry.file_name();
        let Some(name_str) = name.to_str() else {
            continue;
        };
        // Skip in-progress temp directories and flock lockfiles; copy only
        // completed 64-hex-char content-addressed entry directories.
        if name_str.len() != 64 || !name_str.bytes().all(|b| b.is_ascii_hexdigit()) {
            continue;
        }
        let src_entry = entry.path();
        let Ok(entry_meta) = fs::symlink_metadata(&src_entry) else {
            continue;
        };
        if entry_meta.file_type().is_symlink() || !entry_meta.is_dir() {
            continue;
        }
        let dst_entry = dest_v2_dir.join(&name);
        if copy_single_cache_entry_readonly(&src_entry, &dst_entry).is_ok() {
            copied += 1;
        } else {
            make_tree_writable_best_effort(&dst_entry);
            let _ = fs::remove_dir_all(&dst_entry);
        }
    }
    Ok(copied)
}

fn copy_single_cache_entry_readonly(src: &Path, dst: &Path) -> TestResult {
    create_private_dir_all(dst)?;
    let mut saw_metadata = false;
    let entries = fs::read_dir(src).map_err(|error| format!("list {}: {error}", src.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| format!("read {}: {error}", src.display()))?;
        let src_file = entry.path();
        let meta = fs::symlink_metadata(&src_file)
            .map_err(|error| format!("stat {}: {error}", src_file.display()))?;
        if meta.file_type().is_symlink() || !meta.is_file() {
            return Err(format!("refusing non-regular cache entry member {}", src_file.display()));
        }
        if entry.file_name() == "metadata.json" {
            saw_metadata = true;
        }
        let dst_file = dst.join(entry.file_name());
        fs::copy(&src_file, &dst_file).map_err(|error| {
            format!("copy {} -> {}: {error}", src_file.display(), dst_file.display())
        })?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&dst_file, fs::Permissions::from_mode(0o444))
                .map_err(|error| format!("freeze {}: {error}", dst_file.display()))?;
        }
    }
    if !saw_metadata {
        return Err(format!("cache entry {} missing metadata.json", src.display()));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(dst, fs::Permissions::from_mode(0o500))
            .map_err(|error| format!("freeze {}: {error}", dst.display()))?;
    }
    Ok(())
}

fn make_tree_writable_best_effort(path: &Path) {
    let Ok(meta) = fs::symlink_metadata(path) else {
        return;
    };
    if meta.file_type().is_symlink() {
        return;
    }
    if meta.is_dir() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o700));
        }
        if let Ok(entries) = fs::read_dir(path) {
            for entry in entries.flatten() {
                make_tree_writable_best_effort(&entry.path());
            }
        }
    } else if meta.is_file() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o600));
        }
    }
}

fn path_to_utf8(path: &Path, label: &str) -> TestResult<String> {
    path.to_str()
        .map(ToOwned::to_owned)
        .ok_or_else(|| format!("{label} is not valid UTF-8: {}", path.display()))
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;

    use super::*;

    #[test]
    fn stages_locks_and_writes_hashed_inputs() {
        let checkout = tempfile::tempdir().unwrap();
        for rel in [
            "trusted/lean/lean-toolchain",
            "trusted/lean/foundation-lock.json",
            "trusted/audit/TrustedBoundary.lean",
            "trusted/audit/library-lock.json",
        ] {
            let p = checkout.path().join(rel);
            fs::create_dir_all(p.parent().unwrap()).unwrap();
            fs::write(p, rel.as_bytes()).unwrap();
        }

        let without_lib =
            LeanAuditFixture::new(checkout.path(), "test-nolib-", None, false).unwrap();
        assert!(without_lib.root().join("trusted/lean/Trusted.lean").is_file());
        assert!(!without_lib.root().join("trusted/audit/library-lock.json").exists());
        assert_eq!(without_lib.cache_policy(), OleanCachePolicy::Isolated);
        assert!(!without_lib.olean_cache().is_persistent());

        let shared_dir = tempfile::tempdir().unwrap();
        let persistent =
            SharedOleanCache::in_persistent_dir(shared_dir.path().join("target-cache")).unwrap();
        let with_lib = LeanAuditFixture::with_cache(
            checkout.path(),
            "test-lib-",
            Some("prelude\n"),
            true,
            OleanCachePolicy::Shared,
            persistent,
        )
        .unwrap();
        assert!(with_lib.root().join("trusted/audit/library-lock.json").is_file());
        assert_eq!(with_lib.cache_policy(), OleanCachePolicy::Shared);
        assert!(with_lib.olean_cache().is_persistent());
        assert_ne!(with_lib.olean_cache().home_dir(), without_lib.olean_cache().home_dir());
        let (path, hash) = with_lib.write_input_lean("Spec", "def x := 1\n").unwrap();
        assert_eq!(fs::read_to_string(path).unwrap(), "def x := 1\n");
        assert_eq!(hash, sha256_hex(b"def x := 1\n"));
    }

    #[test]
    fn write_rel_and_write_input_lean_reject_escape_and_non_normal_paths() {
        let checkout = tempfile::tempdir().unwrap();
        for rel in [
            "trusted/lean/lean-toolchain",
            "trusted/lean/foundation-lock.json",
            "trusted/audit/TrustedBoundary.lean",
        ] {
            let p = checkout.path().join(rel);
            fs::create_dir_all(p.parent().unwrap()).unwrap();
            fs::write(p, rel.as_bytes()).unwrap();
        }
        let outside = tempfile::tempdir().unwrap();
        let outside_file = outside.path().join("escaped.txt");
        let fix = LeanAuditFixture::new(checkout.path(), "test-escape-", None, false).unwrap();

        for bad in [
            "",
            ".",
            "..",
            "../escaped.txt",
            "sub/../escaped.txt",
            "./nested.txt",
            outside_file.to_str().unwrap(),
        ] {
            assert!(fix.write_rel(bad, b"boom").is_err(), "write_rel must reject {bad:?}");
        }
        for bad_name in
            ["", ".", "..", "../Escape", "Sub/../Escape", "./Spec", outside_file.to_str().unwrap()]
        {
            assert!(
                fix.write_input_lean(bad_name, "def x := 0\n").is_err(),
                "write_input_lean must reject {bad_name:?}"
            );
        }
        assert!(!outside_file.exists());
    }

    #[cfg(unix)]
    #[test]
    fn fixture_succeeds_under_symlinked_temp_parent() {
        let checkout = tempfile::tempdir().unwrap();
        for rel in [
            "trusted/lean/lean-toolchain",
            "trusted/lean/foundation-lock.json",
            "trusted/audit/TrustedBoundary.lean",
        ] {
            let p = checkout.path().join(rel);
            fs::create_dir_all(p.parent().unwrap()).unwrap();
            fs::write(p, rel.as_bytes()).unwrap();
        }
        let outer = tempfile::tempdir().unwrap();
        let real_tmp = outer.path().join("real-tmp");
        let sym_tmp = outer.path().join("sym-tmp");
        fs::create_dir_all(&real_tmp).unwrap();
        std::os::unix::fs::symlink(&real_tmp, &sym_tmp).unwrap();

        let cache = SharedOleanCache::isolated().unwrap();
        let fix = LeanAuditFixture::with_cache_in_temp(
            &sym_tmp,
            checkout.path(),
            "test-sym-tmp-",
            None,
            false,
            OleanCachePolicy::Isolated,
            cache,
        )
        .unwrap();
        assert_eq!(fix.root(), fs::canonicalize(fix.root()).unwrap());
        let written = fix.write_rel("nested/Extra.lean", b"def y := 2\n").unwrap();
        assert_eq!(fs::read(&written).unwrap(), b"def y := 2\n");
        let (inp, _) = fix.write_input_lean("Spec", "def z := 3\n").unwrap();
        assert!(inp.is_file());
    }

    #[test]
    fn persistent_cache_root_prefers_override_then_cargo_target_dir() {
        let explicit = resolve_persistent_cache_root(|k| match k {
            "ANNEAL_TEST_OLEAN_CACHE_DIR" => Some(OsString::from("/custom/cache-root")),
            "CARGO_TARGET_DIR" => Some(OsString::from("/ignored/target")),
            _ => None,
        })
        .unwrap();
        assert_eq!(explicit, PathBuf::from("/custom/cache-root"));

        let from_target = resolve_persistent_cache_root(|k| match k {
            "CARGO_TARGET_DIR" => Some(OsString::from("/build/target")),
            _ => None,
        })
        .unwrap();
        assert_eq!(from_target, PathBuf::from("/build/target/anneal-test-olean-cache"));

        let fallback = resolve_persistent_cache_root(|_| None).unwrap();
        assert!(fallback.ends_with("target/anneal-test-olean-cache"));
    }

    #[test]
    fn persistent_cache_survives_drop_and_ephemeral_cache_cleans_up() {
        let parent = tempfile::tempdir().unwrap();
        let persistent_root = parent.path().join("shared-cache");
        let persisted_v2 = {
            let cache = SharedOleanCache::in_persistent_dir(persistent_root.clone()).unwrap();
            assert!(cache.is_persistent());
            let marker = cache.olean_cache_dir().join("v2/marker");
            fs::write(&marker, b"ok").unwrap();
            marker
        };
        assert_eq!(fs::read(&persisted_v2).unwrap(), b"ok");

        let ephemeral_home = {
            let cache = SharedOleanCache::isolated().unwrap();
            assert!(!cache.is_persistent());
            cache.home_dir().to_path_buf()
        };
        assert!(!ephemeral_home.exists());
    }

    #[test]
    fn seeded_olean_cache_freezes_v2_entries_readonly_skips_junk_and_drops_cleanly() {
        let seed_root = tempfile::tempdir().unwrap();
        let key = "a".repeat(64);
        let valid_entry = seed_root.path().join("v2").join(&key);
        fs::create_dir_all(&valid_entry).unwrap();
        fs::write(valid_entry.join("metadata.json"), b"{}").unwrap();
        fs::write(valid_entry.join("module.olean"), b"olean-bytes").unwrap();
        // Temp dir, lockfile, and incomplete entry must be skipped.
        fs::create_dir_all(seed_root.path().join("v2/.tmp-inflight")).unwrap();
        fs::write(seed_root.path().join(format!("v2/{key}.lock")), b"").unwrap();
        let incomplete = seed_root.path().join("v2").join("b".repeat(64));
        fs::create_dir_all(&incomplete).unwrap();
        fs::write(incomplete.join("module.olean"), b"no-meta").unwrap();

        let home_path = {
            let cache = SharedOleanCache::from_seed_dir(Some(seed_root.path()), true).unwrap();
            assert_eq!(cache.seeded_entries(), 1);
            assert!(cache.is_readonly_root());
            let dst_entry = cache.olean_cache_dir().join("v2").join(&key);
            assert_eq!(fs::read(dst_entry.join("module.olean")).unwrap(), b"olean-bytes");
            assert!(!cache.olean_cache_dir().join("v2/.tmp-inflight").exists());
            assert!(!cache.olean_cache_dir().join("v2").join("b".repeat(64)).exists());

            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                assert_eq!(fs::metadata(&dst_entry).unwrap().permissions().mode() & 0o777, 0o500);
                assert_eq!(
                    fs::metadata(dst_entry.join("module.olean")).unwrap().permissions().mode()
                        & 0o777,
                    0o444
                );
                assert_eq!(
                    fs::metadata(cache.olean_cache_dir()).unwrap().permissions().mode() & 0o777,
                    0o500
                );
            }

            let env = cache.checker_env().unwrap();
            assert!(env.iter().any(|(k, v)| k == "HOME" && Path::new(v) == cache.home_dir()));
            assert!(
                env.iter()
                    .any(|(k, v)| k == "XDG_CACHE_HOME" && Path::new(v) == cache.xdg_cache_home())
            );
            cache.home_dir().to_path_buf()
        };
        // Drop must restore permissions on the frozen tree and remove it.
        assert!(!home_path.exists());
    }

    #[test]
    fn from_seed_dir_skips_symlinked_and_regular_file_seed_roots() {
        let outer = tempfile::tempdir().unwrap();
        let real_seed = outer.path().join("real-seed");
        let key = "c".repeat(64);
        let valid_entry = real_seed.join("v2").join(&key);
        fs::create_dir_all(&valid_entry).unwrap();
        fs::write(valid_entry.join("metadata.json"), b"{}").unwrap();
        fs::write(valid_entry.join("module.olean"), b"olean-bytes").unwrap();

        // Regular file at `seed_olean_cache_dir` must return `Ok` with 0
        // entries rather than failing with `ENOTDIR` on `<file>/v2`.
        let regular_file = outer.path().join("not-a-dir");
        fs::write(&regular_file, b"regular file").unwrap();
        let from_file = SharedOleanCache::from_seed_dir(Some(&regular_file), false).unwrap();
        assert_eq!(from_file.seeded_entries(), 0);
        assert!(!from_file.olean_cache_dir().join("v2").join(&key).exists());

        #[cfg(unix)]
        {
            // Symlinked `seed_olean_cache_dir` (both bare and with trailing
            // `/`) must not be traversed to copy `real_seed/v2/*`.
            let sym_seed = outer.path().join("sym-seed");
            std::os::unix::fs::symlink(&real_seed, &sym_seed).unwrap();
            let from_sym = SharedOleanCache::from_seed_dir(Some(&sym_seed), false).unwrap();
            assert_eq!(from_sym.seeded_entries(), 0);
            assert!(!from_sym.olean_cache_dir().join("v2").join(&key).exists());

            let sym_trailing = PathBuf::from(format!("{}/", sym_seed.display()));
            let from_sym_slash =
                SharedOleanCache::from_seed_dir(Some(&sym_trailing), false).unwrap();
            assert_eq!(from_sym_slash.seeded_entries(), 0);
            assert!(!from_sym_slash.olean_cache_dir().join("v2").join(&key).exists());
        }
    }
}
