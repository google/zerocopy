#[derive(Debug, Clone)]
pub struct RemoteArchive<'a, E>(pub &'a str, pub std::marker::PhantomData<E>);

#[derive(Debug, Clone)]
pub struct Checksum<'a, D>(pub &'a [u8], pub std::marker::PhantomData<D>);

impl<'a, E> RemoteArchive<'a, E> {
    pub fn new(url: &'a str) -> Self {
        Self(url, std::marker::PhantomData)
    }
    pub fn url(&self) -> &'a str {
        self.0
    }
}

impl<'a, D> Checksum<'a, D> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self(bytes, std::marker::PhantomData)
    }
    pub fn bytes(&self) -> &'a [u8] {
        self.0
    }
}

/// Setup configuration specifying platform, remote source, and remote checksum.
#[derive(Debug, Clone)]
pub struct Config<'a, E, D> {
    pub os: &'a str,
    pub arch: &'a str,
    pub remote: RemoteArchive<'a, E>,
    pub checksum: Checksum<'a, D>,
}

/// Local toolchain definition that overrides remote specified in [`Config`].
#[derive(Debug, Clone)]
pub enum LocalOverride<'a, E: Extractor = NoExtractor> {
    Dir(&'a std::path::Path),
    Archive((&'a std::path::Path, std::marker::PhantomData<E>)),
}

impl<'a, E: Extractor> LocalOverride<'a, E> {
    pub fn dir(path: &'a std::path::Path) -> Self {
        Self::Dir(path)
    }

    pub fn archive(path: &'a std::path::Path) -> Self {
        Self::Archive((path, std::marker::PhantomData))
    }
}

impl<'a, E: Extractor, D: digest::Digest> Config<'a, E, D> {
    /// Instantiates static toolchain parameters auto-detecting current runtime OS and Architecture.
    pub fn new(remote: RemoteArchive<'a, E>, checksum: Checksum<'a, D>) -> Self {
        Self { os: std::env::consts::OS, arch: std::env::consts::ARCH, remote, checksum }
    }

    /// Explicitly overrides target platform parameters for specialized configurations.
    pub fn new_platform(
        os: &'a str,
        arch: &'a str,
        remote: RemoteArchive<'a, E>,
        checksum: Checksum<'a, D>,
    ) -> Self {
        Self { os, arch, remote, checksum }
    }

    /// Resolves the deterministic subdirectory path containing the verified toolchain files.
    pub fn toolchain_dir(&self, root: &std::path::Path) -> std::path::PathBuf {
        let expected_hex = encode_hex(self.checksum.bytes());
        root.join(&format!("{}-{}-{}", self.os, self.arch, &expected_hex[..12]))
    }
}

/// An abstract extraction factory instantiating operational output streams targeting designated
/// filesystem paths.
pub trait Extractor {
    /// Instantiates a new instance of this extractor type.
    ///
    /// Instantiated and used for extracting archives downloaded from [`Config::url`] or archives
    /// designated by [`LocalOverride::Archive`].
    fn new() -> Self
    where
        Self: Sized;

    /// Unpacks stream bytes directly into the specified target directory synchronously on the calling thread.
    fn extract(&self, src: &mut dyn std::io::Read, dst: &std::path::Path) -> std::io::Result<()>;
}

/// Marker type used by [`LocalOverride::Dir`] (which implies no archive extraction).
pub struct NoExtractor;

impl Extractor for NoExtractor {
    fn new() -> Self {
        panic!("NoExtractor is not constructible");
    }
    fn extract(&self, _src: &mut dyn std::io::Read, _dst: &std::path::Path) -> std::io::Result<()> {
        panic!("Attempt to extract using NoExtractor");
    }
}

/// A concrete [`Extractor`] implementation delegating archive extraction duties entirely in-process
/// via synchronous streaming pipelines using the `tar` and `zstd` library crates.
pub struct TarZstLibraryExtractor;

impl Extractor for TarZstLibraryExtractor {
    fn new() -> Self {
        Self
    }
    fn extract(&self, src: &mut dyn std::io::Read, dst: &std::path::Path) -> std::io::Result<()> {
        let decoder = zstd::Decoder::new(src)?;
        let mut archive = tar::Archive::new(decoder);
        archive.unpack(dst)
    }
}

fn encode_hex(bytes: &[u8]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        write!(&mut s, "{:02x}", b).unwrap();
    }
    s
}

/// [`std::io::Read`] abstraction that encapsulates read-and-update-hasher.
struct HashReader<R, D> {
    inner: R,
    hasher: D,
}

impl<R: std::io::Read, D: digest::Digest> HashReader<R, D> {
    fn new(inner: R) -> Self {
        Self { inner, hasher: D::new() }
    }

    fn finalize(self) -> Vec<u8> {
        self.hasher.finalize().to_vec()
    }
}

impl<R: std::io::Read, D: digest::Digest> std::io::Read for HashReader<R, D> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = self.inner.read(buf)?;
        self.hasher.update(&buf[..n]);
        Ok(n)
    }
}

fn install_from_archive<E: Extractor, D: digest::Digest>(
    src: impl std::io::Read,
    dst: &std::path::Path,
    extractor: &E,
) -> Result<Vec<u8>, std::io::Error> {
    let parent = dst.parent().expect("toolchains directory has parent");
    std::fs::create_dir_all(parent)?;
    let temp_dir = tempfile::Builder::new().prefix("setup-").tempdir_in(parent)?;

    let mut hash_reader = HashReader::<_, D>::new(src);
    extractor.extract(&mut hash_reader, temp_dir.path())?;

    // Handle atomic overwrite if dst already occupies the target path
    let old_dir = if dst.symlink_metadata().is_ok() {
        let old = tempfile::Builder::new().prefix("setup-old-").tempdir_in(parent)?;
        let target_old = old.path().join("old");
        std::fs::rename(dst, &target_old)?;
        Some(old)
    } else {
        None
    };

    // Retain (renamed) extraction directory.
    let temp_dir_path = temp_dir.keep();
    std::fs::rename(&temp_dir_path, dst)?;

    // Drop/delete (renamed) old directory (if it exists).
    drop(old_dir);

    Ok(hash_reader.finalize())
}

#[cfg(not(unix))]
fn copy_dir_all(src: &std::path::Path, dst: &std::path::Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;
    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let ft = entry.file_type()?;
        let target = dst.join(entry.file_name());
        if ft.is_dir() {
            copy_dir_all(&entry.path(), &target)?;
        } else {
            std::fs::copy(&entry.path(), &target)?;
        }
    }
    Ok(())
}

fn link_or_copy_dir(src: &std::path::Path, dst: &std::path::Path) -> std::io::Result<()> {
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(src, dst)
    }
    #[cfg(not(unix))]
    {
        #[cfg(windows)]
        {
            if std::os::windows::fs::symlink_dir(src, dst).is_ok() {
                return Ok(());
            }
            log::warn!(
                "Native directory symlink creation failed. Falling back to recursive directory copy."
            );
        }
        #[cfg(not(windows))]
        {
            log::warn!(
                "Symbolic linking not natively configured for this platform. Falling back to recursive directory copy."
            );
        }

        copy_dir_all(src, dst)
    }
}

fn install_from_directory(src: &std::path::Path, dst: &std::path::Path) -> Result<(), String> {
    let parent = dst.parent().expect("toolchains directory has parent");
    std::fs::create_dir_all(parent)
        .map_err(|e| format!("Failed to create toolchain parent directory: {e}"))?;
    let old_dir = if dst.symlink_metadata().is_ok() {
        let old = tempfile::Builder::new()
            .prefix("setup-old-")
            .tempdir_in(parent)
            .map_err(|e| format!("Failed to create temp dir for old target: {e}"))?;
        let target_old = old.path().join("old");
        std::fs::rename(dst, &target_old)
            .map_err(|e| format!("Failed to rename existing target: {e}"))?;
        Some(old)
    } else {
        None
    };

    link_or_copy_dir(src, dst)
        .map_err(|e| format!("Failed to link or copy local directory: {e}"))?;

    drop(old_dir);
    Ok(())
}

fn install_inner<CE: Extractor, D: digest::Digest, LE: Extractor>(
    config: &Config<'_, CE, D>,
    local_override: Option<LocalOverride<'_, LE>>,
    toolchain_root: &std::path::Path,
    fetcher: impl FnOnce(&str) -> Result<Box<dyn std::io::Read>, String>,
) -> Result<(), String> {
    let toolchain_dir = config.toolchain_dir(toolchain_root);
    let expected_hex = encode_hex(config.checksum.bytes());

    if let Some(override_src) = local_override {
        match override_src {
            LocalOverride::Archive((path, _)) => {
                log::warn!(
                    "Toolchain contents from local archive may not match expected toolchain hash/version number."
                );
                let extractor = LE::new();
                let file = std::fs::File::open(path)
                    .map_err(|e| format!("Failed to open local archive: {e}"))?;
                install_from_archive::<LE, D>(file, &toolchain_dir, &extractor)
                    .map_err(|e| format!("Failed to extract archive: {e}"))?;
            }
            LocalOverride::Dir(path) => {
                log::warn!(
                    "Toolchain contents from local directory may not match expected toolchain hash/version number."
                );
                install_from_directory(path, &toolchain_dir)?;
            }
        }
    } else {
        let extractor = CE::new();
        let response = fetcher(config.remote.url())?;

        let actual_hash = install_from_archive::<CE, D>(response, &toolchain_dir, &extractor)
            .map_err(|e| format!("Failed to extract downloaded archive: {e}"))?;

        if actual_hash.as_slice() != config.checksum.bytes() {
            let _ = std::fs::remove_dir_all(&toolchain_dir);
            return Err(format!(
                "Checksum mismatch for downloaded archive. Expected {}, got {}",
                expected_hex,
                encode_hex(&actual_hash)
            ));
        }
    }

    Ok(())
}

/// Install a toolchain packaged with all its dependencies.
///
/// The default behaviour is to install according to the remote URL and checksom in `config`. If
/// `local_override` is provided, however, the toolchain naming convention associated with `config`
/// will be used to install a local directory or archive.
pub fn install<CE: Extractor, D: digest::Digest, LE: Extractor>(
    config: &Config<'_, CE, D>,
    local_override: Option<LocalOverride<'_, LE>>,
    toolchain_root: &std::path::Path,
) -> Result<(), String> {
    install_inner(config, local_override, toolchain_root, |url| {
        let response =
            reqwest::blocking::get(url).map_err(|e| format!("Failed to download archive: {e}"))?;
        let response = response
            .error_for_status()
            .map_err(|e| format!("HTTP error downloading archive: {e}"))?;
        Ok(Box::new(response))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_archive(src_dir: &std::path::Path, archive_path: &std::path::Path) {
        let file = std::fs::File::create(archive_path).unwrap();
        let encoder = zstd::Encoder::new(file, 0).unwrap();
        let mut builder = tar::Builder::new(encoder);
        builder.append_dir_all(".", src_dir).unwrap();
        let encoder = builder.into_inner().unwrap();
        encoder.finish().unwrap();
    }

    fn compute_sha256(path: &std::path::Path) -> Vec<u8> {
        use sha2::Digest;
        let mut file = std::fs::File::open(path).unwrap();
        let mut hasher = sha2::Sha256::new();
        std::io::copy(&mut file, &mut hasher).unwrap();
        hasher.finalize().to_vec()
    }

    #[test]
    fn test_setup_from_directory() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("file.txt"), "hello").unwrap();

        let dst = temp.path().join("dst");
        install_from_directory(&src, &dst).unwrap();

        assert!(dst.join("file.txt").exists());
        assert_eq!(std::fs::read_to_string(dst.join("file.txt")).unwrap(), "hello");

        // Test atomic replacement by running it again with updated contents
        let src2 = temp.path().join("src2");
        std::fs::create_dir(&src2).unwrap();
        std::fs::write(src2.join("file.txt"), "world").unwrap();

        install_from_directory(&src2, &dst).unwrap();
        assert_eq!(std::fs::read_to_string(dst.join("file.txt")).unwrap(), "world");
    }

    #[test]
    fn test_setup_from_archive() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("data.txt"), "archive_content").unwrap();

        let archive_path = temp.path().join("test.tar.zst");
        create_test_archive(&src, &archive_path);

        let dst = temp.path().join("dst");
        let file = std::fs::File::open(&archive_path).unwrap();
        let hash = install_from_archive::<TarZstLibraryExtractor, sha2::Sha256>(
            file,
            &dst,
            &TarZstLibraryExtractor,
        )
        .unwrap();

        assert_eq!(hash, compute_sha256(&archive_path));
        assert_eq!(std::fs::read_to_string(dst.join("data.txt")).unwrap(), "archive_content");
    }

    #[test]
    fn test_setup_inner_local_directory() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "local_dir").unwrap();

        let expected_hash = [1u8; 32];
        let config = Config::<TarZstLibraryExtractor, sha2::Sha256>::new(
            RemoteArchive::new("http://example.com"),
            Checksum::new(&expected_hash),
        );
        let target_dir = config.toolchain_dir(temp.path());

        install_inner(
            &config,
            Some(LocalOverride::<NoExtractor>::dir(&src)),
            temp.path(),
            |_| unreachable!(),
        )
        .unwrap();

        assert_eq!(std::fs::read_to_string(target_dir.join("test.txt")).unwrap(), "local_dir");
    }

    #[test]
    fn test_setup_inner_local_archive() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "local_archive").unwrap();

        let archive_path = temp.path().join("archive.tar.zst");
        create_test_archive(&src, &archive_path);

        let expected_hash = [2u8; 32];
        let config = Config::<TarZstLibraryExtractor, sha2::Sha256>::new(
            RemoteArchive::new("http://example.com"),
            Checksum::new(&expected_hash),
        );
        let target_dir = config.toolchain_dir(temp.path());

        install_inner(
            &config,
            Some(LocalOverride::<TarZstLibraryExtractor>::archive(&archive_path)),
            temp.path(),
            |_| unreachable!(),
        )
        .unwrap();

        assert_eq!(std::fs::read_to_string(target_dir.join("test.txt")).unwrap(), "local_archive");
    }

    #[test]
    fn test_setup_inner_remote_success() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "remote_content").unwrap();

        let archive_path = temp.path().join("remote.tar.zst");
        create_test_archive(&src, &archive_path);

        let actual_hash = compute_sha256(&archive_path);
        let config = Config::<TarZstLibraryExtractor, sha2::Sha256>::new(
            RemoteArchive::new("http://example.com"),
            Checksum::new(&actual_hash),
        );
        let target_dir = config.toolchain_dir(temp.path());

        let archive_path_clone = archive_path.clone();
        install_inner::<_, _, NoExtractor>(&config, None, temp.path(), move |_url| {
            let file = std::fs::File::open(&archive_path_clone).unwrap();
            Ok(Box::new(file))
        })
        .unwrap();

        assert_eq!(std::fs::read_to_string(target_dir.join("test.txt")).unwrap(), "remote_content");
    }

    #[test]
    fn test_setup_inner_remote_checksum_mismatch() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "bad_remote").unwrap();

        let archive_path = temp.path().join("bad_remote.tar.zst");
        create_test_archive(&src, &archive_path);

        let actual_hash = compute_sha256(&archive_path);
        let mut expected_hash = actual_hash;
        expected_hash[0] ^= 1; // invalidate checksum

        let config = Config::<TarZstLibraryExtractor, sha2::Sha256>::new(
            RemoteArchive::new("http://example.com"),
            Checksum::new(&expected_hash),
        );
        let target_dir = config.toolchain_dir(temp.path());

        let archive_path_clone = archive_path.clone();
        let res = install_inner::<_, _, NoExtractor>(&config, None, temp.path(), move |_url| {
            let file = std::fs::File::open(&archive_path_clone).unwrap();
            Ok(Box::new(file))
        });

        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Checksum mismatch"));
        assert!(!target_dir.exists());
    }
}
