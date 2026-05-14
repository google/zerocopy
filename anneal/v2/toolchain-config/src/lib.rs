/// Setup configuration binding external platform environments and baseline paths.
#[derive(Debug, Clone)]
pub struct Config<'a> {
    pub os: &'a str,
    pub arch: &'a str,
    pub url: &'a str,
    pub sha256: [u8; 32],
}

/// Optional runtime override directing installation from local dev builds instead of remote hosts.
#[derive(Debug, Clone)]
pub enum LocalOverride {
    Dir(std::path::PathBuf),
    Archive(std::path::PathBuf),
}

impl<'a> Config<'a> {
    /// Instantiates static toolchain parameters auto-detecting current runtime OS and Architecture.
    pub fn new(url: &'a str, sha256: [u8; 32]) -> Self {
        Self {
            os: std::env::consts::OS,
            arch: std::env::consts::ARCH,
            url,
            sha256,
        }
    }

    /// Explicitly overrides target platform parameters for specialized configurations.
    pub fn new_platform(os: &'a str, arch: &'a str, url: &'a str, sha256: [u8; 32]) -> Self {
        Self {
            os,
            arch,
            url,
            sha256,
        }
    }

    /// Resolves the deterministic subdirectory path containing the verified toolchain files.
    pub fn toolchain_dir(&self, root: &std::path::Path) -> std::path::PathBuf {
        let expected_hex = encode_hex(&self.sha256);
        root.join(&expected_hex[..6])
    }
}

/// An abstract extraction factory instantiating operational output streams targeting designated
/// filesystem paths.
///
/// Consuming software can utilize this trait interface to decouple core processing workflows
/// from concrete decompressor tools, facilitating modular injection of specialized archiving logic
/// or isolated testing frameworks.
pub trait Extractor {
    /// Unpacks stream bytes directly into the specified target directory synchronously on the calling thread.
    fn extract(&self, src: &mut dyn std::io::Read, dst: &std::path::Path) -> std::io::Result<()>;
}

/// A concrete [`Extractor`] implementation delegating archive extraction duties entirely in-process
/// via synchronous streaming pipelines using the `tar` and `zstd` library crates.
pub struct TarZstLibraryExtractor;

impl Extractor for TarZstLibraryExtractor {
    fn extract(&self, src: &mut dyn std::io::Read, dst: &std::path::Path) -> std::io::Result<()> {
        let decoder = zstd::Decoder::new(src)?;
        let mut archive = tar::Archive::new(decoder);
        archive.unpack(dst)
    }
}

fn encode_hex(bytes: &[u8; 32]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(64);
    for &b in bytes {
        write!(&mut s, "{:02x}", b).unwrap();
    }
    s
}

struct HashReader<R> {
    inner: R,
    hasher: sha2::Sha256,
}

impl<R: std::io::Read> HashReader<R> {
    fn new(inner: R) -> Self {
        use sha2::Digest;
        Self { inner, hasher: sha2::Sha256::new() }
    }

    fn finalize(self) -> [u8; 32] {
        use sha2::Digest;
        self.hasher.finalize().into()
    }
}

impl<R: std::io::Read> std::io::Read for HashReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        use sha2::Digest;
        let n = self.inner.read(buf)?;
        self.hasher.update(&buf[..n]);
        Ok(n)
    }
}

fn setup_from_archive(
    src: impl std::io::Read,
    dst: &std::path::Path,
    extractor: &dyn Extractor,
) -> Result<[u8; 32], std::io::Error> {
    let parent = dst.parent().expect("toolchains directory has parent");
    let temp_dir = tempfile::Builder::new().prefix("setup-").tempdir_in(parent)?;

    let mut hash_reader = HashReader::new(src);
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

fn setup_from_directory(src: &std::path::Path, dst: &std::path::Path) -> Result<(), String> {
    let parent = dst.parent().expect("toolchains directory has parent");
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

fn setup_inner(
    config: &Config<'_>,
    local_override: Option<LocalOverride>,
    toolchain_dir: std::path::PathBuf,
    fetcher: impl FnOnce(&str) -> Result<Box<dyn std::io::Read>, String>,
) -> Result<(), String> {
    let target_dir = config.toolchain_dir(&toolchain_dir);
    let expected_hex = encode_hex(&config.sha256);

    if let Some(override_src) = local_override {
        match override_src {
            LocalOverride::Archive(path) => {
                log::warn!(
                    "Toolchain contents from local archive may not match expected toolchain hash/version number."
                );
                let extractor = TarZstLibraryExtractor;
                let file = std::fs::File::open(path)
                    .map_err(|e| format!("Failed to open local archive: {e}"))?;
                setup_from_archive(file, &target_dir, &extractor)
                    .map_err(|e| format!("Failed to extract archive: {e}"))?;
            }
            LocalOverride::Dir(path) => {
                log::warn!(
                    "Toolchain contents from local directory may not match expected toolchain hash/version number."
                );
                setup_from_directory(&path, &target_dir)?;
            }
        }
    } else {
        let extractor = TarZstLibraryExtractor;
        let response = fetcher(config.url)?;

        let actual_hash: [u8; 32] = setup_from_archive(response, &target_dir, &extractor)
            .map_err(|e| format!("Failed to extract downloaded archive: {e}"))?;

        if actual_hash != config.sha256 {
            let _ = std::fs::remove_dir_all(&target_dir);
            return Err(format!(
                "Checksum mismatch for downloaded archive. Expected {}, got {}",
                expected_hex,
                encode_hex(&actual_hash)
            ));
        }
    }

    Ok(())
}

/// Coordinates the provisioning and verification of the active toolchain dependency environment.
///
/// This function processes the incoming dependency source and installs it into a toolchain
/// directory named according to the source SHA256 hash.
pub fn setup(
    config: &Config<'_>,
    local_override: Option<LocalOverride>,
    toolchain_dir: std::path::PathBuf,
) -> Result<(), String> {
    setup_inner(config, local_override, toolchain_dir, |url| {
        let response = reqwest::blocking::get(url)
            .map_err(|e| format!("Failed to download archive: {e}"))?;
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

    fn compute_sha256(path: &std::path::Path) -> [u8; 32] {
        use sha2::Digest;
        let mut file = std::fs::File::open(path).unwrap();
        let mut hasher = sha2::Sha256::new();
        std::io::copy(&mut file, &mut hasher).unwrap();
        hasher.finalize().into()
    }

    #[test]
    fn test_setup_from_directory() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("file.txt"), "hello").unwrap();

        let dst = temp.path().join("dst");
        setup_from_directory(&src, &dst).unwrap();

        assert!(dst.join("file.txt").exists());
        assert_eq!(std::fs::read_to_string(dst.join("file.txt")).unwrap(), "hello");

        // Test atomic replacement by running it again with updated contents
        let src2 = temp.path().join("src2");
        std::fs::create_dir(&src2).unwrap();
        std::fs::write(src2.join("file.txt"), "world").unwrap();

        setup_from_directory(&src2, &dst).unwrap();
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
        let hash = setup_from_archive(file, &dst, &TarZstLibraryExtractor).unwrap();

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
        let config = Config::new("http://example.com", expected_hash);
        let target_dir = config.toolchain_dir(temp.path());

        setup_inner(
            &config,
            Some(LocalOverride::Dir(src)),
            temp.path().to_path_buf(),
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
        let config = Config::new("http://example.com", expected_hash);
        let target_dir = config.toolchain_dir(temp.path());

        setup_inner(
            &config,
            Some(LocalOverride::Archive(archive_path)),
            temp.path().to_path_buf(),
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
        let config = Config::new("http://example.com", actual_hash);
        let target_dir = config.toolchain_dir(temp.path());

        let archive_path_clone = archive_path.clone();
        setup_inner(
            &config,
            None,
            temp.path().to_path_buf(),
            move |_url| {
                let file = std::fs::File::open(&archive_path_clone).unwrap();
                Ok(Box::new(file))
            },
        )
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

        let config = Config::new("http://example.com", expected_hash);
        let target_dir = config.toolchain_dir(temp.path());

        let archive_path_clone = archive_path.clone();
        let res = setup_inner(
            &config,
            None,
            temp.path().to_path_buf(),
            move |_url| {
                let file = std::fs::File::open(&archive_path_clone).unwrap();
                Ok(Box::new(file))
            },
        );

        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Checksum mismatch"));
        assert!(!target_dir.exists());
    }
}
