#[derive(Debug)]
pub struct RemoteArchive<'a> {
    url: &'a str,
    extractor: &'a dyn Extractor,
}

pub struct Checksum<'a> {
    bytes: &'a [u8],
    digest: &'a mut dyn digest::DynDigest,
}

impl<'a> RemoteArchive<'a> {
    pub fn new(url: &'a str, extractor: &'a dyn Extractor) -> Self {
        Self { url, extractor }
    }
    pub fn url(&self) -> &'a str {
        self.url
    }
    pub fn extractor(&self) -> &'a dyn Extractor {
        self.extractor
    }
}

impl<'a> Checksum<'a> {
    pub fn new(bytes: &'a [u8], digest: &'a mut dyn digest::DynDigest) -> Self {
        Self { bytes, digest }
    }
    pub fn bytes(&self) -> &'a [u8] {
        self.bytes
    }
}

/// Setup configuration specifying platform, remote source, and remote checksum.
pub struct Config<'a> {
    pub os: &'a str,
    pub arch: &'a str,
    pub remote: RemoteArchive<'a>,
    pub checksum: Checksum<'a>,
}

/// Local toolchain definition that overrides remote specified in [`Config`].
#[derive(Debug, Clone)]
pub enum LocalOverride<'a> {
    Dir(&'a std::path::Path),
    Archive(&'a std::path::Path, &'a dyn Extractor),
}

impl<'a> LocalOverride<'a> {
    pub fn dir(path: &'a std::path::Path) -> Self {
        Self::Dir(path)
    }

    pub fn archive(path: &'a std::path::Path, extractor: &'a dyn Extractor) -> Self {
        Self::Archive(path, extractor)
    }
}

impl<'a> Config<'a> {
    /// Instantiates static toolchain parameters auto-detecting current runtime OS and Architecture.
    pub fn new(remote: RemoteArchive<'a>, checksum: Checksum<'a>) -> Self {
        Self { os: std::env::consts::OS, arch: std::env::consts::ARCH, remote, checksum }
    }

    /// Explicitly overrides target platform parameters for specialized configurations.
    pub fn new_platform(
        os: &'a str,
        arch: &'a str,
        remote: RemoteArchive<'a>,
        checksum: Checksum<'a>,
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
    /// Unpacks stream bytes directly into the specified target directory synchronously on the calling thread.
    fn extract(&self, src: &mut dyn std::io::Read, dst: &std::path::Path) -> std::io::Result<()>;
}

/// Implement core Extractor methods natively on generic references dynamically.
impl<'a> std::fmt::Debug for dyn Extractor + 'a {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Extractor")
    }
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

fn encode_hex(bytes: &[u8]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        write!(&mut s, "{:02x}", b).unwrap();
    }
    s
}

/// [`std::io::Read`] abstraction that encapsulates read-and-update-hasher dynamically.
struct HashReader<'a, R> {
    inner: R,
    hasher: &'a mut dyn digest::DynDigest,
}

impl<'a, R: std::io::Read> HashReader<'a, R> {
    fn new(inner: R, hasher: &'a mut dyn digest::DynDigest) -> Self {
        Self { inner, hasher }
    }

    fn finalize(self) -> Box<[u8]> {
        self.hasher.finalize_reset()
    }
}

impl<'a, R: std::io::Read> std::io::Read for HashReader<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = self.inner.read(buf)?;
        self.hasher.update(&buf[..n]);
        Ok(n)
    }
}

fn install_from_archive(
    src: impl std::io::Read,
    dst: &std::path::Path,
    extractor: &dyn Extractor,
    hasher: &mut dyn digest::DynDigest,
) -> Result<Box<[u8]>, std::io::Error> {
    let parent = dst.parent().expect("toolchains directory has parent");
    std::fs::create_dir_all(parent)?;
    let temp_dir = tempfile::Builder::new().prefix("setup-").tempdir_in(parent)?;

    let mut hash_reader = HashReader::new(src, hasher);
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

fn install_inner(
    config: &mut Config<'_>,
    local_override: Option<LocalOverride<'_>>,
    toolchain_root: &std::path::Path,
    fetcher: impl FnOnce(&str) -> Result<Box<dyn std::io::Read>, String>,
) -> Result<(), String> {
    let toolchain_dir = config.toolchain_dir(toolchain_root);
    let expected_hex = encode_hex(config.checksum.bytes());

    if let Some(override_src) = local_override {
        match override_src {
            LocalOverride::Archive(path, extractor) => {
                log::warn!(
                    "Toolchain contents from local archive may not match expected toolchain hash/version number."
                );
                let file = std::fs::File::open(path)
                    .map_err(|e| format!("Failed to open local archive: {e}"))?;
                install_from_archive(file, &toolchain_dir, extractor, &mut *config.checksum.digest)
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
        let response = fetcher(config.remote.url())?;

        let actual_hash = install_from_archive(
            response,
            &toolchain_dir,
            config.remote.extractor(),
            &mut *config.checksum.digest,
        )
        .map_err(|e| format!("Failed to extract downloaded archive: {e}"))?;

        if actual_hash.as_ref() != config.checksum.bytes() {
            let _ = std::fs::remove_dir_all(&toolchain_dir);
            return Err(format!(
                "Checksum mismatch for downloaded archive. Expected {}, got {}",
                expected_hex,
                encode_hex(actual_hash.as_ref())
            ));
        }
    }

    Ok(())
}

/// Install a toolchain packaged with all its dependencies.
///
/// The default behaviour is to install according to the remote URL and checksum in `config`. If
/// `local_override` is provided, however, the toolchain naming convention associated with `config`
/// will be used to install a local directory or archive natively.
pub fn install_config(
    config: &mut Config<'_>,
    local_override: Option<LocalOverride<'_>>,
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

pub struct Config2<'a> {
    pub url: &'a str,
    pub checksum: &'a [u8],
}

#[macro_export]
macro_rules! auto_install {
    ($vis:vis const $name:ident = $toml_config_file_path:literal ;) => {
        $vis const $name: $crate::Config2 = {
            // TODO: This doesn't actually work without the consumer depending on `toml_const`. Bleh.
            use $crate::macro_util::toml_const;
            toml_const::toml_const! {
                const TOML_CONFIG: $toml_config_file_path;
            }

            use std::env::consts::*;
            let config = match ($crate::macro_util::pack(OS), $crate::macro_util::pack(ARCH)) {
                ($crate::macro_util::LINUX, $crate::macro_util::X86_64) => TOML_CONFIG.package.toolchain.linux.x86_64,
                (_, _) => panic!("Unsupported os.arch on this machine"),
            };
            let url = config.url;
            let checksum = config.checksum;
            $crate::Config2 {
                url: url,
                checksum: &match $crate::macro_util::decode_hex(checksum) {
                    Some(checksum) => checksum,
                    None => panic!("Invalid hex-digit checksum in this machine's package.toolchain.<os>.<arch>.checksum field"),
                },
            }
        };
    }
}

#[doc(hidden)]
pub mod macro_util {
    pub use toml_const;

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

    pub const LINUX: u128 = pack("linux");
    pub const MACOS: u128 = pack("macos");
    pub const X86_64: u128 = pack("x86_64");
    pub const AARCH64: u128 = pack("aarch64");
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::Digest;

    fn create_test_archive(src_dir: &std::path::Path, archive_path: &std::path::Path) {
        let file = std::fs::File::create(archive_path).unwrap();
        let encoder = zstd::Encoder::new(file, 0).unwrap();
        let mut builder = tar::Builder::new(encoder);
        builder.append_dir_all(".", src_dir).unwrap();
        let encoder = builder.into_inner().unwrap();
        encoder.finish().unwrap();
    }

    fn compute_sha256(path: &std::path::Path) -> Vec<u8> {
        let mut file = std::fs::File::open(path).unwrap();
        let mut hasher = sha2::Sha256::new();
        std::io::copy(&mut file, &mut hasher).unwrap();
        hasher.finalize().to_vec()
    }

    #[test]
    fn test_install_from_directory() {
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
    fn test_install_from_archive() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("data.txt"), "archive_content").unwrap();

        let archive_path = temp.path().join("test.tar.zst");
        create_test_archive(&src, &archive_path);

        let dst = temp.path().join("dst");
        let file = std::fs::File::open(&archive_path).unwrap();
        let mut hasher = sha2::Sha256::new();
        let hash = install_from_archive(file, &dst, &TarZstLibraryExtractor, &mut hasher).unwrap();

        assert_eq!(hash.as_ref(), compute_sha256(&archive_path));
        assert_eq!(std::fs::read_to_string(dst.join("data.txt")).unwrap(), "archive_content");
    }

    #[test]
    fn test_install_inner_local_directory() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "local_dir").unwrap();

        let expected_hash = [1u8; 32];
        let mut hasher = sha2::Sha256::new();
        let mut config = Config::new(
            RemoteArchive::new("http://example.com", &TarZstLibraryExtractor),
            Checksum::new(&expected_hash, &mut hasher),
        );
        let target_dir = config.toolchain_dir(temp.path());

        install_inner(&mut config, Some(LocalOverride::dir(&src)), temp.path(), |_| unreachable!())
            .unwrap();

        assert_eq!(std::fs::read_to_string(target_dir.join("test.txt")).unwrap(), "local_dir");
    }

    #[test]
    fn test_install_inner_local_archive() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "local_archive").unwrap();

        let archive_path = temp.path().join("archive.tar.zst");
        create_test_archive(&src, &archive_path);

        let expected_hash = [2u8; 32];
        let mut hasher = sha2::Sha256::new();
        let mut config = Config::new(
            RemoteArchive::new("http://example.com", &TarZstLibraryExtractor),
            Checksum::new(&expected_hash, &mut hasher),
        );
        let target_dir = config.toolchain_dir(temp.path());

        install_inner(
            &mut config,
            Some(LocalOverride::archive(&archive_path, &TarZstLibraryExtractor)),
            temp.path(),
            |_| unreachable!(),
        )
        .unwrap();

        assert_eq!(std::fs::read_to_string(target_dir.join("test.txt")).unwrap(), "local_archive");
    }

    #[test]
    fn test_install_inner_remote_success() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "remote_content").unwrap();

        let archive_path = temp.path().join("remote.tar.zst");
        create_test_archive(&src, &archive_path);

        let actual_hash = compute_sha256(&archive_path);
        let mut hasher = sha2::Sha256::new();
        let mut config = Config::new(
            RemoteArchive::new("http://example.com", &TarZstLibraryExtractor),
            Checksum::new(&actual_hash, &mut hasher),
        );
        let target_dir = config.toolchain_dir(temp.path());

        let archive_path_clone = archive_path.clone();
        install_inner(&mut config, None, temp.path(), move |_url| {
            let file = std::fs::File::open(&archive_path_clone).unwrap();
            Ok(Box::new(file))
        })
        .unwrap();

        assert_eq!(std::fs::read_to_string(target_dir.join("test.txt")).unwrap(), "remote_content");
    }

    #[test]
    fn test_install_inner_remote_checksum_mismatch() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "bad_remote").unwrap();

        let archive_path = temp.path().join("bad_remote.tar.zst");
        create_test_archive(&src, &archive_path);

        let actual_hash = compute_sha256(&archive_path);
        let mut expected_hash = actual_hash;
        expected_hash[0] ^= 1; // invalidate checksum

        let mut hasher = sha2::Sha256::new();
        let mut config = Config::new(
            RemoteArchive::new("http://example.com", &TarZstLibraryExtractor),
            Checksum::new(&expected_hash, &mut hasher),
        );
        let target_dir = config.toolchain_dir(temp.path());

        let archive_path_clone = archive_path.clone();
        let res = install_inner(&mut config, None, temp.path(), move |_url| {
            let file = std::fs::File::open(&archive_path_clone).unwrap();
            Ok(Box::new(file))
        });

        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Checksum mismatch"));
        assert!(!target_dir.exists());
    }
}
