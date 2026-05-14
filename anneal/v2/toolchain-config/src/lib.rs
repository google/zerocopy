/// Decodes a hexadecimal string into its byte representation.
const fn decode_hex(s: &str) -> Option<[u8; 32]> {
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

macro_rules! decode_hex_env {
    ($key:expr) => {
        const { decode_hex(env!($key)).expect("valid hex") }
    };
}

/// Supported platforms for Anneal dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Platform {
    LinuxX86_64,
    LinuxAArch64,
    MacosAArch64,
    MacosX86_64,
}

impl Platform {
    /// Returns the target triple for this platform.
    pub fn triple(&self) -> &'static str {
        match self {
            Self::LinuxX86_64 => "x86_64-unknown-linux-gnu",
            Self::LinuxAArch64 => "aarch64-unknown-linux-gnu",
            Self::MacosAArch64 => "aarch64-apple-darwin",
            Self::MacosX86_64 => "x86_64-apple-darwin",
        }
    }

    /// Detects the current host platform.
    pub fn detect() -> Result<Self, String> {
        let os = std::env::consts::OS;
        let arch = std::env::consts::ARCH;

        match (os, arch) {
            ("linux", "x86_64") => Ok(Self::LinuxX86_64),
            ("linux", "aarch64") => Ok(Self::LinuxAArch64),
            ("macos", "aarch64") => Ok(Self::MacosAArch64),
            ("macos", "x86_64") => Ok(Self::MacosX86_64),
            _ => Err(format!("Unsupported platform: {}-{}", os, arch)),
        }
    }

    /// Returns the expected SHA-256 checksum for the specified archive on this
    /// platform.
    ///
    /// These hashes are baked into the binary at compile time from values
    /// provided by `build.rs` from the project's `Cargo.toml`. This ensures
    /// that we always download and verify the exact versions of dependencies
    /// that this version of Anneal was built to work with.
    pub fn expected_archive_hash(&self) -> [u8; 32] {
        use Platform::*;
        match self {
            LinuxX86_64 => decode_hex_env!("SETUP_ARCHIVE_SHA256_LINUX_X86_64"),
            LinuxAArch64 => decode_hex_env!("SETUP_ARCHIVE_SHA256_LINUX_AARCH64"),
            MacosAArch64 => decode_hex_env!("SETUP_ARCHIVE_SHA256_MACOS_AARCH64"),
            MacosX86_64 => decode_hex_env!("SETUP_ARCHIVE_SHA256_MACOS_X86_64"),
        }
    }

    /// Returns the baseline remote URL from which the pre-verified toolchain archive
    /// for this platform can be downloaded.
    ///
    /// This function constructs an absolute URL by interpolating the target platform's
    /// specific archive filename onto a base URL baked into the binary at compile time
    /// via `SETUP_ARCHIVE_BASE_URL`. This compile-time binding guarantees that downloads
    /// exactly correspond to the release artifacts verified during the build phase.
    pub fn remote_url(&self) -> String {
        use Platform::*;
        const BASE: &str = env!("SETUP_ARCHIVE_BASE_URL");
        match self {
            LinuxX86_64 => format!("{BASE}/anneal-toolchain-linux-x86_64.tar.zst"),
            LinuxAArch64 => format!("{BASE}/anneal-toolchain-linux-aarch64.tar.zst"),
            MacosAArch64 => format!("{BASE}/anneal-toolchain-macos-aarch64.tar.zst"),
            MacosX86_64 => format!("{BASE}/anneal-toolchain-macos-x64_64.tar.zst"),
        }
    }
}

/// Setup configuration
pub struct Config {}

/// An archive format that can be extracted using a particular [`Extractor`] implementation.
pub enum ArchiveFormat {
    TarZst,
}

impl ArchiveFormat {
    fn new_extractor(&self) -> impl Extractor {
        use ArchiveFormat::*;
        match self {
            TarZst => TarZstLibraryExtractor,
        }
    }
}

/// The source for an archive of dependencies that `setup` must put in place.
pub enum Source {
    /// A fully assembled local directory tree containing uncompressed toolchain components.
    LocalDirectory(std::path::PathBuf),
    /// A local archive awaiting extraction.
    LocalArchive(std::path::PathBuf, ArchiveFormat),
    /// The archive format to expect from the statically configured remote URL source.
    Remote(ArchiveFormat),
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
    src: Source,
    toolchain_dir: std::path::PathBuf,
    expected_hash: [u8; 32],
    fetcher: impl FnOnce(&str) -> Result<Box<dyn std::io::Read>, String>,
) -> Result<(), String> {
    let expected_hex = encode_hex(&expected_hash);
    let subdir_name = &expected_hex[..6];
    let target_dir = toolchain_dir.join(subdir_name);

    use Source::*;
    match src {
        LocalArchive(path, format) => {
            log::warn!(
                "Toolchain contents from local archive may not match expected toolchain hash/version number."
            );
            let extractor = format.new_extractor();
            let file = std::fs::File::open(path)
                .map_err(|e| format!("Failed to open local archive: {e}"))?;
            setup_from_archive(file, &target_dir, &extractor)
                .map_err(|e| format!("Failed to extract archive: {e}"))?;
        }
        LocalDirectory(path) => {
            log::warn!(
                "Toolchain contents from local directory may not match expected toolchain hash/version number."
            );
            setup_from_directory(&path, &target_dir)?;
        }
        Remote(format) => {
            let extractor = format.new_extractor();
            let platform = Platform::detect().map_err(|e| format!("Failed to detect platform: {e}"))?;
            let response = fetcher(&platform.remote_url())?;

            let actual_hash: [u8; 32] = setup_from_archive(response, &target_dir, &extractor)
                .map_err(|e| format!("Failed to extract downloaded archive: {e}"))?;

            if actual_hash != expected_hash {
                let _ = std::fs::remove_dir_all(&target_dir);
                return Err(format!(
                    "Checksum mismatch for downloaded archive. Expected {}, got {}",
                    expected_hex,
                    encode_hex(&actual_hash)
                ));
            }
        }
    }

    Ok(())
}

/// Coordinates the provisioning and verification of the active toolchain dependency environment.
///
/// This function processes the incoming dependency source and installs it into a toolchain
/// directory named according to the source SHA256 hash.
///
/// # Caveats
///
/// - When `src` is a `Source::Local*` variant, the toolchain will be installed in a directory
///   named after the _expected_ SHA256 hash associated with the detected platform. This will not
///   necessarily match the behaviour of the platform's archive and should only be used for local
///   development of the managed toolchain itself.
pub fn setup(src: Source, toolchain_dir: std::path::PathBuf) -> Result<(), String> {
    let platform = Platform::detect().expect("detect platform");
    let expected_hash = platform.expected_archive_hash();
    setup_inner(src, toolchain_dir, expected_hash, |url| {
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
        let expected_hex = encode_hex(&expected_hash);
        let target_dir = temp.path().join(&expected_hex[..6]);

        setup_inner(
            Source::LocalDirectory(src),
            temp.path().to_path_buf(),
            expected_hash,
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
        let expected_hex = encode_hex(&expected_hash);
        let target_dir = temp.path().join(&expected_hex[..6]);

        setup_inner(
            Source::LocalArchive(archive_path, ArchiveFormat::TarZst),
            temp.path().to_path_buf(),
            expected_hash,
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
        let expected_hex = encode_hex(&actual_hash);
        let target_dir = temp.path().join(&expected_hex[..6]);

        setup_inner(
            Source::Remote(ArchiveFormat::TarZst),
            temp.path().to_path_buf(),
            actual_hash,
            move |_url| {
                let file = std::fs::File::open(&archive_path).unwrap();
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

        let expected_hex = encode_hex(&expected_hash);
        let target_dir = temp.path().join(&expected_hex[..6]);

        let res = setup_inner(
            Source::Remote(ArchiveFormat::TarZst),
            temp.path().to_path_buf(),
            expected_hash,
            move |_url| {
                let file = std::fs::File::open(&archive_path).unwrap();
                Ok(Box::new(file))
            },
        );

        assert!(res.is_err());
        assert!(res.unwrap_err().contains("Checksum mismatch"));
        assert!(!target_dir.exists());
    }
}
