pub mod build;

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

fn encode_hex_256(bytes: &[u8; 32]) -> String {
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

pub trait Config {
    const OS: &'static str;
    const ARCH: &'static str;
    const ARCHIVE_SHA256: [u8; 32];
    const ARCHIVE_URL: &'static str;
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
pub fn setup<C: Config>(src: Source, toolchain_dir: std::path::PathBuf) -> Result<(), String> {
    setup_inner::<C>(src, toolchain_dir, |url| {
        let response =
            reqwest::blocking::get(url).map_err(|e| format!("Failed to download archive: {e}"))?;
        let response = response
            .error_for_status()
            .map_err(|e| format!("HTTP error downloading archive: {e}"))?;
        Ok(Box::new(response))
    })
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

fn setup_inner<C: Config>(
    src: Source,
    toolchain_dir: std::path::PathBuf,
    fetcher: impl FnOnce(&str) -> Result<Box<dyn std::io::Read>, String>,
) -> Result<(), String> {
    let expected_hex = encode_hex_256(&C::ARCHIVE_SHA256);
    let target_dir = toolchain_dir.join(setup_dir_name::<C>());

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
            let response = fetcher(C::ARCHIVE_URL)?;

            let actual_hash: [u8; 32] = setup_from_archive(response, &target_dir, &extractor)
                .map_err(|e| format!("Failed to extract downloaded archive: {e}"))?;

            if actual_hash != C::ARCHIVE_SHA256 {
                let _ = std::fs::remove_dir_all(&target_dir);
                return Err(format!(
                    "Checksum mismatch for downloaded archive. Expected {}, got {}",
                    expected_hex,
                    encode_hex_256(&actual_hash)
                ));
            }
        }
    }

    Ok(())
}

fn setup_dir_name<C: Config>() -> String {
    let archive_sha256_hex = encode_hex_256(&C::ARCHIVE_SHA256);
    format!("{}-{}-{}", C::OS, C::ARCH, &archive_sha256_hex[..12])
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_ARCHIVE: &[u8] = include_bytes!("../testdata/archive.tar.zst");

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

        struct TestConfig;

        impl Config for TestConfig {
            const OS: &'static str = std::env::consts::OS;
            const ARCH: &'static str = std::env::consts::ARCH;
            const ARCHIVE_SHA256: [u8; 32] = [1u8; 32];
            const ARCHIVE_URL: &'static str = "http://example.com/archive.tar.zst";
        }

        setup_inner::<TestConfig>(
            Source::LocalDirectory(src),
            temp.path().to_path_buf(),
            |_| unreachable!(),
        )
        .unwrap();

        let target_dir = temp.path().join(setup_dir_name::<TestConfig>());
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

        struct TestConfig;

        impl Config for TestConfig {
            const OS: &'static str = std::env::consts::OS;
            const ARCH: &'static str = std::env::consts::ARCH;
            const ARCHIVE_SHA256: [u8; 32] = [2u8; 32];
            const ARCHIVE_URL: &'static str = "http://example.com/archive.tar.zst";
        }

        setup_inner::<TestConfig>(
            Source::LocalArchive(archive_path, ArchiveFormat::TarZst),
            temp.path().to_path_buf(),
            |_| unreachable!(),
        )
        .unwrap();

        let target_dir = temp.path().join(setup_dir_name::<TestConfig>());
        assert_eq!(std::fs::read_to_string(target_dir.join("test.txt")).unwrap(), "local_archive");
    }

    #[test]
    fn test_setup_inner_remote_success() {
        let temp = tempfile::tempdir().unwrap();

        // To (re)compute test archive hash:
        // use sha2::Digest;
        // let mut hasher = sha2::Sha256::new();
        // std::io::copy(&mut TEST_ARCHIVE, &mut hasher).unwrap();
        // let actual_hash = hasher.finalize().into();
        // let expected_hex = encode_hex_256(&actual_hash);
        // panic!("ACTUAL HASH: {:?}\nACTUAL HASH: {:?}", actual_hash, expected_hex);

        struct TestConfig;

        impl Config for TestConfig {
            const OS: &'static str = std::env::consts::OS;
            const ARCH: &'static str = std::env::consts::ARCH;
            // Manually observed with commented-out code above.
            const ARCHIVE_SHA256: [u8; 32] = [
                78, 126, 202, 220, 170, 27, 159, 91, 201, 226, 162, 235, 212, 250, 206, 165, 178,
                77, 19, 69, 48, 181, 169, 14, 87, 54, 8, 222, 13, 75, 192, 188,
            ];
            const ARCHIVE_URL: &'static str = "http://example.com/archive.tar.zst";
        }

        setup_inner::<TestConfig>(
            Source::Remote(ArchiveFormat::TarZst),
            temp.path().to_path_buf(),
            move |_url| Ok(Box::new(TEST_ARCHIVE)),
        )
        .expect("setup_inner failed");
    }

    #[test]
    fn test_setup_inner_remote_checksum_mismatch() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        std::fs::create_dir(&src).unwrap();
        std::fs::write(src.join("test.txt"), "bad_remote").unwrap();

        let archive_path = temp.path().join("bad_remote.tar.zst");
        create_test_archive(&src, &archive_path);

        // To (re)compute mutated hash:
        // use sha2::Digest;
        // let mut hasher = sha2::Sha256::new();
        // std::io::copy(&mut TEST_ARCHIVE, &mut hasher).unwrap();
        // let actual_hash: [u8; 32] = hasher.finalize().into();
        // let mut expected_hash = actual_hash.clone();
        // expected_hash[0] ^= 1;
        // let expected_hex = encode_hex_256(&expected_hash);
        // panic!("MUTATED HASH: {:?}\nMUTATED HASH: {:?}", expected_hash, expected_hex);

        struct TestConfig;

        impl Config for TestConfig {
            const OS: &'static str = std::env::consts::OS;
            const ARCH: &'static str = std::env::consts::ARCH;
            // Manually observed with commented-out code above.
            const ARCHIVE_SHA256: [u8; 32] = [
                79, 126, 202, 220, 170, 27, 159, 91, 201, 226, 162, 235, 212, 250, 206, 165, 178,
                77, 19, 69, 48, 181, 169, 14, 87, 54, 8, 222, 13, 75, 192, 188,
            ];
            const ARCHIVE_URL: &'static str = "http://example.com/archive.tar.zst";
        }

        setup_inner::<TestConfig>(
            Source::Remote(ArchiveFormat::TarZst),
            temp.path().to_path_buf(),
            move |_url| Ok(Box::new(TEST_ARCHIVE)),
        )
        .expect_err("setup_inner succeeded, but should have failed");
    }
}
