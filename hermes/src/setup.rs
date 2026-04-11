//! Subcommand for installing Hermes dependencies.
//!
//! This module handles the automated download, verification, and installation
//! of `charon`, `charon-driver`, and `aeneas`.

use std::{fs, io::Read, path::Path};

use anyhow::{Context, Result, bail};
use flate2::read::GzDecoder;
use sha2::{Digest, Sha256};
use tar::Archive;

use crate::util::DirLock;

macro_rules! decode_hex_env {
    ($key:expr) => {
        const { decode_hex(env!($key)).expect("valid hex") }
    };
}

/// Supported platforms for Hermes dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Platform {
    LinuxX86_64,
    LinuxAArch64,
    MacosAArch64,
    MacosX86_64,
}

/// A specific tool within a Hermes dependency.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tool {
    Charon,
    CharonDriver,
    Aeneas,
    Lake,
}

impl Tool {
    /// Returns the name of the binary for this tool.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Charon => "charon",
            Self::CharonDriver => "charon-driver",
            Self::Aeneas => "aeneas",
            Self::Lake => "lake",
        }
    }
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
    pub fn detect() -> Result<Self> {
        let os = std::env::consts::OS;
        let arch = std::env::consts::ARCH;

        match (os, arch) {
            ("linux", "x86_64") => Ok(Self::LinuxX86_64),
            ("linux", "aarch64") => Ok(Self::LinuxAArch64),
            ("macos", "aarch64") => Ok(Self::MacosAArch64),
            ("macos", "x86_64") => Ok(Self::MacosX86_64),
            _ => bail!("Unsupported platform: {}-{}", os, arch),
        }
    }

    /// Returns the expected SHA-256 checksum for the specified archive on this
    /// platform.
    ///
    /// These hashes are baked into the binary at compile time from values
    /// provided by `build.rs` from the project's `Cargo.toml`. This ensures
    /// that we always download and verify the exact versions of dependencies
    /// that this version of Hermes was built to work with.
    pub fn expected_archive_hash(&self) -> [u8; 32] {
        use Platform::*;
        match self {
            LinuxX86_64 => decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_X86_64"),
            LinuxAArch64 => decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_AARCH64"),
            MacosAArch64 => decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_AARCH64"),
            MacosX86_64 => decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_X86_64"),
        }
    }

    /// Returns the expected SHA-256 checksum for a specific binary on this
    /// platform.
    ///
    /// This is used for verifying individual binaries within a toolchain,
    /// allowing the `setup` command to detect and repair corruption of any
    /// of the toolchain components.
    pub fn expected_bin_hash(&self, tool: Tool) -> [u8; 32] {
        use Platform::*;
        match (self, tool) {
            (LinuxX86_64, Tool::Charon) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_X86_64_CHARON")
            }
            (LinuxX86_64, Tool::CharonDriver) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_X86_64_CHARON_DRIVER")
            }
            (LinuxAArch64, Tool::Charon) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_AARCH64_CHARON")
            }
            (LinuxAArch64, Tool::CharonDriver) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_AARCH64_CHARON_DRIVER")
            }
            (MacosAArch64, Tool::Charon) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_AARCH64_CHARON")
            }
            (MacosAArch64, Tool::CharonDriver) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_AARCH64_CHARON_DRIVER")
            }
            (MacosX86_64, Tool::Charon) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_X86_64_CHARON")
            }
            (MacosX86_64, Tool::CharonDriver) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_X86_64_CHARON_DRIVER")
            }
            (LinuxX86_64, Tool::Aeneas) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_X86_64_AENEAS")
            }
            (LinuxAArch64, Tool::Aeneas) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_LINUX_AARCH64_AENEAS")
            }
            (MacosAArch64, Tool::Aeneas) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_AARCH64_AENEAS")
            }
            (MacosX86_64, Tool::Aeneas) => {
                decode_hex_env!("HERMES_AENEAS_CHECKSUM_MACOS_X86_64_AENEAS")
            }
            _ => {
                unreachable!("unsupported tool combination for individual verification")
            }
        }
    }
}

pub struct Toolchain {
    pub root: std::path::PathBuf,
    // Holds the shared lock for the lifetime of the Toolchain object.
    _lock: Option<DirLock>,
}

impl Toolchain {
    /// Resolves the toolchain manager and acquires a shared lock.
    pub fn resolve() -> Result<Self> {
        let home = if let Ok(dir) = std::env::var("HERMES_TOOLCHAIN_DIR") {
            std::path::PathBuf::from(dir)
        } else if std::env::var("__ZEROCOPY_LOCAL_DEV").is_ok() {
            let base = std::env::var("CARGO_MANIFEST_DIR")
                .map(std::path::PathBuf::from)
                // Fall back to current directory if CARGO_MANIFEST_DIR is not set,
                // which can happen if the binary is executed directly rather than
                // via `cargo run`.
                .unwrap_or_else(|_| std::env::current_dir().unwrap());
            base.join("target").join("hermes-home")
        } else {
            dirs::home_dir().ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?
        };
        let platform = Platform::detect()?;
        let aeneas_hash = platform.expected_archive_hash();

        // We produce a unique hash of the toolchain component versions to
        // ensure that each combination of versions is installed into its own
        // isolated directory. This allows multiple versions of Hermes to
        // coexist on the same machine without colliding, and ensures that
        // switching branches or updating Hermes will automatically point to
        // the correct toolchain version.
        //
        // We hash the expected archive checksum rather than version tags.
        // Checksums provide a stable, data-anchored identity for the toolchain
        // components that cannot drift from the underlying binaries.
        let mut hasher = Sha256::new();
        hasher.update(aeneas_hash);
        let hash = format!("{:x}", hasher.finalize());
        let short_hash = &hash[..12];

        // We include the host platform's target triple in the directory name.
        // This ensures that toolchains for different architectures remain isolated
        // if they are stored in a shared filesystem (e.g., a networked home directory).
        let root = home.join(".hermes").join("toolchain").join(format!(
            "{}-{}",
            platform.triple(),
            short_hash
        ));

        // Acquire a shared lock to ensure the toolchain isn't modified while
        // we use it. If the directory doesn't exist yet, we still acquire the
        // lock on the path (which setup will also use).
        let lock = DirLock::lock_shared(root.clone())
            .with_context(|| format!("Failed to acquire shared lock on {:?}", root))?;

        Ok(Self { root, _lock: Some(lock) })
    }

    /// Returns the bin directory for this toolchain.
    pub fn bin_dir(&self) -> std::path::PathBuf {
        self.root.clone()
    }

    /// Acquires an exclusive lock on the toolchain directory.
    pub fn lock_exclusive(&self) -> Result<DirLock> {
        DirLock::lock_exclusive(self.root.clone())
    }

    /// Returns a Command for the specified tool, prioritizing the managed
    /// toolchain.
    pub fn command(&self, tool: Tool) -> std::process::Command {
        let bin_name = tool.name();
        let managed_path = self.bin_dir().join(bin_name);

        if std::env::var("HERMES_USE_PATH_FOR_TOOLS").is_ok() {
            std::process::Command::new(bin_name)
        } else if managed_path.exists() {
            std::process::Command::new(managed_path)
        } else {
            std::process::Command::new(bin_name)
        }
    }

    /// Takes the shared lock from the toolchain, if it exists.
    ///
    /// This is used when we need to upgrade from a shared lock (held during
    /// normal operation) to an exclusive lock (needed during `setup` or
    /// repair). Because file locks cannot be atomically upgraded, we must
    /// drop the shared lock before acquiring the exclusive one.
    pub fn take_lock(&mut self) -> Option<DirLock> {
        self._lock.take()
    }
}

/// Calculates the SHA-256 hash of a file on disk.
fn calculate_file_hash(path: &Path) -> Result<[u8; 32]> {
    let mut file = fs::File::open(path).context("Failed to open file for hashing")?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 8192];
    loop {
        let n = file.read(&mut buffer).context("Failed to read file for hashing")?;
        if n == 0 {
            break;
        }
        hasher.update(&buffer[..n]);
    }
    Ok(hasher.finalize().into())
}

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

const TOOLS: &[Tool] = &[Tool::Aeneas, Tool::Charon, Tool::CharonDriver];

/// Extracts a tar.gz archive to the target directory.
fn extract_artifact(data: &[u8], target_dir: &Path) -> Result<()> {
    log::info!("Extracting to {:?}...", target_dir);
    let tar = GzDecoder::new(data);
    let mut archive = Archive::new(tar);

    fs::create_dir_all(target_dir).context("Failed to create target directory")?;

    for entry in archive.entries().context("Failed to read archive entries")? {
        let mut entry = entry.context("Failed to get archive entry")?;
        let path = entry.path().context("Failed to get entry path")?.to_path_buf();

        entry.unpack_in(target_dir).context("Failed to unpack archive entry")?;
        let unpacked_path = target_dir.join(&path);

        // Ensure that the extracted file/directory has write permissions.
        // Some archives (like Nix-built ones) may contain read-only files,
        // which prevents us from repairing or corrupting them in tests.
        if unpacked_path.exists() {
            let mut perms = fs::metadata(&unpacked_path)?.permissions();
            if perms.readonly() {
                #[allow(clippy::permissions_set_readonly_false)]
                perms.set_readonly(false);
                fs::set_permissions(&unpacked_path, perms)
                    .context("Failed to set toolchain permissions")?;
            }
        }
    }

    Ok(())
}

/// Ensures that `elan` (the Lean toolchain manager) is installed on the
/// system. If it is not found in the system `PATH`, it downloads the latest
/// release from GitHub and runs `elan-init` to install it for the current
/// user. It also attempts to add the `elan` bin directory to the current
/// process's `PATH` to ensure subsequent commands can find it immediately.
fn ensure_elan_installed() -> Result<()> {
    println!("Checking for elan...");
    let status = std::process::Command::new("elan")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();

    if status.is_ok() && status.unwrap().success() {
        println!("elan is already installed.");
        return Ok(());
    }

    println!("elan not found. Installing elan...");
    let platform = Platform::detect()?;
    let arch = match platform {
        Platform::LinuxX86_64 => "x86_64-unknown-linux-gnu",
        Platform::LinuxAArch64 => "aarch64-unknown-linux-gnu",
        Platform::MacosAArch64 => "aarch64-apple-darwin",
        Platform::MacosX86_64 => "x86_64-apple-darwin",
    };

    let url =
        format!("https://github.com/leanprover/elan/releases/latest/download/elan-{}.tar.gz", arch);

    println!("Downloading elan from {}...", url);
    let response = reqwest::blocking::get(&url).context("Failed to download elan")?;
    if !response.status().is_success() {
        bail!("Failed to download elan: HTTP {}", response.status());
    }
    let data = response.bytes().context("Failed to read elan response")?;

    let temp_dir = std::env::temp_dir();
    let elan_extract_dir = temp_dir.join("elan-extract-hermes");
    fs::create_dir_all(&elan_extract_dir).context("Failed to create elan extract dir")?;

    extract_artifact(&data, &elan_extract_dir)?;

    let elan_init_path = elan_extract_dir.join("elan-init");

    let status = std::process::Command::new(&elan_init_path)
        .args(["-y", "--default-toolchain", "none"])
        .status()
        .context("Failed to run elan-init")?;

    let _ = fs::remove_dir_all(&elan_extract_dir);

    if !status.success() {
        bail!("elan-init failed");
    }

    // Add elan to PATH for current process
    let home = dirs::home_dir().ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?;
    let elan_bin = home.join(".elan").join("bin");
    if elan_bin.exists() {
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut paths = std::env::split_paths(&path).collect::<Vec<_>>();
        if !paths.contains(&elan_bin) {
            paths.insert(0, elan_bin);
            let new_path = std::env::join_paths(paths)?;
            // SAFETY: This is a single-threaded setup context.
            unsafe {
                std::env::set_var("PATH", new_path);
            }
        }
    }

    println!("elan installed successfully.");
    Ok(())
}

/// Installs the pinned Lean toolchain required by Hermes using `elan`.
/// It checks the environment variable `HERMES_LEAN_TOOLCHAIN` to determine
/// which version to install. If the version is already listed in `elan
/// toolchain list`, it skips installation to save time.
fn install_lean_toolchain() -> Result<()> {
    let version = env!("HERMES_LEAN_TOOLCHAIN");
    println!("Installing Lean toolchain {}...", version);

    // Check if already installed
    let output = std::process::Command::new("elan")
        .args(["toolchain", "list"])
        .output()
        .context("Failed to run elan toolchain list")?;

    if output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        if stdout.lines().any(|line| line.contains(version)) {
            println!("Lean toolchain {} is already installed.", version);
            return Ok(());
        }
    }

    let status = std::process::Command::new("elan")
        .args(["toolchain", "install", version])
        .status()
        .context("Failed to run elan toolchain install")?;

    if !status.success() {
        bail!("Failed to install Lean toolchain");
    }

    println!("Lean toolchain {} installed successfully.", version);
    Ok(())
}

/// Pre-builds the Aeneas Lean library in the extracted toolchain directory.
/// This prevents compiling the library from source when users verify their
/// projects, which is slow and disk-heavy. It first attempts to fetch
/// pre-compiled Mathlib artifacts using `lake exe cache get` to avoid
/// compiling Mathlib from source, and then runs `lake build`.
fn prebuild_lean_library(lean_dir: &Path) -> Result<()> {
    println!("Pre-building Aeneas Lean library at {:?}...", lean_dir);

    // Fetch Mathlib cache
    println!("Fetching Mathlib cache...");
    let status = std::process::Command::new("lake")
        .args(["exe", "cache", "get"])
        .current_dir(lean_dir)
        .status()
        .context("Failed to run `lake exe cache get`")?;

    if !status.success() {
        bail!("Failed to fetch Mathlib cache; refusing to build from scratch");
    }

    // Build the library
    println!("Building Aeneas Lean library...");
    let status = std::process::Command::new("lake")
        .arg("build")
        .current_dir(lean_dir)
        .status()
        .context("Failed to run `lake build`")?;

    if !status.success() {
        bail!("Failed to build Aeneas Lean library");
    }

    println!("Successfully pre-built Aeneas Lean library.");
    Ok(())
}

/// Sets up the Hermes toolchain by downloading and extracting dependencies.
pub fn run_setup() -> Result<()> {
    ensure_elan_installed()?;
    install_lean_toolchain()?;

    let mut toolchain = Toolchain::resolve()?;
    // Drop the shared lock acquired by resolve() so we can acquire an
    // exclusive one.
    drop(toolchain.take_lock());

    // Acquire global lock to prevent concurrent installations or repairs.
    // This ensures that two instances of Hermes don't try to download or
    // modify the toolchain at the same time.
    let _lock = toolchain.lock_exclusive()?;
    let platform = Platform::detect()?;

    let tag = env!("HERMES_AENEAS_TAG");
    let mut needs_install = false;

    for tool in TOOLS {
        let bin_path = toolchain.bin_dir().join(tool.name());
        if !bin_path.exists() {
            log::info!("{} is missing, re-installing toolchain", tool.name());
            needs_install = true;
            break;
        }

        // Check if an expected SHA-256 checksum is available for this
        // binary. If so, verify that the existing binary matches the
        // expected hash. If the hash does not match, we re-install the
        // entire toolchain component to ensure we have a consistent
        // and verified set of binaries. This protects against
        // accidental corruption of toolchain components and ensures
        // that all binaries match the versions expected by this build
        // of Hermes.
        let expected_bin_hash = platform.expected_bin_hash(*tool);
        let actual_hash = calculate_file_hash(&bin_path)?;
        if actual_hash != expected_bin_hash {
            log::info!(
                "{} hash mismatch (expected {}, got {}), re-installing toolchain",
                tool.name(),
                format_hex(&expected_bin_hash),
                format_hex(&actual_hash)
            );
            needs_install = true;
            break;
        }
    }

    if needs_install {
        // Perform installation. Note that, because we validate SHA-256
        // checksums against values baked into the binary, allowing the user to
        // override the download URL does not represent a security risk.
        let env_key = "HERMES_SETUP_BASE_URL";
        let base_url = std::env::var(env_key).unwrap_or_else(|_| {
            "https://github.com/AeneasVerif/aeneas/releases/download".to_string()
        });

        let url = format!(
            "{}/{}/aeneas-{}.tar.gz",
            base_url,
            tag,
            match platform {
                Platform::LinuxX86_64 => "linux-x86_64",
                Platform::LinuxAArch64 => "linux-aarch64",
                Platform::MacosAArch64 => "macos-aarch64",
                Platform::MacosX86_64 => "macos-x86_64",
            }
        );

        let expected_archive_hash = platform.expected_archive_hash();

        let data = download_artifact(&url, &expected_archive_hash)?;

        extract_artifact(&data, &toolchain.root)?;

        let lean_dir = toolchain.root.join("backends").join("lean");
        if lean_dir.exists() {
            prebuild_lean_library(&lean_dir)?;
        } else {
            log::warn!("Lean directory not found at {:?}", lean_dir);
        }

        println!("Successfully installed toolchain v{tag}");
    } else {
        log::info!("toolchain is already installed and verified");
    }

    Ok(())
}

/// Downloads an artifact from the specified URL and verifies its SHA-256 hash.
fn download_artifact(url: &str, expected_hash: &[u8; 32]) -> Result<Vec<u8>> {
    println!("Downloading: {}", url);
    let mut response = reqwest::blocking::get(url).context("Failed to download artifact")?;
    if !response.status().is_success() {
        bail!("Failed to download artifact: HTTP {}", response.status());
    }

    let mut data = Vec::new();
    response.read_to_end(&mut data).context("Failed to read artifact data")?;

    let mut hasher = Sha256::new();
    hasher.update(&data);
    let actual_hash: [u8; 32] = hasher.finalize().into();

    if actual_hash != *expected_hash {
        bail!(
            "Checksum mismatch for artifact! Expected {}, got {}",
            format_hex(expected_hash),
            format_hex(&actual_hash)
        );
    }

    Ok(data)
}

fn format_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        use std::fmt::Write;
        write!(&mut s, "{:02x}", b).unwrap();
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_platform_detection() {
        let platform = Platform::detect().expect("Should detect current platform");
        // Verify that the detected platform triple matches the Rust target triple
        // used to compile this test (roughly).
        let triple = platform.triple();
        if cfg!(target_os = "linux") {
            assert!(triple.contains("linux"));
        } else if cfg!(target_os = "macos") {
            assert!(triple.contains("apple-darwin"));
        }
    }

    #[test]
    fn test_locking() {
        let temp = tempfile::tempdir().unwrap();
        let lock_path = temp.path().join(".lock");

        // First lock
        let lock1 =
            DirLock::lock_exclusive(temp.path().to_path_buf()).expect("First lock should succeed");

        // Try second lock in another thread (should block/fail if we used try_lock, but DirLock::lock blocks)
        // To test non-blocking, we'd need another helper, but we can verify that the second lock
        // succeeds after the first one is dropped.
        let lock_path_clone = lock_path.clone();
        let handle = std::thread::spawn(move || {
            let _lock2 = DirLock::lock_exclusive(lock_path_clone.parent().unwrap().to_path_buf())
                .expect("Second lock should succeed after first is dropped");
        });

        std::thread::sleep(std::time::Duration::from_millis(100));
        drop(lock1);
        handle.join().expect("Thread should finish");
    }

    #[test]
    fn test_extraction() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("extracted");

        // Create a dummy tar.gz in memory
        let mut enc = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
        {
            let mut tar = tar::Builder::new(&mut enc);
            let mut header = tar::Header::new_gnu();
            header.set_path("hello.txt").unwrap();
            header.set_size(5);
            #[cfg(unix)]
            {
                header.set_mode(0o755);
            }
            header.set_cksum();
            tar.append(&header, b"world" as &[u8]).unwrap();
            tar.finish().unwrap();
        }
        let data = enc.finish().unwrap();

        // Test normal extraction
        extract_artifact(&data, &target).expect("Extraction should succeed");

        let hello_path = target.join("hello.txt");
        assert!(hello_path.exists());
        assert_eq!(fs::read_to_string(&hello_path).unwrap(), "world");

        // Test aeneas extraction (should extract everything)
        let aeneas_target = temp.path().join("aeneas_extracted");
        let mut enc = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
        {
            let mut tar = tar::Builder::new(&mut enc);

            // Add aeneas binary
            let mut header = tar::Header::new_gnu();
            header.set_path("aeneas").unwrap();
            header.set_size(6);
            header.set_cksum();
            tar.append(&header, b"binary" as &[u8]).unwrap();

            // Add backends directory
            let mut header = tar::Header::new_gnu();
            header.set_path("backends/lean/test.lean").unwrap();
            header.set_size(4);
            header.set_cksum();
            tar.append(&header, b"lean" as &[u8]).unwrap();

            tar.finish().unwrap();
        }
        let aeneas_data = enc.finish().unwrap();
        extract_artifact(&aeneas_data, &aeneas_target).expect("Aeneas extraction should succeed");

        assert!(aeneas_target.join("aeneas").exists());
        assert!(aeneas_target.join("backends/lean/test.lean").exists());

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let metadata = fs::metadata(&hello_path).unwrap();
            assert!(metadata.permissions().mode() & 0o111 != 0, "Executable bit should be set");
        }
    }

    #[test]
    fn test_download() {
        use std::{
            io::{Read, Write},
            net::TcpListener,
        };

        // Start a minimal mock HTTP server
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let port = listener.local_addr().unwrap().port();
        let url = format!("http://127.0.0.1:{}", port);

        let handle = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut buffer = [0; 1024];
            let _ = stream.read(&mut buffer).unwrap();

            let response = "HTTP/1.1 200 OK\r\nContent-Length: 13\r\n\r\nMock Artifact";
            stream.write_all(response.as_bytes()).unwrap();
        });

        let expected_hash_hex = "5fed9305f5a694b6b33ee9f783596ecf08ed89ea00c2960699ba8285e0d67c71"; // sha256 of "Mock Artifact"
        let expected_hash = decode_hex(expected_hash_hex).expect("Mock hex should be valid");

        let data = download_artifact(&url, &expected_hash).expect("Download should succeed");
        assert_eq!(data, b"Mock Artifact");
        handle.join().unwrap();
    }
}
