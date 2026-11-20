// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pre-capture compiler identity verification and Linux driver residency.
//!
//! All checks in this module use 100% safe Rust without FFI or extra crates.

use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::Path;
use std::process::Command;

use sha2::{Digest, Sha256};

use crate::{Failure, ir};

/// Device and inode identity `(st_dev, st_ino)` for a regular file.
#[cfg(unix)]
pub(crate) type DevIno = (u64, u64);

/// Format a SHA-256 digest as lowercase hex using a byte loop compatible with
/// both `sha2` 0.10 and 0.11.
fn digest_to_hex(bytes: &[u8]) -> String {
    let mut hex = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}

pub(crate) fn sha256_bytes(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest_to_hex(digest.as_ref())
}

fn sha256_reader<R: io::Read>(mut reader: R) -> io::Result<String> {
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    let digest = hasher.finalize();
    Ok(digest_to_hex(digest.as_ref()))
}

#[cfg(unix)]
pub(crate) fn regular_file_dev_ino(path: &Path) -> io::Result<DevIno> {
    use std::os::unix::fs::MetadataExt;

    let meta = fs::metadata(path)?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    Ok((meta.dev(), meta.ino()))
}

/// Open a regular file once, verify regular-file metadata on the open handle,
/// and return its SHA-256 digest together with `(st_dev, st_ino)` on Unix.
#[cfg(unix)]
fn open_regular_and_hash(path: &Path) -> io::Result<(String, DevIno)> {
    use std::os::unix::fs::MetadataExt;

    let mut file = fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    let dev_ino = (meta.dev(), meta.ino());
    let digest = sha256_reader(&mut file)?;
    Ok((digest, dev_ino))
}

#[cfg(not(unix))]
fn open_regular_and_hash(path: &Path) -> io::Result<(String, ())> {
    let mut file = fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    let digest = sha256_reader(&mut file)?;
    Ok((digest, ()))
}

struct RustcVerboseVersion {
    version: String,
    commit: String,
    host: String,
}

fn parse_rustc_version_verbose(text: &str) -> Result<RustcVerboseVersion, Failure> {
    let mut version = None;
    let mut commit = None;
    let mut host = None;
    for line in text.lines() {
        if version.is_none()
            && let Some(rest) = line.strip_prefix("rustc ")
            && !rest.is_empty()
        {
            version = Some(rest.to_owned());
        } else if let Some(rest) = line.strip_prefix("commit-hash: ")
            && !rest.is_empty()
        {
            commit = Some(rest.to_owned());
        } else if let Some(rest) = line.strip_prefix("host: ")
            && !rest.is_empty()
        {
            host = Some(rest.to_owned());
        }
    }
    Ok(RustcVerboseVersion {
        version: version.ok_or_else(|| {
            Failure::tool("sysroot rustc --version --verbose omitted version header")
        })?,
        commit: commit.ok_or_else(|| {
            Failure::tool("sysroot rustc --version --verbose omitted commit-hash")
        })?,
        host: host
            .ok_or_else(|| Failure::tool("sysroot rustc --version --verbose omitted host"))?,
    })
}

/// Restrict host triples to single path-safe component characters so `host`
/// cannot traverse outside `<sysroot>/lib/rustlib/`.
fn is_valid_host_triple(host: &str) -> bool {
    !host.is_empty()
        && host != "."
        && host != ".."
        && host
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
}

/// Confirm that the linked driver's version string embeds the short prefix of
/// the full `commit-hash` from `<sysroot>/bin/rustc --version --verbose`.
fn linked_version_matches_commit(linked_version: &str, commit: &str) -> bool {
    if commit.len() < 9 || !commit.bytes().all(|b| b.is_ascii_hexdigit()) {
        return false;
    }
    let short = &commit[..9];
    let needle = format!("({short}");
    let Some(pos) = linked_version.find(&needle) else {
        return false;
    };
    let tail = &linked_version[pos + needle.len()..];
    let mut tail_bytes = tail.as_bytes().iter();
    let mut commit_bytes = commit.as_bytes()[9..].iter();
    loop {
        match tail_bytes.next() {
            Some(b' ' | b')') => return true,
            Some(&tb) => match commit_bytes.next() {
                Some(&cb) if tb.eq_ignore_ascii_case(&cb) => continue,
                _ => return false,
            },
            None => return false,
        }
    }
}

fn is_rustc_driver_filename(name: &str) -> bool {
    name.starts_with("librustc_driver-") && name.ends_with(".so")
}

/// Encode Linux kernel `(major, minor)` device numbers into the userspace
/// `st_dev` (`dev_t`) representation returned by `MetadataExt::dev()`.
#[cfg(any(target_os = "linux", test))]
fn linux_makedev(major: u64, minor: u64) -> u64 {
    ((major & 0xffff_f000) << 32)
        | ((major & 0x0000_0fff) << 8)
        | ((minor & 0xffff_ff00) << 12)
        | (minor & 0x0000_00ff)
}

#[cfg(any(target_os = "linux", test))]
#[derive(Debug, PartialEq, Eq)]
struct MapsEntry<'a> {
    start: usize,
    end: usize,
    perms: &'a [u8],
    dev: u64,
    inode: u64,
    pathname: Option<&'a [u8]>,
}

/// Parse one raw `/proc/self/maps` line without requiring UTF-8 or trimming
/// trailing spaces from file paths.
#[cfg(any(target_os = "linux", test))]
fn parse_maps_line(raw_line: &[u8]) -> Option<MapsEntry<'_>> {
    let line = raw_line.strip_suffix(b"\r").unwrap_or(raw_line);
    let mut rest = strip_leading_ascii_ws(line);
    let mut fields: [&[u8]; 5] = [b""; 5];
    for (idx, slot) in fields.iter_mut().enumerate() {
        let end = rest
            .iter()
            .position(|b| b.is_ascii_whitespace())
            .unwrap_or(rest.len());
        if end == 0 {
            return None;
        }
        *slot = &rest[..end];
        rest = strip_leading_ascii_ws(&rest[end..]);
        if idx < 4 && rest.is_empty() {
            return None;
        }
    }
    let (start_hex, end_hex) = split_once_byte(fields[0], b'-')?;
    let start = parse_hex_usize(start_hex)?;
    let end = parse_hex_usize(end_hex)?;
    if start >= end {
        return None;
    }
    let (maj_hex, min_hex) = split_once_byte(fields[3], b':')?;
    let major = parse_hex_u64(maj_hex)?;
    let minor = parse_hex_u64(min_hex)?;
    let inode = parse_dec_u64(fields[4])?;
    let pathname = if rest.is_empty() { None } else { Some(rest) };
    Some(MapsEntry {
        start,
        end,
        perms: fields[1],
        dev: linux_makedev(major, minor),
        inode,
        pathname,
    })
}

#[cfg(any(target_os = "linux", test))]
fn strip_leading_ascii_ws(mut bytes: &[u8]) -> &[u8] {
    while let Some((first, tail)) = bytes.split_first() {
        if first.is_ascii_whitespace() {
            bytes = tail;
        } else {
            break;
        }
    }
    bytes
}

#[cfg(any(target_os = "linux", test))]
fn split_once_byte(bytes: &[u8], needle: u8) -> Option<(&[u8], &[u8])> {
    let pos = bytes.iter().position(|&b| b == needle)?;
    Some((&bytes[..pos], &bytes[pos + 1..]))
}

#[cfg(any(target_os = "linux", test))]
fn parse_hex_usize(bytes: &[u8]) -> Option<usize> {
    let text = std::str::from_utf8(bytes).ok()?;
    usize::from_str_radix(text, 16).ok()
}

#[cfg(any(target_os = "linux", test))]
fn parse_hex_u64(bytes: &[u8]) -> Option<u64> {
    let text = std::str::from_utf8(bytes).ok()?;
    u64::from_str_radix(text, 16).ok()
}

#[cfg(any(target_os = "linux", test))]
fn parse_dec_u64(bytes: &[u8]) -> Option<u64> {
    let text = std::str::from_utf8(bytes).ok()?;
    text.parse::<u64>().ok()
}

/// Locate the executable, file-backed, non-deleted `/proc/self/maps` mapping
/// containing `driver_addr` and return its kernel `(st_dev, st_ino)`.
#[cfg(any(target_os = "linux", test))]
fn resolve_driver_mapping_dev_ino(
    maps_bytes: &[u8],
    driver_addr: usize,
) -> Result<(u64, u64), Failure> {
    let mut found: Option<(u64, u64)> = None;
    for raw_line in maps_bytes.split(|&b| b == b'\n') {
        let Some(entry) = parse_maps_line(raw_line) else {
            continue;
        };
        if !(entry.start <= driver_addr && driver_addr < entry.end) {
            continue;
        }
        if !entry.perms.contains(&b'x') {
            return Err(Failure::tool(
                "loaded rustc driver mapping is not executable",
            ));
        }
        if entry.inode == 0 {
            return Err(Failure::tool(
                "loaded rustc driver mapping is not file-backed",
            ));
        }
        let Some(pathname) = entry.pathname else {
            return Err(Failure::tool(
                "loaded rustc driver mapping has no backing pathname",
            ));
        };
        if pathname.ends_with(b" (deleted)") {
            return Err(Failure::tool(format!(
                "loaded rustc driver mapping is deleted: {}",
                String::from_utf8_lossy(pathname)
            )));
        }
        let dev_ino = (entry.dev, entry.inode);
        match found {
            None => found = Some(dev_ino),
            Some(prev) if prev == dev_ino => {}
            Some(_) => {
                return Err(Failure::tool(
                    "multiple overlapping rustc driver mappings match run_compiler",
                ));
            }
        }
    }
    found.ok_or_else(|| {
        Failure::tool("cannot locate loaded rustc driver mapping for run_compiler address")
    })
}

/// Open each `librustc_driver-*.so` under `<sysroot>/lib` or
/// `<sysroot>/lib/rustlib/<host>/lib` once, match `(st_dev, st_ino)` on the
/// open descriptor against `loaded_dev_ino`, and hash from that same handle.
#[cfg(any(target_os = "linux", test))]
fn match_and_hash_sysroot_driver(
    sysroot: &Path,
    host: &str,
    loaded_dev_ino: (u64, u64),
) -> Result<String, Failure> {
    if !is_valid_host_triple(host) {
        return Err(Failure::tool(format!(
            "invalid rustc host triple: {host:?}"
        )));
    }
    let mut search_dirs = vec![sysroot.join("lib")];
    let host_lib = sysroot.join("lib/rustlib").join(host).join("lib");
    if host_lib.is_dir() {
        search_dirs.push(host_lib);
    }
    let mut saw_candidate = false;
    for dir in search_dirs {
        let entries = match fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(Failure::io(error)),
        };
        for entry in entries {
            let entry = entry.map_err(Failure::io)?;
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if !is_rustc_driver_filename(name) {
                continue;
            }
            let Ok(matched_digest) = open_and_hash_if_dev_ino_matches(&path, loaded_dev_ino) else {
                continue;
            };
            saw_candidate = true;
            if let Some(digest) = matched_digest {
                return Ok(digest);
            }
        }
    }
    if !saw_candidate {
        return Err(Failure::tool(format!(
            "no librustc_driver-*.so found in sysroot {}",
            sysroot.display()
        )));
    }
    Err(Failure::tool(format!(
        "loaded rustc driver does not match any librustc_driver-*.so in sysroot {}",
        sysroot.display()
    )))
}

#[cfg(all(any(target_os = "linux", test), unix))]
fn open_and_hash_if_dev_ino_matches(
    path: &Path,
    expected: (u64, u64),
) -> io::Result<Option<String>> {
    use std::os::unix::fs::MetadataExt;

    let mut file = fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    if (meta.dev(), meta.ino()) != expected {
        return Ok(None);
    }
    let digest = sha256_reader(&mut file)?;
    Ok(Some(digest))
}

#[cfg(all(test, not(unix)))]
fn open_and_hash_if_dev_ino_matches(
    _path: &Path,
    _expected: (u64, u64),
) -> io::Result<Option<String>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "residency hashing requires unix metadata",
    ))
}

#[cfg(target_os = "linux")]
fn verify_driver_residency(sysroot: &Path, host: &str) -> Result<Option<String>, Failure> {
    let driver_addr = rustc_driver::run_compiler as *const () as usize;
    let maps_bytes = fs::read("/proc/self/maps").map_err(Failure::io)?;
    let loaded_dev_ino = resolve_driver_mapping_dev_ino(&maps_bytes, driver_addr)?;
    let driver_sha256 = match_and_hash_sysroot_driver(sysroot, host, loaded_dev_ino)?;
    Ok(Some(driver_sha256))
}

#[cfg(not(target_os = "linux"))]
fn verify_driver_residency(_sysroot: &Path, _host: &str) -> Result<Option<String>, Failure> {
    // On macOS (`#[cfg(target_os = "macos")]`) and other non-Linux hosts,
    // System Integrity Protection (SIP) and platform loader constraints prevent
    // Linux `/proc/self/maps` residency parity without FFI. Driver validation
    // on non-Linux hosts is best-effort developer-only, relying on the
    // sanitized `<sysroot>/bin/rustc --version --verbose` check.
    Ok(None)
}

/// Verify sysroot layout, pinned linked driver version, sanitized
/// `<sysroot>/bin/rustc --version --verbose` agreement with the pinned commit,
/// pre/post `<sysroot>/bin/rustc` TOCTOU identity, and Linux driver residency
/// before entering `rustc`'s fatal-error handler.
pub(crate) fn verify_compiler(sysroot: &Path, target: &str) -> Result<(), Failure> {
    if !sysroot.is_dir()
        || !sysroot.join("lib").is_dir()
        || !sysroot.join("lib/rustlib").is_dir()
        || !sysroot
            .join("lib/rustlib")
            .join(target)
            .join("lib")
            .is_dir()
    {
        return Err(Failure::tool(format!(
            "invalid Rust sysroot layout at {}",
            sysroot.display()
        )));
    }
    let rustc_bin = sysroot.join("bin/rustc");
    let (rustc_sha256, rustc_id_before) = open_regular_and_hash(&rustc_bin).map_err(|error| {
        Failure::tool(format!(
            "invalid sysroot rustc binary at {}: {error}",
            rustc_bin.display()
        ))
    })?;

    // `rustc_version_str` reports the "version string for `rustc` itself".
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_interface/src/util.rs#L688-L691
    let linked_version = rustc_interface::util::rustc_version_str()
        .ok_or_else(|| Failure::tool("capture was linked against an unknown rustc revision"))?;
    if linked_version != ir::COMPILER_VERSION {
        return Err(Failure::tool(
            "capture was linked against an unexpected rustc revision",
        ));
    }

    let output = Command::new(&rustc_bin)
        .env_clear()
        .args(["--version", "--verbose"])
        .output()
        .map_err(Failure::io)?;
    if !output.status.success() {
        return Err(Failure::tool(format!(
            "sysroot rustc --version --verbose failed with status {}",
            output.status
        )));
    }
    let (rustc_sha256_after, rustc_id_after) =
        open_regular_and_hash(&rustc_bin).map_err(|error| {
            Failure::tool(format!(
                "cannot re-verify sysroot rustc binary at {}: {error}",
                rustc_bin.display()
            ))
        })?;
    if rustc_sha256 != rustc_sha256_after || rustc_id_before != rustc_id_after {
        return Err(Failure::tool(
            "sysroot rustc binary changed during compiler identity verification",
        ));
    }

    let text =
        String::from_utf8(output.stdout).map_err(|error| Failure::tool(error.to_string()))?;
    let verbose = parse_rustc_version_verbose(&text)?;
    if verbose.version != linked_version {
        return Err(Failure::tool(format!(
            "sysroot rustc version ({}) does not match linked rustc driver ({linked_version})",
            verbose.version
        )));
    }
    if !linked_version_matches_commit(linked_version, &verbose.commit) {
        return Err(Failure::tool(format!(
            "sysroot rustc commit ({}) does not match linked rustc version ({linked_version})",
            verbose.commit
        )));
    }
    if !is_valid_host_triple(&verbose.host) {
        return Err(Failure::tool(format!(
            "sysroot rustc reported invalid host triple: {:?}",
            verbose.host
        )));
    }
    let linked_host = rustc_session::config::host_tuple();
    if verbose.host != linked_host {
        return Err(Failure::tool(format!(
            "sysroot rustc host ({}) does not match linked rustc host ({linked_host})",
            verbose.host
        )));
    }
    if verbose.commit != ir::COMPILER_COMMIT {
        return Err(Failure::tool(
            "sysroot rustc does not match the pinned full compiler commit",
        ));
    }

    let _driver_sha256 = verify_driver_residency(sysroot, &verbose.host)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_maps_preserves_trailing_spaces_handles_non_utf8_and_decodes_dev() {
        let normal = parse_maps_line(
            b"7f1234560000-7f1234570000 r-xp 00000000 fd:01 12345   /usr/lib/librustc_driver-abc.so",
        )
        .unwrap();
        assert_eq!(normal.start, 0x7f12_3456_0000);
        assert_eq!(normal.end, 0x7f12_3457_0000);
        assert_eq!(normal.perms, b"r-xp");
        assert_eq!(normal.dev, linux_makedev(0xfd, 0x01));
        assert_eq!(normal.inode, 12345);
        assert_eq!(
            normal.pathname,
            Some(b"/usr/lib/librustc_driver-abc.so".as_slice())
        );

        let trailing_space = parse_maps_line(
            b"7f1234560000-7f1234570000 r-xp 00000000 08:01 12345   /opt/my rust dir/librustc_driver-a.so ",
        )
        .unwrap();
        assert_eq!(
            trailing_space.pathname,
            Some(b"/opt/my rust dir/librustc_driver-a.so ".as_slice())
        );

        let non_utf8 =
            parse_maps_line(b"7f1234560000-7f1234570000 r-xp 00000000 08:01 99   /tmp/\xff/blob")
                .unwrap();
        assert_eq!(non_utf8.inode, 99);
        assert_eq!(non_utf8.pathname, Some(b"/tmp/\xff/blob".as_slice()));

        let anon = parse_maps_line(b"7f1234560000-7f1234570000 rw-p 00000000 00:00 0   ").unwrap();
        assert_eq!(anon.pathname, None);
    }

    #[test]
    fn address_residency_ignores_decoys_and_rejects_deleted_non_exec_and_anonymous() {
        let addr: usize = 0x7f00_0025_0000;
        let maps = b"\
555555554000-555555558000 r--p 00000000 08:01 100   /usr/bin/anneal-rustc-capture\n\
7f0000000000-7f0000100000 r--p 00000000 08:01 200   /sysroot/lib/librustc_driver-decoy.so\n\
7f0000100000-7f0000200000 r-xp 00000000 08:01 201   /lib/x86_64-linux-gnu/libc.so.6\n\
7f0000200000-7f0000500000 r-xp 00100000 fd:01 300   /cas/blob-non-utf8-\xff\n\
7fff00000000-7fff00010000 rw-p 00000000 00:00 0     [stack]\n";
        assert_eq!(
            resolve_driver_mapping_dev_ino(maps, addr).unwrap(),
            (linux_makedev(0xfd, 0x01), 300)
        );

        let deleted =
            b"7f0000200000-7f0000500000 r-xp 00100000 fd:01 300   /opt/librustc_driver-1.so (deleted)\n";
        let err = resolve_driver_mapping_dev_ino(deleted, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("deleted"), "{err:?}");

        let non_exec =
            b"7f0000200000-7f0000500000 r--p 00100000 fd:01 300   /opt/librustc_driver-1.so\n";
        let err = resolve_driver_mapping_dev_ino(non_exec, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("not executable"), "{err:?}");

        let anon = b"7f0000200000-7f0000500000 r-xp 00000000 00:00 0\n";
        let err = resolve_driver_mapping_dev_ino(anon, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("not file-backed"), "{err:?}");

        let missing = b"7fff00000000-7fff00010000 rw-p 00000000 00:00 0 [stack]\n";
        let err = resolve_driver_mapping_dev_ino(missing, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("cannot locate"), "{err:?}");
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_sysroot_matches_by_dev_ino_and_rejects_decoy_and_host_traversal() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let cas = dir.path().join("cas");
        let sysroot = dir.path().join("runfiles-sysroot");
        fs::create_dir_all(&cas).unwrap();
        fs::create_dir_all(sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();

        let real_driver = cas.join("blob-driver");
        fs::write(&real_driver, b"driver-elf-bytes").unwrap();
        let real_dev_ino = regular_file_dev_ino(&real_driver).unwrap();
        let link_driver = sysroot.join("lib/librustc_driver-deadbeef.so");
        symlink(&real_driver, &link_driver).unwrap();

        // Decoy file symlinked to an unrelated file does not satisfy residency
        // when the executing driver address maps `real_dev_ino`.
        let decoy_target = cas.join("libc.so.6");
        fs::write(&decoy_target, b"decoy-libc").unwrap();
        let decoy_sysroot = dir.path().join("decoy-sysroot");
        fs::create_dir_all(decoy_sysroot.join("lib")).unwrap();
        symlink(
            &decoy_target,
            decoy_sysroot.join("lib/librustc_driver-0123.so"),
        )
        .unwrap();

        let digest =
            match_and_hash_sysroot_driver(&sysroot, "x86_64-unknown-linux-gnu", real_dev_ino)
                .unwrap();
        assert_eq!(digest, sha256_bytes(b"driver-elf-bytes"));

        let err =
            match_and_hash_sysroot_driver(&decoy_sysroot, "x86_64-unknown-linux-gnu", real_dev_ino)
                .unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");

        // Host path traversal must be rejected before joining paths.
        for bad_host in ["", ".", "..", "/tmp/evil", "../../tmp/evil", "a/b"] {
            let err = match_and_hash_sysroot_driver(&sysroot, bad_host, real_dev_ino).unwrap_err();
            assert!(
                err.diagnostics[0].contains("invalid rustc host triple"),
                "{bad_host:?}: {err:?}"
            );
        }
    }

    #[test]
    fn linked_version_commit_binding_validates_short_prefix() {
        let ver = "1.98.0-nightly (f8a08b688 2026-05-30)";
        assert!(linked_version_matches_commit(
            ver,
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"
        ));
        assert!(linked_version_matches_commit(
            "1.98.0-dev (f8a08b688cbe)",
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"
        ));
        assert!(!linked_version_matches_commit(
            ver,
            "0000000000000000000000000000000000000000"
        ));
        assert!(!linked_version_matches_commit(ver, "f8a08b68"));
        assert!(!linked_version_matches_commit(
            "1.98.0-nightly (f8a08b688zzz 2026-05-30)",
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"
        ));
    }

    #[test]
    fn parses_rustc_version_verbose_and_rejects_incomplete_output() {
        let valid = "\
rustc 1.98.0-nightly (f8a08b688 2026-05-30)\n\
binary: rustc\n\
commit-hash: f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\n\
commit-date: 2026-05-30\n\
host: x86_64-unknown-linux-gnu\n\
release: 1.98.0-nightly\n\
LLVM version: 22.1.6\n";
        let parsed = parse_rustc_version_verbose(valid).unwrap();
        assert_eq!(parsed.version, "1.98.0-nightly (f8a08b688 2026-05-30)");
        assert_eq!(parsed.commit, "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1");
        assert_eq!(parsed.host, "x86_64-unknown-linux-gnu");

        assert!(parse_rustc_version_verbose("rustc 1.98.0\n").is_err());
        assert!(parse_rustc_version_verbose("commit-hash: abc\nhost: x\n").is_err());
    }
}
