// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `anneal-scaffold`: writes or checks an identity-keyed `AutoScaffold.lean`.

use std::{
    fs,
    io::Read as _,
    path::{Component, Path, PathBuf},
    process::ExitCode,
};

const USAGE: &str = "\
usage: anneal-scaffold --capture FILE (--out FILE | --check FILE) [--module NAME]

Renders an identity-keyed Lean scaffold for the bodies in a capture.

  --capture FILE  The capture's capture.json.
  --out FILE      Write the scaffold to FILE.
  --check FILE    Exit 1 unless FILE already matches the scaffold byte for byte.
  --module NAME   The Lean module and namespace name (default AutoScaffold).

Paths must not contain `..` components or name symlinks. Exit status: 0 on
success, 1 on a failed --check or an unusable capture, 2 on usage or I/O
errors.";

/// The largest capture accepted, so a wrong path cannot exhaust memory.
const MAX_CAPTURE_BYTES: u64 = 512 * 1024 * 1024;

enum Mode {
    Write(PathBuf),
    Check(PathBuf),
}

enum Failure {
    /// A failed check or an unusable capture (exit 1).
    Rejected(String),
    /// A usage or I/O error (exit 2).
    Usage(String),
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(Failure::Rejected(msg)) => {
            eprintln!("anneal-scaffold: {msg}");
            ExitCode::from(1)
        }
        Err(Failure::Usage(msg)) => {
            eprintln!("anneal-scaffold: {msg}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<(), Failure> {
    // Paths need not be UTF-8, so read arguments as `OsString`s.
    let mut args = std::env::args_os().skip(1);
    let mut capture = None;
    let mut mode = None;
    let mut module = String::from("AutoScaffold");
    while let Some(arg) = args.next() {
        let mut value = |flag: &str| {
            args.next().ok_or_else(|| Failure::Usage(format!("{flag} needs a value\n\n{USAGE}")))
        };
        match arg.to_str() {
            Some("-h" | "--help") => {
                println!("{USAGE}");
                return Ok(());
            }
            Some("--capture") => capture = Some(PathBuf::from(value("--capture")?)),
            Some("--out") => set_mode(&mut mode, Mode::Write(value("--out")?.into()))?,
            Some("--check") => set_mode(&mut mode, Mode::Check(value("--check")?.into()))?,
            Some("--module") => {
                module = value("--module")?
                    .into_string()
                    .map_err(|_| Failure::Usage(format!("--module must be UTF-8\n\n{USAGE}")))?;
            }
            _ => {
                return Err(Failure::Usage(format!(
                    "unknown argument `{}`\n\n{USAGE}",
                    arg.to_string_lossy()
                )));
            }
        }
    }
    let capture =
        capture.ok_or_else(|| Failure::Usage(format!("--capture is required\n\n{USAGE}")))?;
    let mode = mode
        .ok_or_else(|| Failure::Usage(format!("one of --out or --check is required\n\n{USAGE}")))?;
    anneal_scaffold::validate_module_name(&module).map_err(|e| Failure::Usage(e.0))?;
    if let Mode::Write(out) = &mode {
        if aliases(&capture, out) {
            return Err(Failure::Usage(format!(
                "--out {} names the --capture file",
                out.display()
            )));
        }
    }
    let text = read_capture(&capture)?;
    let scaffold = anneal_scaffold::render(&text, &module)
        .map_err(|e| Failure::Rejected(format!("{}: {e}", capture.display())))?;
    match mode {
        Mode::Write(out) => write_output(&out, &scaffold),
        Mode::Check(path) => {
            let path = path.as_path();
            // A missing file is stale, not an error.
            let current = read_regular(path)?.unwrap_or_default();
            if current == scaffold.as_bytes() {
                Ok(())
            } else {
                Err(Failure::Rejected(format!(
                    "{} is stale; regenerate it with --out",
                    path.display()
                )))
            }
        }
    }
}

fn set_mode(slot: &mut Option<Mode>, mode: Mode) -> Result<(), Failure> {
    if slot.replace(mode).is_some() {
        return Err(Failure::Usage(format!("give exactly one of --out or --check\n\n{USAGE}")));
    }
    Ok(())
}

/// Refuse `..` components, which could leave the directory the caller named.
fn check_path(path: &Path) -> Result<(), Failure> {
    if path.as_os_str().is_empty() || path.components().any(|c| c == Component::ParentDir) {
        return Err(Failure::Usage(format!(
            "path must be non-empty and contain no `..` component: {}",
            path.display()
        )));
    }
    Ok(())
}

fn read_capture(path: &Path) -> Result<String, Failure> {
    let bytes = read_regular(path)?
        .ok_or_else(|| Failure::Usage(format!("{} does not exist", path.display())))?;
    String::from_utf8(bytes).map_err(|_| Failure::Usage(format!("{} is not UTF-8", path.display())))
}

/// Linux `O_NOFOLLOW`, whose value differs by architecture: x86-64 uses
/// `include/uapi/asm-generic/fcntl.h`, and AArch64 overrides it in
/// `arch/arm64/include/uapi/asm/fcntl.h`, where `0o400000` is `O_LARGEFILE`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const O_NOFOLLOW: i32 = 0o400000;
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const O_NOFOLLOW: i32 = 0o100000;

/// `open(2)` flags that keep the final path component from being a symlink
/// and keep a FIFO swapped in for the file from blocking the open. Linux
/// `O_NONBLOCK` is `0o4000` on both architectures.
#[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")))]
const OPEN_FLAGS: i32 = O_NOFOLLOW | 0o4000;

/// Read a regular file of at most `MAX_CAPTURE_BYTES`, or return `None` if
/// nothing exists at `path`. A symlink, directory, or other non-regular file
/// is refused. The path is inspected without following symlinks, and the
/// opened descriptor must denote that same regular file, so swapping the
/// path between the check and the open cannot redirect the read.
fn read_regular(path: &Path) -> Result<Option<Vec<u8>>, Failure> {
    check_path(path)?;
    let before = match fs::symlink_metadata(path) {
        Ok(meta) => meta,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(Failure::Usage(format!("cannot inspect {}: {e}", path.display()))),
    };
    if !before.is_file() {
        return Err(Failure::Usage(format!("{} is not a regular file", path.display())));
    }
    let io = |e: std::io::Error| Failure::Usage(format!("cannot read {}: {e}", path.display()));
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(OPEN_FLAGS);
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt as _;
        options.custom_flags(FILE_FLAG_OPEN_REPARSE_POINT);
    }
    let file = options.open(path).map_err(io)?;
    let opened = file.metadata().map_err(io)?;
    if !opened.is_file() || !same_file(&before, &opened) {
        return Err(Failure::Usage(format!("{} changed while being opened", path.display())));
    }
    if opened.len() > MAX_CAPTURE_BYTES {
        return Err(Failure::Usage(format!(
            "{} is larger than {MAX_CAPTURE_BYTES} bytes",
            path.display()
        )));
    }
    let mut bytes = Vec::new();
    file.take(MAX_CAPTURE_BYTES + 1).read_to_end(&mut bytes).map_err(io)?;
    if bytes.len() as u64 > MAX_CAPTURE_BYTES {
        return Err(Failure::Usage(format!("{} grew while being read", path.display())));
    }
    Ok(Some(bytes))
}

#[cfg(unix)]
fn same_file(a: &fs::Metadata, b: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt as _;
    a.dev() == b.dev() && a.ino() == b.ino()
}

/// Windows `FILE_ATTRIBUTE_REPARSE_POINT`, set on symlinks and junctions.
#[cfg(windows)]
const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x400;

/// Windows `FILE_FLAG_OPEN_REPARSE_POINT`, which opens a reparse point itself
/// rather than what it points to.
#[cfg(windows)]
const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;

/// Stable Rust exposes no file ID on Windows, so compare everything it does
/// expose about the file, and refuse a reparse point outright. Together
/// with opening the path with `FILE_FLAG_OPEN_REPARSE_POINT`, a symlink or
/// junction swapped in for the file is refused rather than followed.
#[cfg(windows)]
fn same_file(a: &fs::Metadata, b: &fs::Metadata) -> bool {
    use std::os::windows::fs::MetadataExt as _;
    a.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT == 0
        && a.file_attributes() == b.file_attributes()
        && a.creation_time() == b.creation_time()
        && a.last_write_time() == b.last_write_time()
        && a.file_size() == b.file_size()
}

/// Elsewhere there is no way to tell whether two paths name one file, so
/// none is ever taken to, and every read is refused.
#[cfg(not(any(unix, windows)))]
fn same_file(_: &fs::Metadata, _: &fs::Metadata) -> bool {
    false
}

/// Whether `out` already names the file `capture` names, through another
/// spelling of the path or a hard link. Writing through another spelling
/// would replace the capture; writing through a hard link would only detach
/// that name from it, but is refused too, as almost certainly a mistake.
fn aliases(capture: &Path, out: &Path) -> bool {
    match (fs::metadata(capture), fs::symlink_metadata(out)) {
        #[cfg(unix)]
        (Ok(c), Ok(o)) => same_file(&c, &o),
        #[cfg(not(unix))]
        (Ok(_), Ok(_)) => fs::canonicalize(capture).ok() == fs::canonicalize(out).ok(),
        _ => false,
    }
}

/// Write through a sibling temporary file and rename it into place, so a
/// failed write never leaves a truncated scaffold. An existing output must be
/// a regular file; a symlink is refused rather than followed.
fn write_output(path: &Path, contents: &str) -> Result<(), Failure> {
    check_path(path)?;
    match fs::symlink_metadata(path) {
        Ok(meta) if !meta.is_file() => {
            return Err(Failure::Usage(format!("{} is not a regular file", path.display())));
        }
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(Failure::Usage(format!("cannot inspect {}: {e}", path.display()))),
    }
    let name = path
        .file_name()
        .ok_or_else(|| Failure::Usage(format!("{} has no file name", path.display())))?;
    let io = |e: std::io::Error| Failure::Usage(format!("cannot write {}: {e}", path.display()));
    // `create_new` refuses any existing entry, including a symlink, so a
    // stale or concurrent temporary file only moves on to the next name.
    let (tmp, mut file) = (0..100)
        .find_map(|n| {
            let mut tmp_name = std::ffi::OsString::from(".");
            tmp_name.push(name);
            tmp_name.push(format!(".tmp-{}-{n}", std::process::id()));
            let tmp = path.with_file_name(tmp_name);
            match fs::OpenOptions::new().write(true).create_new(true).open(&tmp) {
                Ok(file) => Some(Ok((tmp, file))),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => None,
                Err(e) => Some(Err(e)),
            }
        })
        .unwrap_or_else(|| {
            Err(std::io::Error::other("no free temporary file name next to the output"))
        })
        .map_err(io)?;
    // `rename` replaces the directory entry itself, so even an output swapped
    // for a symlink after the check above is replaced, never written through.
    let result = (|| {
        std::io::Write::write_all(&mut file, contents.as_bytes())?;
        file.sync_all()?;
        fs::rename(&tmp, path)
    })();
    if result.is_err() {
        let _ = fs::remove_file(&tmp);
    }
    result.map_err(io)
}
