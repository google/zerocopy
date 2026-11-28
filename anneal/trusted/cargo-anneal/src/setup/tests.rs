// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    ffi::OsString,
    fs, io,
    path::{Path, PathBuf},
};

use super::*;

mod tools;
mod reinstall;
mod markers;
mod prune;
mod install_dir;

/// Return a successful `current_exe` result for a workspace-built CLI.
fn cli() -> io::Result<PathBuf> {
    Ok(PathBuf::from("/workspace/target/debug/cargo-anneal"))
}

/// Return a failed `current_exe` result.
fn unknown_cli() -> io::Result<PathBuf> {
    Err(io::Error::other("executable path unavailable"))
}

fn write_archive(path: &Path) {
    write_archive_with(path, b"archive under test");
}

fn write_archive_with(path: &Path, contents: &[u8]) {
    write_archive_entries(path, &[("marker.txt", contents)]);
}

fn write_archive_entries(path: &Path, entries: &[(&str, &[u8])]) {
    let file = fs::File::create(path).expect("create archive");
    let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
    let mut archive = tar::Builder::new(encoder);
    for (name, contents) in entries {
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(0o644);
        header.set_cksum();
        archive
            .append_data(&mut header, name, *contents)
            .expect("write archive entry");
    }
    archive
        .into_inner()
        .expect("finish tar archive")
        .finish()
        .expect("finish compressed archive");
}

#[test]
fn bundle_paths_follow_omnibus_archive_layout() {
    let bundle = Bundle::new(PathBuf::from("/opt/anneal-bundle"));
    assert_eq!(
        bundle.capture(),
        Path::new("/opt/anneal-bundle/bin/anneal-rustc-capture")
    );
    assert_eq!(bundle.sysroot(), Path::new("/opt/anneal-bundle/rust"));
    assert_eq!(bundle.lean(), Path::new("/opt/anneal-bundle/lean/bin/lean"));
    assert_eq!(
        bundle.prebuilt_dir(),
        Path::new("/opt/anneal-bundle/share/anneal/prebuilt")
    );
}

fn child_dirs(parent: &Path) -> Vec<OsString> {
    fs::read_dir(parent)
        .unwrap()
        .map(|entry| entry.unwrap())
        .filter(|entry| entry.path().is_dir())
        .map(|entry| entry.file_name())
        .collect()
}
