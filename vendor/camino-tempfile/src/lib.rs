// Copyright (c) The camino-tempfile Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

// Setting html_root_url allows links from camino-tempfile-ext to work. This
// line is updated by cargo-release.
#![doc(html_root_url = "https://docs.rs/camino-tempfile/1.4.1")]

//! Temporary files and directories with UTF-8 paths.
//!
//! `camino-tempfile` is a wrapper around the [`tempfile`](mod@::tempfile) crate that returns
//! [`Utf8Path`](camino::Utf8Path) rather than [`Path`](std::path::Path).
//!
//! If your code mostly uses [`camino`], it can be annoying to have to convert temporary paths to
//! `Utf8Path` over and over again. This crate takes care of that for you.
//!
//! This library and its documentation are adapted from the [`tempfile`](mod@::tempfile) crate, and
//! are used under the MIT and Apache 2.0 licenses.
//!
//! This crate closely mirrors tempfile's interface. For extensions that provide
//! quality-of-life improvements such as the ability to create files easily, see
//! [`camino-tempfile-ext`](https://crates.io/crates/camino-tempfile-ext).
//!
//! # Synopsis
//!
//! - Use the [`tempfile()`] function for temporary files
//! - Use the [`tempdir()`] function for temporary directories.
//!
//! # Design
//!
//! This crate provides several approaches to creating temporary files and directories.
//! [`tempfile()`] relies on the OS to remove the temporary file once the last handle is closed.
//! [`Utf8TempDir`] and [`NamedUtf8TempFile`] both rely on Rust destructors for cleanup.
//!
//! When choosing between the temporary file variants, prefer `tempfile` unless you either need to
//! know the file's path or to be able to persist it.
//!
//! ## Resource Leaking
//!
//! [`tempfile()`] will (almost) never fail to cleanup temporary resources. However, [`Utf8TempDir`]
//! and [`NamedUtf8TempFile`] will fail if their destructors don't run. This is because
//! [`tempfile()`] relies on the OS to cleanup the underlying file, while [`Utf8TempDir`] and
//! [`NamedUtf8TempFile`] rely on Rust destructors to do so. Destructors may fail to run if the
//! process exits through an unhandled signal interrupt (like `SIGINT`), or if the instance is
//! declared statically, among other possible reasons.
//!
//! ## Security
//!
//! In the presence of pathological temporary file cleaner, relying on file paths is unsafe because
//! a temporary file cleaner could delete the temporary file which an attacker could then replace.
//!
//! [`tempfile()`] doesn't rely on file paths so this isn't an issue. However, [`NamedUtf8TempFile`]
//! does rely on file paths for _some_ operations. See the security documentation on the
//! [`NamedUtf8TempFile`] type for more information.
//!
//! ## Early drop pitfall
//!
//! Because [`Utf8TempDir`] and [`NamedUtf8TempFile`] rely on their destructors for cleanup, this
//! can lead to an unexpected early removal of the directory/file, usually when working with APIs
//! which are generic over `AsRef<Utf8Path>` or `AsRef<Path>`. Consider the following example:
//!
//! ```no_run
//! # use camino_tempfile::tempdir;
//! # use std::io;
//! # use std::process::Command;
//! # fn main() {
//! #     if let Err(_) = run() {
//! #         ::std::process::exit(1);
//! #     }
//! # }
//! # fn run() -> Result<(), io::Error> {
//! // Create a directory inside of `std::env::temp_dir()`.
//! let temp_dir = tempdir()?;
//!
//! // Spawn the `touch` command inside the temporary directory and collect the exit status
//! // Note that `temp_dir` is **not** moved into `current_dir`, but passed as a reference
//! let exit_status = Command::new("touch").arg("tmp").current_dir(&temp_dir).status()?;
//! assert!(exit_status.success());
//!
//! # Ok(())
//! # }
//! ```
//!
//! This works because a reference to `temp_dir` is passed to `current_dir`, resulting in the
//! destructor of `temp_dir` being run after the `Command` has finished execution. Moving the
//! [`Utf8TempDir`] into the `current_dir` call would result in the [`Utf8TempDir`] being converted
//! into an internal representation, with the original value being dropped and the directory thus
//! being deleted, before the command can be executed.
//!
//! The `touch` command would fail with an `No such file or directory` error.
//!
//! ## Examples
//!
//! Create a temporary file and write some data into it:
//!
//! ```
//! use camino_tempfile::tempfile;
//! use std::io::{self, Write};
//!
//! # fn main() {
//! #     if let Err(_) = run() {
//! #         ::std::process::exit(1);
//! #     }
//! # }
//! # fn run() -> Result<(), io::Error> {
//! // Create a file inside of `std::env::temp_dir()`.
//! let mut file = tempfile()?;
//!
//! writeln!(file, "Brian was here. Briefly.")?;
//! # Ok(())
//! # }
//! ```
//!
//! Create a named temporary file and open an independent file handle:
//!
//! ```
//! use camino_tempfile::NamedUtf8TempFile;
//! use std::io::{self, Write, Read};
//!
//! # fn main() {
//! #     if let Err(_) = run() {
//! #         ::std::process::exit(1);
//! #     }
//! # }
//! # fn run() -> Result<(), io::Error> {
//! let text = "Brian was here. Briefly.";
//!
//! // Create a file inside of `std::env::temp_dir()`.
//! let mut file1 = NamedUtf8TempFile::new()?;
//!
//! // Re-open it.
//! let mut file2 = file1.reopen()?;
//!
//! // Write some test data to the first handle.
//! file1.write_all(text.as_bytes())?;
//!
//! // Read the test data using the second handle.
//! let mut buf = String::new();
//! file2.read_to_string(&mut buf)?;
//! assert_eq!(buf, text);
//! # Ok(())
//! # }
//! ```
//!
//! Create a temporary directory and add a file to it:
//!
//! ```
//! use camino_tempfile::tempdir;
//! use std::fs::File;
//! use std::io::{self, Write};
//!
//! # fn main() {
//! #     if let Err(_) = run() {
//! #         ::std::process::exit(1);
//! #     }
//! # }
//! # fn run() -> Result<(), io::Error> {
//! // Create a directory inside of `std::env::temp_dir()`.
//! let dir = tempdir()?;
//!
//! let file_path = dir.path().join("my-temporary-note.txt");
//! let mut file = File::create(file_path)?;
//! writeln!(file, "Brian was here. Briefly.")?;
//!
//! // By closing the `Utf8TempDir` explicitly, we can check that it has
//! // been deleted successfully. If we don't close it explicitly,
//! // the directory will still be deleted when `dir` goes out
//! // of scope, but we won't know whether deleting the directory
//! // succeeded.
//! drop(file);
//! dir.close()?;
//! # Ok(())
//! # }
//! ```

#![deny(rust_2018_idioms)]

mod builder;
mod dir;
mod errors;
mod file;
mod helpers;

pub use builder::*;
pub use dir::*;
pub use file::*;
