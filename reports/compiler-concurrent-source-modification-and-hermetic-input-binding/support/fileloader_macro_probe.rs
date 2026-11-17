// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Closed-namespace `FileLoader` probe that admits only declared source files
//! and their lexical parent directories, mirroring strict Pattern 4 input
//! gating (`RecordingLoader`), and logs every `FileLoader` access and refusal.
//! Any refusal fails closed (exit code `3`) even if `rustc` exits `0`.

#![feature(rustc_private)]
#![feature(normalize_lexically)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_span;

use std::collections::BTreeSet;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use rustc_interface::interface;
use rustc_span::source_map::{FileLoader, RealFileLoader};

struct ClosedLoader {
    allowed: BTreeSet<PathBuf>,
    directories: BTreeSet<PathBuf>,
    refusals: Arc<Mutex<Vec<String>>>,
    backtrace: bool,
}

impl ClosedLoader {
    fn lookup(&self, path: &Path) -> io::Result<PathBuf> {
        let absolute = std::path::absolute(path)?;
        for parent in absolute.ancestors().skip(1) {
            let parent = parent.normalize_lexically().map_err(io::Error::other)?;
            if !self.directories.contains(&parent) {
                return Err(io::Error::other("undeclared source directory"));
            }
        }
        let path = absolute.normalize_lexically().map_err(io::Error::other)?;
        if !self.allowed.contains(&path) {
            return Err(io::Error::other("undeclared source filename"));
        }
        if path.canonicalize()? != path || !path.is_file() {
            return Err(io::Error::other(
                "declared source is not a canonical regular file",
            ));
        }
        Ok(path)
    }

    fn read_path(&self, op: &str, path: &Path) -> io::Result<PathBuf> {
        match self.lookup(path) {
            Ok(p) => {
                eprintln!("[probe] {op} ADMIT {}", path.display());
                Ok(p)
            }
            Err(cause) => {
                let error = format!("undeclared compiler read: {}: {cause}", path.display());
                eprintln!("[probe] {op} REFUSE {error}");
                if self.backtrace {
                    let bt = std::backtrace::Backtrace::force_capture().to_string();
                    for line in bt.lines().filter(|l| {
                        l.contains("rustc_") && !l.contains("at /rustc") && !l.contains("std::")
                    }) {
                        eprintln!("[probe-bt] {}", line.trim());
                    }
                }
                self.refusals.lock().unwrap().push(error.clone());
                Err(io::Error::other(error))
            }
        }
    }
}

impl FileLoader for ClosedLoader {
    fn file_exists(&self, path: &Path) -> bool {
        let ok = self.lookup(path).is_ok();
        eprintln!("[probe] file_exists {} -> {ok}", path.display());
        ok
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        let p = self.read_path("read_file", path)?;
        RealFileLoader.read_file(&p)
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        let p = self.read_path("read_binary_file", path)?;
        RealFileLoader.read_binary_file(&p)
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        RealFileLoader.current_directory()
    }
}

struct Callbacks {
    allowed: BTreeSet<PathBuf>,
    refusals: Arc<Mutex<Vec<String>>>,
    backtrace: bool,
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut interface::Config) {
        let directories = self
            .allowed
            .iter()
            .flat_map(|p| p.ancestors().skip(1).map(Path::to_path_buf))
            .collect();
        config.file_loader = Some(Box::new(ClosedLoader {
            allowed: self.allowed.clone(),
            directories,
            refusals: self.refusals.clone(),
            backtrace: self.backtrace,
        }));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let allowed: BTreeSet<PathBuf> = std::env::var("PROBE_ALLOWED")
        .expect("PROBE_ALLOWED")
        .split(':')
        .map(PathBuf::from)
        .collect();
    let backtrace = std::env::var_os("PROBE_BACKTRACE").is_some();
    let refusals = Arc::new(Mutex::new(Vec::new()));
    let mut callbacks = Callbacks {
        allowed,
        refusals: refusals.clone(),
        backtrace,
    };
    let code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut callbacks)
    });
    let refusals = refusals.lock().unwrap();
    eprintln!("[probe] rustc_exit={code:?} refusals={}", refusals.len());
    for r in refusals.iter() {
        eprintln!("[probe] REFUSAL: {r}");
    }
    std::process::exit(if refusals.is_empty() { 0 } else { 3 });
}
