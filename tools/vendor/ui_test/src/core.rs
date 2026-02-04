//! Basic operations useful for building a testsuite

use crate::test_result::Errored;
use bstr::ByteSlice as _;
use color_eyre::eyre::Result;
use crossbeam_channel::unbounded;
use crossbeam_channel::Receiver;
use crossbeam_channel::Sender;
use std::num::NonZeroUsize;
use std::path::Component;
use std::path::Path;
use std::path::Prefix;
use std::process::Command;
use std::process::Output;
use std::thread;

pub(crate) fn run_command(cmd: &mut Command) -> Result<Output, Errored> {
    match cmd.output() {
        Err(err) => Err(Errored {
            errors: vec![],
            stderr: err.to_string().into_bytes(),
            stdout: format!("could not spawn `{:?}` as a process", cmd.get_program()).into_bytes(),
            command: format!("{cmd:?}"),
        }),
        Ok(output) => Ok(output),
    }
}

/// Remove the common prefix of this path and the `root_dir`.
pub(crate) fn strip_path_prefix<'a>(
    path: &'a Path,
    prefix: &Path,
) -> impl Iterator<Item = Component<'a>> {
    let mut components = path.components();
    for c in prefix.components() {
        // Windows has some funky paths. This is probably wrong, but works well in practice.
        let deverbatimize = |c| match c {
            Component::Prefix(prefix) => Err(match prefix.kind() {
                Prefix::VerbatimUNC(a, b) => Prefix::UNC(a, b),
                Prefix::VerbatimDisk(d) => Prefix::Disk(d),
                other => other,
            }),
            c => Ok(c),
        };
        let c2 = components.next();
        if Some(deverbatimize(c)) == c2.map(deverbatimize) {
            continue;
        }
        return c2.into_iter().chain(components);
    }
    None.into_iter().chain(components)
}

impl CrateType {
    /// Heuristic:
    /// * if the file contains `#[test]`, automatically pass `--cfg test`.
    /// * if the file does not contain `fn main()` or `#[start]`, automatically pass `--crate-type=lib`.
    /// This avoids having to spam `fn main() {}` in almost every test.
    pub fn from_file_contents(file_contents: &[u8]) -> CrateType {
        if file_contents.find(b"#[proc_macro").is_some() {
            CrateType::ProcMacro
        } else if file_contents.find(b"#[test]").is_some() {
            CrateType::Test
        } else if file_contents.find(b"fn main()").is_none()
            && file_contents.find(b"#[start]").is_none()
        {
            CrateType::Lib
        } else {
            CrateType::Bin
        }
    }
}

/// The kind of crate we're building here. Corresponds to `--crate-type` flags of rustc
pub enum CrateType {
    /// A proc macro
    ProcMacro,
    /// A file containing unit tests
    Test,
    /// A binary file containing a main function or start function
    Bin,
    /// A library crate
    Lib,
}

/// A generic multithreaded runner that has a thread for producing work,
/// a thread for collecting work, and `num_threads` threads for doing the work.
pub fn run_and_collect<SUBMISSION: Send, RESULT: Send>(
    num_threads: NonZeroUsize,
    submitter: impl FnOnce(Sender<SUBMISSION>) + Send,
    runner: impl Sync + Fn(&Receiver<SUBMISSION>, Sender<RESULT>) -> Result<()>,
    collector: impl FnOnce(Receiver<RESULT>) + Send,
) -> Result<()> {
    // A channel for files to process
    let (submit, receive) = unbounded();

    thread::scope(|s| {
        // Create a thread that is in charge of walking the directory and submitting jobs.
        // It closes the channel when it is done.
        s.spawn(|| submitter(submit));

        // A channel for the messages emitted by the individual test threads.
        // Used to produce live updates while running the tests.
        let (finished_files_sender, finished_files_recv) = unbounded();

        s.spawn(|| collector(finished_files_recv));

        let mut threads = vec![];

        // Create N worker threads that receive files to test.
        for _ in 0..num_threads.get() {
            let finished_files_sender = finished_files_sender.clone();
            threads.push(s.spawn(|| runner(&receive, finished_files_sender)));
        }

        for thread in threads {
            thread.join().unwrap()?;
        }
        Ok(())
    })
}
