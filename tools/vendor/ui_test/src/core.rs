//! Basic operations useful for building a testsuite

use color_eyre::eyre::Result;
use crossbeam_channel::unbounded;
use crossbeam_channel::Receiver;
use crossbeam_channel::Sender;
use regex::bytes::RegexSet;
use std::num::NonZeroUsize;
use std::path::Component;
use std::path::Path;
use std::path::Prefix;
use std::sync::OnceLock;
use std::thread;

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
    /// * [`CrateType::ProcMacro`] if the file contains a [proc macro attribute]
    /// * [`CrateType::Test`] if the file contains `#[test]`
    /// * [`CrateType::Bin`] if the file contains `fn main()` or `#[start]`
    /// * otherwise [`CrateType::Lib`]
    ///
    /// [proc macro attribute]: https://doc.rust-lang.org/reference/procedural-macros.html
    pub fn from_file_contents(file_contents: &[u8]) -> CrateType {
        static RE: OnceLock<RegexSet> = OnceLock::new();
        let re = RE.get_or_init(|| {
            RegexSet::new([
                r"#\[proc_macro(_derive|_attribute)?[\](]",
                r"#\[test\]",
                r"fn main()|#\[start\]",
            ])
            .unwrap()
        });

        match re.matches(file_contents).iter().next() {
            Some(0) => CrateType::ProcMacro,
            Some(1) => CrateType::Test,
            Some(2) => CrateType::Bin,
            _ => CrateType::Lib,
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
pub fn run_and_collect<const N: usize, SUBMISSION: Send, RESULT: Send>(
    num_threads: NonZeroUsize,
    submitter: impl FnOnce([Sender<SUBMISSION>; N]) + Send,
    runner: impl Sync + Fn(&[Receiver<SUBMISSION>; N], Sender<RESULT>) -> Result<()>,
    collector: impl FnOnce(Receiver<RESULT>) + Send,
) -> Result<()> {
    // A channel for files to process
    let (submit, receive): (Vec<_>, Vec<_>) = std::iter::repeat_with(unbounded).take(N).unzip();
    let receive = receive[..].try_into().unwrap();
    let mut submit = submit.into_iter();
    let submit = std::array::from_fn(|_| submit.next().unwrap());

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
            threads.push(s.spawn(|| runner(receive, finished_files_sender)));
        }

        for thread in threads {
            thread.join().unwrap()?;
        }
        Ok(())
    })
}
