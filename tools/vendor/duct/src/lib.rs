//! Duct is a library for running child processes. Duct makes it easy to build
//! pipelines and redirect IO like a shell. At the same time, Duct helps you
//! write correct, portable code: whitespace is never significant, errors from
//! child processes get reported by default, and a variety of [gotchas, bugs,
//! and platform
//! inconsistencies](https://github.com/oconnor663/duct.py/blob/master/gotchas.md)
//! are handled for you the Right Way™.
//!
//! - [Documentation](https://docs.rs/duct)
//! - [Crate](https://crates.io/crates/duct)
//! - [GitHub repo](https://github.com/oconnor663/duct.rs)
//! - [the same library, in Python](https://github.com/oconnor663/duct.py)
//!
//! Examples
//! --------
//!
//! Run a command without capturing any output. Here "hi" is printed directly
//! to the terminal:
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! use duct::cmd;
//! cmd!("echo", "hi").run()?;
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Capture the standard output of a command. Here "hi" is returned as a
//! `String`:
//!
//! ```
//! # use duct::cmd;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! let stdout = cmd!("echo", "hi").read()?;
//! assert_eq!(stdout, "hi");
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Capture the standard output of a pipeline:
//!
//! ```
//! # use duct::cmd;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! let stdout = cmd!("echo", "hi").pipe(cmd!("sed", "s/i/o/")).read()?;
//! assert_eq!(stdout, "ho");
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Merge standard error into standard output and read both incrementally:
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! use duct::cmd;
//! use std::io::prelude::*;
//! use std::io::BufReader;
//!
//! let big_cmd = cmd!("bash", "-c", "echo out && echo err 1>&2");
//! let reader = big_cmd.stderr_to_stdout().reader()?;
//! let mut lines = BufReader::new(reader).lines();
//! assert_eq!(lines.next().unwrap()?, "out");
//! assert_eq!(lines.next().unwrap()?, "err");
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Children that exit with a non-zero status return an error by default:
//!
//! ```
//! # use duct::cmd;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! let result = cmd!("false").run();
//! assert!(result.is_err());
//! let result = cmd!("false").unchecked().run();
//! assert!(result.is_ok());
//! # }
//! # Ok(())
//! # }
//! ```

use env_name_str::EnvNameString;
use shared_child::SharedChild;
use shared_thread::SharedThread;
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::mem;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::{Arc, MutexGuard, OnceLock, RwLock};

#[cfg(not(windows))]
use std::os::unix::prelude::*;
#[cfg(windows)]
use std::os::windows::prelude::*;

#[cfg(not(windows))]
use std::os::fd::IntoRawFd as IntoRawFdOrHandle;
#[cfg(windows)]
use std::os::windows::io::IntoRawHandle as IntoRawFdOrHandle;

mod env_name_str;

/// Unix-specific extensions to duct, for sending signals.
#[cfg(unix)]
pub mod unix;

// enums defined below
use ExpressionInner::*;
use IoExpressionInner::*;

/// Create a command given a program name and a collection of arguments. See
/// also the [`cmd!`](macro.cmd.html) macro, which doesn't require a collection.
///
/// # Example
///
/// ```
/// use duct::cmd;
///
/// let args = vec!["foo", "bar", "baz"];
///
/// # // NOTE: Normally this wouldn't work on Windows, but we have an "echo"
/// # // binary that gets built for our main tests, and it's sitting around by
/// # // the time we get here. If this ever stops working, then we can disable
/// # // the tests that depend on it.
/// let output = cmd("echo", &args).read();
///
/// assert_eq!("foo bar baz", output.unwrap());
/// ```
pub fn cmd<T, U>(program: T, args: U) -> Expression
where
    T: IntoExecutablePath,
    U: IntoIterator,
    U::Item: Into<OsString>,
{
    let mut argv_vec = Vec::new();
    argv_vec.push(program.to_executable());
    argv_vec.extend(args.into_iter().map(Into::<OsString>::into));
    Expression::new(Cmd(argv_vec))
}

/// Create a command with any number of of positional arguments, which may be
/// different types (anything that implements
/// [`Into<OsString>`](https://doc.rust-lang.org/std/convert/trait.From.html)).
/// See also the [`cmd`](fn.cmd.html) function, which takes a collection of
/// arguments.
///
/// # Example
///
/// ```
/// use duct::cmd;
/// use std::path::Path;
///
/// let arg1 = "foo";
/// let arg2 = "bar".to_owned();
/// let arg3 = Path::new("baz");
///
/// let output = cmd!("echo", arg1, arg2, arg3).read();
///
/// assert_eq!("foo bar baz", output.unwrap());
/// ```
#[macro_export]
macro_rules! cmd {
    ( $program:expr $(, $arg:expr )* $(,)? ) => {
        {
            use std::ffi::OsString;
            let args: std::vec::Vec<OsString> = std::vec![$( Into::<OsString>::into($arg) ),*];
            $crate::cmd($program, args)
        }
    };
}

/// The central objects in Duct, created with
/// [`cmd`](fn.cmd.html) or [`cmd!`](macro.cmd.html).
///
/// Expressions can be combined with [`pipe`](struct.Expression.html#method.pipe) and executed with
/// [`run`](struct.Expression.html#method.run), [`read`](struct.Expression.html#method.read),
/// [`start`](struct.Expression.html#method.start), or
/// [`reader`](struct.Expression.html#method.reader). There are many other methods to control their
/// execution, like [`stdin_bytes`](struct.Expression.html#method.stdin_bytes),
/// [`stdout_capture`](struct.Expression.html#method.stdout_capture),
/// [`env`](struct.Expression.html#method.env), and
/// [`unchecked`](struct.Expression.html#method.unchecked).
///
/// Expressions are immutable, and they do a lot of
/// [`Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html) sharing
/// internally, so all of the methods below take `&self` and return a new
/// `Expression` cheaply.
///
/// Expressions using `pipe` form trees, and the order in which you call
/// different methods can matter, just like it matters where you put
/// redirections in Bash. For example, each of these expressions suppresses
/// output differently:
///
/// ```no_run
/// # use duct::cmd;
/// # fn main() -> std::io::Result<()> {
/// // Only suppress stderr on the left side.
/// cmd!("foo").stderr_null().pipe(cmd!("bar")).run()?; // foo 2>/dev/null | bar
///
/// // Only suppress stderr on the right side.
/// cmd!("foo").pipe(cmd!("bar").stderr_null()).run()?; // foo | bar 2>/dev/null
///
/// // Suppress stderr on both sides.
/// cmd!("foo").pipe(cmd!("bar")).stderr_null().run()?; // (foo | bar) 2>/dev/null
/// # Ok(())
/// # }
/// ```
#[derive(Clone)]
#[must_use]
pub struct Expression(Arc<ExpressionInner>);

impl Expression {
    /// Execute an expression, wait for it to complete, and return a
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// object containing the results. Nothing is captured by default, but if
    /// you build the expression with
    /// [`stdout_capture`](struct.Expression.html#method.stdout_capture) or
    /// [`stderr_capture`](struct.Expression.html#method.stderr_capture) then
    /// the `Output` will hold those captured bytes.
    ///
    /// # Errors
    ///
    /// In addition to all the IO errors possible with
    /// [`std::process::Command`](https://doc.rust-lang.org/std/process/struct.Command.html),
    /// `run` will return an
    /// [`ErrorKind::Other`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html)
    /// IO error if child returns a non-zero exit status. To suppress this error
    /// and return an `Output` even when the exit status is non-zero, use the
    /// [`unchecked`](struct.Expression.html#method.unchecked) method.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").stdout_capture().run().unwrap();
    /// assert_eq!(b"hi\n".to_vec(), output.stdout);
    /// # }
    /// # }
    /// ```
    pub fn run(&self) -> io::Result<Output> {
        // This could be optimized to avoid creating a background threads, by
        // using the current thread to read stdout or stderr if only one of
        // them is captured, or by using async IO to read both.
        self.start()?.into_output()
    }

    /// Execute an expression, capture its standard output, and return the
    /// captured output as a `String`. This is a convenience wrapper around
    /// [`reader`](struct.Expression.html#method.reader). Like backticks and
    /// `$()` in the shell, `read` trims trailing newlines.
    ///
    /// # Errors
    ///
    /// In addition to all the errors possible with
    /// [`run`](struct.Expression.html#method.run), `read` will return an error
    /// if the captured bytes aren't valid UTF-8.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").stdout_capture().read().unwrap();
    /// assert_eq!("hi", output);
    /// # }
    /// # }
    /// ```
    pub fn read(&self) -> io::Result<String> {
        let mut reader = self.reader()?;
        let mut output = String::new();
        reader.read_to_string(&mut output)?;
        while output.ends_with('\n') || output.ends_with('\r') {
            output.truncate(output.len() - 1);
        }
        Ok(output)
    }

    /// Start running an expression, and immediately return a
    /// [`Handle`](struct.Handle.html) that represents all the child processes.
    /// This is analogous to the
    /// [`spawn`](https://doc.rust-lang.org/std/process/struct.Command.html#method.spawn)
    /// method in the standard library. The `Handle` may be shared between
    /// multiple threads.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let handle = cmd!("echo", "hi").stdout_capture().start().unwrap();
    /// let output = handle.wait().unwrap();
    /// assert_eq!(b"hi\n".to_vec(), output.stdout);
    /// # }
    /// # }
    /// ```
    pub fn start(&self) -> io::Result<Handle> {
        let stdout_capture = OutputCaptureContext::new();
        let stderr_capture = OutputCaptureContext::new();
        let context = IoContext::new(&stdout_capture, &stderr_capture);

        Ok(Handle {
            inner: self.0.start(context)?,
            result: OnceLock::new(),
            readers: RwLock::new((
                stdout_capture.maybe_read_thread(),
                stderr_capture.maybe_read_thread(),
            )),
        })
    }

    /// Start running an expression, and immediately return a
    /// [`ReaderHandle`](struct.ReaderHandle.html) attached to the child's
    /// stdout. This is similar to `.stdout_capture().start()`, but it returns
    /// the reader to the caller rather than reading from a background thread.
    ///
    /// Note that because this method doesn't read child output on a background
    /// thread, it's a best practice to only create one `ReaderHandle` at a
    /// time. Child processes with a lot of output will eventually block if
    /// their stdout pipe isn't read from. If you have multiple children
    /// running, but you're only reading from one of them at a time, that could
    /// block the others and lead to performance issues or deadlocks. For
    /// reading from multiple children at once, prefer
    /// `.stdout_capture().start()`.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # use std::io::prelude::*;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let mut reader = cmd!("echo", "hi").reader().unwrap();
    /// let mut stdout = Vec::new();
    /// reader.read_to_end(&mut stdout).unwrap();
    /// assert_eq!(b"hi\n".to_vec(), stdout);
    /// # }
    /// # }
    /// ```
    pub fn reader(&self) -> io::Result<ReaderHandle> {
        let stdout_capture = OutputCaptureContext::new();
        let stderr_capture = OutputCaptureContext::new();
        let context = IoContext::new(&stdout_capture, &stderr_capture);
        let handle = Handle {
            inner: self.stdout_capture().0.start(context)?,
            result: OnceLock::new(),
            readers: RwLock::new((None, stderr_capture.maybe_read_thread())),
        };
        Ok(ReaderHandle {
            handle,
            reader: stdout_capture.pair.into_inner().expect("pipe opened").0,
        })
    }

    /// Join two expressions into a pipe expression, where the standard output
    /// of the left will be hooked up to the standard input of the right, like
    /// `|` in the shell.
    ///
    /// # Errors
    ///
    /// During execution, if one side of the pipe returns a non-zero exit
    /// status, that becomes the status of the whole pipe. If both sides return
    /// non-zero, and one of them is
    /// [`unchecked`](struct.Expression.html#method.unchecked), the checked
    /// side wins. Otherwise the right side wins. This is close to the behavior
    /// of Bash with `-o pipefail`.
    ///
    /// During spawning, if the left side of the pipe spawns successfully but
    /// the right side fails to spawn (e.g. the binary doesn't exist), the left
    /// side will be cleaned up without blocking, which might require spawning
    /// a thread. See the [`Handle`] docs for more on this behavior.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").pipe(cmd!("sed", "s/h/p/")).read();
    /// assert_eq!("pi", output.unwrap());
    /// # }
    /// # }
    /// ```
    pub fn pipe<T: Into<Expression>>(&self, right: T) -> Expression {
        Self::new(Pipe(self.clone(), right.into()))
    }

    /// Use bytes or a string as input for an expression, like `<<<` in the
    /// shell. A worker thread will write the input at runtime.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<Vec<u8>>. Here's a string.
    /// let output = cmd!("cat").stdin_bytes("foo").read().unwrap();
    /// assert_eq!("foo", output);
    ///
    /// // And here's a byte slice.
    /// let output = cmd!("cat").stdin_bytes(&b"foo"[..]).read().unwrap();
    /// assert_eq!("foo", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_bytes<T: Into<Vec<u8>>>(&self, bytes: T) -> Expression {
        Self::new(Io(StdinBytes(Arc::new(bytes.into())), self.clone()))
    }

    /// Open a file at the given path and use it as input for an expression,
    /// like `<` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let output = cmd!("head", "-c", "3").stdin_path("/dev/zero").read().unwrap();
    /// assert_eq!("\0\0\0", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_path<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(StdinPath(path.into()), self.clone()))
    }

    /// Use an already opened file or pipe as input for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let input_file = std::fs::File::open("/dev/zero").unwrap();
    /// let output = cmd!("head", "-c", "3").stdin_file(input_file).read().unwrap();
    /// assert_eq!("\0\0\0", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_file<T: IntoRawFdOrHandle>(&self, file: T) -> Expression {
        Self::new(Io(StdinFile(owned_from_raw(file)), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as input for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("cat").stdin_null().read().unwrap();
    /// assert_eq!("", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_null(&self) -> Expression {
        Self::new(Io(StdinNull, self.clone()))
    }

    /// Open a file at the given path and use it as output for an expression,
    /// like `>` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let path = cmd!("mktemp").read().unwrap();
    /// cmd!("echo", "wee").stdout_path(&path).run().unwrap();
    /// let mut output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut output).unwrap();
    /// assert_eq!("wee\n", output);
    /// # }
    /// # }
    /// ```
    pub fn stdout_path<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(StdoutPath(path.into()), self.clone()))
    }

    /// Use an already opened file or pipe as output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// let path = cmd!("mktemp").read().unwrap();
    /// let file = std::fs::File::create(&path).unwrap();
    /// cmd!("echo", "wee").stdout_file(file).run().unwrap();
    /// let mut output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut output).unwrap();
    /// assert_eq!("wee\n", output);
    /// # }
    /// # }
    /// ```
    pub fn stdout_file<T: IntoRawFdOrHandle>(&self, file: T) -> Expression {
        Self::new(Io(StdoutFile(owned_from_raw(file)), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// // This echo command won't print anything.
    /// cmd!("echo", "foo", "bar", "baz").stdout_null().run().unwrap();
    ///
    /// // And you won't get anything even if you try to read its output! The
    /// // null redirect happens farther down in the expression tree than the
    /// // implicit `stdout_capture`, and so it takes precedence.
    /// let output = cmd!("echo", "foo", "bar", "baz").stdout_null().read().unwrap();
    /// assert_eq!("", output);
    /// # }
    /// ```
    pub fn stdout_null(&self) -> Expression {
        Self::new(Io(StdoutNull, self.clone()))
    }

    /// Capture the standard output of an expression. The captured bytes will
    /// be available on the `stdout` field of the
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// object returned by [`run`](struct.Expression.html#method.run) or
    /// [`wait`](struct.Handle.html#method.wait). Output is read by a
    /// background thread, so the child will never block writing to stdout. But
    /// note that [`read`](struct.Expression.html#method.read) and
    /// [`reader`](struct.Expression.html#method.reader) can be more
    /// convenient, and they don't require the background thread.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // The most direct way to read stdout bytes is `stdout_capture`.
    /// let output1 = cmd!("echo", "foo").stdout_capture().run().unwrap().stdout;
    /// assert_eq!(&b"foo\n"[..], &output1[..]);
    ///
    /// // The `read` method is a shorthand for `stdout_capture`, and it also
    /// // does string parsing and newline trimming.
    /// let output2 = cmd!("echo", "foo").read().unwrap();
    /// assert_eq!("foo", output2)
    /// # }
    /// # }
    /// ```
    pub fn stdout_capture(&self) -> Expression {
        Self::new(Io(StdoutCapture, self.clone()))
    }

    /// Join the standard output of an expression to its standard error pipe,
    /// similar to `1>&2` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "foo").stdout_to_stderr().stderr_capture().run().unwrap();
    /// assert_eq!(&b"foo\n"[..], &output.stderr[..]);
    /// # }
    /// # }
    /// ```
    pub fn stdout_to_stderr(&self) -> Expression {
        Self::new(Io(StdoutToStderr, self.clone()))
    }

    /// Open a file at the given path and use it as error output for an
    /// expression, like `2>` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let path = cmd!("mktemp").read().unwrap();
    /// cmd!("sh", "-c", "echo wee >&2").stderr_path(&path).run().unwrap();
    /// let mut error_output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut error_output).unwrap();
    /// assert_eq!("wee\n", error_output);
    /// # }
    /// # }
    /// ```
    pub fn stderr_path<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(StderrPath(path.into()), self.clone()))
    }

    /// Use an already opened file or pipe as error output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// let path = cmd!("mktemp").read().unwrap();
    /// let file = std::fs::File::create(&path).unwrap();
    /// cmd!("sh", "-c", "echo wee >&2").stderr_file(file).run().unwrap();
    /// let mut error_output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut error_output).unwrap();
    /// assert_eq!("wee\n", error_output);
    /// # }
    /// # }
    /// ```
    pub fn stderr_file<T: IntoRawFdOrHandle>(&self, file: T) -> Expression {
        Self::new(Io(StderrFile(owned_from_raw(file)), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as error output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // This echo-to-stderr command won't print anything.
    /// cmd!("sh", "-c", "echo foo bar baz >&2").stderr_null().run().unwrap();
    /// # }
    /// # }
    /// ```
    pub fn stderr_null(&self) -> Expression {
        Self::new(Io(StderrNull, self.clone()))
    }

    /// Capture the error output of an expression. The captured bytes will be
    /// available on the `stderr` field of the `Output` object returned by
    /// [`run`](struct.Expression.html#method.run) or
    /// [`wait`](struct.Handle.html#method.wait). Output is read by a
    /// background thread, so the child will never block writing to stderr.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output_obj = cmd!("sh", "-c", "echo foo >&2").stderr_capture().run().unwrap();
    /// assert_eq!(&b"foo\n"[..], &output_obj.stderr[..]);
    /// # }
    /// # }
    /// ```
    pub fn stderr_capture(&self) -> Expression {
        Self::new(Io(StderrCapture, self.clone()))
    }

    /// Join the standard error of an expression to its standard output pipe,
    /// similar to `2>&1` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let error_output = cmd!("sh", "-c", "echo foo >&2").stderr_to_stdout().read().unwrap();
    /// assert_eq!("foo", error_output);
    /// # }
    /// # }
    /// ```
    pub fn stderr_to_stdout(&self) -> Expression {
        Self::new(Io(StderrToStdout, self.clone()))
    }

    /// Swap the stdout and stderr of an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("sh", "-c", "echo foo && echo bar >&2")
    ///     .stdout_stderr_swap()
    ///     .stdout_capture()
    ///     .stderr_capture()
    ///     .run()
    ///     .unwrap();
    /// assert_eq!(b"bar\n", &*output.stdout);
    /// assert_eq!(b"foo\n", &*output.stderr);
    /// # }
    /// # }
    /// ```
    pub fn stdout_stderr_swap(&self) -> Expression {
        Self::new(Io(StdoutStderrSwap, self.clone()))
    }

    /// Set the working directory where the expression will execute.
    ///
    /// Note that in some languages (Rust and Python at least), there are
    /// tricky platform differences in the way relative exe paths interact with
    /// child working directories. In particular, the exe path will be
    /// interpreted relative to the child dir on Unix, but relative to the
    /// parent dir on Windows. Duct prefers the Windows behavior, and in order
    /// to get that behavior on all platforms it calls
    /// [`std::fs::canonicalize`](https://doc.rust-lang.org/std/fs/fn.canonicalize.html)
    /// on relative exe paths when `dir` is in use. Paths in this sense are any
    /// program name containing a path separator, regardless of the type. (Note
    /// also that `Path` and `PathBuf` program names get a `./` prepended to
    /// them automatically by the
    /// [`IntoExecutablePath`](trait.IntoExecutablePath.html) trait, and so
    /// will always contain a separator.)
    ///
    /// # Errors
    ///
    /// Canonicalization can fail on some filesystems, or if the current
    /// directory has been removed, and
    /// [`run`](struct.Expression.html#method.run) will return those errors
    /// rather than trying any sneaky workarounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("pwd").dir("/").read().unwrap();
    /// assert_eq!("/", output);
    /// # }
    /// # }
    /// ```
    pub fn dir<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(Dir(path.into()), self.clone()))
    }

    /// Set a variable in the expression's environment.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("sh", "-c", "echo $FOO").env("FOO", "bar").read().unwrap();
    /// assert_eq!("bar", output);
    /// # }
    /// # }
    /// ```
    pub fn env<T, U>(&self, name: T, val: U) -> Expression
    where
        T: Into<OsString>,
        U: Into<OsString>,
    {
        Self::new(Io(Env(EnvNameString::from(name), val.into()), self.clone()))
    }

    /// Remove a variable from the expression's environment.
    ///
    /// Note that all the environment functions try to do whatever the platform
    /// does with respect to case sensitivity. That means that
    /// `env_remove("foo")` will unset the uppercase variable `FOO` on Windows,
    /// but not on Unix.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// std::env::set_var("TESTING", "true");
    /// let output = cmd!("sh", "-c", "echo a${TESTING}b")
    ///     .env_remove("TESTING")
    ///     .read()
    ///     .unwrap();
    /// assert_eq!("ab", output);
    /// # }
    /// # }
    /// ```
    pub fn env_remove<T>(&self, name: T) -> Expression
    where
        T: Into<OsString>,
    {
        Self::new(Io(EnvRemove(EnvNameString::from(name)), self.clone()))
    }

    /// Set the expression's entire environment, from a collection of
    /// name-value pairs (like a `HashMap`). Note that some environment
    /// variables are required for normal program execution (like `SystemRoot`
    /// on Windows), so copying the parent's environment is usually preferable
    /// to starting with an empty one.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::collections::HashMap;
    /// # if cfg!(not(windows)) {
    /// let mut env_map: HashMap<_, _> = std::env::vars().collect();
    /// env_map.insert("FOO".into(), "bar".into());
    /// let output = cmd!("sh", "-c", "echo $FOO").full_env(&env_map).read().unwrap();
    /// assert_eq!("bar", output);
    /// // The IntoIterator/Into<OsString> bounds are pretty flexible. Passing
    /// // by value works here too.
    /// let output = cmd!("sh", "-c", "echo $FOO").full_env(env_map).read().unwrap();
    /// assert_eq!("bar", output);
    /// # }
    /// # }
    /// ```
    pub fn full_env<T, U, V>(&self, name_vals: T) -> Expression
    where
        T: IntoIterator<Item = (U, V)>,
        U: Into<OsString>,
        V: Into<OsString>,
    {
        let env_map = name_vals
            .into_iter()
            .map(|(k, v)| (EnvNameString::from(k), v.into()))
            .collect();
        Self::new(Io(FullEnv(env_map), self.clone()))
    }

    /// Prevent a non-zero exit status from causing
    /// [`run`](struct.Expression.html#method.run) or
    /// [`read`](struct.Expression.html#method.read) to return an error. The
    /// unchecked exit code will still be there on the `Output` returned by
    /// `run`; its value doesn't change.
    ///
    /// "Uncheckedness" sticks to an exit code as it bubbles up through
    /// complicated pipelines, but it doesn't "infect" other exit codes. So for
    /// example, if only one sub-expression in a pipe has `unchecked`, then
    /// errors returned by the other side will still be checked. That said,
    /// most commonly you'll just call `unchecked` right before `run`, and
    /// it'll apply to an entire expression.
    ///
    /// # Example
    ///
    /// Note the differences among these three cases:
    ///
    /// ```no_run
    /// # use duct::cmd;
    /// # fn main() -> std::io::Result<()> {
    /// // Don't check errors on the left side.
    /// cmd!("foo").unchecked().pipe(cmd!("bar")).run()?;
    ///
    /// // Don't check errors on the right side.
    /// cmd!("foo").pipe(cmd!("bar").unchecked()).run()?;
    ///
    /// // Don't check errors on either side.
    /// cmd!("foo").pipe(cmd!("bar")).unchecked().run()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn unchecked(&self) -> Expression {
        Self::new(Io(Unchecked, self.clone()))
    }

    /// Add a hook for modifying
    /// [`std::process::Command`](https://doc.rust-lang.org/std/process/struct.Command.html)
    /// objects immediately before they're executed.
    ///
    /// The hook is called for each command in its sub-expression, and each time the expression is
    /// executed. The call happens after other features like `stdout` and `env` have been applied,
    /// so any changes made by the hook take priority. More than one hook can be added, in which
    /// case the innermost is executed last. For example, if one call to `before_spawn` is applied
    /// to an entire pipe expression, and another call is applied to just one command within the
    /// pipe, the hook for the entire pipeline will be called first over the command where both
    /// hooks apply.
    ///
    /// This is intended for rare and tricky cases, like callers who want to change the group ID of
    /// their child processes, or who want to run code in `before_exec`. Most callers shouldn't
    /// need to use it.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// let output = cmd!("echo", "foo")
    ///     .before_spawn(|cmd| {
    ///         // Sneakily add an extra argument.
    ///         cmd.arg("bar");
    ///         Ok(())
    ///     })
    ///     .read()
    ///     .unwrap();
    /// assert_eq!("foo bar", output);
    /// # }
    /// ```
    pub fn before_spawn<F>(&self, hook: F) -> Expression
    where
        F: Fn(&mut Command) -> io::Result<()> + Send + Sync + 'static,
    {
        Self::new(Io(BeforeSpawn(BeforeSpawnHook::new(hook)), self.clone()))
    }

    fn new(inner: ExpressionInner) -> Expression {
        Expression(Arc::new(inner))
    }
}

// Delegate to the ExpressionInner for debug formatting. This avoids printing
// redundant Expression() constructors around everything.
impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

// Implementing Into<Expression> for references lets us accept both references
// and values in `pipe`.
impl<'a> From<&'a Expression> for Expression {
    fn from(expr: &Expression) -> Expression {
        expr.clone()
    }
}

/// A handle to a running [`Expression`], returned by the
/// [`start`](struct.Expression.html#method.start) method.
///
/// Calling `start` followed by
/// [`into_output`](struct.Handle.html#method.into_output) on the handle is
/// equivalent to [`run`](struct.Expression.html#method.run). Note that unlike
/// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html),
/// most of the methods on `Handle` take `&self` rather than `&mut self`, and a
/// `Handle` may be shared between multiple threads.
///
/// If you drop a `Handle` without first [`wait`][Handle::wait]ing on the child to exit, it will
/// [`try_wait`][Handle::try_wait] internally to see if it can reap the child. If the child is
/// still running, its handle will be added to a global list and polled whenever new child
/// processes are spawned. This avoids leaking [zombie
/// processes](https://en.wikipedia.org/wiki/Zombie_process) on Unix platforms. This `Drop`
/// implementation is omitted on Windows, where zombies aren't a problem.
///
/// See the [`shared_child`](https://github.com/oconnor663/shared_child.rs)
/// crate for implementation details behind making handles thread safe.
#[derive(Debug)]
pub struct Handle {
    inner: HandleInner,
    result: OnceLock<(ExpressionStatus, Output)>,
    readers: RwLock<(Option<ReaderThread>, Option<ReaderThread>)>,
}

impl Handle {
    /// Wait for the running [`Expression`] to finish, and return a reference to its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html).
    /// Multiple threads may wait at the same time, and waiting more than once returns the same
    /// output again.
    ///
    /// # Errors
    ///
    /// In addition to all the IO errors possible with
    /// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html), `wait`
    /// will return an [`ErrorKind::Other`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html)
    /// IO error if the child returns a non-zero exit status. To suppress this error and return an
    /// `Output` even when the exit status is non-zero, use the
    /// [`unchecked`](struct.Expression.html#method.unchecked) method.
    pub fn wait(&self) -> io::Result<&Output> {
        wait_on_handle_and_output(self, WaitMode::Blocking)?;
        self.try_wait().transpose().expect("already exited")
    }

    /// Same as [`wait`][Self::wait], but with a timeout. If the running [`Expression`] finishes
    /// within the timeout (or if it's already finished), return a reference to its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html).
    /// Otherwise, return `Ok(None)`.
    ///
    /// # Errors
    ///
    /// Same as [`wait`][Self::wait].
    #[cfg(feature = "timeout")]
    pub fn wait_timeout(&self, timeout: std::time::Duration) -> io::Result<Option<&Output>> {
        let deadline = std::time::Instant::now() + timeout;
        self.wait_deadline(deadline)
    }

    /// Same as [`wait_timeout`][Self::wait_timeout], but with a deadline instead of a timeout.
    ///
    /// # Errors
    ///
    /// Same as [`wait`][Self::wait].
    #[cfg(feature = "timeout")]
    pub fn wait_deadline(&self, deadline: std::time::Instant) -> io::Result<Option<&Output>> {
        wait_on_handle_and_output(self, WaitMode::Deadline(deadline))?;
        self.try_wait()
    }

    /// Check whether the running [`Expression`] has already finished. If it has, return a
    /// reference to its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html).
    /// Otherwise, return `Ok(None)`.
    ///
    /// # Errors
    ///
    /// Same as [`wait`][Self::wait].
    pub fn try_wait(&self) -> io::Result<Option<&Output>> {
        let Some((expression_status, output)) =
            wait_on_handle_and_output(self, WaitMode::NonBlocking)?
        else {
            return Ok(None);
        };
        // If the child returned a "checked" non-zero exit status, make that an error.
        if expression_status.is_checked_error() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                expression_status.message(),
            ));
        }
        Ok(Some(output))
    }

    /// Same as [`wait`][Self::wait], but consume the `Handle` and return its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html) by
    /// value. Calling [`start`](struct.Expression.html#method.start) followed by `into_output` is
    /// equivalent to [`run`](struct.Expression.html#method.run).
    ///
    /// # Errors
    ///
    /// Same as [`wait`][Self::wait].
    pub fn into_output(self) -> io::Result<Output> {
        self.wait()?;
        let (_, output) = self.result.into_inner().expect("result missing");
        Ok(output)
    }

    /// Kill all the child processes in the running [`Expression`].
    ///
    /// Note that as with
    /// [`std::process::Child::kill`](https://doc.rust-lang.org/beta/std/process/struct.Child.html#method.kill),
    /// this does not kill any grandchild processes that the children have
    /// spawned on their own. It only kills the child processes that Duct
    /// spawned itself. See
    /// [`gotchas.md`](https://github.com/oconnor663/duct.py/blob/master/gotchas.md)
    /// for an extensive discussion of this behavior.
    ///
    /// This method does not wait on the child processes to exit. Calling [`wait`][Handle::wait]
    /// after `kill` usually returns quickly, but there are edge cases where it might not. The most
    /// common case is if a grandchild process has inherited one or more of the child's
    /// stdin/stdout/stderr pipes, and a worker thread related to
    /// [`stdin_bytes`][Expression::stdin_bytes]/[`stdout_capture][Expression::stdout_capture]/[`stderr_capture][Expression::stderr_capture]
    /// is still running. The kill signal might also be delayed if the child is blocked reading an
    /// unresponsive FUSE filesystem, or paused by a debugger.
    pub fn kill(&self) -> io::Result<()> {
        self.inner.kill()
    }

    /// Return a `Vec<u32>` containing the PIDs of all of the child processes.
    /// The PIDs are given in pipeline order, from left to right.
    pub fn pids(&self) -> Vec<u32> {
        self.inner.pids()
    }
}

// Wait on the handle and on captured output. Depending on the mode, this wait might or might not
// be blocking. This does not do any status checking.
fn wait_on_handle_and_output(
    handle: &Handle,
    mode: WaitMode,
) -> io::Result<Option<&(ExpressionStatus, Output)>> {
    let Some(status) = handle.inner.wait(mode)? else {
        return Ok(None);
    };
    // We need non-blocking waiters (try_wait) to be able to access the SharedThread IO readers,
    // even while a blocking waiter (wait) is blocking, so we can't take RwLock::write until we
    // know the threads have already exited.
    let shared_lock = handle.readers.read().unwrap();
    let (maybe_stdout_reader, maybe_stderr_reader) = &*shared_lock;
    if let Some(stdout_reader) = maybe_stdout_reader {
        if mode.maybe_join_io_thread(stdout_reader)?.is_none() {
            return Ok(None);
        }
    }
    if let Some(stderr_reader) = maybe_stderr_reader {
        if mode.maybe_join_io_thread(stderr_reader)?.is_none() {
            return Ok(None);
        }
    }
    drop(shared_lock);

    // At this point we know that the child and all its IO threads (if any) have exited, so we can
    // collect output without blocking. Take the RwLock::write lock and take ownership of the
    // output vectors. If another thread has already done this, .unwrap_or_default() will return
    // empty Vecs, and result.set() will be a no-op.
    let mut unique_lock = handle.readers.write().unwrap();
    let (maybe_stdout_reader, maybe_stderr_reader) = &mut *unique_lock;
    let stdout: Vec<u8> = maybe_stdout_reader
        .take()
        .map(SharedThread::into_output)
        .transpose()
        .expect("IO errors already short-circuited")
        .unwrap_or_default();
    let stderr: Vec<u8> = maybe_stderr_reader
        .take()
        .map(SharedThread::into_output)
        .transpose()
        .expect("IO errors already short-circuited")
        .unwrap_or_default();
    let output = Output {
        status: status.status,
        stdout,
        stderr,
    };
    let _ = handle.result.set((status, output)); // might already be set
    Ok(handle.result.get())
}

#[derive(Debug)]
enum ExpressionInner {
    Cmd(Vec<OsString>),
    Pipe(Expression, Expression),
    Io(IoExpressionInner, Expression),
}

impl ExpressionInner {
    fn start(&self, context: IoContext) -> io::Result<HandleInner> {
        Ok(match self {
            Cmd(argv) => HandleInner::Child(ChildHandle::start(argv, context)?),
            Pipe(left, right) => {
                HandleInner::Pipe(Box::new(PipeHandle::start(left, right, context)?))
            }
            Io(io_inner, expr) => start_io(io_inner, expr, context)?,
        })
    }
}

#[derive(Debug)]
enum HandleInner {
    Child(ChildHandle),
    // If the left side of a pipe fails to start, there's nothing to wait for,
    // and we return an error immediately. But if the right side fails to start,
    // the caller still needs to wait on the left, and we must return a handle.
    // Thus the handle preserves the right side's errors here.
    Pipe(Box<PipeHandle>),
    StdinBytes(Box<StdinBytesHandle>),
    // Why does "uncheckedness" need to be a handle type and not just a field on
    // IoContext? Because when one side of a pipe is checked, that side's errors
    // take priority over the checked side, even when the pipe expression
    // *itself* is also unchecked.
    Unchecked(Box<HandleInner>),
}

impl HandleInner {
    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        match self {
            HandleInner::Child(child_handle) => child_handle.wait(mode),
            HandleInner::Pipe(pipe_handle) => pipe_handle.wait(mode),
            HandleInner::StdinBytes(stdin_bytes_handle) => stdin_bytes_handle.wait(mode),
            HandleInner::Unchecked(inner_handle) => {
                Ok(inner_handle.wait(mode)?.map(|mut status| {
                    status.checked = false;
                    status
                }))
            }
        }
    }

    fn kill(&self) -> io::Result<()> {
        match self {
            HandleInner::Child(child_handle) => child_handle.kill(),
            HandleInner::Pipe(pipe_handle) => pipe_handle.kill(),
            HandleInner::StdinBytes(stdin_bytes_handle) => stdin_bytes_handle.kill(),
            HandleInner::Unchecked(inner_handle) => inner_handle.kill(),
        }
    }

    fn pids(&self) -> Vec<u32> {
        match self {
            HandleInner::Child(child_handle) => vec![child_handle.child().id()],
            HandleInner::Pipe(pipe_handle) => pipe_handle.pids(),
            HandleInner::StdinBytes(stdin_bytes_handle) => stdin_bytes_handle.inner_handle.pids(),
            HandleInner::Unchecked(inner_handle) => inner_handle.pids(),
        }
    }
}

// Use std::process::Child instead of SharedChild to avoid taking extra locks when we poll.
#[cfg(not(windows))]
static LEAKED_CHILDREN: RwLock<Vec<std::process::Child>> = RwLock::new(Vec::new());

// In `impl Drop for ChildHandle` below, children who are still running when they're dropped get
// added to this global list. Poll the list to reap as many zombie children as possible each time
// we spawn a new child process. See the comments in the Drop impl regarding tradeoffs.
#[cfg(not(windows))]
fn cleanup_leaked_children() {
    if !LEAKED_CHILDREN.read().unwrap().is_empty() {
        LEAKED_CHILDREN.write().unwrap().retain_mut(|child| {
            match child.try_wait() {
                Ok(Some(_)) => false, // remove
                Ok(None) => true,     // retain
                Err(e) => {
                    // try_wait errors require odd circumstances to trigger. For example, something
                    // else might call libc::waitpid (or its safe wrapper from `nix`) and reap the
                    // child, causing us to get a "process not found" error here. If that happens
                    // in a test, go ahead and panic, but otherwise ignore the error. The most
                    // important thing is that we don't leave the whole process in a broken state
                    // where every future call to ChildHandle::start returns an error. Also, it
                    // might not be helpful or appropriate to report this error to our caller.
                    // Remember that this is lazy, global cleanup of some state that might belong
                    // to some other thread, running code from some other crate. Let it go...
                    if cfg!(test) {
                        panic!("cleanup_leaked_children failed: {e}");
                    }
                    false // remove
                }
            }
        });
    }
}

#[derive(Debug)]
struct ChildHandle {
    child: Option<shared_child::SharedChild>, // optional so that `drop` can take ownership
    command_string: String,
}

impl ChildHandle {
    fn start(argv: &[OsString], context: IoContext) -> io::Result<ChildHandle> {
        // See comments in the Drop impl below.
        #[cfg(not(windows))]
        cleanup_leaked_children();

        let exe = canonicalize_exe_path_for_dir(&argv[0], &context)?;
        let mut command = Command::new(exe);
        command.args(&argv[1..]);
        if !matches!(context.stdin, IoValue::ParentStdin) {
            command.stdin(context.stdin.into_stdio()?);
        }
        if !matches!(context.stdout, IoValue::ParentStdout) {
            command.stdout(context.stdout.into_stdio()?);
        }
        if !matches!(context.stderr, IoValue::ParentStderr) {
            command.stderr(context.stderr.into_stdio()?);
        }
        if let Some(dir) = context.dir {
            command.current_dir(dir);
        }
        command.env_clear();
        for (name, val) in context.env {
            command.env(name, val);
        }
        // The innermost hooks are pushed last, and we execute them last.
        for hook in context.before_spawn_hooks.iter() {
            hook.call(&mut command)?;
        }

        // See comments below about why we take this lock (macOS only).
        let spawn_guard = pipe_and_spawn_lock_guard();
        let shared_child = SharedChild::spawn(&mut command)?;
        drop(spawn_guard);

        let command_string = format!("{:?}", argv);
        Ok(ChildHandle {
            child: Some(shared_child),
            command_string,
        })
    }

    // a helper to reduce the need for .as_ref().unwrap() everywhere
    fn child(&self) -> &SharedChild {
        self.child
            .as_ref()
            .expect("ChildHandle should not yet have been dropped")
    }

    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        let maybe_status = mode.maybe_wait_on_child(self.child())?;
        if let Some(status) = maybe_status {
            Ok(Some(ExpressionStatus {
                status,
                checked: true,
                command: self.command_string.clone(),
            }))
        } else {
            Ok(None)
        }
    }

    fn kill(&self) -> io::Result<()> {
        self.child().kill()
    }
}

// Use Drop to prevent zombie processes on Unix. Zombies aren't a thing on Windows, so omit the
// entire impl there.
#[cfg(not(windows))]
impl Drop for ChildHandle {
    fn drop(&mut self) {
        let child = self.child.take().expect("only drop should take the child");
        match child.try_wait() {
            // The child has been cleaned up. Cool.
            Ok(Some(_)) => (),

            // Ignore IO errors here unless we're running tests. It's hard to provoke these without
            // doing something very weird (transmute, libc::waitpid, etc).
            Err(e) => {
                if cfg!(test) {
                    panic!("ChildHandle cleanup failed: {e}");
                }
            }

            // This child is still running, but the caller is never going to wait on it. Add it to
            // a global list of (potentially) zombie children. We poll this list whenever we spawn
            // new child processes, to mitigate leaks. This is the same strategy used in the
            // CPython `subprocess` module:
            //   - https://github.com/python/cpython/blob/v3.13.3/Lib/subprocess.py#L1133-L1146
            //   - https://github.com/python/cpython/blob/v3.13.3/Lib/subprocess.py#L268-L285
            // The main downside of this strategy is that spawning N child processes becomes O(N^2)
            // if you leak all of them and they're all long-lived. I think that's an ok tradeoff
            // for a couple of reasons:
            //   1. Dropping un-waited-for child handles isn't usually what you want to be doing in
            //      your happy path, because it means you can't hear about error codes your
            //      children return. Children whose handles are retained don't enter this list and
            //      don't contribute to O(N^2) behavior.
            //   2. Callers who do "very advanced" things (say, a systemd clone) probably shouldn't
            //      be using Duct. They need more fine-grained control than Duct is designed to
            //      provide.
            Ok(None) => LEAKED_CHILDREN.write().unwrap().push(child.into_inner()),
        }
    }
}

#[derive(Debug)]
struct PipeHandle {
    left_handle: HandleInner,
    right_handle: HandleInner,
}

impl PipeHandle {
    fn start(left: &Expression, right: &Expression, context: IoContext) -> io::Result<PipeHandle> {
        let (reader, writer) = open_pipe_protected()?;
        // dup'ing stdin/stdout isn't strictly necessary, but no big deal
        let mut left_context = context.try_clone()?;
        left_context.stdout = IoValue::Handle(writer.into());
        let mut right_context = context;
        right_context.stdin = IoValue::Handle(reader.into());
        let left_handle = left.0.start(left_context)?;
        // The left side has already started. If we fail to start the right
        // side, ChildHandle::drop will clean it up one way or another. Note
        // that `right_context` is passed by value here, so if start() returns
        // an error, all pipe readers will already have been closed, and
        // there's a decent chance the left side will exit quickly via EPIPE
        // before we .try_wait() it in ChildHandle::drop.
        let right_handle = right.0.start(right_context)?;
        Ok(PipeHandle {
            left_handle,
            right_handle,
        })
    }

    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        // Wait on both sides first, without propagating any errors.
        let left_wait_result = self.left_handle.wait(mode);
        let right_wait_result = self.right_handle.wait(mode);

        // Now we deal with errors from either of those waits. The left wait
        // happened first, so that one takes precedence. Note that this is the
        // reverse order of exit status precedence.
        let left_status = left_wait_result?;
        let right_status = right_wait_result?;

        // If both waits succeeded, return one of the two statuses.
        Ok(pipe_status_precedence(left_status, right_status))
    }

    // As with wait, we need to call kill on both sides even if the left side
    // returns an error.
    fn kill(&self) -> io::Result<()> {
        let left_kill_result = self.left_handle.kill();
        let right_kill_result = self.right_handle.kill();
        // As with wait, the left side happened first, so its errors take
        // precedence.
        left_kill_result.and(right_kill_result)
    }

    fn pids(&self) -> Vec<u32> {
        let mut pids = self.left_handle.pids();
        pids.extend_from_slice(&self.right_handle.pids());
        pids
    }
}

// The rules of precedence are:
// 1) If either side unfinished, the result is unfinished.
// 2) Checked errors trump unchecked errors.
// 3) Any errors trump success.
// 4) All else equal, the right side wins (as in Bash).
fn pipe_status_precedence(
    left_maybe_status: Option<ExpressionStatus>,
    right_maybe_status: Option<ExpressionStatus>,
) -> Option<ExpressionStatus> {
    let (left_status, right_status) = match (left_maybe_status, right_maybe_status) {
        (Some(left), Some(right)) => (left, right),
        _ => return None,
    };
    Some(if right_status.is_checked_error() {
        right_status
    } else if left_status.is_checked_error() {
        left_status
    } else if !right_status.status.success() {
        right_status
    } else {
        left_status
    })
}

fn start_io(
    io_inner: &IoExpressionInner,
    expr_inner: &Expression,
    mut context: IoContext,
) -> io::Result<HandleInner> {
    match io_inner {
        StdinBytes(v) => {
            return Ok(HandleInner::StdinBytes(Box::new(StdinBytesHandle::start(
                expr_inner,
                context,
                Arc::clone(v),
            )?)));
        }
        StdinPath(p) => {
            context.stdin = IoValue::Handle(File::open(p)?.into());
        }
        StdinFile(f) => {
            context.stdin = IoValue::Handle(f.try_clone()?);
        }
        StdinNull => {
            context.stdin = IoValue::Null;
        }
        StdoutPath(p) => {
            context.stdout = IoValue::Handle(File::create(p)?.into());
        }
        StdoutFile(f) => {
            context.stdout = IoValue::Handle(f.try_clone()?);
        }
        StdoutNull => {
            context.stdout = IoValue::Null;
        }
        StdoutCapture => {
            context.stdout = IoValue::Handle(context.stdout_capture.write_pipe()?.into());
        }
        StdoutToStderr => {
            context.stdout = context.stderr.try_clone()?;
        }
        StderrPath(p) => {
            context.stderr = IoValue::Handle(File::create(p)?.into());
        }
        StderrFile(f) => {
            context.stderr = IoValue::Handle(f.try_clone()?);
        }
        StderrNull => {
            context.stderr = IoValue::Null;
        }
        StderrCapture => {
            context.stderr = IoValue::Handle(context.stderr_capture.write_pipe()?.into());
        }
        StderrToStdout => {
            context.stderr = context.stdout.try_clone()?;
        }
        StdoutStderrSwap => {
            mem::swap(&mut context.stdout, &mut context.stderr);
        }
        Dir(p) => {
            context.dir = Some(p.clone());
        }
        Env(name, val) => {
            // Note that HashMap::insert overwrites a preexisting *value*, but not a preexisting
            // *key*. We rely on this to match platform behavior on Windows, where the original
            // casing of a variable name is preserved even if an equivalent name with a different
            // casing is added.
            context.env.insert(name.clone(), val.clone());
        }
        EnvRemove(name) => {
            context.env.remove(name);
        }
        FullEnv(map) => {
            context.env = map.clone();
        }
        Unchecked => {
            let inner_handle = expr_inner.0.start(context)?;
            return Ok(HandleInner::Unchecked(Box::new(inner_handle)));
        }
        BeforeSpawn(hook) => {
            context.before_spawn_hooks.push(hook.clone());
        }
    }
    expr_inner.0.start(context)
}

#[derive(Debug)]
struct StdinBytesHandle {
    inner_handle: HandleInner,
    writer_thread: SharedThread<io::Result<()>>,
}

impl StdinBytesHandle {
    fn start(
        expression: &Expression,
        mut context: IoContext,
        input: Arc<Vec<u8>>,
    ) -> io::Result<StdinBytesHandle> {
        let (reader, mut writer) = open_pipe_protected()?;
        context.stdin = IoValue::Handle(reader.into());
        let inner_handle = expression.0.start(context)?;
        let writer_thread = SharedThread::spawn(move || {
            // Broken pipe errors are expected here. Suppress them.
            match writer.write_all(&input) {
                Err(e) if e.kind() != io::ErrorKind::BrokenPipe => Err(e),
                _ => Ok(()),
            }
        });
        Ok(StdinBytesHandle {
            inner_handle,
            writer_thread,
        })
    }

    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        let maybe_status = self.inner_handle.wait(mode)?;
        // Even if the child has exited, some grandchild process might keep this pipe open and keep
        // reading from it. It's tempting not to wait for this IO thread at all and just let it run
        // in the background, but that wouldn't work if the current process exited. (When the main
        // function returns and the process exits, all background threads are terminated.) Waiting
        // on this Handle might be the last thing the caller does in main, who knows, so for
        // correctness a blocking waiter does need to wait until this IO thread is finished.
        let io_finished = mode.maybe_join_io_thread(&self.writer_thread)?.is_some();
        if !io_finished {
            return Ok(None);
        }
        Ok(maybe_status)
    }

    fn kill(&self) -> io::Result<()> {
        self.inner_handle.kill()
    }
}

#[derive(Debug)]
enum IoExpressionInner {
    StdinBytes(Arc<Vec<u8>>),
    StdinPath(PathBuf),
    StdinFile(FdOrHandle),
    StdinNull,
    StdoutPath(PathBuf),
    StdoutFile(FdOrHandle),
    StdoutNull,
    StdoutCapture,
    StdoutToStderr,
    StderrPath(PathBuf),
    StderrFile(FdOrHandle),
    StderrNull,
    StderrCapture,
    StderrToStdout,
    StdoutStderrSwap,
    Dir(PathBuf),
    Env(EnvNameString, OsString),
    EnvRemove(EnvNameString),
    FullEnv(HashMap<EnvNameString, OsString>),
    Unchecked,
    BeforeSpawn(BeforeSpawnHook),
}

type HookFn = Arc<dyn Fn(&mut Command) -> io::Result<()> + Send + Sync>;

#[derive(Clone)]
struct BeforeSpawnHook {
    inner: HookFn,
}

impl BeforeSpawnHook {
    fn new<F>(hook: F) -> Self
    where
        F: Fn(&mut Command) -> io::Result<()> + Send + Sync + 'static,
    {
        Self {
            inner: Arc::new(hook),
        }
    }

    fn call(&self, command: &mut Command) -> io::Result<()> {
        (self.inner)(command)
    }
}

impl fmt::Debug for BeforeSpawnHook {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<closure>")
    }
}

// An IoContext represents the file descriptors child processes are talking to at execution time.
// It's initialized in run(), with dups of the stdin/stdout/stderr pipes, and then passed down to
// sub-expressions. Compound expressions will clone() it, and redirections will modify it.
#[derive(Debug)]
struct IoContext<'a> {
    stdin: IoValue,
    stdout: IoValue,
    stderr: IoValue,
    stdout_capture: &'a OutputCaptureContext,
    stderr_capture: &'a OutputCaptureContext,
    dir: Option<PathBuf>,
    env: HashMap<EnvNameString, OsString>,
    before_spawn_hooks: Vec<BeforeSpawnHook>,
}

impl<'a> IoContext<'a> {
    // Returns (context, stdout_reader, stderr_reader).
    fn new(
        stdout_capture: &'a OutputCaptureContext,
        stderr_capture: &'a OutputCaptureContext,
    ) -> Self {
        Self {
            stdin: IoValue::ParentStdin,
            stdout: IoValue::ParentStdout,
            stderr: IoValue::ParentStderr,
            stdout_capture,
            stderr_capture,
            dir: None,
            env: std::env::vars_os().map(|(k, v)| (k.into(), v)).collect(),
            before_spawn_hooks: Vec::new(),
        }
    }

    fn try_clone(&self) -> io::Result<IoContext<'a>> {
        Ok(IoContext {
            stdin: self.stdin.try_clone()?,
            stdout: self.stdout.try_clone()?,
            stderr: self.stderr.try_clone()?,
            stdout_capture: self.stdout_capture,
            stderr_capture: self.stderr_capture,
            dir: self.dir.clone(),
            env: self.env.clone(),
            before_spawn_hooks: self.before_spawn_hooks.clone(),
        })
    }
}

#[derive(Debug)]
enum IoValue {
    ParentStdin,
    ParentStdout,
    ParentStderr,
    Null,
    Handle(FdOrHandle),
}

impl IoValue {
    fn try_clone(&self) -> io::Result<IoValue> {
        Ok(match self {
            IoValue::ParentStdin => IoValue::ParentStdin,
            IoValue::ParentStdout => IoValue::ParentStdout,
            IoValue::ParentStderr => IoValue::ParentStderr,
            IoValue::Null => IoValue::Null,
            IoValue::Handle(f) => IoValue::Handle(f.try_clone()?),
        })
    }

    fn into_stdio(self) -> io::Result<Stdio> {
        Ok(match self {
            IoValue::ParentStdin => os_pipe::dup_stdin()?.into(),
            IoValue::ParentStdout => os_pipe::dup_stdout()?.into(),
            IoValue::ParentStderr => os_pipe::dup_stderr()?.into(),
            IoValue::Null => Stdio::null(),
            IoValue::Handle(f) => f.into(),
        })
    }
}

// This struct keeps track of a child exit status, whether or not it's been
// unchecked(), and what the command was that gave it (for error messages).
#[derive(Clone, Debug)]
struct ExpressionStatus {
    status: ExitStatus,
    checked: bool,
    command: String,
}

impl ExpressionStatus {
    fn is_checked_error(&self) -> bool {
        self.checked && !self.status.success()
    }

    fn message(&self) -> String {
        format!(
            "command {} exited with code {}",
            self.command,
            self.exit_code_string()
        )
    }

    #[cfg(not(windows))]
    fn exit_code_string(&self) -> String {
        if self.status.code().is_none() {
            return format!("<signal {}>", self.status.signal().unwrap());
        }
        self.status.code().unwrap().to_string()
    }

    #[cfg(windows)]
    fn exit_code_string(&self) -> String {
        self.status.code().unwrap().to_string()
    }
}

fn canonicalize_exe_path_for_dir(exe_name: &OsStr, context: &IoContext) -> io::Result<OsString> {
    // There's a tricky interaction between exe paths and `dir`. Exe paths can
    // be relative, and so we have to ask: Is an exe path interpreted relative
    // to the parent's cwd, or the child's? The answer is that it's platform
    // dependent! >.< (Windows uses the parent's cwd, but because of the
    // fork-chdir-exec pattern, Unix usually uses the child's.)
    //
    // We want to use the parent's cwd consistently, because that saves the
    // caller from having to worry about whether `dir` will have side effects,
    // and because it's easy for the caller to use Path::join if they want to.
    // That means that when `dir` is in use, we need to detect exe names that
    // are relative paths, and absolutify them. We want to do that as little as
    // possible though, both because canonicalization can fail, and because we
    // prefer to let the caller control the child's argv[0].
    //
    // We never want to absolutify a name like "emacs", because that's probably
    // a program in the PATH rather than a local file. So we look for slashes
    // in the name to determine what's a filepath and what isn't. Note that
    // anything given as a std::path::Path will always have a slash by the time
    // we get here, because we specialize the IntoExecutablePath trait to
    // prepend a ./ to them when they're relative. This leaves the case where
    // Windows users might pass a local file like "foo.bat" as a string, which
    // we can't distinguish from a global program name. However, because the
    // Windows has the preferred "relative to parent's cwd" behavior already,
    // this case actually works without our help. (Windows users previously
    // needed to watch out for local files shadowing global program names, but
    // Rust 1.58 improved this.)

    let has_separator = exe_name
        .to_string_lossy()
        .chars()
        .any(std::path::is_separator);
    let is_relative = Path::new(exe_name).is_relative();
    if context.dir.is_some() && has_separator && is_relative {
        Path::new(exe_name).canonicalize().map(Into::into)
    } else {
        Ok(exe_name.to_owned())
    }
}

// We want to allow Path("foo") to refer to the local file "./foo" on
// Unix, and we want to *prevent* Path("echo") from referring to the
// global "echo" command on either Unix or Windows. Prepend a dot to all
// relative paths to accomplish both of those.
fn dotify_relative_exe_path(path: &Path) -> PathBuf {
    // This is a no-op if path is absolute or begins with a Windows prefix.
    Path::new(".").join(path)
}

/// An implementation detail of [`cmd`](fn.cmd.html), to distinguish paths from
/// other string types.
///
/// `Path("foo.sh")` means the file named `foo.sh` in the current directory.
/// However if you try to execute that path with
/// [`std::process::Command`](https://doc.rust-lang.org/std/process/struct.Command.html),
/// Unix will get upset that it doesn't have a leading `./`. Rust knows that the
/// string is a path, but that distinction gets lost by the time execution
/// happens.
///
/// To execute relative paths correctly, duct prepends the `./` to them
/// automatically. This trait captures the distinction between the path types
/// and other types of strings, which don't get modified. See the trait bounds
/// on [`cmd`](fn.cmd.html).
pub trait IntoExecutablePath {
    fn to_executable(self) -> OsString;
}

// TODO: Get rid of most of these impls once specialization lands.

impl<'a> IntoExecutablePath for &'a Path {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(self).into()
    }
}

impl IntoExecutablePath for PathBuf {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(&self).into()
    }
}

impl<'a> IntoExecutablePath for &'a PathBuf {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(self).into()
    }
}

impl<'a> IntoExecutablePath for &'a str {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl IntoExecutablePath for String {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl<'a> IntoExecutablePath for &'a String {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl<'a> IntoExecutablePath for &'a OsStr {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl IntoExecutablePath for OsString {
    fn to_executable(self) -> OsString {
        self
    }
}

impl<'a> IntoExecutablePath for &'a OsString {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

// io::Error doesn't implement clone directly, so we kind of hack it together.
fn clone_io_error(error: &io::Error) -> io::Error {
    if let Some(code) = error.raw_os_error() {
        io::Error::from_raw_os_error(code)
    } else {
        io::Error::new(error.kind(), error.to_string())
    }
}

#[derive(Clone, Copy, Debug)]
enum WaitMode {
    // block until everything is finished, as in .wait()
    Blocking,
    // don't block at all, as in .try_wait()
    NonBlocking,
    // block with a deadline, as in .wait_deadline() or .wait_timeout()
    #[cfg(feature = "timeout")]
    Deadline(std::time::Instant),
}

impl WaitMode {
    fn maybe_wait_on_child(self, child: &SharedChild) -> io::Result<Option<ExitStatus>> {
        match self {
            WaitMode::Blocking => child.wait().map(Some),
            WaitMode::NonBlocking => child.try_wait(),
            #[cfg(feature = "timeout")]
            WaitMode::Deadline(deadline) => child.wait_deadline(deadline),
        }
    }

    /// Returns Ok(true) if IO finished successfully, Ok(false) if IO is not yet finished (and the
    /// mode is not Blocking), or Err(e) if IO failed with an error.
    fn maybe_join_io_thread<T>(
        self,
        io_thread: &SharedThread<io::Result<T>>,
    ) -> io::Result<Option<&T>> {
        match self {
            WaitMode::Blocking => match io_thread.join() {
                Ok(val) => Ok(Some(val)),
                Err(e) => Err(clone_io_error(e)),
            },
            WaitMode::NonBlocking => match io_thread.try_join() {
                Some(Ok(val)) => Ok(Some(val)),
                Some(Err(e)) => Err(clone_io_error(e)),
                None => Ok(None),
            },
            #[cfg(feature = "timeout")]
            WaitMode::Deadline(deadline) => match io_thread.join_deadline(deadline) {
                Some(Ok(val)) => Ok(Some(val)),
                Some(Err(e)) => Err(clone_io_error(e)),
                None => Ok(None),
            },
        }
    }
}

type ReaderThread = SharedThread<io::Result<Vec<u8>>>;

#[derive(Debug)]
struct OutputCaptureContext {
    pair: OnceLock<(os_pipe::PipeReader, os_pipe::PipeWriter)>,
}

impl OutputCaptureContext {
    fn new() -> Self {
        Self {
            pair: OnceLock::new(),
        }
    }

    fn write_pipe(&self) -> io::Result<os_pipe::PipeWriter> {
        // OnceLock::get_or_try_init would be nice if it stabilizes.
        match self.pair.get() {
            Some((_, writer)) => writer.try_clone(),
            None => {
                let (reader, writer) = open_pipe_protected()?;
                let clone = writer.try_clone();
                self.pair.set((reader, writer)).unwrap();
                clone
            }
        }
    }

    // Only spawn a read thread if the write pipe was used.
    fn maybe_read_thread(self) -> Option<ReaderThread> {
        if let Some((mut reader, _)) = self.pair.into_inner() {
            Some(SharedThread::spawn(move || {
                let mut output = Vec::new();
                reader.read_to_end(&mut output)?;
                Ok(output)
            }))
        } else {
            None
        }
    }
}

/// An incremental reader created with the
/// [`Expression::reader`](struct.Expression.html#method.reader) method.
///
/// When this reader reaches EOF, it automatically calls
/// [`wait`](struct.Handle.html#method.wait) on the inner handle. If the child
/// returns a non-zero exit status, the read at EOF will return an error,
/// unless you use [`unchecked`](struct.Expression.html#method.unchecked).
///
/// Both `ReaderHandle` and `&ReaderHandle` implement
/// [`std::io::Read`](https://doc.rust-lang.org/std/io/trait.Read.html). The
/// latter makes it possible for one thread to
/// [`kill`](struct.ReaderHandle.html#method.kill) the `ReaderHandle` while
/// another thread is reading it. That can be useful for effectively canceling
/// the read and unblocking the reader thread. However, note that killed child
/// processes return a non-zero exit status, which is an error for the reader
/// by default, unless you use
/// [`unchecked`](struct.Expression.html#method.unchecked).
///
/// `ReaderHandle` contains a [`Handle`] internally, and it takes the same
/// approach to cleaning up zombie processess on Unix.
///
/// # Example
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// # if cfg!(not(windows)) {
/// use duct::cmd;
/// use duct::ReaderHandle;
/// use std::sync::Arc;
/// use std::io::prelude::*;
///
/// // This child process prints a single byte and then sleeps.
/// //
/// // CAUTION: Using Bash for this example would probably hang, because Bash
/// // would spawn a `sleep` grandchild processes, and that grandchild wouldn't
/// // receive the kill signal.
/// let python_child = "\
/// import sys
/// import time
/// print()
/// sys.stdout.flush()
/// time.sleep(24 * 60 * 60)
/// ";
/// let reader: ReaderHandle = cmd!("python3", "-c", python_child)
///     .unchecked()
///     .reader()?;
///
/// // Spawn two threads that both try to read the single byte. Whichever one
/// // succeeds then calls kill() to unblock the other.
/// let arc_reader: Arc<ReaderHandle> = Arc::new(reader);
/// let mut threads = Vec::new();
/// for _ in 0..2 {
///     let arc_reader = arc_reader.clone();
///     threads.push(std::thread::spawn(move || -> std::io::Result<()> {
///         let mut single_byte = [0u8];
///         (&*arc_reader).read(&mut single_byte)?;
///         arc_reader.kill()?;
///         Ok(())
///     }));
/// }
///
/// // Join both threads. Because of the kill() above, both threads will exit
/// // quickly.
/// for thread in threads {
///     thread.join().unwrap()?;
/// }
/// # }
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct ReaderHandle {
    handle: Handle,
    reader: os_pipe::PipeReader,
}

impl ReaderHandle {
    /// Check whether the underlying expression is finished. This is equivalent
    /// to [`Handle::try_wait`](struct.Handle.html#method.try_wait). If the
    /// `ReaderHandle` has indicated EOF successfully, then it's guaranteed
    /// that this method will return `Ok(Some(_))`.
    ///
    /// Note that the
    /// [`stdout`](https://doc.rust-lang.org/std/process/struct.Output.html#structfield.stdout)
    /// field of the returned
    /// [`Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// will always be empty, because the `ReaderHandle` itself owns the
    /// child's stdout pipe.
    pub fn try_wait(&self) -> io::Result<Option<&Output>> {
        self.handle.try_wait()
    }

    /// Kill all the child processes in the running expression.
    ///
    /// See [`Handle::kill`]. Note that as with
    /// [`std::process::Child::kill`](https://doc.rust-lang.org/beta/std/process/struct.Child.html#method.kill),
    /// this does not kill any grandchild processes that the children have
    /// spawned on their own. It only kills the child processes that Duct
    /// spawned itself. This is **especially relevant** for `ReaderHandle`,
    /// because if you're using `kill` to unblock another thread that's
    /// reading, an unkilled grandchild process might keep the child's stdout
    /// pipe open and keep your reader thread blocked. For that use case, you
    /// need to ensure that any grandchild processes your child might spawn are
    /// going to be short-lived. See
    /// [`gotchas.md`](https://github.com/oconnor663/duct.py/blob/master/gotchas.md)
    /// for an extensive discussion of these issues.
    pub fn kill(&self) -> io::Result<()> {
        self.handle.kill()
    }

    /// Return a `Vec<u32>` containing the PIDs of all of the child processes.
    /// The PIDs are given in pipeline order, from left to right.
    pub fn pids(&self) -> Vec<u32> {
        self.handle.pids()
    }
}

impl<'a> Read for &'a ReaderHandle {
    /// Note that if you don't use
    /// [`unchecked`](struct.Expression.html#method.unchecked), and the child
    /// returns a non-zero exit status, the final call to `read` will return an
    /// error, just as [`run`](struct.Expression.html#method.run) would.
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = (&self.reader).read(buf)?;
        if n == 0 && !buf.is_empty() {
            // EOF detected. Wait on the child to clean it up before returning.
            self.handle.wait()?;
        }
        Ok(n)
    }
}

impl Read for ReaderHandle {
    /// Note that if you don't use
    /// [`unchecked`](struct.Expression.html#method.unchecked), and the child
    /// returns a non-zero exit status, the final call to `read` will return an
    /// error, just as [`run`](struct.Expression.html#method.run) would.
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        (&*self).read(buf)
    }
}

#[cfg(not(windows))]
type FdOrHandle = OwnedFd;
#[cfg(windows)]
type FdOrHandle = OwnedHandle;

// Without these conversions this crate could be 100% safe code, so this is kind of a shame, but I
// don't want to change the trait bounds on stdin_file/stdout_file/stderr_file. There are types
// that implement IntoRawFd but not Into<OwnedFd>, including RawFd itself.
#[cfg(not(windows))]
fn owned_from_raw(raw: impl IntoRawFd) -> OwnedFd {
    unsafe { OwnedFd::from_raw_fd(raw.into_raw_fd()) }
}
#[cfg(windows)]
fn owned_from_raw(raw: impl IntoRawHandle) -> OwnedHandle {
    unsafe { OwnedHandle::from_raw_handle(raw.into_raw_handle()) }
}

fn open_pipe_protected() -> io::Result<(os_pipe::PipeReader, os_pipe::PipeWriter)> {
    let _guard = pipe_and_spawn_lock_guard(); // See comments below.
    os_pipe::pipe()
}

#[allow(unreachable_code)]
fn pipe_and_spawn_lock_guard() -> Option<MutexGuard<'static, ()>> {
    // macOS and some other Unixes are missing the pipe2() syscall, which means that opening pipes
    // can't atomically set CLOEXEC. That creates a race condition between pipe opening threads and
    // child spawning threads, where children can unintentionally inherit extra pipes, possibly
    // leading to deadlocks. Use a global lock to prevent this race within Duct itself.
    // Unfortunately, callers who open their own pipes with e.g. std::io::pipe(), and who can't
    // guarantee that other (macOS) threads aren't spawning child processes at the same time, need
    // to create their own global lock.
    //
    // Ideally we'd keep this list of targets in sync with the `os_pipe` create, which also should
    // try to stay in sync with `std::io::pipe()`. In practice I haven't set up any automation for
    // that, so if you're reading this in 10+ years it might be stale :)
    #[cfg(any(target_os = "aix", target_vendor = "apple", target_os = "haiku"))]
    {
        use std::sync::Mutex;
        static PIPE_OPENING_LOCK: Mutex<()> = Mutex::new(());
        return Some(PIPE_OPENING_LOCK.lock().unwrap());
    }
    // On Windows, Linux, and most other Unixes, this lock isn't needed.
    None
}

#[cfg(test)]
mod test;
