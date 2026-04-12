//! An interface to github actions workflow commands.

use std::{
    fmt::{Debug, Write},
    num::NonZeroUsize,
};

/// Shows an error message directly in a github diff view on drop.
pub struct Error {
    file: String,
    line: usize,
    title: String,
    message: String,
}
impl Error {
    /// Set a line for this error. By default the message is shown at the top of the file.
    pub fn line(mut self, line: NonZeroUsize) -> Self {
        self.line = line.get();
        self
    }
}

/// Create an error to be shown for the given file and with the given title.
pub fn error(file: impl std::fmt::Display, title: impl Into<String>) -> Error {
    Error {
        file: file.to_string(),
        line: 0,
        title: title.into(),
        message: String::new(),
    }
}

impl Write for Error {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.message.write_str(s)
    }
}

impl Drop for Error {
    fn drop(&mut self) {
        if std::env::var_os("GITHUB_ACTION").is_some() {
            let Error {
                file,
                line,
                title,
                message,
            } = self;
            let message = message.trim();
            let message = if message.is_empty() {
                "::no message".into()
            } else {
                format!("::{}", github_action_multiline_escape(message))
            };
            println!("::error file={file},line={line},title={title}{message}");
        }
    }
}

/// Append to the summary file that will be shown for the entire CI run.
pub fn summary() -> Option<impl std::io::Write> {
    let path = std::env::var_os("GITHUB_STEP_SUMMARY")?;
    Some(std::fs::OpenOptions::new().append(true).open(path).unwrap())
}

fn github_action_multiline_escape(s: &str) -> String {
    s.replace('%', "%25")
        .replace('\n', "%0A")
        .replace('\r', "%0D")
}

/// All github actions log messages from this call to the Drop of the return value
/// will be grouped and hidden by default in logs. Note that nesting these does
/// not really work.
pub fn group(name: impl std::fmt::Display) -> Group {
    if std::env::var_os("GITHUB_ACTION").is_some() {
        println!("::group::{name}");
    }
    Group(())
}

/// A guard that closes the current github actions log group on drop.
pub struct Group(());

impl Debug for Group {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("a handle that will close the github action group on drop")
    }
}

impl Drop for Group {
    fn drop(&mut self) {
        if std::env::var_os("GITHUB_ACTION").is_some() {
            println!("::endgroup::");
        }
    }
}
