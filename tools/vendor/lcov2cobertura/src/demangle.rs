//! Interface and implemtation of different demanglers
use regex::Regex;
use rustc_demangle::demangle;
use std::borrow::Cow;
use std::io::{self, BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

/// Basic interface to demangle function/method names
pub trait Demangler<'a, 'b> {
    /// demangles an identifier
    fn demangle(&'b mut self, ident: &'a str) -> io::Result<Cow<'a, str>>;
    /// consumes the instance closing opened resources
    fn stop(self) -> io::Result<()>;
}

/// C++ demangling, actually accepts any demangler tool that works over stdin/stdout
/// it writes the mangled named to spawned process' stdin and reads the demangled response from
/// stdout
pub struct CppDemangler {
    child: Child,
    child_in: ChildStdin,
    child_out: BufReader<ChildStdout>,
}

impl CppDemangler {
    /// pass in full path to command that does the demangling
    // safety: stdin/stdout is only taken once, panic unlikely
    #[allow(clippy::unwrap_used, clippy::unwrap_in_result)]
    pub fn new(cmd: &str) -> io::Result<Self> {
        let mut child = Command::new(cmd)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let child_in = child.stdin.take().unwrap();
        let child_out = BufReader::new(child.stdout.take().unwrap());
        Ok(Self {
            child,
            child_in,
            child_out,
        })
    }
}

impl<'a> Demangler<'a, '_> for CppDemangler {
    fn demangle(&mut self, ident: &str) -> io::Result<Cow<'a, str>> {
        self.child_in.write_all(format!("{}\n", ident).as_bytes())?;
        let mut line = String::new();
        self.child_out.read_line(&mut line)?;
        Ok(Cow::Owned(line.trim().into()))
    }

    fn stop(mut self) -> io::Result<()> {
        self.child.kill()?;
        Ok(())
    }
}

/// Demangles rustc names, uses [rustc_demangle](https://docs.rs/rustc-demangle/) crate
pub struct RustDemangler {
    /// strips crate disambiguators
    disambiguator: Regex,
}
impl Default for RustDemangler {
    fn default() -> Self {
        Self::new()
    }
}

impl RustDemangler {
    /// creates the Regex instance needed for later demangling
    // safety: regex is known to compile fine, no panic
    #[allow(clippy::unwrap_used)]
    pub fn new() -> Self {
        Self {
            disambiguator: Regex::new(r"\[[0-9a-f]{5,16}\]::").unwrap(),
        }
    }
}
impl<'a> Demangler<'a, '_> for RustDemangler {
    fn demangle(&mut self, ident: &str) -> io::Result<Cow<'a, str>> {
        let demangled = demangle(ident).to_string();
        Ok(Cow::Owned(
            self.disambiguator.replace_all(&demangled, "::").to_string(),
        ))
    }

    fn stop(self) -> io::Result<()> {
        Ok(())
    }
}

/// default demangler, does nothing to the identifier names
pub struct NullDemangler {}
impl Default for NullDemangler {
    fn default() -> Self {
        Self::new()
    }
}

impl NullDemangler {
    /// constructs the NullDemangler
    pub fn new() -> Self {
        Self {}
    }
}
impl<'a, 'b> Demangler<'a, 'b> for NullDemangler {
    fn demangle(&'b mut self, ident: &'a str) -> io::Result<Cow<'a, str>> {
        Ok(Cow::Borrowed(ident))
    }

    fn stop(self) -> io::Result<()> {
        Ok(())
    }
}
