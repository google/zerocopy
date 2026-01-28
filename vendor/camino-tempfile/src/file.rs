// Copyright (c) The camino-tempfile Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{errors::IoResultExt, Builder};
use camino::{Utf8Path, Utf8PathBuf};
use std::{
    convert::{TryFrom, TryInto},
    error,
    ffi::OsStr,
    fmt,
    fs::File,
    io,
    io::{Read, Seek, SeekFrom, Write},
    ops::Deref,
    path::Path,
};
use tempfile::{NamedTempFile, TempPath};

/// Create a new temporary file.
///
/// The file will be created in the location returned by [`std::env::temp_dir()`].
///
/// # Security
///
/// This variant is secure/reliable in the presence of a pathological temporary file cleaner.
///
/// # Resource Leaking
///
/// The temporary file will be automatically removed by the OS when the last handle to it is closed.
/// This doesn't rely on Rust destructors being run, so will (almost) never fail to clean up the
/// temporary file.
///
/// # Errors
///
/// If the file can not be created, `Err` is returned.
///
/// # Examples
///
/// ```
/// use camino_tempfile::tempfile;
/// use std::io::{self, Write};
///
/// # fn main() {
/// #     if let Err(_) = run() {
/// #         ::std::process::exit(1);
/// #     }
/// # }
/// # fn run() -> Result<(), io::Error> {
/// // Create a file inside of `std::env::temp_dir()`.
/// let mut file = tempfile()?;
///
/// writeln!(file, "Brian was here. Briefly.")?;
/// # Ok(())
/// # }
/// ```
pub fn tempfile() -> io::Result<File> {
    tempfile::tempfile()
}

/// Create a new temporary file in the specified directory.
///
/// This method accepts `AsRef<Path>` rather than `AsRef<Utf8Path>` because it returns a
/// [`std::fs::File`].
///
/// # Security
///
/// This variant is secure/reliable in the presence of a pathological temporary file cleaner. If the
/// temporary file isn't created in [`std::env::temp_dir()`] then temporary file cleaners aren't an
/// issue.
///
/// # Resource Leaking
///
/// The temporary file will be automatically removed by the OS when the last handle to it is closed.
/// This doesn't rely on Rust destructors being run, so will (almost) never fail to clean up the
/// temporary file.
///
/// # Errors
///
/// If the file can not be created, `Err` is returned.
///
/// # Examples
///
/// ```
/// use camino_tempfile::tempfile_in;
/// use std::io::{self, Write};
///
/// # fn main() {
/// #     if let Err(_) = run() {
/// #         ::std::process::exit(1);
/// #     }
/// # }
/// # fn run() -> Result<(), io::Error> {
/// // Create a file inside of the current working directory
/// let mut file = tempfile_in("./")?;
///
/// writeln!(file, "Brian was here. Briefly.")?;
/// # Ok(())
/// # }
/// ```
pub fn tempfile_in<P: AsRef<Path>>(dir: P) -> io::Result<File> {
    tempfile::tempfile_in(dir)
}

/// Error returned when persisting a temporary file path fails.
#[derive(Debug)]
pub struct Utf8PathPersistError {
    /// The underlying IO error.
    pub error: io::Error,
    /// The temporary file path that couldn't be persisted.
    pub path: Utf8TempPath,
}

impl From<Utf8PathPersistError> for io::Error {
    #[inline]
    fn from(error: Utf8PathPersistError) -> io::Error {
        error.error
    }
}

impl From<Utf8PathPersistError> for Utf8TempPath {
    #[inline]
    fn from(error: Utf8PathPersistError) -> Utf8TempPath {
        error.path
    }
}

impl fmt::Display for Utf8PathPersistError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to persist temporary file path: {}", self.error)
    }
}

impl error::Error for Utf8PathPersistError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.error)
    }
}

/// A path to a named temporary file without an open file handle.
///
/// This is useful when the temporary file needs to be used by a child process,
/// for example.
///
/// When dropped, the temporary file is deleted.
pub struct Utf8TempPath {
    // Invariant: inner stores a UTF-8 path.
    inner: TempPath,
}

impl Utf8TempPath {
    pub(crate) fn from_temp_path(inner: TempPath) -> io::Result<Self> {
        let path: &Path = inner.as_ref();
        // This produces a better error message.
        Utf8PathBuf::try_from(path.to_path_buf()).map_err(|error| error.into_io_error())?;
        Ok(Self { inner })
    }

    /// Close and remove the temporary file.
    ///
    /// Use this if you want to detect errors in deleting the file.
    ///
    /// # Errors
    ///
    /// If the file cannot be deleted, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io;
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let file = NamedUtf8TempFile::new()?;
    ///
    /// // Close the file, but keep the path to it around.
    /// let path = file.into_temp_path();
    ///
    /// // By closing the `Utf8TempPath` explicitly, we can check that it has
    /// // been deleted successfully. If we don't close it explicitly, the
    /// // file will still be deleted when `file` goes out of scope, but we
    /// // won't know whether deleting the file succeeded.
    /// path.close()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn close(self) -> io::Result<()> {
        self.inner.close()
    }

    /// Persist the temporary file at the target path.
    ///
    /// If a file exists at the target path, persist will atomically replace it. If this method
    /// fails, it will return `self` in the resulting [`Utf8PathPersistError`].
    ///
    /// # Notes
    ///
    /// * This method accepts `AsRef<Path>` rather than `AsRef<Utf8Path>`, because in the success
    ///   case it does not return anything.
    /// * Temporary files cannot be persisted across filesystems.
    /// * Neither the file contents nor the containing directory are synchronized, so the update may
    ///   not yet have reached the disk when `persist` returns.
    ///
    /// # Security
    ///
    /// Only use this method if you're positive that a temporary file cleaner won't have deleted
    /// your file. Otherwise, you might end up persisting an attacker controlled file.
    ///
    /// # Errors
    ///
    /// If the file cannot be moved to the new location, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let mut file = NamedUtf8TempFile::new()?;
    /// writeln!(file, "Brian was here. Briefly.")?;
    ///
    /// let path = file.into_temp_path();
    /// path.persist("./saved_file.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`PathPersistError`]: struct.PathPersistError.html
    pub fn persist<P: AsRef<Path>>(self, new_path: P) -> Result<(), Utf8PathPersistError> {
        self.inner.persist(new_path.as_ref()).map_err(|error| {
            Utf8PathPersistError {
                error: error.error,
                // This is OK because the path returned here is self
                path: Self { inner: error.path },
            }
        })
    }

    /// Persist the temporary file at the target path if and only if no file exists there.
    ///
    /// If a file exists at the target path, fail. If this method fails, it will return `self` in
    /// the resulting [`Utf8PathPersistError`].
    ///
    /// # Notes
    ///
    /// * This method accepts `AsRef<Path>` rather than `AsRef<Utf8Path>`, because in the success
    ///   case it does not return anything.
    /// * Temporary files cannot be persisted across filesystems.
    /// * This method is not atomic. It can leave the original link to the temporary file behind.
    ///
    /// # Security
    ///
    /// Only use this method if you're positive that a temporary file cleaner won't have deleted
    /// your file. Otherwise, you might end up persisting an attacker controlled file.
    ///
    /// # Errors
    ///
    /// If the file cannot be moved to the new location or a file already exists there, `Err` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let mut file = NamedUtf8TempFile::new()?;
    /// writeln!(file, "Brian was here. Briefly.")?;
    ///
    /// let path = file.into_temp_path();
    /// path.persist_noclobber("./saved_file.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`PathPersistError`]: struct.PathPersistError.html
    pub fn persist_noclobber<P: AsRef<Path>>(
        self,
        new_path: P,
    ) -> Result<(), Utf8PathPersistError> {
        self.inner
            .persist_noclobber(new_path.as_ref())
            .map_err(|error| {
                Utf8PathPersistError {
                    error: error.error,
                    // This is OK because the path returned here is self
                    path: Self { inner: error.path },
                }
            })
    }

    /// Keep the temporary file from being deleted. This function will turn the temporary file into
    /// a non-temporary file without moving it.
    ///
    ///
    /// # Errors
    ///
    /// On some platforms (e.g., Windows), we need to mark the file as non-temporary. This operation
    /// could fail.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let mut file = NamedUtf8TempFile::new()?;
    /// writeln!(file, "Brian was here. Briefly.")?;
    ///
    /// let path = file.into_temp_path();
    /// let path = path.keep()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn keep(self) -> Result<Utf8PathBuf, Utf8PathPersistError> {
        match self.inner.keep() {
            Ok(path) => Ok(Utf8PathBuf::try_from(path).expect("invariant: path is UTF-8")),
            Err(error) => {
                Err(Utf8PathPersistError {
                    error: error.error,
                    // This is OK because the path returned here is self
                    path: Self { inner: error.path },
                })
            }
        }
    }

    /// Disable cleanup of the temporary file. If `disable_cleanup` is `true`,
    /// the temporary file will not be deleted when this `Utf8TempPath` is
    /// dropped. This method is equivalent to calling
    /// [`Builder::disable_cleanup`] when creating the original `Utf8TempPath`,
    /// which see for relevant warnings.
    ///
    /// **NOTE:** this method is primarily useful for testing/debugging. If you
    /// want to simply turn a temporary file-path into a non-temporary
    /// file-path, prefer [`Utf8TempPath::keep`].
    pub fn disable_cleanup(&mut self, disable_cleanup: bool) {
        self.inner.disable_cleanup(disable_cleanup);
    }

    /// Create a new `Utf8TempPath` from an existing path. This can be done even if no file exists
    /// at the given path.
    ///
    /// This is mostly useful for interacting with libraries and external components that provide
    /// files to be consumed or expect a path with no existing file to be given.
    pub fn from_path(path: impl Into<Utf8PathBuf>) -> Self {
        Self {
            inner: TempPath::from_path(path.into()),
        }
    }
}

impl fmt::Debug for Utf8TempPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl Deref for Utf8TempPath {
    type Target = Utf8Path;

    fn deref(&self) -> &Utf8Path {
        self.inner
            .deref()
            .try_into()
            .expect("invariant: path is UTF-8")
    }
}

impl AsRef<Utf8Path> for Utf8TempPath {
    #[inline]
    fn as_ref(&self) -> &Utf8Path {
        let path: &Path = self.as_ref();
        path.try_into().expect("invariant: path is valid UTF-8")
    }
}

impl AsRef<Path> for Utf8TempPath {
    #[inline]
    fn as_ref(&self) -> &Path {
        self.inner.as_ref()
    }
}

impl AsRef<str> for Utf8TempPath {
    #[inline]
    fn as_ref(&self) -> &str {
        let path: &Utf8Path = self.as_ref();
        path.as_str()
    }
}

impl AsRef<OsStr> for Utf8TempPath {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        let path: &Path = self.as_ref();
        path.as_os_str()
    }
}

/// A named temporary file.
///
/// The default constructor, [`NamedUtf8TempFile::new()`], creates files in
/// the location returned by [`std::env::temp_dir()`], but `NamedUtf8TempFile`
/// can be configured to manage a temporary file in any location
/// by constructing with [`NamedUtf8TempFile::new_in()`].
///
/// # Security
///
/// Most operating systems employ temporary file cleaners to delete old
/// temporary files. Unfortunately these temporary file cleaners don't always
/// reliably _detect_ whether the temporary file is still being used.
///
/// Specifically, the following sequence of events can happen:
///
/// 1. A user creates a temporary file with `NamedUtf8TempFile::new()`.
/// 2. Time passes.
/// 3. The temporary file cleaner deletes (unlinks) the temporary file from the
///    filesystem.
/// 4. Some other program creates a new file to replace this deleted temporary
///    file.
/// 5. The user tries to re-open the temporary file (in the same program or in a
///    different program) by path. Unfortunately, they'll end up opening the
///    file created by the other program, not the original file.
///
/// ## Operating System Specific Concerns
///
/// The behavior of temporary files and temporary file cleaners differ by
/// operating system.
///
/// ### Windows
///
/// On Windows, open files _can't_ be deleted. This removes most of the concerns
/// around temporary file cleaners.
///
/// Furthermore, temporary files are, by default, created in per-user temporary
/// file directories so only an application running as the same user would be
/// able to interfere (which they could do anyways). However, an application
/// running as the same user can still _accidentally_ re-create deleted
/// temporary files if the number of random bytes in the temporary file name is
/// too small.
///
/// So, the only real concern on Windows is:
///
/// 1. Opening a named temporary file in a world-writable directory.
/// 2. Using the `into_temp_path()` and/or `into_parts()` APIs to close the file
///    handle without deleting the underlying file.
/// 3. Continuing to use the file by path.
///
/// ### UNIX
///
/// Unlike on Windows, UNIX (and UNIX like) systems allow open files to be
/// "unlinked" (deleted).
///
/// #### MacOS
///
/// Like on Windows, temporary files are created in per-user temporary file
/// directories by default so calling `NamedUtf8TempFile::new()` should be
/// relatively safe.
///
/// #### Linux
///
/// Unfortunately, most _Linux_ distributions don't create per-user temporary
/// file directories. Worse, systemd's tmpfiles daemon (a common temporary file
/// cleaner) will happily remove open temporary files if they haven't been
/// modified within the last 10 days.
///
/// # Resource Leaking
///
/// If the program exits before the `NamedUtf8TempFile` destructor is
/// run, the temporary file will not be deleted. This can happen
/// if the process exits using [`std::process::exit()`], a segfault occurs,
/// receiving an interrupt signal like `SIGINT` that is not handled, or by using
/// a statically declared `NamedUtf8TempFile` instance (like with `lazy_static`).
///
/// Use the [`tempfile()`] function unless you need a named file path.
pub struct NamedUtf8TempFile<F = File> {
    // Invariant: inner.path is a valid Utf8TempPath
    inner: NamedTempFile<F>,
}

impl<F> NamedUtf8TempFile<F> {
    pub(crate) fn from_temp_file(inner: NamedTempFile<F>) -> io::Result<Self> {
        let path = inner.path();
        // This produces a better error message.
        Utf8PathBuf::try_from(path.to_owned()).map_err(|error| error.into_io_error())?;
        Ok(Self { inner })
    }
}

impl<F> fmt::Debug for NamedUtf8TempFile<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NamedUtf8TempFile({})", self.path())
    }
}

impl<F> AsRef<Utf8Path> for NamedUtf8TempFile<F> {
    #[inline]
    fn as_ref(&self) -> &Utf8Path {
        self.path()
    }
}
impl<F> AsRef<Path> for NamedUtf8TempFile<F> {
    #[inline]
    fn as_ref(&self) -> &Path {
        self.path().as_std_path()
    }
}

impl NamedUtf8TempFile<File> {
    /// Create a new named temporary file.
    ///
    /// See [`Builder`] for more configuration.
    ///
    /// # Security
    ///
    /// This will create a temporary file in the default temporary file
    /// directory (platform dependent). This has security implications on many
    /// platforms so please read the security section of this type's
    /// documentation.
    ///
    /// Reasons to use this method:
    ///
    ///   1. The file has a short lifetime and your temporary file cleaner is
    ///      sane (doesn't delete recently accessed files).
    ///
    ///   2. You trust every user on your system (i.e. you are the only user).
    ///
    ///   3. You have disabled your system's temporary file cleaner or verified
    ///      that your system doesn't have a temporary file cleaner.
    ///
    /// Reasons not to use this method:
    ///
    ///   1. You'll fix it later. No you won't.
    ///
    ///   2. You don't care about the security of the temporary file. If none of
    ///      the "reasons to use this method" apply, referring to a temporary
    ///      file by name may allow an attacker to create/overwrite your
    ///      non-temporary files. There are exceptions but if you don't already
    ///      know them, don't use this method.
    ///
    /// # Errors
    ///
    /// If the file can not be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// Create a named temporary file and write some data to it:
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), ::std::io::Error> {
    /// let mut file = NamedUtf8TempFile::new()?;
    ///
    /// writeln!(file, "Brian was here. Briefly.")?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`Builder`]: struct.Builder.html
    pub fn new() -> io::Result<NamedUtf8TempFile> {
        Builder::new().tempfile()
    }

    /// Create a new named temporary file in the specified directory.
    ///
    /// See [`NamedUtf8TempFile::new()`] for details.
    pub fn new_in<P: AsRef<Utf8Path>>(dir: P) -> io::Result<NamedUtf8TempFile> {
        Builder::new().tempfile_in(dir)
    }

    /// Create a new named temporary file with the specified filename prefix.
    ///
    /// See [`NamedUtf8TempFile::new()`] for details.
    pub fn with_prefix<S: AsRef<str>>(prefix: S) -> io::Result<NamedUtf8TempFile> {
        Builder::new().prefix(&prefix).tempfile()
    }

    /// Create a new named temporary file with the specified filename prefix,
    /// in the specified directory.
    ///
    /// This is equivalent to:
    ///
    /// ```ignore
    /// Builder::new().prefix(&prefix).tempfile_in(directory)
    /// ```
    ///
    /// See [`NamedUtf8TempFile::new()`] for details.
    pub fn with_prefix_in<S: AsRef<str>, P: AsRef<Utf8Path>>(
        prefix: S,
        dir: P,
    ) -> io::Result<NamedUtf8TempFile> {
        Builder::new().prefix(&prefix).tempfile_in(dir)
    }

    /// Create a new named temporary file with the specified filename suffix.
    ///
    /// See [`NamedUtf8TempFile::new()`] for details.
    pub fn with_suffix<S: AsRef<str>>(suffix: S) -> io::Result<NamedUtf8TempFile> {
        Builder::new().suffix(&suffix).tempfile()
    }

    /// Create a new named temporary file with the specified filename suffix,
    /// in the specified directory.
    ///
    /// This is equivalent to:
    ///
    /// ```ignore
    /// Builder::new().suffix(&suffix).tempfile_in(directory)
    /// ```
    ///
    /// See [`NamedUtf8TempFile::new()`] for details.
    pub fn with_suffix_in<S: AsRef<str>, P: AsRef<Utf8Path>>(
        suffix: S,
        dir: P,
    ) -> io::Result<NamedUtf8TempFile> {
        Builder::new().suffix(&suffix).tempfile_in(dir)
    }
}

impl<F> NamedUtf8TempFile<F> {
    /// Get the temporary file's path.
    ///
    /// # Security
    ///
    /// Referring to a temporary file's path may not be secure in all cases.
    /// Please read the security section on the top level documentation of this
    /// type for details.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), ::std::io::Error> {
    /// let file = NamedUtf8TempFile::new()?;
    ///
    /// println!("{}", file.path());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn path(&self) -> &Utf8Path {
        self.inner
            .path()
            .try_into()
            .expect("invariant: path is valid UTF-8")
    }

    /// Close and remove the temporary file.
    ///
    /// Use this if you want to detect errors in deleting the file.
    ///
    /// # Errors
    ///
    /// If the file cannot be deleted, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io;
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let file = NamedUtf8TempFile::new()?;
    ///
    /// // By closing the `NamedUtf8TempFile` explicitly, we can check that it
    /// // has been deleted successfully. If we don't close it explicitly,
    /// // the file will still be deleted when `file` goes out
    /// // of scope, but we won't know whether deleting the file
    /// // succeeded.
    /// file.close()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn close(self) -> io::Result<()> {
        self.inner.close()
    }

    /// Persist the temporary file at the target path.
    ///
    /// If a file exists at the target path, persist will atomically replace it. If this method
    /// fails, it will return `self` in the resulting [`Utf8PersistError`].
    ///
    /// # Notes
    ///
    /// * This method accepts `AsRef<Path>` rather than `AsRef<Utf8Path>` because it returns the
    ///   underlying file type `F`.
    /// * Temporary files cannot be persisted across filesystems.
    /// * Neither the file contents nor the containing directory are synchronized, so the update may
    ///   not yet have reached the disk when `persist` returns.
    ///
    /// # Security
    ///
    /// This method persists the temporary file using its path and may not be secure in the in all
    /// cases. Please read the security section on the top level documentation of this type for
    /// details.
    ///
    /// # Errors
    ///
    /// If the file cannot be moved to the new location, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let file = NamedUtf8TempFile::new()?;
    ///
    /// let mut persisted_file = file.persist("./saved_file.txt")?;
    /// writeln!(persisted_file, "Brian was here. Briefly.")?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`PersistError`]: struct.PersistError.html
    pub fn persist<P: AsRef<Path>>(self, new_path: P) -> Result<F, Utf8PersistError<F>> {
        self.inner.persist(new_path).map_err(|error| {
            Utf8PersistError {
                // This is valid because self is exactly error.file.
                file: NamedUtf8TempFile { inner: error.file },
                error: error.error,
            }
        })
    }

    /// Persist the temporary file at the target path if and only if no file exists there.
    ///
    /// If a file exists at the target path, fail. If this method fails, it will return `self` in
    /// the resulting [`Utf8PersistError`].
    ///
    /// # Notes
    ///
    /// * This method accepts `AsRef<Path>` rather than `AsRef<Utf8Path>` because it returns the
    ///   underlying file type `F`.
    /// * Temporary files cannot be persisted across filesystems.
    /// * This method is not atomic. It can leave the original link to the temporary file behind.
    ///
    /// # Security
    ///
    /// This method persists the temporary file using its path and may not be secure in the in all
    /// cases. Please read the security section on the top level documentation of this type for
    /// details.
    ///
    /// # Errors
    ///
    /// If the file cannot be moved to the new location or a file already exists there, `Err` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let file = NamedUtf8TempFile::new()?;
    ///
    /// let mut persisted_file = file.persist_noclobber("./saved_file.txt")?;
    /// writeln!(persisted_file, "Brian was here. Briefly.")?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn persist_noclobber<P: AsRef<Path>>(self, new_path: P) -> Result<F, Utf8PersistError<F>> {
        self.inner.persist_noclobber(new_path).map_err(|error| {
            Utf8PersistError {
                // This is valid because self is exactly error.file.
                file: NamedUtf8TempFile { inner: error.file },
                error: error.error,
            }
        })
    }

    /// Keep the temporary file from being deleted. This function will turn the
    /// temporary file into a non-temporary file without moving it.
    ///
    ///
    /// # Errors
    ///
    /// On some platforms (e.g., Windows), we need to mark the file as
    /// non-temporary. This operation could fail.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io::{self, Write};
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let mut file = NamedUtf8TempFile::new()?;
    /// writeln!(file, "Brian was here. Briefly.")?;
    ///
    /// let (file, path) = file.keep()?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`PathPersistError`]: struct.PathPersistError.html
    pub fn keep(self) -> Result<(F, Utf8PathBuf), Utf8PersistError<F>> {
        match self.inner.keep() {
            Ok((file, path)) => Ok((
                file,
                path.try_into().expect("invariant: path is valid UTF-8"),
            )),
            Err(error) => Err(Utf8PersistError {
                // This is valid because self is exactly error.file.
                file: NamedUtf8TempFile { inner: error.file },
                error: error.error,
            }),
        }
    }

    /// Disable cleanup of the temporary file. If `disable_cleanup` is `true`,
    /// the temporary file will not be deleted when this `NamedUtf8TempFile` is
    /// dropped. This method is equivalent to calling
    /// [`Builder::disable_cleanup`] when creating the original
    /// `NamedUtf8TempFile`, which see for relevant warnings.
    ///
    /// **NOTE:** this method is primarily useful for testing/debugging. If you
    /// want to simply turn a temporary file into a non-temporary file, prefer
    /// [`NamedUtf8TempFile::keep`].
    pub fn disable_cleanup(&mut self, disable_cleanup: bool) {
        self.inner.disable_cleanup(disable_cleanup);
    }

    /// Get a reference to the underlying file.
    pub fn as_file(&self) -> &F {
        self.inner.as_file()
    }

    /// Get a mutable reference to the underlying file.
    pub fn as_file_mut(&mut self) -> &mut F {
        self.inner.as_file_mut()
    }

    /// Convert the temporary file into a `std::fs::File`.
    ///
    /// The inner file will be deleted.
    pub fn into_file(self) -> F {
        self.inner.into_file()
    }

    /// Closes the file, leaving only the temporary file path.
    ///
    /// This is useful when another process must be able to open the temporary
    /// file.
    pub fn into_temp_path(self) -> Utf8TempPath {
        Utf8TempPath::from_temp_path(self.inner.into_temp_path())
            .expect("invariant: inner path is UTF-8")
    }

    /// Converts the named temporary file into its constituent parts.
    ///
    /// Note: When the path is dropped, the file is deleted but the file handle
    /// is still usable.
    pub fn into_parts(self) -> (F, Utf8TempPath) {
        let (file, path) = self.inner.into_parts();
        let path = Utf8TempPath::from_temp_path(path).expect("invariant: inner path is UTF-8");
        (file, path)
    }

    /// Creates a `NamedUtf8TempFile` from its constituent parts.
    ///
    /// This can be used with [`NamedUtf8TempFile::into_parts`] to reconstruct the
    /// `NamedUtf8TempFile`.
    pub fn from_parts(file: F, path: Utf8TempPath) -> Self {
        let inner = NamedTempFile::from_parts(file, path.inner);
        // This is valid because it was constructed from a Utf8TempPath
        Self { inner }
    }
}

impl NamedUtf8TempFile<File> {
    /// Securely reopen the temporary file.
    ///
    /// This function is useful when you need multiple independent handles to the same file. It's
    /// perfectly fine to drop the original `NamedUtf8TempFile` while holding on to `File`s returned
    /// by this function; the `File`s will remain usable. However, they may not be nameable.
    ///
    /// # Errors
    ///
    /// If the file cannot be reopened, `Err` is returned.
    ///
    /// # Security
    ///
    /// Unlike `File::open(my_temp_file.path())`, `NamedUtf8TempFile::reopen()` guarantees that the
    /// re-opened file is the _same_ file, even in the presence of pathological temporary file
    /// cleaners.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use std::io;
    /// use camino_tempfile::NamedUtf8TempFile;
    ///
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// let file = NamedUtf8TempFile::new()?;
    ///
    /// let another_handle = file.reopen()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn reopen(&self) -> io::Result<File> {
        self.inner.reopen()
    }
}

impl<F: Read> Read for NamedUtf8TempFile<F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.as_file_mut().read(buf).with_err_path(|| self.path())
    }
}

impl Read for &NamedUtf8TempFile<File> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.as_file().read(buf).with_err_path(|| self.path())
    }
}

impl<F: Write> Write for NamedUtf8TempFile<F> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.as_file_mut().write(buf).with_err_path(|| self.path())
    }
    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        self.as_file_mut().flush().with_err_path(|| self.path())
    }
}

impl Write for &NamedUtf8TempFile<File> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.as_file().write(buf).with_err_path(|| self.path())
    }
    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        self.as_file().flush().with_err_path(|| self.path())
    }
}

impl<F: Seek> Seek for NamedUtf8TempFile<F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        self.as_file_mut().seek(pos).with_err_path(|| self.path())
    }
}

impl Seek for &NamedUtf8TempFile<File> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        self.as_file().seek(pos).with_err_path(|| self.path())
    }
}

#[cfg(unix)]
impl<F> std::os::unix::io::AsRawFd for NamedUtf8TempFile<F>
where
    F: std::os::unix::io::AsRawFd,
{
    #[inline]
    fn as_raw_fd(&self) -> std::os::unix::io::RawFd {
        self.as_file().as_raw_fd()
    }
}

#[cfg(windows)]
impl<F> std::os::windows::io::AsRawHandle for NamedUtf8TempFile<F>
where
    F: std::os::windows::io::AsRawHandle,
{
    #[inline]
    fn as_raw_handle(&self) -> std::os::windows::io::RawHandle {
        self.as_file().as_raw_handle()
    }
}

/// Error returned when persisting a temporary file fails.
pub struct Utf8PersistError<F = File> {
    /// The underlying IO error.
    pub error: io::Error,
    /// The temporary file that couldn't be persisted.
    pub file: NamedUtf8TempFile<F>,
}

impl<F> fmt::Debug for Utf8PersistError<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Utf8PersistError({:?})", self.error)
    }
}

impl<F> From<Utf8PersistError<F>> for io::Error {
    #[inline]
    fn from(error: Utf8PersistError<F>) -> io::Error {
        error.error
    }
}

impl<F> From<Utf8PersistError<F>> for NamedUtf8TempFile<F> {
    #[inline]
    fn from(error: Utf8PersistError<F>) -> NamedUtf8TempFile<F> {
        error.file
    }
}

impl<F> fmt::Display for Utf8PersistError<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to persist temporary file: {}", self.error)
    }
}

impl<F> error::Error for Utf8PersistError<F> {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.error)
    }
}
