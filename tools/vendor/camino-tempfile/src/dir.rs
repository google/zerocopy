// Copyright (c) The camino-tempfile Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::Builder;
use camino::{Utf8Path, Utf8PathBuf};
use std::{
    convert::{TryFrom, TryInto},
    fmt, io,
    path::Path,
};
use tempfile::TempDir;

/// Create a new temporary directory.
///
/// The `tempdir` function creates a directory in the file system and returns a [`Utf8TempDir`]. The
/// directory will be automatically deleted when the [`Utf8TempDir`]'s destructor is run.
///
/// # Resource Leaking
///
/// See [the resource leaking][resource-leaking] docs on `Utf8TempDir`.
///
/// # Errors
///
/// If the directory can not be created, `Err` is returned.
///
/// # Examples
///
/// ```
/// use camino_tempfile::tempdir;
/// use std::fs::File;
/// use std::io::{self, Write};
///
/// # fn main() {
/// #     if let Err(_) = run() {
/// #         ::std::process::exit(1);
/// #     }
/// # }
/// # fn run() -> Result<(), io::Error> {
/// // Create a directory inside of `std::env::temp_dir()`
/// let dir = tempdir()?;
///
/// let file_path = dir.path().join("my-temporary-note.txt");
/// let mut file = File::create(file_path)?;
/// writeln!(file, "Brian was here. Briefly.")?;
///
/// // `tmp_dir` goes out of scope, the directory as well as
/// // `tmp_file` will be deleted here.
/// drop(file);
/// dir.close()?;
/// # Ok(())
/// # }
/// ```
///
/// [resource-leaking]: struct.Utf8TempDir.html#resource-leaking
pub fn tempdir() -> io::Result<Utf8TempDir> {
    Utf8TempDir::new()
}

/// Create a new temporary directory in a specific directory.
///
/// The `tempdir_in` function creates a directory in the specified directory and returns a
/// [`Utf8TempDir`]. The directory will be automatically deleted when the [`Utf8TempDir`]'s
/// destructor is run.
///
/// # Resource Leaking
///
/// See [the resource leaking][resource-leaking] docs on `Utf8TempDir`.
///
/// # Errors
///
/// If the directory can not be created, `Err` is returned.
///
/// # Examples
///
/// ```
/// use camino_tempfile::tempdir_in;
/// use std::fs::File;
/// use std::io::{self, Write};
///
/// # fn main() {
/// #     if let Err(_) = run() {
/// #         ::std::process::exit(1);
/// #     }
/// # }
/// # fn run() -> Result<(), io::Error> {
/// // Create a directory inside of the current directory.
/// let dir = tempdir_in(".")?;
///
/// let file_path = dir.path().join("my-temporary-note.txt");
/// let mut file = File::create(file_path)?;
/// writeln!(file, "Brian was here. Briefly.")?;
///
/// // `tmp_dir` goes out of scope, the directory as well as
/// // `tmp_file` will be deleted here.
/// drop(file);
/// dir.close()?;
/// # Ok(())
/// # }
/// ```
///
/// [resource-leaking]: struct.TempDir.html#resource-leaking
pub fn tempdir_in<P: AsRef<Utf8Path>>(dir: P) -> io::Result<Utf8TempDir> {
    Utf8TempDir::new_in(dir)
}

/// A directory in the filesystem that is automatically deleted when it goes out of scope.
///
/// The [`Utf8TempDir`] type creates a directory on the file system that is deleted once it goes out
/// of scope. At construction, the [`Utf8TempDir`] creates a new directory with a randomly generated
/// name.
///
/// The default constructor, [`Utf8TempDir::new()`], creates directories in the location returned by
/// [`std::env::temp_dir()`], but `Utf8TempDir` can be configured to manage a temporary directory in
/// any location by constructing with a [`Builder`].
///
/// After creating a `Utf8TempDir`, work with the file system by doing standard [`std::fs`] file
/// system operations on its [`Utf8Path`], which can be retrieved with [`Utf8TempDir::path()`]. Once
/// the `Utf8TempDir` value is dropped, the directory at the path will be deleted, along with any
/// files and directories it contains. It is your responsibility to ensure that no further file
/// system operations are attempted inside the temporary directory once it has been deleted.
///
/// # Resource Leaking
///
/// Various platform-specific conditions may cause `Utf8TempDir` to fail to delete the underlying
/// directory. It's important to ensure that handles (like [`File`](std::fs::File) and
/// [`ReadDir`](std::fs::ReadDir)) to files inside the directory are dropped before the `TempDir`
/// goes out of scope. The `Utf8TempDir` destructor will silently ignore any errors in deleting the
/// directory; to instead handle errors call [`Utf8TempDir::close()`].
///
/// Note that if the program exits before the `Utf8TempDir` destructor is run, such as via
/// [`std::process::exit()`], by segfaulting, or by receiving a signal like `SIGINT`, then the
/// temporary directory will not be deleted.
///
/// # Examples
///
/// Create a temporary directory with a generated name:
///
/// ```
/// use std::fs::File;
/// use std::io::Write;
/// use camino_tempfile::Utf8TempDir;
///
/// # use std::io;
/// # fn run() -> Result<(), io::Error> {
/// // Create a directory inside of `std::env::temp_dir()`
/// let tmp_dir = Utf8TempDir::new()?;
/// # Ok(())
/// # }
/// ```
///
/// Create a temporary directory with a prefix in its name:
///
/// ```
/// use std::fs::File;
/// use std::io::Write;
/// use camino_tempfile::Builder;
///
/// # use std::io;
/// # fn run() -> Result<(), io::Error> {
/// // Create a directory inside of `std::env::temp_dir()`,
/// // whose name will begin with 'example'.
/// let tmp_dir = Builder::new().prefix("example").tempdir()?;
/// # Ok(())
/// # }
/// ```
pub struct Utf8TempDir {
    inner: TempDir,
}

impl Utf8TempDir {
    pub(crate) fn from_temp_dir(inner: TempDir) -> io::Result<Self> {
        let path = inner.path();
        // This produces a better error message.
        Utf8PathBuf::try_from(path.to_path_buf()).map_err(|error| error.into_io_error())?;
        Ok(Self { inner })
    }

    /// Attempts to make a temporary directory inside of `env::temp_dir()`.
    ///
    /// See [`Builder`] for more configuration.
    ///
    /// The directory and everything inside it will be automatically deleted once the returned
    /// `Utf8TempDir` is destroyed.
    ///
    /// # Errors
    ///
    /// If the directory can not be created, or if `env::temp_dir` is a non-UTF-8 path, `Err` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::Write;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// // Create a directory inside of `std::env::temp_dir()`
    /// let tmp_dir = Utf8TempDir::new()?;
    ///
    /// let file_path = tmp_dir.path().join("my-temporary-note.txt");
    /// let mut tmp_file = File::create(file_path)?;
    /// writeln!(tmp_file, "Brian was here. Briefly.")?;
    ///
    /// // `tmp_dir` goes out of scope, the directory as well as
    /// // `tmp_file` will be deleted here.
    /// # Ok(())
    /// # }
    /// ```
    pub fn new() -> io::Result<Utf8TempDir> {
        Builder::new().tempdir()
    }

    /// Attempts to make a temporary directory inside of `dir`. The directory and everything inside
    /// it will be automatically deleted once the returned `Utf8TempDir` is destroyed.
    ///
    /// # Errors
    ///
    /// If the directory can not be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::{self, File};
    /// use std::io::Write;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// // Create a directory inside of the current directory
    /// let tmp_dir = Utf8TempDir::new_in(".")?;
    /// let file_path = tmp_dir.path().join("my-temporary-note.txt");
    /// let mut tmp_file = File::create(file_path)?;
    /// writeln!(tmp_file, "Brian was here. Briefly.")?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn new_in<P: AsRef<Utf8Path>>(dir: P) -> io::Result<Utf8TempDir> {
        Builder::new().tempdir_in(dir)
    }

    /// Attempts to make a temporary directory with the specified prefix inside of
    /// `env::temp_dir()`. The directory and everything inside it will be automatically
    /// deleted once the returned `Utf8TempDir` is destroyed.
    ///
    /// # Errors
    ///
    /// If the directory can not be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::{self, File};
    /// use std::io::Write;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// // Create a directory inside of the current directory
    /// let tmp_dir = Utf8TempDir::with_prefix("foo-")?;
    /// let tmp_name = tmp_dir.path().file_name().unwrap();
    /// assert!(tmp_name.starts_with("foo-"));
    /// # Ok(())
    /// # }
    /// ```
    pub fn with_prefix<S: AsRef<str>>(prefix: S) -> io::Result<Utf8TempDir> {
        Builder::new().prefix(&prefix).tempdir()
    }

    /// Attempts to make a temporary directory with the specified prefix inside
    /// the specified directory. The directory and everything inside it will be
    /// automatically deleted once the returned `Utf8TempDir` is destroyed.
    ///
    /// # Errors
    ///
    /// If the directory can not be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::{self, File};
    /// use std::io::Write;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// // Create a directory inside of the current directory
    /// let tmp_dir = Utf8TempDir::with_prefix_in("foo-", ".")?;
    /// let tmp_name = tmp_dir.path().file_name().unwrap();
    /// assert!(tmp_name.starts_with("foo-"));
    /// # Ok(())
    /// # }
    /// ```
    pub fn with_prefix_in<S: AsRef<str>, P: AsRef<Utf8Path>>(
        prefix: S,
        dir: P,
    ) -> io::Result<Utf8TempDir> {
        Builder::new().prefix(&prefix).tempdir_in(dir)
    }

    /// Attempts to make a temporary directory with the specified suffix inside of
    /// `env::temp_dir()`. The directory and everything inside it will be automatically
    /// deleted once the returned `TempDir` is destroyed.
    ///
    /// # Errors
    ///
    /// If the directory can not be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::{self, File};
    /// use std::io::Write;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// // Create a directory inside of the current directory
    /// let tmp_dir = Utf8TempDir::with_suffix("-foo")?;
    /// let tmp_name = tmp_dir.path().file_name().unwrap();
    /// assert!(tmp_name.ends_with("-foo"));
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn with_suffix<S: AsRef<str>>(suffix: S) -> io::Result<Utf8TempDir> {
        Builder::new().suffix(&suffix).tempdir()
    }

    /// Attempts to make a temporary directory with the specified suffix inside
    /// the specified directory. The directory and everything inside it will be
    /// automatically deleted once the returned `TempDir` is destroyed.
    ///
    /// # Errors
    ///
    /// If the directory can not be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::{self, File};
    /// use std::io::Write;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// // Create a directory inside of the current directory
    /// let tmp_dir = Utf8TempDir::with_suffix_in("-foo", ".")?;
    /// let tmp_name = tmp_dir.path().file_name().unwrap();
    /// assert!(tmp_name.ends_with("-foo"));
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn with_suffix_in<S: AsRef<str>, P: AsRef<Utf8Path>>(
        suffix: S,
        dir: P,
    ) -> io::Result<Utf8TempDir> {
        Builder::new().suffix(&suffix).tempdir_in(dir)
    }

    /// Accesses the [`Utf8Path`] to the temporary directory.
    ///
    /// # Examples
    ///
    /// ```
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// let tmp_path;
    ///
    /// {
    ///    let tmp_dir = Utf8TempDir::new()?;
    ///    tmp_path = tmp_dir.path().to_owned();
    ///
    ///    // Check that the temp directory actually exists.
    ///    assert!(tmp_path.exists());
    ///
    ///    // End of `tmp_dir` scope, directory will be deleted
    /// }
    ///
    /// // Temp directory should be deleted by now
    /// assert_eq!(tmp_path.exists(), false);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn path(&self) -> &Utf8Path {
        self.as_ref()
    }

    /// Deprecated alias for [`Utf8TempDir::keep`].
    #[must_use]
    #[deprecated(since = "1.4.0", note = "use Utf8TempDir::keep")]
    pub fn into_path(self) -> Utf8PathBuf {
        self.keep()
    }

    /// Persist the temporary directory to disk, returning the [`Utf8PathBuf`] where it is located.
    ///
    /// This consumes the [`Utf8TempDir`] without deleting directory on the filesystem, meaning that
    /// the directory will no longer be automatically deleted.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// let tmp_dir = Utf8TempDir::new()?;
    ///
    /// // Persist the temporary directory to disk,
    /// // getting the path where it is.
    /// let tmp_path = tmp_dir.keep();
    ///
    /// // Delete the temporary directory ourselves.
    /// fs::remove_dir_all(tmp_path)?;
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn keep(self) -> Utf8PathBuf {
        self.inner
            .keep()
            .try_into()
            .expect("invariant: path is valid UTF-8")
    }

    /// Disable cleanup of the temporary directory. If `disable_cleanup` is
    /// `true`, the temporary directory will not be deleted when this
    /// `Utf8TempDir` is dropped. This method is equivalent to calling
    /// [`Builder::disable_cleanup`] when creating the `Utf8TempDir`.
    ///
    /// **NOTE:** this method is primarily useful for testing/debugging. If you
    /// want to simply turn a temporary directory into a non-temporary
    /// directory, prefer [`Utf8TempDir::keep`].
    pub fn disable_cleanup(&mut self, disable_cleanup: bool) {
        self.inner.disable_cleanup(disable_cleanup);
    }

    /// Closes and removes the temporary directory, returning a `Result`.
    ///
    /// Although `Utf8TempDir` removes the directory on drop, in the destructor any errors are
    /// ignored. To detect errors cleaning up the temporary directory, call `close` instead.
    ///
    /// # Errors
    ///
    /// This function may return a variety of [`std::io::Error`]s that result from deleting the
    /// files and directories contained with the temporary directory, as well as from deleting the
    /// temporary directory itself. These errors may be platform specific.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::Write;
    /// use camino_tempfile::Utf8TempDir;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// // Create a directory inside of `std::env::temp_dir()`.
    /// let tmp_dir = Utf8TempDir::new()?;
    /// let file_path = tmp_dir.path().join("my-temporary-note.txt");
    /// let mut tmp_file = File::create(file_path)?;
    /// writeln!(tmp_file, "Brian was here. Briefly.")?;
    ///
    /// // By closing the `Utf8TempDir` explicitly we can check that it has
    /// // been deleted successfully. If we don't close it explicitly,
    /// // the directory will still be deleted when `tmp_dir` goes out
    /// // of scope, but we won't know whether deleting the directory
    /// // succeeded.
    /// drop(tmp_file);
    /// tmp_dir.close()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn close(self) -> io::Result<()> {
        self.inner.close()
    }
}

impl AsRef<Utf8Path> for Utf8TempDir {
    #[inline]
    fn as_ref(&self) -> &Utf8Path {
        let path: &Path = self.as_ref();
        path.try_into().expect("invariant: path is valid UTF-8")
    }
}

impl AsRef<Path> for Utf8TempDir {
    fn as_ref(&self) -> &Path {
        self.inner.path()
    }
}

impl fmt::Debug for Utf8TempDir {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Utf8TempDir")
            .field("path", &self.path())
            .finish()
    }
}

// The Drop impl is implicit since `Utf8TempDir` wraps a `TempDir`.
