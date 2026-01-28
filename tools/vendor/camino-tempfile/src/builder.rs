// Copyright (c) The camino-tempfile Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{helpers::utf8_env_temp_dir, NamedUtf8TempFile, Utf8TempDir};
use camino::{Utf8Path, Utf8PathBuf};
use std::{convert::TryFrom, io};

/// Create a new temporary file or directory with custom parameters.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Builder<'a, 'b> {
    inner: tempfile::Builder<'a, 'b>,
}

impl<'a, 'b> Builder<'a, 'b> {
    /// Create a new `Builder`.
    ///
    /// # Examples
    ///
    /// Create a named temporary file and write some data into it:
    ///
    /// ```
    /// # use std::io;
    /// # use std::ffi::OsStr;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// use camino_tempfile::Builder;
    ///
    /// let named_tempfile = Builder::new()
    ///     .prefix("my-temporary-note")
    ///     .suffix(".txt")
    ///     .rand_bytes(5)
    ///     .tempfile()?;
    ///
    /// let name = named_tempfile.path().file_name();
    ///
    /// if let Some(name) = name {
    ///     assert!(name.starts_with("my-temporary-note"));
    ///     assert!(name.ends_with(".txt"));
    ///     assert_eq!(name.len(), "my-temporary-note.txt".len() + 5);
    /// }
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Create a temporary directory and add a file to it:
    ///
    /// ```
    /// # use std::io::{self, Write};
    /// # use std::fs::File;
    /// # use std::ffi::OsStr;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// use camino_tempfile::Builder;
    ///
    /// let dir = Builder::new()
    ///     .prefix("my-temporary-dir")
    ///     .rand_bytes(5)
    ///     .tempdir()?;
    ///
    /// let file_path = dir.path().join("my-temporary-note.txt");
    /// let mut file = File::create(file_path)?;
    /// writeln!(file, "Brian was here. Briefly.")?;
    ///
    /// // By closing the `Utf8TempDir` explicitly, we can check that it has
    /// // been deleted successfully. If we don't close it explicitly,
    /// // the directory will still be deleted when `dir` goes out
    /// // of scope, but we won't know whether deleting the directory
    /// // succeeded.
    /// drop(file);
    /// dir.close()?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Create a temporary directory with a chosen prefix under a chosen folder:
    ///
    /// ```ignore
    /// let dir = Builder::new()
    ///     .prefix("my-temporary-dir")
    ///     .tempdir_in("folder-with-tempdirs")?;
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set a custom filename prefix.
    ///
    /// Path separators are legal but not advisable.
    /// Default: `.tmp`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// let named_tempfile = Builder::new()
    ///     .prefix("my-temporary-note")
    ///     .tempfile()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn prefix<S: AsRef<str> + ?Sized>(&mut self, prefix: &'a S) -> &mut Self {
        self.inner.prefix(prefix.as_ref());
        self
    }

    /// Set a custom filename suffix.
    ///
    /// Path separators are legal but not advisable.
    /// Default: empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// let named_tempfile = Builder::new()
    ///     .suffix(".txt")
    ///     .tempfile()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn suffix<S: AsRef<str> + ?Sized>(&mut self, suffix: &'b S) -> &mut Self {
        self.inner.suffix(suffix.as_ref());
        self
    }

    /// Set the number of random bytes.
    ///
    /// Default: `6`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// let named_tempfile = Builder::new()
    ///     .rand_bytes(5)
    ///     .tempfile()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn rand_bytes(&mut self, rand: usize) -> &mut Self {
        self.inner.rand_bytes(rand);
        self
    }

    /// Set the file to be opened in append mode.
    ///
    /// Default: `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// let named_tempfile = Builder::new()
    ///     .append(true)
    ///     .tempfile()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn append(&mut self, append: bool) -> &mut Self {
        self.inner.append(append);
        self
    }

    /// The permissions to create the tempfile or [tempdir](Self::tempdir) with.
    ///
    /// # Security
    ///
    /// By default, the permissions of tempfiles on Unix are set for it to be
    /// readable and writable by the owner only, yielding the greatest amount of
    /// security. As this method allows to widen the permissions, security would
    /// be reduced in such cases.
    ///
    /// # Platform Notes
    ///
    /// ## Unix
    ///
    /// The actual permission bits set on the tempfile or tempdir will be
    /// affected by the `umask` applied by the underlying syscall. The actual
    /// permission bits are calculated via `permissions & !umask`.
    ///
    /// Permissions default to `0o600` for tempfiles and `0o777` for tempdirs.
    /// Note, this doesn't include effects of the current `umask`. For example,
    /// combined with the standard umask `0o022`, the defaults yield `0o600` for
    /// tempfiles and `0o755` for tempdirs.
    ///
    /// ## Windows and others
    ///
    /// This setting is unsupported and trying to set a file or directory
    /// read-only will return an error.
    ///
    /// # Examples
    ///
    /// Create a named temporary file that is world-readable.
    ///
    /// ```
    /// # #[cfg(unix)]
    /// # {
    /// use camino_tempfile::Builder;
    /// use std::os::unix::fs::PermissionsExt;
    ///
    /// let all_read_write = std::fs::Permissions::from_mode(0o666);
    /// let tempfile = Builder::new().permissions(all_read_write).tempfile()?;
    /// let actual_permissions = tempfile.path().metadata()?.permissions();
    /// assert_ne!(
    ///     actual_permissions.mode() & !0o170000,
    ///     0o600,
    ///     "we get broader permissions than the default despite umask"
    /// );
    /// # }
    /// # Ok::<(), std::io::Error>(())
    /// ```
    ///
    /// Create a named temporary directory that is restricted to the owner.
    ///
    /// ```
    /// # #[cfg(unix)]
    /// # {
    /// use camino_tempfile::Builder;
    /// use std::os::unix::fs::PermissionsExt;
    ///
    /// let owner_rwx = std::fs::Permissions::from_mode(0o700);
    /// let tempdir = Builder::new().permissions(owner_rwx).tempdir()?;
    /// let actual_permissions = tempdir.path().metadata()?.permissions();
    /// assert_eq!(
    ///     actual_permissions.mode() & !0o170000,
    ///     0o700,
    ///     "we get the narrow permissions we asked for"
    /// );
    /// # }
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn permissions(&mut self, permissions: std::fs::Permissions) -> &mut Self {
        self.inner.permissions(permissions);
        self
    }

    /// Disable cleanup of the file/folder to even when the
    /// [`NamedUtf8TempFile`]/[`Utf8TempDir`] goes out of scope. Prefer
    /// [`NamedUtf8TempFile::keep`] and [`Utf8TempDir::keep`] where possible,
    /// `disable_cleanup` is provided for testing & debugging.
    ///
    /// By default, the file/folder is automatically cleaned up in the
    /// destructor of [`NamedUtf8TempFile`]/[`Utf8TempDir`]. When
    /// `disable_cleanup` is set to `true`, this behavior is suppressed. If you
    /// wish to disable cleanup after creating a temporary file/directory, call
    /// [`NamedUtf8TempFile::disable_cleanup`] or
    /// [`Utf8TempDir::disable_cleanup`].
    ///
    /// # Warnings
    ///
    /// On some platforms (for now, only Windows), temporary files are marked
    /// with a special "temporary file" (`FILE_ATTRIBUTE_TEMPORARY`) attribute.
    /// Disabling cleanup _will not_ unset this attribute while calling
    /// [`NamedUtf8TempFile::keep`] will.
    ///
    /// # Examples
    ///
    /// ```
    /// use camino_tempfile::Builder;
    ///
    /// let named_tempfile = Builder::new()
    ///     .disable_cleanup(true)
    ///     .tempfile()?;
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn disable_cleanup(&mut self, disable_cleanup: bool) -> &mut Self {
        self.inner.disable_cleanup(disable_cleanup);
        self
    }

    /// Create the named temporary file.
    ///
    /// # Security
    ///
    /// See [the security][security] docs on `NamedUtf8TempFile`.
    ///
    /// # Resource leaking
    ///
    /// See [the resource leaking][resource-leaking] docs on `NamedUtf8TempFile`.
    ///
    /// # Errors
    ///
    /// If the file cannot be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// let tempfile = Builder::new().tempfile()?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [security]: struct.NamedUtf8TempFile.html#security
    /// [resource-leaking]: struct.NamedUtf8TempFile.html#resource-leaking
    pub fn tempfile(&self) -> io::Result<NamedUtf8TempFile> {
        self.tempfile_in(utf8_env_temp_dir()?)
    }

    /// Create the named temporary file in the specified directory.
    ///
    /// # Security
    ///
    /// See [the security][security] docs on `NamedUtf8TempFile`.
    ///
    /// # Resource leaking
    ///
    /// See [the resource leaking][resource-leaking] docs on `NamedUtf8TempFile`.
    ///
    /// # Errors
    ///
    /// If the file cannot be created, `Err` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// let tempfile = Builder::new().tempfile_in("./")?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [security]: struct.NamedUtf8TempFile.html#security
    /// [resource-leaking]: struct.NamedUtf8TempFile.html#resource-leaking
    pub fn tempfile_in<P: AsRef<Utf8Path>>(&self, dir: P) -> io::Result<NamedUtf8TempFile> {
        let temp_file = self.inner.tempfile_in(dir.as_ref())?;
        NamedUtf8TempFile::from_temp_file(temp_file)
    }

    /// Attempts to make a temporary directory inside of [`std::env::temp_dir()`] whose name will
    /// have the prefix, `prefix`. The directory and everything inside it will be automatically
    /// deleted once the returned `Utf8TempDir` is destroyed.
    ///
    /// # Resource leaking
    ///
    /// See [the resource leaking][resource-leaking] docs on `TempDir`.
    ///
    /// # Errors
    ///
    /// If the directory can not be created, or if [`std::env::temp_dir()`] is non-UTF-8, `Err` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use std::io::Write;
    /// use camino_tempfile::Builder;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// let tmp_dir = Builder::new().tempdir()?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [resource-leaking]: struct.Utf8TempDir.html#resource-leaking
    pub fn tempdir(&self) -> io::Result<Utf8TempDir> {
        self.tempdir_in(utf8_env_temp_dir()?)
    }

    /// Attempts to make a temporary directory inside of `dir`.
    /// The directory and everything inside it will be automatically
    /// deleted once the returned `Utf8TempDir` is destroyed.
    ///
    /// # Resource leaking
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
    /// use std::fs::{self, File};
    /// use std::io::Write;
    /// use camino_tempfile::Builder;
    ///
    /// # use std::io;
    /// # fn run() -> Result<(), io::Error> {
    /// let tmp_dir = Builder::new().tempdir_in("./")?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [resource-leaking]: struct.Utf8TempDir.html#resource-leaking
    pub fn tempdir_in<P: AsRef<Utf8Path>>(&self, dir: P) -> io::Result<Utf8TempDir> {
        let temp_dir = self.inner.tempdir_in(dir.as_ref())?;
        Utf8TempDir::from_temp_dir(temp_dir)
    }

    /// Attempts to create a temporary file (or file-like object) using the
    /// provided closure. The closure is passed a temporary file path and
    /// returns an [`std::io::Result`]. The path provided to the closure will be
    /// inside of [`std::env::temp_dir()`]. Use [`Builder::make_in`] to provide
    /// a custom temporary directory. If the closure returns one of the
    /// following errors, then another randomized file path is tried:
    ///  - [`std::io::ErrorKind::AlreadyExists`]
    ///  - [`std::io::ErrorKind::AddrInUse`]
    ///
    /// This can be helpful for taking full control over the file creation, but
    /// leaving the temporary file path construction up to the library. This
    /// also enables creating a temporary UNIX domain socket, since it is not
    /// possible to bind to a socket that already exists.
    ///
    /// Note that [`Builder::append`] is ignored when using [`Builder::make`].
    ///
    /// # Security
    ///
    /// This has the same [security implications][security] as
    /// [`NamedUtf8TempFile`], but with additional caveats. Specifically, it is up
    /// to the closure to ensure that the file does not exist and that such a
    /// check is *atomic*. Otherwise, a [time-of-check to time-of-use
    /// bug][TOCTOU] could be introduced.
    ///
    /// For example, the following is **not** secure:
    ///
    /// ```
    /// # use std::io;
    /// # use std::fs::File;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// // This is NOT secure!
    /// let tempfile = Builder::new().make(|path| {
    ///     if path.is_file() {
    ///         return Err(io::ErrorKind::AlreadyExists.into());
    ///     }
    ///
    ///     // Between the check above and the usage below, an attacker could
    ///     // have replaced `path` with another file, which would get truncated
    ///     // by `File::create`.
    ///
    ///     File::create(path)
    /// })?;
    /// # Ok(())
    /// # }
    /// ```
    /// Note that simply using [`std::fs::File::create`] alone is not correct
    /// because it does not fail if the file already exists:
    /// ```
    /// # use std::io;
    /// # use std::fs::File;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// // This could overwrite an existing file!
    /// let tempfile = Builder::new().make(|path| File::create(path))?;
    /// # Ok(())
    /// # }
    /// ```
    /// For creating regular temporary files, use [`Builder::tempfile`] instead
    /// to avoid these problems. This function is meant to enable more exotic
    /// use-cases.
    ///
    /// # Resource leaking
    ///
    /// See [the resource leaking][resource-leaking] docs on `NamedUtf8TempFile`.
    ///
    /// # Errors
    ///
    /// If the closure returns any error besides
    /// [`std::io::ErrorKind::AlreadyExists`] or
    /// [`std::io::ErrorKind::AddrInUse`], then `Err` is returned.
    ///
    /// # Examples
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// # #[cfg(unix)]
    /// use std::os::unix::net::UnixListener;
    /// # #[cfg(unix)]
    /// let tempsock = Builder::new().make(|path| UnixListener::bind(path))?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [TOCTOU]: https://en.wikipedia.org/wiki/Time-of-check_to_time-of-use
    /// [security]: struct.NamedUtf8TempFile.html#security
    /// [resource-leaking]: struct.NamedUtf8TempFile.html#resource-leaking
    pub fn make<F, R>(&self, f: F) -> io::Result<NamedUtf8TempFile<R>>
    where
        F: FnMut(&Utf8Path) -> io::Result<R>,
    {
        self.make_in(utf8_env_temp_dir()?, f)
    }

    /// This is the same as [`Builder::make`], except `dir` is used as the base
    /// directory for the temporary file path.
    ///
    /// See [`Builder::make`] for more details and security implications.
    ///
    /// # Examples
    /// ```
    /// # use std::io;
    /// # fn main() {
    /// #     if let Err(_) = run() {
    /// #         ::std::process::exit(1);
    /// #     }
    /// # }
    /// # fn run() -> Result<(), io::Error> {
    /// # use camino_tempfile::Builder;
    /// # #[cfg(unix)]
    /// use std::os::unix::net::UnixListener;
    /// # #[cfg(unix)]
    /// let tempsock = Builder::new().make_in("./", |path| UnixListener::bind(path))?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn make_in<F, R, P>(&self, dir: P, mut f: F) -> io::Result<NamedUtf8TempFile<R>>
    where
        F: FnMut(&Utf8Path) -> io::Result<R>,
        P: AsRef<Utf8Path>,
    {
        let temp_file = self.inner.make_in(dir.as_ref(), |path| {
            // This produces a better error message.
            let utf8_path =
                Utf8PathBuf::try_from(path.to_path_buf()).map_err(|error| error.into_io_error())?;
            f(&utf8_path)
        })?;
        NamedUtf8TempFile::from_temp_file(temp_file)
    }
}
