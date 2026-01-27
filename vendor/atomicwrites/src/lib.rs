// INSERT_README_VIA_MAKE
#[cfg(unix)]
extern crate rustix;
extern crate tempfile;

use std::convert::AsRef;
use std::error::Error as ErrorTrait;
use std::fmt;
use std::fs;
use std::io;
use std::path;

pub use OverwriteBehavior::{AllowOverwrite, DisallowOverwrite};

/// Whether to allow overwriting if the target file exists.
#[derive(Clone, Copy)]
pub enum OverwriteBehavior {
    /// Overwrite files silently.
    AllowOverwrite,

    /// Don't overwrite files. `AtomicFile.write` will raise errors for such conditions only after
    /// you've already written your data.
    DisallowOverwrite,
}

/// Represents an error raised by `AtomicFile.write`.
#[derive(Debug)]
pub enum Error<E> {
    /// The error originated in the library itself, while it was either creating a temporary file
    /// or moving the file into place.
    Internal(io::Error),
    /// The error originated in the user-supplied callback.
    User(E),
}

/// If your callback returns a `std::io::Error`, you can unwrap this type to `std::io::Error`.
impl From<Error<io::Error>> for io::Error {
    fn from(e: Error<io::Error>) -> Self {
        match e {
            Error::Internal(x) => x,
            Error::User(x) => x,
        }
    }
}

impl<E: fmt::Display> fmt::Display for Error<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Internal(ref e) => e.fmt(f),
            Error::User(ref e) => e.fmt(f),
        }
    }
}

impl<E: ErrorTrait> ErrorTrait for Error<E> {
    fn cause(&self) -> Option<&dyn ErrorTrait> {
        match *self {
            Error::Internal(ref e) => Some(e),
            Error::User(ref e) => Some(e),
        }
    }
}

fn safe_parent(p: &path::Path) -> Option<&path::Path> {
    match p.parent() {
        None => None,
        Some(x) if x.as_os_str().is_empty() => Some(path::Path::new(".")),
        x => x,
    }
}

/// Create a file and write to it atomically, in a callback.
pub struct AtomicFile {
    /// Path to the final file that is atomically written.
    path: path::PathBuf,
    overwrite: OverwriteBehavior,
    /// Directory to which to write the temporary subdirectories.
    tmpdir: path::PathBuf,
}

impl AtomicFile {
    /// Helper for writing to the file at `path` atomically, in write-only mode.
    ///
    /// If `OverwriteBehaviour::DisallowOverwrite` is given,
    /// an `Error::Internal` containing an `std::io::ErrorKind::AlreadyExists`
    /// will be returned from `self.write(...)` if the file exists.
    ///
    /// The temporary file is written to a temporary subdirectory in `.`, to ensure
    /// it’s on the same filesystem (so that the move is atomic).
    pub fn new<P>(path: P, overwrite: OverwriteBehavior) -> Self
    where
        P: AsRef<path::Path>,
    {
        let p = path.as_ref();
        AtomicFile::new_with_tmpdir(
            p,
            overwrite,
            safe_parent(p).unwrap_or_else(|| path::Path::new(".")),
        )
    }

    /// Like `AtomicFile::new`, but the temporary file is written to a temporary subdirectory in `tmpdir`.
    ///
    /// TODO: does `tmpdir` have to exist?
    pub fn new_with_tmpdir<P, Q>(path: P, overwrite: OverwriteBehavior, tmpdir: Q) -> Self
    where
        P: AsRef<path::Path>,
        Q: AsRef<path::Path>,
    {
        AtomicFile {
            path: path.as_ref().to_path_buf(),
            overwrite,
            tmpdir: tmpdir.as_ref().to_path_buf(),
        }
    }

    /// Move the file to `self.path()`. Only call once! Not exposed!
    fn commit(&self, tmppath: &path::Path) -> io::Result<()> {
        match self.overwrite {
            AllowOverwrite => replace_atomic(tmppath, self.path()),
            DisallowOverwrite => move_atomic(tmppath, self.path()),
        }
    }

    /// Get the target filepath.
    pub fn path(&self) -> &path::Path {
        &self.path
    }

    /// Open a temporary file, call `f` on it (which is supposed to write to it), then move the
    /// file atomically to `self.path`.
    ///
    /// The temporary file is written to a randomized temporary subdirectory with prefix `.atomicwrite`.
    pub fn write<T, E, F>(&self, f: F) -> Result<T, Error<E>>
    where
        F: FnOnce(&mut fs::File) -> Result<T, E>,
    {
        let mut options = fs::OpenOptions::new();
        // These are the same options as `File::create`.
        options.write(true).create(true).truncate(true);
        self.write_with_options(f, options)
    }

    /// Open a temporary file with custom [`OpenOptions`], call `f` on it (which is supposed to
    /// write to it), then move the file atomically to `self.path`.
    ///
    /// The temporary file is written to a randomized temporary subdirectory with prefix
    /// `.atomicwrite`.
    ///
    /// [`OpenOptions`]: fs::OpenOptions
    pub fn write_with_options<T, E, F>(&self, f: F, options: fs::OpenOptions) -> Result<T, Error<E>>
    where
        F: FnOnce(&mut fs::File) -> Result<T, E>,
    {
        let tmpdir = tempfile::Builder::new()
            .prefix(".atomicwrite")
            .tempdir_in(&self.tmpdir)
            .map_err(Error::Internal)?;

        let tmppath = tmpdir.path().join("tmpfile.tmp");
        let rv = {
            let mut tmpfile = options.open(&tmppath).map_err(Error::Internal)?;
            let r = f(&mut tmpfile).map_err(Error::User)?;
            tmpfile.sync_all().map_err(Error::Internal)?;
            r
        };
        self.commit(&tmppath).map_err(Error::Internal)?;
        Ok(rv)
    }
}

#[cfg(unix)]
mod imp {
    use super::safe_parent;

    use rustix::fs::AtFlags;
    use std::{fs, io, path};

    pub fn replace_atomic(src: &path::Path, dst: &path::Path) -> io::Result<()> {
        let src_parent_path = safe_parent(src).unwrap();
        let dst_parent_path = safe_parent(dst).unwrap();
        let src_child_path = src.file_name().unwrap();
        let dst_child_path = dst.file_name().unwrap();

        // Open the parent directories. If src and dst have the same parent
        // path, open it once and reuse it.
        let src_parent = fs::File::open(src_parent_path)?;
        let dst_parent;
        let dst_parent = if src_parent_path == dst_parent_path {
            &src_parent
        } else {
            dst_parent = fs::File::open(dst_parent_path)?;
            &dst_parent
        };

        // Do the `renameat`.
        rustix::fs::renameat(&src_parent, src_child_path, dst_parent, dst_child_path)?;

        // Fsync the parent directory (or directories, if they're different).
        src_parent.sync_all()?;
        if src_parent_path != dst_parent_path {
            dst_parent.sync_all()?;
        }

        Ok(())
    }

    pub fn move_atomic(src: &path::Path, dst: &path::Path) -> io::Result<()> {
        let src_parent_path = safe_parent(src).unwrap();
        let dst_parent_path = safe_parent(dst).unwrap();
        let src_child_path = src.file_name().unwrap();
        let dst_child_path = dst.file_name().unwrap();

        // Open the parent directories. If src and dst have the same parent
        // path, open it once and reuse it.
        let src_parent = fs::File::open(src_parent_path)?;
        let dst_parent;
        let dst_parent = if src_parent_path == dst_parent_path {
            &src_parent
        } else {
            dst_parent = fs::File::open(dst_parent_path)?;
            &dst_parent
        };

        // On Linux, use `renameat2` with `RENAME_NOREPLACE` if we have it, as
        // that does an atomic rename.
        #[cfg(any(target_os = "android", target_os = "linux"))]
        {
            use rustix::fs::RenameFlags;
            use std::sync::atomic::AtomicBool;
            use std::sync::atomic::Ordering::Relaxed;

            static NO_RENAMEAT2: AtomicBool = AtomicBool::new(false);
            if !NO_RENAMEAT2.load(Relaxed) {
                match rustix::fs::renameat_with(
                    &src_parent,
                    src_child_path,
                    dst_parent,
                    dst_child_path,
                    RenameFlags::NOREPLACE,
                ) {
                    Ok(()) => {
                        // Fsync the parent directory (or directories, if
                        // they're different).
                        src_parent.sync_all()?;
                        if src_parent_path != dst_parent_path {
                            dst_parent.sync_all()?;
                        }
                        return Ok(());
                    }
                    Err(rustix::io::Errno::INVAL) | Err(rustix::io::Errno::NOSYS) => {
                        // `NOSYS` means the OS doesn't support `renameat2`;
                        // remember this so that we don't bother calling it
                        // again.
                        //
                        // `INVAL` might mean we're on a filesystem that
                        // doesn't support the `NOREPLACE` flag, such as ZFS,
                        // so let's conservatively avoid using `renameat2`
                        // again as well.
                        //
                        // (Or, `INVAL` might mean that the user is trying to
                        // make a directory a subdirectory of itself, in which
                        // case responding by disabling further use of
                        // `renameat2` is unfortunate but what else can we do?)
                        NO_RENAMEAT2.store(true, Relaxed);
                    }
                    Err(e) => return Err(e.into()),
                }
            }
        }

        // Otherwise, hard-link the src to the dst, and then delete the dst.
        rustix::fs::linkat(
            &src_parent,
            src_child_path,
            dst_parent,
            dst_child_path,
            AtFlags::empty(),
        )?;
        rustix::fs::unlinkat(&src_parent, src_child_path, AtFlags::empty())?;

        // Fsync the parent directory (or directories, if they're different).
        src_parent.sync_all()?;
        if src_parent_path != dst_parent_path {
            dst_parent.sync_all()?;
        }

        Ok(())
    }
}

#[cfg(windows)]
mod imp {
    extern crate windows_sys;

    use std::ffi::OsStr;
    use std::os::windows::ffi::OsStrExt;
    use std::{io, path};

    macro_rules! call {
        ($e: expr) => {
            if $e != 0 {
                Ok(())
            } else {
                Err(io::Error::last_os_error())
            }
        };
    }

    fn path_to_windows_str<T: AsRef<OsStr>>(x: T) -> Vec<u16> {
        x.as_ref().encode_wide().chain(Some(0)).collect()
    }

    pub fn replace_atomic(src: &path::Path, dst: &path::Path) -> io::Result<()> {
        call!(unsafe {
            windows_sys::Win32::Storage::FileSystem::MoveFileExW(
                path_to_windows_str(src).as_ptr(),
                path_to_windows_str(dst).as_ptr(),
                windows_sys::Win32::Storage::FileSystem::MOVEFILE_WRITE_THROUGH
                    | windows_sys::Win32::Storage::FileSystem::MOVEFILE_REPLACE_EXISTING,
            )
        })
    }

    pub fn move_atomic(src: &path::Path, dst: &path::Path) -> io::Result<()> {
        call!(unsafe {
            windows_sys::Win32::Storage::FileSystem::MoveFileExW(
                path_to_windows_str(src).as_ptr(),
                path_to_windows_str(dst).as_ptr(),
                windows_sys::Win32::Storage::FileSystem::MOVEFILE_WRITE_THROUGH,
            )
        })
    }
}

/// Move `src` to `dst`. If `dst` exists, it will be silently overwritten.
///
/// Both paths must reside on the same filesystem for the operation to be atomic.
pub fn replace_atomic(src: &path::Path, dst: &path::Path) -> io::Result<()> {
    imp::replace_atomic(src, dst)
}

/// Move `src` to `dst`. An error will be returned if `dst` exists.
///
/// Both paths must reside on the same filesystem for the operation to be atomic.
pub fn move_atomic(src: &path::Path, dst: &path::Path) -> io::Result<()> {
    imp::move_atomic(src, dst)
}
