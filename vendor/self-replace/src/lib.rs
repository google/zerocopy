//! `self-replace` is a crate that allows binaries to replace themselves with newer
//! versions or to uninstall themselves.  On Unix systems this is a simple feat, but
//! on Windows a few hacks are needed which is why this crate exists.
//!
//! This is a useful operation when working with single-executable utilties that
//! want to implement a form of self updating or self uninstallation.
//!
//! ## Self Deletion
//!
//! The [`self_delete`] function schedules a binary for self deletion.  On Unix the
//! file system entry is immediately deleted, on Windows the file is deleted after the
//! process shuts down.  Note that you should not use this function to be followed up
//! by a replacement operation, for that use [`self_replace`] as on Windows the file
//! will still be locked.
//!
//! ```
//! # fn foo() -> Result<(), std::io::Error> {
//! self_replace::self_delete()?;
//! # Ok(()) }
//! ```
//!
//! On Windows self deletion requires some place in the folder the deletion is taking
//! place.  This will prevent the abiltiy of the program to also delete the folder the
//! executable is placed in.  To avoid this you can use the [`self_delete_outside_path`]
//! function which will ensure that the deletion does not take place in the path
//! provided if it's possible to do so.  That way you can delete entire structures safely.
//!
//! ```
//! # use std::fs;
//! # fn foo() -> Result<(), std::io::Error> {
//! let itself = std::env::current_exe().unwrap();
//! let parent = itself.parent().unwrap();
//! self_replace::self_delete_outside_path(&parent)?;
//! fs::remove_dir_all(&parent);
//! # Ok(()) }
//! ```
//!
//! ## Self Replacing
//!
//! This replaces the binary with another binary.  The provided path is copied over and
//! if the function successfully completes, you can delete the source binary.
//!
//! ```
//! use std::fs;
//!
//! # fn foo() -> Result<(), std::io::Error> {
//! let new_binary = "/path/to/new/binary";
//! self_replace::self_replace(&new_binary)?;
//! fs::remove_file(&new_binary)?;
//! # Ok(()) }
//! ```
//!
//! ## Implementation
//!
//! The way this is implemented depends on the operating system.  On UNIX systems you
//! can usually not directly write into an executable, but you can swap it out which is
//! exactly what this is doing.  For deleting, the file is just unlinked, for replacing
//! a new file is placed right next to the current executable and an atomic move with
//! `rename` is performed.
//!
//! On Windows the situation is trickier because when an executable launches it can be
//! renamed, but it cannot be unlinked.  This means that we cannot clean up after
//! ourselves easily.  In either case, we first move our executable aside so the name
//! on the file system is made available for the new executable.  Then for both
//! deleting and replacing, we create a copy of our own executable first.  After this we
//! open that copied executable with `FILE_FLAG_DELETE_ON_CLOSE`.  Then we spawn it and
//! wait for our own shut down.
//!
//! This library contains a special glue code that detects this copy of the executable
//! and does nothing else but waiting for the parent to quit and to then delete the
//! parent executable.  There is an extra hack in there in that it spawns another system
//! executable that stays alive until after we shut down to make the self deletion of
//! the copy work.  This is necessary because our running executable must not be the
//! last user of that file handle as otherwise the deletion won't work as the
//! executable still cannot be deleted.  Presumably this is because `CreateProcess`
//! and friends do not open the executable with `FILE_FLAG_DELETE_ON_CLOSE`.
//!
//! **Special note on Windows:** the system will attempt to run the parent deletion logic
//! if the executable has the suffix `.__selfdelete__.exe`.  This means if you
//! name your executable `foo.exe.__selfdelete__.exe`, this logic would kick in.
//!
//! ## Alternatives for Windows
//!
//! Various proposals were made and tried for alternative solutions on Windows.  One
//! quite popular option is to spawn a batch file for the deletion job as a batch file
//! can self delete.  This could be used for both replace and self deletion, but it
//! has the disadvantage that this is a very racy and quite dirty approach as the batch
//! file cannot easily wait for the shutdown of the parent process.
//!
//! For just replaces, co-operation between parent and client could be implemented in
//! simpler terms where first the new executable replaces the old, and then on
//! startup replaces the new one.  There are two downsides of this approach: the first
//! is that it requires that the new replacing executable has matching logic for the
//! cleanup.  The second issue with this approach is that it requires either launching
//! the new executable or waiting for the executable to launch for natural reasons.
//! The former might not always be preferrable, the second leaves files lingering
//! around for an extended period of time.
//!
//! The third, and somewhat official solution is to use `MOVEFILE_DELAY_UNTIL_REBOOT`
//! with `MoveFileEx`.  This causes windows to store an entry in the registry and
//! will perform the delete / move on restart.  This means that if a restart of the
//! machine does not happen, no cleanup is performed.  It also is a privileged
//! operation that is not available to all user accounts.
//!
//! ## Limitations
//!
//! Because files need to be placed temporarily on the file system, there is a chance
//! that if power is cut in just the wrong moment, some files are left over.  These
//! files resemble the original names of the executable prefixed with a dot (`.`) and
//! a random suffix.  The likelihood of this happening should be small.  It's not
//! recommended to run automatic cleanup on startup as the location of those temporary
//! files placed is left undefined.  In many cases the temporary files will be placed
//! in temporary locations and the operating system will take care of the deletion on
//! restart.
use std::io;
use std::path::Path;

#[cfg(unix)]
mod unix;
#[cfg(windows)]
mod windows;

/// Deletes the executable in a platform independent manner.
///
/// The deletion on windows is delayed until the process shuts down.  For updating
/// instead of deleting, use [`self_replace`] instead.  Not that you must only
/// only call this function once during the execution of the program and you should
/// exist quickly afterwards to make the delete take effect on Windows.
///
/// ```
/// # fn foo() -> Result<(), std::io::Error> {
/// self_replace::self_delete()?;
/// # Ok(()) }
/// ```
pub fn self_delete() -> Result<(), io::Error> {
    self_delete_at(std::env::current_exe()?)
}

/// Like [`self_delete`] but accepts a path which is assumed to be the current executable path.
///
/// This can be useful if the executable was moved to a different location while
/// it was running.  Note that on Windows this has no effect on the name given
/// to the temporary files.  They are always based on the original, reported
/// file name of the current executable.
pub fn self_delete_at<P: AsRef<Path>>(exe: P) -> Result<(), io::Error> {
    #[cfg(unix)]
    {
        crate::unix::self_delete(exe.as_ref())
    }
    #[cfg(windows)]
    {
        crate::windows::self_delete(exe.as_ref(), None)
    }
}

/// Like [`self_delete`] but accepts a path which must not be used for temporary operations.
///
/// This is equivalent to [`self_delete`] on Unix, but it instructs the deletion logic to
/// not place temporary files in the given path (or any subdirectory of) for the duration
/// of the deletion operation.  This is necessary to demolish folder more complex folder
/// structures on Windows.
pub fn self_delete_outside_path<P: AsRef<Path>>(p: P) -> Result<(), io::Error> {
    let exe = std::env::current_exe()?;
    #[cfg(unix)]
    {
        let _ = p;
        crate::unix::self_delete(&exe)
    }
    #[cfg(windows)]
    {
        crate::windows::self_delete(&exe, Some(p.as_ref()))
    }
}

/// Replaces the running executable with a different one.
///
/// This replaces the binary with another binary.  The provided path is copied over and
/// if the function successfully completes, you can delete the source binary.
///
/// ```
/// use std::fs;
///
/// # fn foo() -> Result<(), std::io::Error> {
/// let new_binary = "/path/to/new/binary";
/// self_replace::self_replace(&new_binary)?;
/// fs::remove_file(&new_binary)?;
/// # Ok(()) }
/// ```
///
/// Note that after this function concludes, the new executable is already placed at the
/// old location, and the previous executable has been moved to a temporary alternative
/// location.  This also means that if you want to manipulate that file further (for
/// instance to change the permissions) you can do so.
///
/// By default the permissions of the original file are restored.
pub fn self_replace<P: AsRef<Path>>(new_executable: P) -> Result<(), io::Error> {
    #[cfg(unix)]
    {
        crate::unix::self_replace(new_executable.as_ref())
    }
    #[cfg(windows)]
    {
        crate::windows::self_replace(new_executable.as_ref())
    }
}
