// Copyright (c) The enable-ansi-support Contributors
// SPDX-License-Identifier: MIT

//! Enable ANSI code support on Windows 10 and above.
//!
//! This crate provides one function, `enable_ansi_support`, which allows [ANSI escape codes]
//! to work on Windows 10 and above.
//!
//! Call `enable_ansi_support` *once*, early on in `main()`, to enable ANSI escape codes generated
//! by crates like
//! [`ansi_term`](https://docs.rs/ansi_term) or [`owo-colors`](https://docs.rs/owo-colors)
//! to work on Windows just like they do on Unix platforms.
//!
//! ## Examples
//!
//! ```rust
//! fn main() {
//!     match enable_ansi_support::enable_ansi_support() {
//!         Ok(()) => {
//!             // ANSI escape codes were successfully enabled, or this is a non-Windows platform.
//!             println!("\x1b[31mHello, world\x1b[0m");
//!         }
//!         Err(_) => {
//!             // The operation was unsuccessful, typically because it's running on an older
//!             // version of Windows. The program may choose to disable ANSI color code output in
//!             // this case.
//!         }
//!     }
//!
//!     // Use your terminal color library of choice here.
//! }
//! ```
//!
//! ## How it works
//!
//! `enable_ansi_support` uses Windows API calls to alter the properties of the console that
//! the program is running in. See the
//! [Windows documentation](https://docs.microsoft.com/en-us/windows/console/console-virtual-terminal-sequences)
//! for more information.
//!
//! On non-Windows platforms, `enable_ansi_support` is a no-op.
//!
//! [ANSI escape codes]: https://en.wikipedia.org/wiki/ANSI_escape_code
#![allow(clippy::needless_doctest_main)]

/// Enables ANSI code support on Windows 10.
///
/// Returns an [`io::Error`](std::io::Error) with the Windows error code in it if unsuccessful.
///
/// On non-Windows platforms, this is a no-op that always returns `Ok(())`.
///
/// # Examples
///
/// See the [crate documentation](crate).
#[cfg(windows)]
pub fn enable_ansi_support() -> Result<(), std::io::Error> {
    // ref: https://docs.microsoft.com/en-us/windows/console/console-virtual-terminal-sequences#EXAMPLE_OF_ENABLING_VIRTUAL_TERMINAL_PROCESSING @@ https://archive.is/L7wRJ#76%

    use std::{ffi::OsStr, iter::once, os::windows::ffi::OsStrExt};

    use windows_sys::Win32::{
        Foundation::INVALID_HANDLE_VALUE,
        Storage::FileSystem::{
            CreateFileW, FILE_GENERIC_READ, FILE_GENERIC_WRITE, FILE_SHARE_WRITE, OPEN_EXISTING,
        },
        System::Console::{ENABLE_VIRTUAL_TERMINAL_PROCESSING, GetConsoleMode, SetConsoleMode},
    };

    unsafe {
        // ref: https://docs.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-createfilew
        // Using `CreateFileW("CONOUT$", ...)` to retrieve the console handle works correctly even if STDOUT and/or STDERR are redirected
        let console_out_name: Vec<u16> =
            OsStr::new("CONOUT$").encode_wide().chain(once(0)).collect();
        let console_handle = CreateFileW(
            console_out_name.as_ptr(),
            FILE_GENERIC_READ | FILE_GENERIC_WRITE,
            FILE_SHARE_WRITE,
            std::ptr::null(),
            OPEN_EXISTING,
            0,
            std::ptr::null_mut(),
        );
        if console_handle == INVALID_HANDLE_VALUE {
            return Err(std::io::Error::last_os_error());
        }

        // ref: https://docs.microsoft.com/en-us/windows/console/getconsolemode
        let mut console_mode = 0;
        if 0 == GetConsoleMode(console_handle, &mut console_mode) {
            return Err(std::io::Error::last_os_error());
        }

        // VT processing not already enabled?
        if console_mode & ENABLE_VIRTUAL_TERMINAL_PROCESSING == 0 {
            // https://docs.microsoft.com/en-us/windows/console/setconsolemode
            if 0 == SetConsoleMode(
                console_handle,
                console_mode | ENABLE_VIRTUAL_TERMINAL_PROCESSING,
            ) {
                return Err(std::io::Error::last_os_error());
            }
        }
    }

    Ok(())
}

/// Enables ANSI code support on Windows 10.
///
/// Returns an [`io::Error`](std::io::Error) with the Windows error code in it if unsuccessful.
///
/// On non-Windows platforms, this is a no-op that always returns `Ok(())`.
///
/// # Examples
///
/// See the [crate documentation](crate).
#[cfg(not(windows))]
#[inline]
pub fn enable_ansi_support() -> Result<(), std::io::Error> {
    Ok(())
}
