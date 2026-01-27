//! When working on this, there are a couple of things to test:
//! * Works in Flatpak packages (in Flatpak packages the OpenURI interface is used,
//!   because FileManager1 is not available)
//! * Works with relative file paths
//! * Works with directories (and highlights them)
//! * Weird paths work: paths with spaces, unicode characters, non-unicode characters (e.g. `"\u{01}"`)
//! * Path to non-existent file generates an error for both implementations.

use crate::OpenError;
use std::collections::HashMap;
use std::fs::File;
use std::os::fd::AsFd;
use std::path::Path;
use std::{error, fmt, io};
use url::Url;
use zbus::blocking::Connection;

// We should prefer the OpenURI interface, because it correctly handles runtimes such as Flatpak.
// However, OpenURI was broken in the original version of the interface (it did not highlight the items).
// This version is still in use by some distributions, which would result in degraded functionality for some users.
// That's why we're first trying to use the FileManager1 interface, falling back to the OpenURI interface.
// Source: https://chromium-review.googlesource.com/c/chromium/src/+/3009959
pub(crate) fn reveal_with_dbus(path: &Path) -> Result<(), OpenError> {
    let connection = Connection::session().map_err(dbus_to_open_error)?;
    reveal_with_filemanager1(path, &connection)
        .or_else(|_| reveal_with_open_uri_portal(path, &connection))
}

fn reveal_with_filemanager1(path: &Path, connection: &Connection) -> Result<(), OpenError> {
    let uri = path_to_uri(path)?;
    let proxy = FileManager1Proxy::new(connection).map_err(dbus_to_open_error)?;
    proxy.show_items(&[uri], "").map_err(dbus_to_open_error)
}

fn reveal_with_open_uri_portal(path: &Path, connection: &Connection) -> Result<(), OpenError> {
    let file = File::open(path).map_err(OpenError::Io)?;
    let proxy = OpenURIProxy::new(connection).map_err(dbus_to_open_error)?;
    proxy
        .open_directory("", file.as_fd().into(), HashMap::new())
        .map_err(dbus_to_open_error)
        .map(|_| ())
}

fn path_to_uri(path: &Path) -> Result<Url, OpenError> {
    let path = path.canonicalize().map_err(OpenError::Io)?;
    Url::from_file_path(path).map_err(|_| uri_to_open_error())
}

fn uri_to_open_error() -> OpenError {
    OpenError::Io(io::Error::new(
        io::ErrorKind::InvalidInput,
        FilePathToUriError,
    ))
}

fn dbus_to_open_error(error: zbus::Error) -> OpenError {
    OpenError::Io(io::Error::other(error))
}

#[derive(Debug)]
struct FilePathToUriError;

impl fmt::Display for FilePathToUriError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "The given file path could not be converted to a URI")
    }
}

impl error::Error for FilePathToUriError {}

/// # D-Bus interface proxy for `org.freedesktop.FileManager1` interface.
#[zbus::proxy(
    gen_async = false,
    interface = "org.freedesktop.FileManager1",
    default_service = "org.freedesktop.FileManager1",
    default_path = "/org/freedesktop/FileManager1"
)]
trait FileManager1 {
    /// ShowItems method
    fn show_items(&self, uris: &[Url], startup_id: &str) -> zbus::Result<()>;
}

/// # D-Bus interface proxy for: `org.freedesktop.portal.OpenURI`
#[zbus::proxy(
    gen_async = false,
    interface = "org.freedesktop.portal.OpenURI",
    default_service = "org.freedesktop.portal.Desktop",
    default_path = "/org/freedesktop/portal/desktop"
)]
pub trait OpenURI {
    /// OpenDirectory method
    fn open_directory(
        &self,
        parent_window: &str,
        fd: zbus::zvariant::Fd<'_>,
        options: HashMap<&str, &zbus::zvariant::Value<'_>>,
    ) -> zbus::Result<zbus::zvariant::OwnedObjectPath>;
}
