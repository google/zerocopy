// Copyright (c) The datatest-stable Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use camino::{Utf8Component, Utf8Path, Utf8PathBuf};

#[derive(Debug)]
#[doc(hidden)]
pub enum DataSource {
    // The path has had normalize_slashes applied to it.
    Directory(Utf8PathBuf),
    #[cfg(feature = "include-dir")]
    IncludeDir(std::borrow::Cow<'static, include_dir::Dir<'static>>),
}

impl DataSource {
    /// Iterates over all files in the data source.
    ///
    /// This returns entries that have just been discovered, so they're expected
    /// to exist.
    pub(crate) fn walk_files(&self) -> Box<dyn Iterator<Item = std::io::Result<TestEntry>> + '_> {
        match self {
            DataSource::Directory(path) => Box::new(iter_directory(path)),
            #[cfg(feature = "include-dir")]
            DataSource::IncludeDir(dir) => Box::new(iter_include_dir(dir)),
        }
    }

    /// Finds a test path from the filter provided.
    ///
    /// The path might or might not exist -- the caller should call `.exists()`
    /// to ensure it does.
    ///
    /// Used for `--exact` matches.
    pub(crate) fn derive_exact(&self, filter: &str, test_name: &str) -> Option<TestEntry> {
        // include_dir 0.7.4 returns paths with forward slashes, including on
        // Windows. But that isn't part of the stable API it seems, so we call
        // `rel_path_to_forward_slashes` anyway.
        let rel_path = rel_path_to_forward_slashes(
            filter.strip_prefix(test_name)?.strip_prefix("::")?.as_ref(),
        );
        match self {
            DataSource::Directory(path) => Some(TestEntry {
                source: TestSource::Path(normalize_slashes(&path.join(&rel_path))),
                rel_path,
            }),
            #[cfg(feature = "include-dir")]
            DataSource::IncludeDir(dir) => {
                let file = dir.get_file(&rel_path)?;
                Some(TestEntry {
                    source: TestSource::IncludeDir(file),
                    rel_path,
                })
            }
        }
    }

    /// Returns true if data is not available on disk and must be provided from
    /// an in-memory buffer.
    pub(crate) fn is_in_memory(&self) -> bool {
        match self {
            DataSource::Directory(_) => false,
            #[cfg(feature = "include-dir")]
            DataSource::IncludeDir(_) => true,
        }
    }

    pub(crate) fn display(&self) -> String {
        match self {
            DataSource::Directory(path) => format!("directory: `{path}`"),
            #[cfg(feature = "include-dir")]
            DataSource::IncludeDir(_) => "included directory".to_string(),
        }
    }
}

fn iter_directory(root: &Utf8Path) -> impl Iterator<Item = std::io::Result<TestEntry>> + '_ {
    walkdir::WalkDir::new(root)
        .into_iter()
        .filter(|res| {
            // Continue to bubble up all errors to the parent.
            res.as_ref().map_or(true, |entry| {
                entry.file_type().is_file()
                    && entry
                        .file_name()
                        .to_str()
                        .is_some_and(|s| !s.starts_with('.')) // Skip hidden files
            })
        })
        .map(move |res| match res {
            Ok(entry) => {
                let path = Utf8PathBuf::try_from(entry.into_path())
                    .map_err(|error| error.into_io_error())?;
                Ok(TestEntry::from_full_path(root, path))
            }
            Err(error) => Err(error.into()),
        })
}

#[cfg(feature = "include-dir")]
fn iter_include_dir<'a>(
    dir: &'a include_dir::Dir<'static>,
) -> impl Iterator<Item = std::io::Result<TestEntry>> + 'a {
    // Need to maintain a stack to do a depth-first traversal.
    struct IncludeDirIter<'a> {
        stack: Vec<&'a include_dir::DirEntry<'a>>,
    }

    impl<'a> Iterator for IncludeDirIter<'a> {
        type Item = &'a include_dir::File<'a>;

        fn next(&mut self) -> Option<Self::Item> {
            while let Some(entry) = self.stack.pop() {
                match entry {
                    include_dir::DirEntry::File(file) => {
                        return Some(file);
                    }
                    include_dir::DirEntry::Dir(dir) => {
                        self.stack.extend(dir.entries());
                    }
                }
            }

            None
        }
    }

    IncludeDirIter {
        stack: dir.entries().iter().collect(),
    }
    .map(|file| {
        // include_dir 0.7.4 returns paths with forward slashes, including on
        // Windows. But that isn't part of the stable API it seems, so we call
        // `rel_path_to_forward_slashes` anyway.
        let rel_path = match file.path().try_into() {
            Ok(path) => rel_path_to_forward_slashes(path),
            Err(error) => {
                return Err(error.into_io_error());
            }
        };
        Ok(TestEntry {
            source: TestSource::IncludeDir(file),
            rel_path,
        })
    })
}

#[derive(Debug)]
pub(crate) struct TestEntry {
    source: TestSource,
    rel_path: Utf8PathBuf,
}

impl TestEntry {
    pub(crate) fn from_full_path(root: &Utf8Path, path: Utf8PathBuf) -> Self {
        let path = normalize_slashes(&path);
        let rel_path =
            rel_path_to_forward_slashes(path.strip_prefix(root).unwrap_or_else(|_| {
                panic!("failed to strip root '{}' from path '{}'", root, path)
            }));
        Self {
            source: TestSource::Path(path),
            rel_path,
        }
    }

    pub(crate) fn derive_test_name(&self, test_name: &str) -> String {
        format!("{}::{}", test_name, self.rel_path)
    }

    pub(crate) fn read(&self) -> crate::Result<Vec<u8>> {
        match &self.source {
            TestSource::Path(path) => std::fs::read(path)
                .map_err(|err| format!("error reading file '{path}': {err}").into()),
            #[cfg(feature = "include-dir")]
            TestSource::IncludeDir(file) => Ok(file.contents().to_vec()),
        }
    }

    pub(crate) fn read_as_string(&self) -> crate::Result<String> {
        match &self.source {
            TestSource::Path(path) => std::fs::read_to_string(path)
                .map_err(|err| format!("error reading file '{path}' as UTF-8: {err}").into()),
            #[cfg(feature = "include-dir")]
            TestSource::IncludeDir(file) => {
                let contents = file.contents().to_vec();
                String::from_utf8(contents).map_err(|err| {
                    format!(
                        "error reading included file at '{}' as UTF-8: {err}",
                        self.rel_path
                    )
                    .into()
                })
            }
        }
    }

    /// Returns the path to match regexes against.
    ///
    /// This is always the relative path to the file from the include directory.
    pub(crate) fn match_path(&self) -> &Utf8Path {
        &self.rel_path
    }

    /// Returns the path to the test data, as passed into the test function.
    ///
    /// For directories on disk, this is the relative path after being joined
    /// with the include directory. For `include_dir` sources, this is the path
    /// relative to the root of the include directory.
    pub(crate) fn test_path(&self) -> &Utf8Path {
        match &self.source {
            TestSource::Path(path) => path,
            #[cfg(feature = "include-dir")]
            TestSource::IncludeDir(_) => {
                // The UTF-8-encoded version of file.path is stored in `rel_path`.
                &self.rel_path
            }
        }
    }

    /// Returns the path to the file on disk.
    ///
    /// If the data source is an `include_dir`, this will return `None`.
    pub(crate) fn disk_path(&self) -> Option<&Utf8Path> {
        match &self.source {
            TestSource::Path(path) => Some(path),
            #[cfg(feature = "include-dir")]
            TestSource::IncludeDir(_) => None,
        }
    }

    /// Returns true if the path exists.
    pub(crate) fn exists(&self) -> bool {
        match &self.source {
            TestSource::Path(path) => path.exists(),
            #[cfg(feature = "include-dir")]
            TestSource::IncludeDir(_) => {
                // include_dir files are guaranteed to exist.
                true
            }
        }
    }
}

#[cfg(windows)]
#[track_caller]
fn normalize_slashes(path: &Utf8Path) -> Utf8PathBuf {
    if is_truly_relative(path) {
        rel_path_to_forward_slashes(path)
    } else {
        path.as_str().replace('/', "\\").into()
    }
}

#[cfg(windows)]
#[track_caller]
fn rel_path_to_forward_slashes(path: &Utf8Path) -> Utf8PathBuf {
    assert!(is_truly_relative(path), "path {path} must be relative");
    path.as_str().replace('\\', "/").into()
}

#[cfg(not(windows))]
#[track_caller]
fn normalize_slashes(path: &Utf8Path) -> Utf8PathBuf {
    path.to_owned()
}

#[cfg(not(windows))]
#[track_caller]
fn rel_path_to_forward_slashes(path: &Utf8Path) -> Utf8PathBuf {
    assert!(is_truly_relative(path), "path {path} must be relative");
    path.to_owned()
}

/// Returns true if this is a path with no root-dir or prefix components.
///
/// On Windows, unlike `path.is_relative()`, this rejects paths like "C:temp"
/// and "\temp".
#[track_caller]
fn is_truly_relative(path: &Utf8Path) -> bool {
    path.components().all(|c| match c {
        Utf8Component::Normal(_) | Utf8Component::CurDir | Utf8Component::ParentDir => true,
        Utf8Component::RootDir | Utf8Component::Prefix(_) => false,
    })
}

#[derive(Debug)]
#[doc(hidden)]
pub(crate) enum TestSource {
    /// A data source on disk, with the path being the relative path to the file
    /// from the crate root.
    Path(Utf8PathBuf),
    #[cfg(feature = "include-dir")]
    IncludeDir(&'static include_dir::File<'static>),
}

/// Polymorphic dispatch to resolve data sources
///
/// This is similar to how `test_kinds` works. Here, we're assuming that
/// `include_dir::Dir` will never implement `ToString`. This isn't provable to
/// the compiler directly, but is a reasonable assumption.
///
/// This could use auto(de)ref specialization to be more semver-safe, but a
/// `Display` impl on `include_dir::Dir` is exceedingly unlikely by Rust
/// community standards, and meanwhile this produces better error messages.
#[doc(hidden)]
pub mod data_source_kinds {
    use super::*;

    mod private {
        pub trait AsDirectorySealed {}
        #[cfg(feature = "include-dir")]
        pub trait AsIncludeDirSealed {}
    }

    // -- As directory ---

    pub trait AsDirectory: private::AsDirectorySealed {
        fn resolve_data_source(self) -> DataSource;
    }

    impl<T: ToString> private::AsDirectorySealed for T {}

    impl<T: ToString> AsDirectory for T {
        fn resolve_data_source(self) -> DataSource {
            let s = self.to_string();
            let path = Utf8Path::new(&s);

            DataSource::Directory(normalize_slashes(path))
        }
    }

    #[cfg(feature = "include-dir")]
    pub trait AsIncludeDir: private::AsIncludeDirSealed {
        fn resolve_data_source(self) -> DataSource;
    }

    #[cfg(feature = "include-dir")]
    impl private::AsIncludeDirSealed for include_dir::Dir<'static> {}

    #[cfg(feature = "include-dir")]
    impl AsIncludeDir for include_dir::Dir<'static> {
        fn resolve_data_source(self) -> DataSource {
            DataSource::IncludeDir(std::borrow::Cow::Owned(self))
        }
    }

    #[cfg(feature = "include-dir")]
    impl private::AsIncludeDirSealed for &'static include_dir::Dir<'static> {}

    #[cfg(feature = "include-dir")]
    impl AsIncludeDir for &'static include_dir::Dir<'static> {
        fn resolve_data_source(self) -> DataSource {
            DataSource::IncludeDir(std::borrow::Cow::Borrowed(self))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_test_name() {
        assert_eq!(derive_test_path("root".into(), "file", "test_name"), None);
    }

    #[test]
    fn missing_colons() {
        assert_eq!(
            derive_test_path("root".into(), "test_name", "test_name"),
            None
        );
    }

    #[test]
    fn is_relative_to_root() {
        assert_eq!(
            derive_test_path("root".into(), "test_name::file", "test_name"),
            Some("root/file".into())
        );
        assert_eq!(
            derive_test_path("root2".into(), "test_name::file", "test_name"),
            Some("root2/file".into())
        );
    }

    #[test]
    fn nested_dirs() {
        assert_eq!(
            derive_test_path("root".into(), "test_name::dir/dir2/file", "test_name"),
            Some("root/dir/dir2/file".into())
        );
    }

    #[test]
    fn subsequent_module_separators_remain() {
        assert_eq!(
            derive_test_path("root".into(), "test_name::mod::file", "test_name"),
            Some("root/mod::file".into())
        );
    }

    #[test]
    fn inverse_of_derive_test_name() {
        let root: Utf8PathBuf = "root".into();
        for (path, test_name) in [
            (root.join("foo/bar.txt"), "test_name"),
            (root.join("foo::bar.txt"), "test_name"),
            (root.join("foo/bar/baz"), "test_name"),
            (root.join("foo"), "test_name::mod"),
            (root.join("🦀"), "🚀::🚀"),
        ] {
            let derived_test_name = derive_test_name(&root, &path, test_name);
            assert_eq!(
                derive_test_path(&root, &derived_test_name, test_name),
                Some(path)
            );
        }
    }

    fn derive_test_name(root: &Utf8Path, path: &Utf8Path, test_name: &str) -> String {
        TestEntry::from_full_path(root, path.to_owned()).derive_test_name(test_name)
    }

    fn derive_test_path(root: &Utf8Path, path: &str, test_name: &str) -> Option<Utf8PathBuf> {
        DataSource::Directory(root.to_owned())
            .derive_exact(path, test_name)
            .map(|entry| entry.test_path().to_owned())
    }
}
