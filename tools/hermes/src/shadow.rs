use std::{
    collections::HashSet,
    fs,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use walkdir::WalkDir;

// TODO: Call this with `skip_paths` set to all `.rs` files which we've found
// via our traversal using syn.

/// Creates a "Shadow Skeleton" of the source project.
pub fn create_shadow_skeleton(
    source_root: &Path,
    dest_root: &Path,
    target_dir: &Path,
    skip_paths: &HashSet<PathBuf>,
) -> Result<()> {
    let walker = WalkDir::new(source_root)
        .follow_links(false) // Security: don't follow symlinks out of the root.
        .into_iter();

    for entry in walker.filter_entry(|e| e.path() != target_dir && e.file_name() != ".git") {
        let entry = entry.context("Failed to read directory entry")?;
        let src_path = entry.path();

        let relative_path =
            src_path.strip_prefix(source_root).context("File is not inside source root")?;
        let dest_path = dest_root.join(relative_path);

        if entry.file_type().is_dir() {
            fs::create_dir_all(&dest_path)
                .with_context(|| format!("Failed to create shadow directory: {:?}", dest_path))?;
            continue;
        }

        if entry.file_type().is_file() && !skip_paths.contains(src_path) {
            make_symlink(src_path, &dest_path)?;
        }
    }

    Ok(())
}

#[cfg(unix)]
fn make_symlink(original: &Path, link: &Path) -> Result<()> {
    std::os::unix::fs::symlink(original, link)
        .with_context(|| format!("Failed to symlink {:?} -> {:?}", original, link))
}

#[cfg(windows)]
fn make_symlink(original: &Path, link: &Path) -> Result<()> {
    // Windows treats file and directory symlinks differently.
    // Since we only call this on files (checking is_file above),
    // we use symlink_file.
    std::os::windows::fs::symlink_file(original, link)
        .with_context(|| format!("Failed to symlink {:?} -> {:?}", original, link))
}
