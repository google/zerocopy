use std::{
    collections::HashSet,
    fs,
    path::{Path, PathBuf},
    sync::mpsc::Sender,
};

use anyhow::{Context, Result};
use dashmap::DashSet;
use walkdir::WalkDir;

use crate::{parse, resolve::Roots, transform};

/// The main entry point for creating the shadow crate.
///
/// 1. Scans and transforms all reachable source files, printing any errors
///    encountered.
/// 2. Creates symlinks for the remaining skeleton.
pub fn build_shadow_crate(roots: &Roots) -> Result<()> {
    if roots.shadow_root.exists() {
        fs::remove_dir_all(&roots.shadow_root).context("Failed to clear shadow root")?;
    }
    fs::create_dir_all(&roots.shadow_root).context("Failed to create shadow root")?;

    let visited_paths = DashSet::new();
    let (err_tx, err_rx) = std::sync::mpsc::channel();

    let monitor_handle = std::thread::spawn(move || {
        let mut error_count = 0;
        for err in err_rx {
            if error_count == 0 {
                eprintln!("\n=== Hermes Verification Failed ===");
            }
            error_count += 1;
            // Use eprintln! to print immediately to stderr
            eprintln!("\n[Hermes Error] {:#}", err);
        }
        error_count
    });

    rayon::scope(|s| {
        for (_, _, root_path) in &roots.roots {
            let visited = &visited_paths;
            let tx = err_tx.clone();
            let roots_ref = roots;

            s.spawn(move |s| process_file_recursive(s, root_path, roots_ref, visited, tx));
        }
    });

    // Inform the monitor thread that no more errors will be sent, causing it to
    // exit.
    drop(err_tx);

    // Wait for the monitor to finish flushing the errors.
    let count = monitor_handle.join().expect("Error monitor thread panicked");

    if count > 0 {
        return Err(anyhow::anyhow!("Aborting due to {} previous errors.", count));
    }

    let skip_paths: HashSet<PathBuf> = visited_paths.into_iter().collect();

    create_symlink_skeleton(
        &roots.workspace,
        &roots.shadow_root,
        &roots.cargo_target_dir,
        &skip_paths,
    )?;

    Ok(())
}

/// Recursive worker function.
///
/// * `scope`: The Rayon scope to spawn new work into.
/// * `src_path`: The absolute path of the file to process.
/// * `config`: Global configuration (paths).
/// * `visited`: Shared set of processed files.
/// * `err_tx`: Channel to report errors.
fn process_file_recursive<'a>(
    scope: &rayon::Scope<'a>,
    src_path: &Path,
    config: &'a Roots,
    visited: &'a DashSet<PathBuf>,
    err_tx: Sender<anyhow::Error>,
) {
    if !visited.insert(src_path.to_path_buf()) {
        return;
    }

    // shadow_root + (src_path - workspace_root)
    let relative_path = match src_path.strip_prefix(&config.workspace) {
        Ok(p) => p,
        Err(e) => {
            let _ = err_tx.send(anyhow::anyhow!("Source file outside workspace: {:?}", e));
            return;
        }
    };
    let dest_path = config.shadow_root.join(relative_path);

    let result = (|| -> Result<Vec<PathBuf>> {
        if let Some(parent) = dest_path.parent() {
            // NOTE: `create_dir_all` is robust against TOCTOU, so it's fine
            // that we're racing with other threads.
            fs::create_dir_all(parent)?;
        }

        // Walk the AST, collecting edits and new modules to process.
        let mut edits = Vec::new();
        let (source_code, unloaded_modules) =
            parse::read_file_and_scan_compilation_unit(src_path, |_src, item_result| {
                match item_result {
                    Ok(parsed_item) => {
                        transform::append_edits(&parsed_item, &mut edits);
                    }
                    Err(e) => {
                        // A parsing error means we either:
                        // 1. Lost the module graph, causing missing files later.
                        // 2. Lost a specification, causing unsound verification.
                        // We must abort the build.
                        let _ = err_tx.send(anyhow::anyhow!(e));
                    }
                }
            })
            .context(format!("Failed to parse {:?}", src_path))?;

        // Apply edits in-place before writing to disk.
        let mut buffer = source_code.into_bytes();
        transform::apply_edits(&mut buffer, &edits);
        fs::write(&dest_path, &buffer)
            .context(format!("Failed to write shadow file {:?}", dest_path))?;

        // Resolve and queue child modules for processing.
        let base_dir = src_path.parent().unwrap();
        let mut next_paths = Vec::new();
        for module in unloaded_modules {
            if let Some(mod_path) =
                resolve_module_path(base_dir, &module.name, module.path_attr.as_deref())
            {
                next_paths.push(mod_path);
            } else {
                // This is an expected condition – it shows up when modules are
                // conditionally compiled. Instead of implementing conditional
                // compilation ourselves, we can just let rustc error later if
                // this is actually an error.
                log::debug!("Could not resolve module '{}' in {:?}", module.name, src_path);
            }
        }

        Ok(next_paths)
    })();

    match result {
        Ok(children) => {
            // Spawn new tasks for discovered modules.
            for child_path in children {
                let tx = err_tx.clone();
                scope.spawn(move |s| process_file_recursive(s, &child_path, config, visited, tx));
            }
        }
        Err(e) => {
            let _ = err_tx.send(e);
        }
    }
}

/// Resolves a module name to a file path, checking standard Rust locations.
///
/// * `base_dir`: The directory containing the parent file.
/// * `mod_name`: The name of the module (e.g., "foo").
/// * `path_attr`: The optional `#[path = "..."]` attribute string.
fn resolve_module_path(
    base_dir: &Path,
    mod_name: &str,
    path_attr: Option<&str>,
) -> Option<PathBuf> {
    // 1. Handle explicit #[path = "..."]
    if let Some(custom_path) = path_attr {
        let p = base_dir.join(custom_path);
        if p.exists() {
            return Some(p);
        }
        return None;
    }

    // 2. Standard lookup: `foo.rs`
    let inline = base_dir.join(format!("{}.rs", mod_name));
    if inline.exists() {
        return Some(inline);
    }

    // 3. Standard lookup: `foo/mod.rs`
    let nested = base_dir.join(mod_name).join("mod.rs");
    if nested.exists() {
        return Some(nested);
    }

    None
}

fn create_symlink_skeleton(
    source_root: &Path,
    dest_root: &Path,
    target_dir: &Path,
    skip_paths: &HashSet<PathBuf>,
) -> Result<()> {
    let walker = WalkDir::new(source_root)
        .follow_links(false) // Security: don't follow symlinks out of the root.
        .into_iter();

    let filter = |e: &walkdir::DirEntry| {
        let p = e.path();
        // Normally, we expect the `dest_root` to be inside of `target_dir`,
        // so checking both is redundant. However, if we ever add the option
        // for the user to manually specify a `dest_root` that is outside of
        // `target_dir`, this check will prevent us from infinitely recursing
        // into the source root.
        p != target_dir && p != dest_root && e.file_name() != ".git"
    };

    for entry in walker.filter_entry(filter) {
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
