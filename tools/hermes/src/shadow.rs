use std::{
    collections::{HashMap, HashSet},
    fs,
    hash::{Hash, Hasher as _},
    path::{Path, PathBuf},
    sync::mpsc::{self, Sender},
};

use anyhow::{Context, Result};
use cargo_metadata::PackageName;
use dashmap::DashSet;
use walkdir::WalkDir;

use crate::{
    parse,
    resolve::{HermesTargetKind, HermesTargetName, Roots},
};

pub struct HermesArtifact {
    pub name: HermesTargetName,
    pub target_kind: HermesTargetKind,
    /// The path to the shadow crate's `Cargo.toml`.
    pub shadow_manifest_path: PathBuf,
    pub start_from: Vec<String>,
}

impl HermesArtifact {
    /// Returns the name of the `.llbc` file to use for this artifact.
    ///
    /// Guarantees uniqueness based on manifest path even if multiple packages
    /// have the same name.
    pub fn llbc_file_name(&self) -> String {
        fn hash<T: Hash>(t: &T) -> u64 {
            let mut s = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }

        // Double-hash to make sure we can distinguish between e.g.
        // (shadow_manifest_path, target_name) = ("abc", "def") and ("ab",
        // "cdef"), which would hash identically if we just hashed their
        // concatenation.
        let h0 = hash(&self.shadow_manifest_path);
        let h1 = hash(&self.name.target_name);
        let h = hash(&[h0, h1]);
        format!("{}-{}-{:08x}.llbc", self.name.package_name, self.name.target_name, h)
    }
}

/// The main entry point for creating the shadow crate.
///
/// 1. Scans and transforms all reachable source files, printing any errors
///    encountered. Collects all items with Hermes annotations.
/// 2. Creates symlinks for the remaining skeleton.
pub fn build_shadow_crate(roots: &Roots) -> Result<Vec<HermesArtifact>> {
    log::trace!("build_shadow_crate({:?})", roots);
    let shadow_root = roots.shadow_root();
    if shadow_root.exists() {
        fs::remove_dir_all(&shadow_root).context("Failed to clear shadow root")?;
    }
    fs::create_dir_all(&shadow_root).context("Failed to create shadow root")?;

    let visited_paths = DashSet::new();
    let (err_tx, err_rx) = mpsc::channel();
    // Items are `((PackageName, TargetName), ItemPath)`.
    let (path_tx, path_rx) = mpsc::channel::<(HermesTargetName, String)>();

    let mut shadow_manifest_paths: HashMap<PackageName, PathBuf> = HashMap::new();
    for target in &roots.roots {
        if !shadow_manifest_paths.contains_key(&target.name.package_name) {
            let relative_manifest_path = find_package_root(&target.src_path)?
                .strip_prefix(&roots.workspace)
                .context("Package root outside workspace")?
                .join("Cargo.toml");
            let shadow_manifest_path = shadow_root.join(&relative_manifest_path);
            shadow_manifest_paths.insert(target.name.package_name.clone(), shadow_manifest_path);
        }
    }

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
        for target in &roots.roots {
            let visited = &visited_paths;
            let (err_tx, path_tx) = (err_tx.clone(), path_tx.clone());
            let roots_ref = roots;

            // These paths are passed to `charon`'s `--start-from` flag, and
            // are interpreted relative to the crate being compiled.
            //
            // TODO: What should we do about items in other crates?
            let initial_prefix = vec!["crate".to_string()];

            s.spawn(move |s| {
                process_file_recursive(
                    s,
                    &target.src_path,
                    roots_ref,
                    visited,
                    err_tx,
                    path_tx,
                    initial_prefix,
                    target.name.clone(),
                )
            });
        }
    });

    // Inform the monitor thread that no more errors will be sent, causing it to
    // exit.
    drop(err_tx);

    let mut entry_points = {
        drop(path_tx);
        let mut entry_points = HashMap::<HermesTargetName, Vec<String>>::new();
        for (name, path) in path_rx {
            entry_points.entry(name).or_default().push(path);
        }
        entry_points
    };

    // Wait for the monitor to finish flushing the errors.
    let count = monitor_handle.join().expect("Error monitor thread panicked");

    if count > 0 {
        return Err(anyhow::anyhow!("Aborting due to {} previous errors.", count));
    }

    let skip_paths: HashSet<PathBuf> = visited_paths.into_iter().collect();
    create_symlink_skeleton(&roots.workspace, &shadow_root, &roots.cargo_target_dir, &skip_paths)?;

    Ok(roots
        .roots
        .iter()
        .filter_map(|target| {
            // We know that every root has a shadow manifest path, because we
            // inserted one for each package that has a root.
            let shadow_manifest_path =
                shadow_manifest_paths.get(&target.name.package_name).unwrap();
            let start_from = entry_points.remove(&target.name)?;

            Some(HermesArtifact {
                name: target.name.clone(),
                target_kind: target.kind,
                shadow_manifest_path: shadow_manifest_path.clone(),
                start_from,
            })
        })
        .collect())
}

/// Walks up the directory tree from the source file to find the directory
/// containing Cargo.toml.
fn find_package_root(src_path: &Path) -> Result<PathBuf> {
    let mut current = src_path;
    while let Some(parent) = current.parent() {
        if parent.join("Cargo.toml").exists() {
            return Ok(parent.to_path_buf());
        }
        current = parent;
    }
    // This is highly unlikely if the path came from cargo metadata.
    anyhow::bail!("Could not find Cargo.toml in any parent of {:?}", src_path)
}

fn process_file_recursive<'a>(
    scope: &rayon::Scope<'a>,
    src_path: &Path,
    config: &'a Roots,
    visited: &'a DashSet<PathBuf>,
    err_tx: Sender<anyhow::Error>,
    path_tx: Sender<(HermesTargetName, String)>,
    module_prefix: Vec<String>,
    name: HermesTargetName,
) {
    log::trace!("process_file_recursive(src_path: {:?})", src_path);
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
    let dest_path = config.shadow_root().join(relative_path);

    let result = (|| -> Result<Vec<(PathBuf, String)>> {
        if let Some(parent) = dest_path.parent() {
            // NOTE: `create_dir_all` is robust against TOCTOU, so it's fine
            // that we're racing with other threads.
            fs::create_dir_all(parent)?;
        }

        // Walk the AST, collecting new modules to process.
        let (source_code, unloaded_modules) =
            parse::read_file_and_scan_compilation_unit(src_path, |_src, item_result| {
                match item_result {
                    Ok(parsed_item) => {
                        if let Some(item_name) = parsed_item.item.name() {
                            // Calculate the full path to this item.
                            let mut full_path = module_prefix.clone();
                            full_path.extend(parsed_item.module_path);
                            full_path.push(item_name);

                            let _ = path_tx.send((name.clone(), full_path.join("::")));
                        }
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

        let buffer = source_code.into_bytes();
        fs::write(&dest_path, &buffer)
            .context(format!("Failed to write shadow file {:?}", dest_path))?;

        // Resolve and queue child modules for processing.
        let base_dir = src_path.parent().unwrap();
        let mut next_paths = Vec::new();
        for module in unloaded_modules {
            if let Some(mod_path) =
                resolve_module_path(base_dir, &module.name, module.path_attr.as_deref())
            {
                next_paths.push((mod_path, module.name));
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
            for (child_path, mod_name) in children {
                let (err_tx, path_tx) = (err_tx.clone(), path_tx.clone());

                let mut new_prefix = module_prefix.clone();
                new_prefix.push(mod_name);

                let name = name.clone();
                scope.spawn(move |s| {
                    process_file_recursive(
                        s,
                        &child_path,
                        config,
                        visited,
                        err_tx,
                        path_tx,
                        new_prefix,
                        name,
                    )
                })
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
    log::trace!(
        "resolve_module_path(base_dir: {:?}, mod_name: {:?}, path_attr: {:?})",
        base_dir,
        mod_name,
        path_attr
    );
    // Handle explicit #[path = "..."]
    if let Some(custom_path) = path_attr {
        let p = base_dir.join(custom_path);
        if p.exists() {
            return Some(p);
        }
        return None;
    }

    // Standard lookup: `foo.rs`
    let inline = base_dir.join(format!("{}.rs", mod_name));
    if inline.exists() {
        return Some(inline);
    }

    // Standard lookup: `foo/mod.rs`
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
    log::trace!("create_symlink_skeleton(source_root: {:?}, dest_root: {:?}, target_dir: {:?}, skip_paths_count: {})", source_root, dest_root, target_dir, skip_paths.len());
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
