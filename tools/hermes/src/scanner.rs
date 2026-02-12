use std::{
    collections::HashMap,
    ffi::OsStr,
    hash::{Hash, Hasher as _},
    path::{Path, PathBuf},
    sync::mpsc::{self, Sender},
};

use anyhow::Result;

use crate::{
    parse,
    resolve::{HermesTargetKind, HermesTargetName, Roots},
};

pub struct HermesArtifact {
    pub name: HermesTargetName,
    pub target_kind: HermesTargetKind,
    /// The path to the crate's `Cargo.toml`.
    pub manifest_path: PathBuf,
    pub start_from: Vec<String>,
}

impl HermesArtifact {
    /// Returns a unique "slug" for this artifact, used for file naming.
    ///
    /// Guarantees uniqueness based on manifest path even if multiple packages
    /// have the same name.
    ///
    /// Format: `{package_name}-{target_name}-{hash:08x}`
    pub fn artifact_slug(&self) -> String {
        fn hash<T: Hash>(t: &T) -> u64 {
            let mut s = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }

        // Double-hash to make sure we can distinguish between e.g.
        // (manifest_path, target_name) = ("abc", "def") and ("ab", "cdef"),
        // which would hash identically if we just hashed their concatenation.
        let h0 = hash(&self.manifest_path);
        let h1 = hash(&self.name.target_name);
        let h2 = hash(&self.target_kind);
        let h = hash(&[h0, h1, h2]);

        format!("{}-{}-{:08x}", self.name.package_name, self.name.target_name, h)
    }

    /// Returns the name of the `.llbc` file to use for this artifact.
    pub fn llbc_file_name(&self) -> String {
        format!("{}.llbc", self.artifact_slug())
    }
}

/// Scans the workspace to identify Hermes entry points (`/// ```lean` blocks)
/// and collects targets for verification.
pub fn scan_workspace(roots: &Roots) -> Result<Vec<HermesArtifact>> {
    log::trace!("scan_workspace({:?})", roots);

    let (err_tx, err_rx) = mpsc::channel();
    // Items are `((PackageName, TargetName), ItemPath)`.
    let (path_tx, path_rx) = mpsc::channel::<(HermesTargetName, String)>();

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
                    err_tx,
                    path_tx,
                    initial_prefix,
                    target.name.clone(),
                    false, // Initial call is top-level, so not inside block
                    Vec::new(),
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

    Ok(roots
        .roots
        .iter()
        .filter_map(|target| {
            let manifest_path = target.manifest_path.clone();
            let start_from = entry_points.remove(&target.name)?;

            Some(HermesArtifact {
                name: target.name.clone(),
                target_kind: target.kind,
                manifest_path,
                start_from,
            })
        })
        .collect())
}

// NOTE: It might be tempting to try to deduplicate files to avoid re-processing
// a file that is reachable via multiple paths. However, this is incorrect, as
// this only happens if the file is named in multiple `#[path]` attributes, in
// which case it logically constitutes a distinct module each time it is
// referenced.
fn process_file_recursive<'a>(
    scope: &rayon::Scope<'a>,
    src_path: &Path,
    config: &'a Roots,
    err_tx: Sender<anyhow::Error>,
    path_tx: Sender<(HermesTargetName, String)>,
    current_prefix: Vec<String>,
    name: HermesTargetName,
    inside_block: bool,
    ancestors: Vec<PathBuf>,
) {
    log::trace!("process_file_recursive(src_path: {:?})", src_path);

    // Canonicalize the path to ensure we don't process the same file multiple
    // times (e.g. via symlinks or different relative paths).
    let src_path = match std::fs::canonicalize(src_path) {
        Ok(p) => p,
        Err(e) => {
            // It is valid for a module to be declared but not exist (e.g., if
            // it is cfg-gated for another platform). In strict Rust, we would
            // check the cfg attributes, but since we are just scanning, it is
            // safe to warn and return.
            log::debug!("Skipping unreachable or missing file {:?}: {}", src_path, e);
            return;
        }
    };

    // Cycle detection: prevent infinite recursion on symlinks or recursive mod
    // declarations, while still allowing identical files to be mounted in
    // different branches of the tree. A cycle would represent an invalid crate
    // anyway (i.e., an invalid set of `#[path]` attributes).
    if ancestors.contains(&src_path) {
        return;
    }
    let mut current_ancestors = ancestors.clone();
    current_ancestors.push(src_path.clone());

    let result = parse::read_file_and_scan_compilation_unit(
        &src_path,
        inside_block,
        |_src, res| match res {
            Ok(item) => {
                let mut full_path = current_prefix.clone();
                full_path.extend(item.module_path);

                match &item.item {
                    // Unreliable syntaxes: we have no way of reliably naming
                    // these in Charon's `--start-from` argument, so we fall
                    // back to naming the parent module.
                    parse::ParsedItem::Impl(_) => {
                        let start_from = full_path.join("::");
                        path_tx.send((name.clone(), start_from)).unwrap();
                    }
                    parse::ParsedItem::Function(f) => match &f.item {
                        parse::FunctionItem::Impl(_) | parse::FunctionItem::Trait(_) => {
                            let start_from = full_path.join("::");
                            path_tx.send((name.clone(), start_from)).unwrap();
                        }
                        parse::FunctionItem::Free(_) => {
                            if let Some(item_name) = item.item.name() {
                                full_path.push(item_name);
                                let start_from = full_path.join("::");
                                log::debug!("Found entry point: {}", start_from);
                                path_tx.send((name.clone(), start_from)).unwrap();
                            }
                        }
                    },
                    // Reliable syntaxes: target the specific item.
                    _ => {
                        if let Some(item_name) = item.item.name() {
                            full_path.push(item_name);
                            let start_from = full_path.join("::");
                            log::debug!("Found entry point: {}", start_from);
                            path_tx.send((name.clone(), start_from)).unwrap();
                        }
                    }
                }
            }
            Err(e) => {
                let _ = err_tx.send(e.into());
            }
        },
    );

    let (_, unloaded_modules) = match result {
        Ok(res) => res,
        Err(e) => {
            let _ = err_tx.send(e.into());
            return;
        }
    };

    // Determine the directory to search for child modules in.
    // - For `mod.rs`, `lib.rs`, `main.rs`, children are in the parent directory.
    //   e.g. `src/lib.rs` -> `mod foo` -> `src/foo.rs`
    // - For `my_mod.rs`, children are in a sibling directory of the same name.
    //   e.g. `src/my_mod.rs` -> `mod sub` -> `src/my_mod/sub.rs`
    let file_stem = src_path.file_stem().and_then(OsStr::to_str).unwrap_or("");
    let base_dir = if matches!(file_stem, "mod" | "lib" | "main") {
        src_path.parent().unwrap_or(&src_path).to_path_buf()
    } else {
        // e.g. src/foo.rs -> src/foo/
        src_path.with_extension("")
    };

    // Resolve and queue child modules for processing.
    for module in unloaded_modules {
        if let Some(mod_path) =
            resolve_module_path(&base_dir, &module.name, module.path_attr.as_deref())
        {
            // Spawn new tasks for discovered modules.
            let (err_tx, path_tx) = (err_tx.clone(), path_tx.clone());

            let mut new_prefix = current_prefix.clone();
            new_prefix.push(module.name);

            let name = name.clone();
            // TODO: Can we do something more efficient than cloning here? Maybe
            // a linked list?
            let ancestors = current_ancestors.clone();
            scope.spawn(move |s| {
                process_file_recursive(
                    s,
                    &mod_path,
                    config,
                    err_tx,
                    path_tx,
                    new_prefix,
                    name,
                    module.inside_block,
                    ancestors,
                )
            })
        } else {
            // This is an expected condition – it shows up when modules are
            // conditionally compiled. Instead of implementing conditional
            // compilation ourselves, we can just let rustc error later if
            // this is actually an error.
            log::debug!("Could not resolve module '{}' in {:?}", module.name, src_path);
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

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use cargo_metadata::PackageName;

    use super::*;
    use crate::resolve::{HermesTargetKind, HermesTargetName};

    #[test]
    fn test_llbc_file_name_collision() {
        let name_lib = HermesTargetName {
            package_name: PackageName::new("pkg".to_string()),
            target_name: "name".to_string(),
            kind: HermesTargetKind::Lib,
        };

        let artifact_lib = HermesArtifact {
            name: name_lib,
            target_kind: HermesTargetKind::Lib,
            manifest_path: PathBuf::from("Cargo.toml"),
            start_from: vec![],
        };

        let name_bin = HermesTargetName {
            package_name: PackageName::new("pkg".to_string()),
            target_name: "name".to_string(),
            kind: HermesTargetKind::Bin,
        };

        let artifact_bin = HermesArtifact {
            name: name_bin,
            target_kind: HermesTargetKind::Bin,
            manifest_path: PathBuf::from("Cargo.toml"),
            start_from: vec![],
        };

        // Verify that the file names are distinct, and that they're distinct
        // *because of the trailing hash* (ie, that they have identical
        // prefixes).
        assert_ne!(artifact_lib.llbc_file_name(), artifact_bin.llbc_file_name());
        assert!(artifact_lib.llbc_file_name().starts_with("pkg-name-"));
        assert!(artifact_bin.llbc_file_name().starts_with("pkg-name-"));
    }
}
