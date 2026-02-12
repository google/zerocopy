use std::{
    collections::HashMap,
    ffi::OsStr,
    hash::{Hash, Hasher as _},
    path::{Path, PathBuf},
    sync::mpsc::{self, Sender},
};

use anyhow::Result;
use dashmap::DashSet;

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
        // (manifest_path, target_name) = ("abc", "def") and ("ab", "cdef"),
        // which would hash identically if we just hashed their concatenation.
        let h0 = hash(&self.manifest_path);
        let h1 = hash(&self.name.target_name);
        let h = hash(&[h0, h1]);
        format!("{}-{}-{:08x}.llbc", self.name.package_name, self.name.target_name, h)
    }
}

/// Scans the workspace to identify Hermes entry points (`/// ```lean` blocks)
/// and collects targets for verification.
pub fn scan_workspace(roots: &Roots) -> Result<Vec<HermesArtifact>> {
    log::trace!("scan_workspace({:?})", roots);

    let visited_paths = DashSet::new();
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

    if !visited.insert(src_path.clone()) {
        return;
    }

    // Walk the AST, collecting new modules to process.
    let (_source_code, unloaded_modules) =
        match parse::read_file_and_scan_compilation_unit(&src_path, |_src, item_result| {
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
        }) {
            Ok(res) => res,
            Err(e) => {
                let _ = err_tx
                    .send(anyhow::anyhow!(e).context(format!("Failed to parse {:?}", src_path)));
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

            let mut new_prefix = module_prefix.clone();
            new_prefix.push(module.name);

            let name = name.clone();
            scope.spawn(move |s| {
                process_file_recursive(
                    s, &mod_path, config, visited, err_tx, path_tx, new_prefix, name,
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
