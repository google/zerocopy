use std::{
    collections::{HashMap, HashSet},
    ffi::OsStr,
    hash::{Hash, Hasher as _},
    path::{Path, PathBuf},
    sync::mpsc::{self, Sender},
};

use anyhow::Result;

use crate::{
    parse::{self, ParsedLeanItem},
    resolve::{HermesTargetKind, HermesTargetName, Roots},
};

#[derive(Clone)]
struct ScannerContext {
    err_tx: Sender<anyhow::Error>,
    // `ParsedLeanItem`s must have their `module_path` field updated to be
    // relative to the crate root.
    item_tx: Sender<(HermesTargetName, ParsedLeanItem<crate::parse::hkd::Safe>, String)>,
    name: HermesTargetName,
    current_prefix: Vec<String>,
}

/// A scanned artifact containing all the necessary information to generate
/// a Lean specification.
///
/// This represents a single Rust target (library, binary, etc.) and includes
/// the list of discovered Hermes items and the calculated entry points for
/// Charon.
pub struct HermesArtifact {
    pub name: HermesTargetName,
    pub target_kind: HermesTargetKind,
    /// The path to the crate's `Cargo.toml`.
    pub manifest_path: PathBuf,
    pub items: Vec<ParsedLeanItem<crate::parse::hkd::Safe>>,
    // NOTE: We store `start_from` as a `HashSet` rather than a `Vec` as an
    // optimization: when we encounter items which we can't name (which carry
    // Hermes annotations), we add their parent module to the list of
    // entrypoints. If there are multiple items in the same module, this can
    // lead to duplication in the list of entrypoints. Storing them in a
    // `HashSet` avoids us having to de-dup later.
    pub start_from: HashSet<String>,
}

impl HermesArtifact {
    /// Returns a unique, Lean-compatible "slug" for this artifact that matches
    /// the name that Aeneas will expect for the corresponding Lean module.
    ///
    /// Guarantees uniqueness based on manifest path even if multiple packages
    /// have the same name. The slug is guaranteed to be a valid Lean
    /// identifier (no hyphens).
    pub fn artifact_slug(&self) -> String {
        fn hash<T: Hash>(t: &T) -> u64 {
            let mut s = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }

        // Double-hash to make sure we can distinguish between e.g.
        // (manifest_path, target_name) = ("abc", "def") and ("ab", "cdef"),
        // which would hash identically if we just hashed their concatenation.
        //
        // Note: We use `DefaultHasher` so this slug is not guaranteed to be
        // stable across Rust versions. This is acceptable for local artifact
        // management.
        let h0 = hash(&self.manifest_path);
        let h1 = hash(&self.name.target_name);
        let h2 = hash(&self.target_kind);
        let h = hash(&[h0, h1, h2]);

        // Converts kebab-case -> PascalCase.
        let to_pascal = |s: &str| {
            s.split(|c| matches!(c, '-' | '_'))
                .map(|segment| {
                    let mut chars = segment.chars();
                    match chars.next() {
                        None => String::new(),
                        Some(f) => f.to_uppercase().collect::<String>() + chars.as_str(),
                    }
                })
                .collect::<String>()
        };

        let pkg = to_pascal(self.name.package_name.as_str());
        let target = to_pascal(&self.name.target_name);

        // We use the hash to ensure uniqueness.
        format!("{}{}{:08x}", pkg, target, h)
    }

    /// Returns the name of the `.llbc` file to use for this artifact.
    pub fn llbc_file_name(&self) -> String {
        format!("{}.llbc", self.artifact_slug())
    }

    /// Returns the name of the `.lean` spec file to use for this artifact.
    pub fn lean_spec_file_name(&self) -> String {
        format!("{}.lean", self.artifact_slug())
    }
}

/// Scans the workspace to identify Hermes entry points (`/// ```lean` blocks)
/// and collects targets for verification.
pub fn scan_workspace(roots: &Roots) -> Result<Vec<HermesArtifact>> {
    log::trace!("scan_workspace({:?})", roots);

    let (err_tx, err_rx) = mpsc::channel();
    let (item_tx, item_rx) =
        mpsc::channel::<(HermesTargetName, ParsedLeanItem<crate::parse::hkd::Safe>, String)>();

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
            let ctx = ScannerContext {
                err_tx: err_tx.clone(),
                item_tx: item_tx.clone(),
                name: target.name.clone(),
                current_prefix: vec!["crate".to_string()],
            };
            s.spawn(move |s| {
                process_file_recursive(
                    s,
                    &target.src_path,
                    ctx,
                    false, // Initial call is top-level, so not inside block
                    Vec::new(),
                )
            });
        }
    });

    // Inform the monitor thread that no more errors will be sent, causing it to
    // exit.
    drop(err_tx);

    let (mut entry_points, mut start_from_map) = {
        drop(item_tx);
        let mut entry_points =
            HashMap::<HermesTargetName, Vec<ParsedLeanItem<crate::parse::hkd::Safe>>>::new();
        let mut start_from_map = HashMap::<HermesTargetName, HashSet<String>>::new();
        for (target, item, sf_str) in item_rx {
            start_from_map.entry(target.clone()).or_default().insert(sf_str);
            entry_points.entry(target).or_default().push(item);
        }
        (entry_points, start_from_map)
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
            Some(HermesArtifact {
                name: target.name.clone(),
                target_kind: target.kind,
                manifest_path: target.manifest_path.clone(),
                items: entry_points.remove(&target.name)?,
                start_from: start_from_map.remove(&target.name).unwrap_or_default(),
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
    ctx: ScannerContext,
    inside_block: bool,
    mut ancestors: Vec<PathBuf>,
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
            //
            // Note: The scanner is currently CFG-agnostic. It does not evaluate
            // `#[cfg(...)]` attributes, so it may attempt to scan files that
            // are disabled for the current target (e.g., Windows-specific code
            // on Linux). This is a known limitation that may cause build failures
            // in Charon if it tries to verify non-existent items.
            log::debug!("Skipping unreachable or missing file {:?}: {}", src_path, e);
            return;
        }
    };

    // Cycle detection: prevent infinite recursion on symlinks or recursive mod
    // declarations, while still allowing identical files to be mounted in
    // different branches of the tree. A cycle would represent an invalid crate
    // anyway (i.e., an invalid set of `#[path]` attributes).
    //
    // Note: This check is purely path-based. It does not inspect the content of
    // the file.
    if ancestors.contains(&src_path) {
        return;
    }
    ancestors.push(src_path.clone());

    let result = parse::read_file_and_scan_compilation_unit(
        &src_path,
        inside_block,
        |_src, res| match res {
            Ok(mut item) => {
                item.module_path.splice(0..0, ctx.current_prefix.clone());

                let unreliable = match &item.item {
                    crate::parse::ParsedItem::Impl(_) => true,
                    crate::parse::ParsedItem::Function(f) => {
                        matches!(
                            f.item,
                            crate::parse::FunctionItem::Impl(_)
                                | crate::parse::FunctionItem::Trait(_)
                        )
                    }
                    _ => false,
                };
                let module_path = item.module_path.join("::");
                let start_from_str = if unreliable {
                    // For items where we cannot reliably determine the fully qualified
                    // name (e.g., items inside `impl` blocks or `trait` definitions),
                    // we must fall back to using the containing module as the
                    // entry point. This forces Charon to analyze the entire module,
                    // which is less efficient but ensures we don't miss the item.
                    module_path
                } else {
                    format!("{}::{}", module_path, item.item.name().unwrap())
                };

                use crate::parse::hkd::LiftToSafe;
                ctx.item_tx.send((ctx.name.clone(), item.lift(), start_from_str)).unwrap();
            }
            Err(e) => {
                let _ = ctx.err_tx.send(e.into());
            }
        },
    );

    // After scanning the current file, we look for declared submodules that
    // were not loaded inline (i.e., `mod foo;` instead of `mod foo { ... }`).
    // `read_file_and_scan_compilation_unit` returns a list of these "unloaded"
    // modules so we can resolve their paths and recurse.
    let (_, unloaded_modules) = match result {
        Ok(res) => res,
        Err(e) => {
            let _ = ctx.err_tx.send(e.into());
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
        // If we are in `mod.rs`, `lib.rs`, or `main.rs`, then `mod foo;`
        // looks for `foo.rs` or `foo/mod.rs` in the *same* directory.
        //
        // e.g. `src/lib.rs` -> `mod foo` -> `src/foo.rs`
        src_path.parent().unwrap_or(&src_path).to_path_buf()
    } else {
        // If we are in `src/foo.rs`, then `mod bar;` looks for
        // `src/foo/bar.rs` or `src/foo/bar/mod.rs`.
        //
        // e.g. src/foo.rs -> src/foo/
        src_path.with_extension("")
    };

    // Resolve and queue child modules for processing.
    for module in unloaded_modules {
        if let Some(mod_path) =
            resolve_module_path(&base_dir, &module.name, module.path_attr.as_deref())
        {
            // Spawn new tasks for discovered modules.
            let mut ctx_clone = ctx.clone();
            ctx_clone.current_prefix.push(module.name);

            // TODO: Can we do something more efficient than cloning here? Maybe
            // a linked list?
            let ancestors = ancestors.clone();
            scope.spawn(move |s| {
                process_file_recursive(s, &mod_path, ctx_clone, module.inside_block, ancestors)
            })
        } else {
            // This is an expected condition – it shows up when modules are
            // conditionally compiled. Instead of implementing conditional
            // compilation ourselves, we can just let rustc error later if
            // this is actually an error.
            //
            // Example: `#[cfg(windows)] mod win_only;` on Linux. `win_only.rs`
            // might not exist at all, or might verify successfully but be
            // ignored by rustc. We just skip it here.
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

    // If `#[path = "..."]` is present, it overrides the standard lookup logic.
    // The path is always relative to the current module's directory.
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
            start_from: std::collections::HashSet::new(),
            items: vec![],
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
            start_from: std::collections::HashSet::new(),
            items: vec![],
        };

        // Verify that the file names are distinct, and that they're distinct
        // *because of the trailing hash* (ie, that they have identical
        // prefixes).
        assert_ne!(artifact_lib.llbc_file_name(), artifact_bin.llbc_file_name());
        assert!(artifact_lib.llbc_file_name().starts_with("PkgName"));
        assert!(artifact_bin.llbc_file_name().starts_with("PkgName"));
    }

    #[test]
    fn test_lean_spec_file_name_uses_slug() {
        let name = HermesTargetName {
            package_name: PackageName::new("pkg-foo".to_string()),
            target_name: "name-bar".to_string(),
            kind: HermesTargetKind::Lib,
        };

        let artifact = HermesArtifact {
            name,
            target_kind: HermesTargetKind::Lib,
            manifest_path: PathBuf::from("Cargo.toml"),
            start_from: std::collections::HashSet::new(),
            items: vec![],
        };

        // Slug should be PascalCase: PkgFoo_NameBar_<hash>
        // Spec file should be slug + .lean
        let spec_name = artifact.lean_spec_file_name();
        assert!(spec_name.starts_with("PkgFooNameBar"));
        assert!(spec_name.ends_with(".lean"));
    }
}
