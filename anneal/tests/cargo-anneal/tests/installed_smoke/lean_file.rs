// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The `lean-file` case: compiling packaged Lean sources with the installed
//! toolchain, and the Lean header parsing it needs.

use super::*;

fn next_lean_header_token(
    bytes: &[u8],
    pos: &mut usize,
    module: &str,
) -> TestResult<Option<String>> {
    loop {
        while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
            *pos += 1;
        }
        if *pos >= bytes.len() {
            return Ok(None);
        }
        if bytes[*pos..].starts_with(b"--") {
            *pos += 2;
            while *pos < bytes.len() && bytes[*pos] != b'\n' {
                *pos += 1;
            }
            continue;
        }
        if bytes[*pos..].starts_with(b"/-") {
            *pos += 2;
            let mut depth = 1usize;
            while depth > 0 {
                if *pos + 1 >= bytes.len() {
                    return Err(format!("unclosed block comment in Lean header of {module}"));
                }
                if bytes[*pos..].starts_with(b"/-") {
                    depth += 1;
                    *pos += 2;
                } else if bytes[*pos..].starts_with(b"-/") {
                    depth -= 1;
                    *pos += 2;
                } else {
                    *pos += 1;
                }
            }
            continue;
        }
        break;
    }
    let start = *pos;
    while *pos < bytes.len()
        && !bytes[*pos].is_ascii_whitespace()
        && !bytes[*pos..].starts_with(b"--")
        && !bytes[*pos..].starts_with(b"/-")
    {
        *pos += 1;
    }
    let token = std::str::from_utf8(&bytes[start..*pos])
        .map_err(|error| format!("non-UTF-8 token in Lean header of {module}: {error}"))?;
    Ok(Some(token.to_owned()))
}

fn lean_header_imports(source: &str, module: &str) -> TestResult<Vec<String>> {
    let bytes = source.as_bytes();
    let mut pos = 0;
    let mut imports = Vec::new();
    let mut expecting_import_target = false;
    while let Some(token) = next_lean_header_token(bytes, &mut pos, module)? {
        if expecting_import_target {
            if token == "all" {
                continue;
            }
            if token.split('.').any(|seg| !is_lean_ident(seg)) {
                return Err(format!(
                    "unexpected import module name {token:?} in {module}"
                ));
            }
            imports.push(token);
            expecting_import_target = false;
        } else if token == "import" {
            expecting_import_target = true;
        } else if matches!(token.as_str(), "prelude" | "module" | "public" | "meta") {
            continue;
        } else {
            break;
        }
    }
    if expecting_import_target {
        return Err(format!("truncated import statement in header of {module}"));
    }
    Ok(imports)
}

fn resolve_packaged_lean_source(
    trusted_root: &Path,
    theory_root: &Path,
    module: &str,
) -> TestResult<(PathBuf, PathBuf)> {
    if module.split('.').any(|seg| !is_lean_ident(seg)) {
        return Err(format!("invalid packaged Lean module name {module:?}"));
    }
    let rel = PathBuf::from(format!("{}.lean", module.replace('.', "/")));
    let trusted_path = trusted_root.join(&rel);
    let theory_path = theory_root.join(&rel);
    match (trusted_path.is_file(), theory_path.is_file()) {
        (true, true) => Err(format!(
            "ambiguous packaged Lean module {module} in both trusted/lean and theory"
        )),
        (true, false) => Ok((trusted_root.to_path_buf(), trusted_path)),
        (false, true) => Ok((theory_root.to_path_buf(), theory_path)),
        (false, false) => Err(format!(
            "missing packaged Lean module source for {module} ({})",
            rel.display()
        )),
    }
}

pub(super) fn lean_case(case: &mut CaseDirectory, root: &Path, jobs: usize) -> TestResult {
    let lean = root.join("lean/bin/lean");
    version(case, &lean, "Lean (version 4.34.1")?;
    case.copy(&root.join("share/anneal/trusted/lean"), "trusted/lean")?;
    case.copy(&root.join("share/anneal/theory"), "theory")?;

    let trusted_root = case.path().join("trusted/lean");
    let theory_root = case.path().join("theory");
    if theory_root.join("Anneal.lean").exists() {
        return Err("installed share/anneal/theory unexpectedly ships retired Anneal.lean".into());
    }
    let manifest_path = theory_root.join("bundle-manifest.json");
    let manifest_raw = fs::read_to_string(&manifest_path)
        .map_err(|error| format!("read {}: {error}", manifest_path.display()))?;
    let manifest_json: Value = serde_json::from_str(&manifest_raw)
        .map_err(|error| format!("parse {}: {error}", manifest_path.display()))?;
    if manifest_json["schema_version"] != 1 {
        return Err(format!(
            "unexpected bundle-manifest.json schema_version in {}",
            manifest_path.display()
        ));
    }
    let manifest_entries = manifest_json["modules"]
        .as_array()
        .ok_or_else(|| format!("missing modules array in {}", manifest_path.display()))?;
    if manifest_entries.is_empty() {
        return Err("empty modules array in share/anneal/theory/bundle-manifest.json".into());
    }
    let mut manifest_theory_modules = BTreeSet::new();
    let mut queue = VecDeque::from([String::from("Trusted")]);
    for entry in manifest_entries {
        let rel_path = entry["path"]
            .as_str()
            .ok_or_else(|| format!("non-string path in {}", manifest_path.display()))?;
        let stem = rel_path
            .strip_prefix("theory/")
            .and_then(|s| s.strip_suffix(".lean"))
            .ok_or_else(|| format!("unexpected theory bundle path {rel_path:?}"))?;
        let module = stem.replace('/', ".");
        if !module.starts_with("Anneal.")
            || module.contains("Canaries")
            || module.split('.').any(|seg| !is_lean_ident(seg))
        {
            return Err(format!(
                "unexpected theory module {module:?} in installed bundle-manifest.json"
            ));
        }
        if !manifest_theory_modules.insert(module.clone()) {
            return Err(format!(
                "duplicate theory module {module:?} in installed bundle-manifest.json"
            ));
        }
        queue.push_back(module);
    }

    let mut sources: BTreeMap<String, (PathBuf, PathBuf)> = BTreeMap::new();
    let mut imports_map: BTreeMap<String, Vec<ImportEdge>> = BTreeMap::new();
    while let Some(module) = queue.pop_front() {
        if sources.contains_key(&module) {
            continue;
        }
        let (root_dir, src_path) =
            resolve_packaged_lean_source(&trusted_root, &theory_root, &module)?;
        let content = fs::read_to_string(&src_path)
            .map_err(|error| format!("read {}: {error}", src_path.display()))?;
        let raw_imports = lean_header_imports(&content, &module)?;
        let mut edges = Vec::with_capacity(raw_imports.len());
        for dep in raw_imports {
            let is_init = dep == "Init" || dep.starts_with("Init.");
            let is_packaged =
                dep == "Trusted" || dep.starts_with("Trusted.") || dep.starts_with("Anneal.");
            if !is_init && !is_packaged {
                return Err(format!(
                    "unexpected non-Init/Trusted/Anneal.* import {dep} in {module}"
                ));
            }
            if is_packaged && !sources.contains_key(&dep) {
                queue.push_back(dep.clone());
            }
            edges.push(ImportEdge {
                module: dep,
                import_all: false,
                is_exported: true,
                is_meta: false,
            });
        }
        sources.insert(module.clone(), (root_dir, src_path));
        imports_map.insert(module, edges);
    }

    // `share/anneal/theory` must ship only `bundle-manifest.json` and the exact
    // `Anneal.*` module set in `bundle-manifest.json` (excluding retired
    // `Anneal.lean` and all `*Canaries*.lean` suites, and matching the
    // transitive `Anneal.*` import closure 1-for-1).
    let bundled_sub_modules: BTreeSet<String> =
        sources.keys().filter(|m| m.starts_with("Anneal.")).cloned().collect();
    if bundled_sub_modules.iter().any(|m| m.contains("Canaries")) {
        return Err(format!(
            "installed theory closure unexpectedly imports canary module: {bundled_sub_modules:?}"
        ));
    }
    if bundled_sub_modules != manifest_theory_modules {
        return Err(format!(
            "installed bundle-manifest.json is not transitively closed under Anneal.* imports: \
             manifest={manifest_theory_modules:?}, closure={bundled_sub_modules:?}"
        ));
    }
    let mut installed_theory_modules = BTreeSet::new();
    let mut dirs = vec![theory_root.clone()];
    while let Some(dir) = dirs.pop() {
        let entries = fs::read_dir(&dir)
            .map_err(|error| format!("read installed {}: {error}", dir.display()))?;
        for entry in entries {
            let path = entry
                .map_err(|error| format!("read installed entry in {}: {error}", dir.display()))?
                .path();
            let meta = fs::symlink_metadata(&path)
                .map_err(|error| format!("stat installed {}: {error}", path.display()))?;
            if meta.file_type().is_symlink() {
                return Err(format!(
                    "unexpected symlink in installed share/anneal/theory: {}",
                    path.display()
                ));
            }
            if meta.is_dir() {
                dirs.push(path);
            } else if meta.is_file() {
                let rel = path
                    .strip_prefix(&theory_root)
                    .map_err(|error| format!("strip prefix on {}: {error}", path.display()))?;
                if rel == Path::new("bundle-manifest.json") {
                    continue;
                }
                if path.extension().and_then(|e| e.to_str()) != Some("lean") {
                    return Err(format!(
                        "unexpected non-module file in installed share/anneal/theory: {}",
                        rel.display()
                    ));
                }
                let stem = rel
                    .with_extension("")
                    .to_string_lossy()
                    .replace(std::path::MAIN_SEPARATOR, ".");
                if stem.contains("Canaries") {
                    return Err(format!(
                        "installed share/anneal/theory unexpectedly ships canary file {}",
                        rel.display()
                    ));
                }
                if !stem.starts_with("Anneal.") || stem.split('.').any(|seg| !is_lean_ident(seg)) {
                    return Err(format!(
                        "unexpected Lean file in installed share/anneal/theory: {}",
                        rel.display()
                    ));
                }
                installed_theory_modules.insert(stem);
            } else {
                return Err(format!(
                    "unexpected non-regular entry in installed share/anneal/theory: {}",
                    path.display()
                ));
            }
        }
    }
    if installed_theory_modules != manifest_theory_modules {
        return Err(format!(
            "installed share/anneal/theory modules diverge from bundle-manifest.json: \
             installed={installed_theory_modules:?}, manifest={manifest_theory_modules:?}"
        ));
    }

    let pending: BTreeSet<String> = sources.keys().cloned().collect();
    let order = topo_sort_modules(
        pending,
        &imports_map,
        "import cycle in packaged Anneal Lean sources",
    )
    .map_err(|error| error.to_string())?;
    let plan = ParallelDagPlan::from_module_order(
        &order,
        &imports_map,
        "lean-file",
        "import cycle in packaged Anneal Lean sources",
    )
    .map_err(|error| error.to_string())?;

    let lean_lib = case.path().join("lean-lib");
    fs::create_dir(&lean_lib).map_err(|error| format!("create lean-lib: {error}"))?;
    for module in &order {
        let olean = lean_lib.join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = olean.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
    }

    let lean_path_env = text_path(&lean_lib)?;
    let shared_case = &*case;
    let mut shared = ();
    run_parallel_dag(
        &plan,
        jobs,
        "lean-file",
        "packaged Lean compile worker panicked",
        &mut shared,
        |_, idx| Ok(idx),
        |_, idx| {
            let module = &order[idx];
            let (root_dir, src_path) = &sources[module];
            let olean_out = lean_lib.join(format!("{}.olean", module.replace('.', "/")));
            let mut command = Invocation::new(
                &lean,
                &[
                    "-j1",
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-R",
                    &text_path(root_dir).map_err(|e| Failure::operational("lean-file", e))?,
                    "-o",
                    &text_path(&olean_out).map_err(|e| Failure::operational("lean-file", e))?,
                    &text_path(src_path).map_err(|e| Failure::operational("lean-file", e))?,
                ],
            );
            command
                .environment
                .insert("LEAN_PATH".into(), lean_path_env.clone().into());
            let out = shared_case
                .run_shared(&command)
                .map_err(|e| Failure::operational("lean-file", e))?;
            out.expect_code(0)
                .map_err(|e| Failure::operational("lean-file", e))
        },
        |_, _, ()| Ok(()),
    )
    .map_err(|error| error.to_string())?;

    for required in ["Trusted.olean", "Anneal/Scalar.olean", "Anneal/Wp.olean"] {
        if !lean_lib.join(required).is_file() {
            return Err(format!("missing compiled packaged module {required}"));
        }
    }
    if lean_lib.join("Anneal.olean").exists() {
        return Err("unexpected compiled monolithic Anneal.olean".into());
    }

    case.write(
        "SmallScalar.lean",
        b"prelude\nimport Anneal.Scalar\n\n\
          example := @Anneal.LinearArith.checkIntCutGoal_sound\n\
          example := @Anneal.BitVecArith.bswap32_injective\n\
          example := @Anneal.LeBytes.toLeBytes_injective\n\
          example := @Anneal.ListChunks.divCeil_pos\n\
          example := @Anneal.InitLemmas.bool_and_left\n\
          example := @Anneal.NatBitwise.land_lt_two_pow\n",
    )?;
    case.write(
        "SmallWp.lean",
        b"prelude\nimport Anneal.Wp\n\n\
          example (c : Trusted.MirSemantics.Crate) : Prop :=\n\
          \x20 Trusted.MirSemantics.CrateTheorem c\n\n\
          example := @Anneal.MirWp.wpProg\n\
          example := @Anneal.MirWp.wellFormed_and_spec_of_wp\n\
          example := @Anneal.LoopInv.wpUntil\n",
    )?;
    for smoke_file in ["SmallScalar.lean", "SmallWp.lean"] {
        let mut small = Invocation::new(
            &lean,
            &[
                "-j1",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-DwarningAsError=true",
                "-R",
                &text_path(case.path())?,
                smoke_file,
            ],
        );
        small
            .environment
            .insert("LEAN_PATH".into(), lean_path_env.clone().into());
        let out = case.run(&small)?;
        out.expect_code(0)?;
    }
    Ok(())
}
