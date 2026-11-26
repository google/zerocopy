// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Ratchet on kernel-cost and axiom-hygiene patterns in the bundled theory.
//!
//! The test compiles `trusted/lean` and every module in
//! `theory/bundle-manifest.json`, then runs
//! `fixtures/kernel_physics_census.lean` over the result. It fails if:
//!
//! - the set of pairs of a constant outside `Anneal` that depends on
//!   `Quot.sound` and a bundled declaration that refers to it differs from
//!   `ALLOWED_QUOT_SOUND_ENTRIES`;
//! - a declaration's type or a definition's body mentions a `PTree` of
//!   functions;
//! - user-written code applies a `Trusted.MirAst` recursor with a motive into
//!   `Sort (u + 1)` (`Type` or a `Prop`-valued predicate);
//! - the number of compiler-generated `_sparseCasesOn` helpers differs from
//!   `MAX_SPARSE_CASES_ON`; or
//! - a detector stops firing on its positive control in
//!   `fixtures/KernelPhysicsControls.lean`.
//!
//! The recorded sets and counts must match exactly, so that a change which
//! improves one also records it and the improvement cannot silently regress.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Mutex},
    thread,
};

use anneal_testkit::toolchain::{default_lean_path, lean_prefix};

/// `(entry point, Anneal referrer)` pairs through which `Quot.sound` may enter
/// the bundled theory.
///
/// - `funext` in `prop_em` is inherent: Diaconescu's argument needs function
///   extensionality.
/// - Lean's `Nat.bitwise.eq_def` is proved with `WellFounded.Nat.fix_eq`,
///   which uses `funext`. `NatBitwise.unfold_eq` is the one place that
///   unfolds `Nat.bitwise`.
/// - `Int.instLawfulBEq` and `Nat.instLawfulBEq` reach `Quot.sound` through
///   their `LawfulBEq` proofs; `of_decide_eq_true` avoids them.
///
/// The observed set must equal this list exactly: a new pair is a regression,
/// and a pair that disappears must be removed here so that it cannot return.
const ALLOWED_QUOT_SOUND_ENTRIES: &[(&str, &str)] = &[
    ("funext", "Anneal.ClassicalEm.prop_em"),
    (
        "_private.Init.Data.Nat.Bitwise.Basic.0.Nat.bitwise.eq_def",
        "_private.Anneal.NatBitwise.0.Nat.bitwise.eq_def",
    ),
    ("Int.instLawfulBEq", "Anneal.AiPcc.evalBinOp_sint_div_rem"),
    ("Nat.instLawfulBEq", "Anneal.InitLemmas.canary_list_beq_edge"),
];

/// Exact number of compiler-generated `_sparseCasesOn` helpers in the bundled
/// theory. Each one is a `casesOn` over a large inductive that the kernel
/// unfolds whenever it reduces the enclosing match.
const MAX_SPARSE_CASES_ON: usize = 270;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_path_buf()
}

/// Returns the modules named by `import` commands in `src`'s header, which
/// ends at the first command other than `module`, `prelude`, or an import.
/// Skips line comments and (nested) block comments.
fn header_imports(src: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    for line in src.lines() {
        let mut code = String::new();
        let mut rest = line;
        loop {
            if depth > 0 {
                match (rest.find("/-"), rest.find("-/")) {
                    (Some(open), Some(close)) if open < close => {
                        depth += 1;
                        rest = &rest[open + 2..];
                    }
                    (_, Some(close)) => {
                        depth -= 1;
                        rest = &rest[close + 2..];
                    }
                    _ => break,
                }
            } else {
                let open = rest.find("/-");
                let comment = rest.find("--");
                match (open, comment) {
                    (Some(o), c) if c.is_none_or(|c| o < c) => {
                        code.push_str(&rest[..o]);
                        depth += 1;
                        rest = &rest[o + 2..];
                    }
                    (_, Some(c)) => {
                        code.push_str(&rest[..c]);
                        break;
                    }
                    _ => {
                        code.push_str(rest);
                        break;
                    }
                }
            }
        }
        let tokens: Vec<&str> = code.split_whitespace().collect();
        if tokens.is_empty() || matches!(tokens.as_slice(), ["module"] | ["prelude"]) {
            continue;
        }
        let Some(pos) = tokens.iter().position(|t| *t == "import") else { break };
        if !tokens[..pos].iter().all(|t| matches!(*t, "public" | "private" | "meta")) {
            break;
        }
        out.extend(tokens[pos + 1..].iter().filter(|t| **t != "all").map(|t| t.to_string()));
    }
    out
}

struct Module {
    root: PathBuf,
    source: PathBuf,
    deps: BTreeSet<String>,
}

/// Collects the `trusted/lean` modules and the bundled theory modules, with
/// their dependencies restricted to that set.
fn bundled_modules(root: &Path) -> BTreeMap<String, Module> {
    let mut modules = BTreeMap::new();
    let mut add = |name: String, src_root: PathBuf, source: PathBuf| {
        modules.insert(name, Module { root: src_root, source, deps: BTreeSet::new() });
    };
    for rel in anneal_audit::bundle::TRUSTED_BUNDLE_SOURCES {
        if let Some(stem) = rel.strip_prefix("trusted/lean/").and_then(|r| r.strip_suffix(".lean"))
        {
            add(stem.replace('/', "."), root.join("trusted/lean"), root.join(rel));
        }
    }
    let (_, manifest) = anneal_audit::bundle::load_theory_bundle_manifest(root)
        .expect("load theory/bundle-manifest.json");
    for entry in &manifest.modules {
        let stem = entry
            .path
            .strip_prefix("theory/")
            .and_then(|r| r.strip_suffix(".lean"))
            .expect("bundled theory path under theory/");
        add(stem.replace('/', "."), root.join("theory"), root.join(&entry.path));
    }
    let names: BTreeSet<String> = modules.keys().cloned().collect();
    for module in modules.values_mut() {
        let src = fs::read_to_string(&module.source).unwrap();
        module.deps = header_imports(&src).into_iter().filter(|d| names.contains(d)).collect();
    }
    modules
}

/// Compiles `modules` into `out` in dependency order with up to four `lean`
/// processes at a time.
fn compile_all(lean: &Path, lean_path: &str, modules: &BTreeMap<String, Module>, out: &Path) {
    let done = Arc::new(Mutex::new(BTreeSet::<String>::new()));
    let mut pending: BTreeSet<String> = modules.keys().cloned().collect();
    let workers = thread::available_parallelism().map_or(1, |n| n.get().clamp(1, 4));
    while !pending.is_empty() {
        let ready: Vec<String> = {
            let done = done.lock().unwrap();
            pending
                .iter()
                .filter(|m| modules[*m].deps.iter().all(|d| done.contains(d)))
                .cloned()
                .collect()
        };
        assert!(!ready.is_empty(), "import cycle among {pending:?}");
        for chunk in ready.chunks(workers) {
            thread::scope(|s| {
                for name in chunk {
                    let module = &modules[name];
                    let done = Arc::clone(&done);
                    s.spawn(move || {
                        let olean = out.join(name.replace('.', "/")).with_extension("olean");
                        fs::create_dir_all(olean.parent().unwrap()).unwrap();
                        let output = Command::new(lean)
                            .env("LEAN_PATH", lean_path)
                            .arg("-j1")
                            .arg("-R")
                            .arg(&module.root)
                            .arg("-o")
                            .arg(&olean)
                            .arg(&module.source)
                            .output()
                            .unwrap();
                        assert!(
                            output.status.success(),
                            "compiling {name} failed:\n{}{}",
                            String::from_utf8_lossy(&output.stdout),
                            String::from_utf8_lossy(&output.stderr)
                        );
                        done.lock().unwrap().insert(name.clone());
                    });
                }
            });
            for name in chunk {
                pending.remove(name);
            }
        }
    }
}

#[test]
fn bundled_theory_kernel_physics_ratchet() {
    let root = repo_root();
    let lean = default_lean_path().expect("resolve pinned lean");
    let prefix = lean_prefix(&lean).expect("lean --print-prefix");
    let stdlib = prefix.join("lib/lean");
    let modules = bundled_modules(&root);

    let tmp = tempfile::tempdir().unwrap();
    let out = tmp.path().join("lib");
    fs::create_dir_all(&out).unwrap();
    let lean_path = env::join_paths([out.as_path(), stdlib.as_path()]).unwrap();
    let lean_path = lean_path.to_str().unwrap();
    compile_all(&lean, lean_path, &modules, &out);

    let fixtures = root.join("tests/audit/tests/fixtures");
    let census = Census {
        lean: &lean,
        lean_path,
        sysroot: &prefix,
        script: &fixtures.join("kernel_physics_census.lean"),
    };

    // Positive controls: every detector must fire on `KernelPhysicsControls`.
    let controls = BTreeMap::from([(
        "KernelPhysicsControls".to_owned(),
        Module {
            root: fixtures.clone(),
            source: fixtures.join("KernelPhysicsControls.lean"),
            deps: BTreeSet::new(),
        },
    )]);
    compile_all(&lean, lean_path, &controls, &out);
    let control_out = census.run("KernelPhysicsControls", ["KernelPhysicsControls"]);
    for (kind, needle) in [
        ("QUOT_ENTRY", "QUOT_ENTRY\tInt.instLawfulBEq\tKernelPhysicsControls.int_eq_of_beq"),
        ("AST_REC", "AST_REC\tKernelPhysicsControls.tyDepth\t"),
        (
            "nested AST_REC",
            "AST_REC\tKernelPhysicsControls.tySize.fieldsSize\tTrusted.MirAst.MirTy.brecOn_1",
        ),
        ("PTREE_FUN", "PTREE_FUN\tKernelPhysicsControls.handlers\n"),
        ("point-free PTREE_FUN", "PTREE_FUN\tKernelPhysicsControls.etaHandlers\n"),
        ("identity-alias PTREE_FUN", "PTREE_FUN\tKernelPhysicsControls.idHandlers\n"),
        ("let-alias PTREE_FUN", "PTREE_FUN\tKernelPhysicsControls.letHandlers\n"),
        ("let-body PTREE_FUN", "PTREE_FUN\tKernelPhysicsControls.letBodyHandlers\n"),
    ] {
        assert!(
            control_out.lines().any(|l| match needle.strip_suffix('\n') {
                Some(exact) => l == exact,
                None => l.starts_with(needle),
            }),
            "the census no longer reports {kind} for its positive control:\n{control_out}"
        );
    }

    let theory: Vec<&String> =
        modules.iter().filter(|(_, m)| m.root.ends_with("theory")).map(|(n, _)| n).collect();
    assert!(!theory.is_empty(), "no bundled theory modules found");
    let stdout = census.run("Anneal", theory);

    let allowed: BTreeSet<(&str, &str)> = ALLOWED_QUOT_SOUND_ENTRIES.iter().copied().collect();
    let mut seen_quot = BTreeSet::new();
    let mut problems = Vec::new();
    let mut sparse = None;
    let mut decls = None;
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["QUOT_ENTRY", entry, referrer] if allowed.contains(&(*entry, *referrer)) => {
                seen_quot.insert((*entry, *referrer));
            }
            ["QUOT_ENTRY", entry, referrer] => problems
                .push(format!("{referrer} refers to {entry}, which depends on `Quot.sound`")),
            ["PTREE_FUN", decl] => {
                problems.push(format!("the type or body of {decl} stores functions in a `PTree`"))
            }
            ["AST_REC", decl, rec] => {
                problems.push(format!("{decl} applies {rec} at a nonzero universe level"))
            }
            ["SPARSE", n] => sparse = Some(n.parse::<usize>().unwrap()),
            ["DECLS", n] => decls = Some(n.parse::<usize>().unwrap()),
            _ => problems.push(format!("unrecognized census output: {line}")),
        }
    }
    let sparse = sparse.expect("census reports a `_sparseCasesOn` count");
    let decls = decls.expect("census reports a declaration count");
    // Guard against a census that silently scanned nothing.
    assert!(decls > 0 && sparse > 0, "census scanned {decls} declarations, {sparse} helpers");
    if sparse > MAX_SPARSE_CASES_ON {
        problems.push(format!(
            "{sparse} `_sparseCasesOn` helpers exceed the bound of {MAX_SPARSE_CASES_ON}"
        ));
    } else if sparse < MAX_SPARSE_CASES_ON {
        problems.push(format!(
            "only {sparse} `_sparseCasesOn` helpers remain; lower `MAX_SPARSE_CASES_ON` to {sparse}"
        ));
    }
    for (entry, referrer) in allowed.difference(&seen_quot) {
        problems.push(format!(
            "{referrer} no longer refers to {entry}; remove the pair from `ALLOWED_QUOT_SOUND_ENTRIES`"
        ));
    }
    assert!(problems.is_empty(), "kernel-physics ratchet failed:\n{}", problems.join("\n"));
}

/// How to run `kernel_physics_census.lean` against the compiled modules.
struct Census<'a> {
    lean: &'a Path,
    lean_path: &'a str,
    sysroot: &'a Path,
    script: &'a Path,
}

impl Census<'_> {
    /// Runs the census over `modules`, scanning declarations from modules
    /// whose names start with `scan_prefix`, and returns its output.
    fn run<I, S>(&self, scan_prefix: &str, modules: I) -> String
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        // `findSysroot` in the census prefers `LEAN_SYSROOT` over `PATH`.
        let output = Command::new(self.lean)
            .env("LEAN_PATH", self.lean_path)
            .env("LEAN_SYSROOT", self.sysroot)
            .arg("-j1")
            .arg("--run")
            .arg(self.script)
            .arg(scan_prefix)
            .args(modules)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        assert!(
            output.status.success(),
            "census failed:\n{stdout}{}",
            String::from_utf8_lossy(&output.stderr)
        );
        stdout
    }
}
