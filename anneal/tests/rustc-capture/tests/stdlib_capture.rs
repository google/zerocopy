// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Check the opt-in `--stdlib-crate` capture capability and the diagnostic
//! handling of imported standard-library sources.

#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
};

use serde_json::Value;

fn sysroot() -> PathBuf {
    anneal_testkit::default_rust_sysroot().expect("resolve pinned compiler sysroot")
}

/// A self-contained `#![no_core]` crate that defines its own language items.
const NO_CORE: &str = r#"#![feature(no_core, lang_items)]
#![no_core]
#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u8 {}
pub fn selected(x: u8) -> u8 { x }
"#;

// `-1` would need a `Neg` language item in this `#![no_core]` fixture; the
// cast spells the same `i8` discriminant without one.
const ORDERING_PINNED: &str = r#"
#[lang = "Ordering"]
#[repr(i8)]
pub enum Ordering { Less = 0xff_u8 as i8, Equal = 0, Greater = 1 }
"#;

const ORDERING_FORGED: &str = r#"
#[lang = "Ordering"]
#[repr(i8)]
pub enum Ordering { Less = 0, Equal = 1, Greater = 2 }
"#;

struct Fixture {
    directory: tempfile::TempDir,
    root: PathBuf,
    sources: Vec<PathBuf>,
    outputs: usize,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let directory = tempfile::tempdir().expect("create capture fixture");
        let root = directory.path().canonicalize().unwrap().join("src/lib.rs");
        std::fs::create_dir_all(root.parent().unwrap()).unwrap();
        std::fs::write(&root, source).unwrap();
        Self { directory, sources: vec![root.clone()], root, outputs: 0 }
    }

    /// Run a selected-root capture into a fresh output directory, returning
    /// the process output and that directory.
    fn capture(&mut self, crate_name: &str, extra: &[&str]) -> (Output, PathBuf) {
        self.outputs += 1;
        let output_dir = self.directory.path().join(format!("output-{}", self.outputs));
        let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
        command
            .current_dir(self.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&self.root)
            .arg(format!("--crate-name={crate_name}"))
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&output_dir)
            .arg("--sysroot")
            .arg(sysroot())
            .args(extra);
        for source in &self.sources {
            command.arg("--source-file").arg(source);
        }
        (command.output().expect("run capture"), output_dir)
    }
}

fn status(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("typed capture returns one JSON status ({e}): {output:?}"))
}

fn manifest(output_dir: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(output_dir.join("capture.json")).unwrap()).unwrap()
}

fn assert_refused(output: &Output, output_dir: &Path, status_kind: &str, needle: &str) {
    assert_eq!(status(output)["status"], status_kind, "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains(needle), "{output:?}");
    assert!(std::fs::symlink_metadata(output_dir.join("capture.json")).is_err());
}

#[test]
fn stdlib_capability_is_opt_in_and_scoped_to_a_self_contained_named_crate() {
    let mut fixture = Fixture::new(NO_CORE);

    // Without the capability, `#![feature(no_core, lang_items)]` is refused
    // before macro expansion by the closed positive feature allowlist, even
    // for a crate named `core`.
    for name in ["core", "session"] {
        let (output, dir) = fixture.capture(name, &["--select=selected"]);
        assert_refused(&output, &dir, "unsupported", "lang_items, no_core");
    }

    // Even without any `#![feature(...)]` attributes, a normal library crate
    // defining a stable crate-local language item (`#[panic_handler]`) still
    // hits the post-analysis crate-local language item guard.
    let mut panic_lib = Fixture::new(
        "#![no_std]\n\
         #[panic_handler]\n\
         fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }\n\
         pub fn selected(x: u8) -> u8 { x }\n",
    );
    let (output, dir) = panic_lib.capture("session", &["--select=selected"]);
    assert_refused(&output, &dir, "unsupported", "crate-local language item");

    // The capability admits them for the exact crate it names and records
    // itself in the manifest.
    let (output, dir) = fixture.capture("core", &["--select=selected", "--stdlib-crate=core"]);
    assert!(output.status.success(), "{output:?}");
    let captured = manifest(&dir);
    assert_eq!(captured["configuration"]["stdlib_crate"], "core");
    assert_eq!(captured["selected"][0]["path"], "selected");

    // Even under `--stdlib-crate=core`, features outside the version-pinned
    // `core` allowlist (such as `ergonomic_clones` and `custom_mir`) stay
    // refused fail-closed.
    for disallowed in ["ergonomic_clones", "custom_mir"] {
        let mut bad_core = Fixture::new(&format!("#![feature({disallowed})]\n{NO_CORE}"));
        let (output, dir) = bad_core.capture("core", &["--select=selected", "--stdlib-crate=core"]);
        assert_refused(&output, &dir, "unsupported", disallowed);
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("--stdlib-crate core"),
            "{output:?}"
        );
    }

    // Default captures keep their manifest shape: no `stdlib_crate` key.
    let mut plain = Fixture::new("pub fn selected(x: u8) -> u8 { x }\n");
    let (output, dir) = plain.capture("session", &["--select=selected"]);
    assert!(output.status.success(), "{output:?}");
    assert!(manifest(&dir)["configuration"].get("stdlib_crate").is_none());

    // The capability does not transfer to another crate name, whole-crate
    // scope, binaries, or a compilation that sets `cfg(miri)`.
    let (output, dir) = fixture.capture("session", &["--select=selected", "--stdlib-crate=core"]);
    assert_refused(&output, &dir, "unsupported", "does not match crate name");
    let (output, dir) = fixture.capture("core", &["--scope=crate", "--stdlib-crate=core"]);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_refused(&output, &dir, "unsupported", "requires a library crate and selected roots");
    // `#![no_main]` lets the `#![no_core]` fixture compile as a binary, so
    // the refusal comes from the capability's crate-type check.
    let mut binary = Fixture::new(&format!("#![no_main]\n{NO_CORE}"));
    let (output, dir) = binary.capture(
        "core",
        &["--select=selected", "--stdlib-crate=core", "--crate-type=bin", "--panic=abort"],
    );
    assert_refused(&output, &dir, "unsupported", "requires a library crate");
    let (output, dir) =
        fixture.capture("core", &["--select=selected", "--stdlib-crate=core", "--cfg=miri"]);
    assert_refused(&output, &dir, "unsupported", "cfg(miri)");

    // Profile v2 bodies (here, a reference parameter) stay refused under the
    // capability, whose checks cover only Profile v1.
    let mut by_ref = Fixture::new(&format!("{NO_CORE}pub fn by_ref(x: &u8) -> u8 {{ *x }}\n"));
    let (output, dir) = by_ref.capture("core", &["--select=by_ref", "--stdlib-crate=core"]);
    assert_refused(&output, &dir, "unsupported", "admits only Profile v1 bodies");

    // Runtime overflow checks and primitive Profile v1 `Assert` terminators
    // are refused under the capability: their `Assert` terminators panic
    // through language items (`panic_const_*`) that the captured crate itself
    // defines.
    let (output, dir) =
        fixture.capture("core", &["--select=selected", "--stdlib-crate=core", "--overflow-checks"]);
    assert_refused(&output, &dir, "unsupported", "without overflow checks or Assert terminators");
    let mut div_assert = Fixture::new(&format!(
        "{NO_CORE}\
#[lang = \"div\"]\n\
pub trait Div<Rhs = Self> {{ type Output; fn div(self, rhs: Rhs) -> Self::Output; }}\n\
impl Div for u8 {{ type Output = u8; fn div(self, rhs: u8) -> u8 {{ self / rhs }} }}\n\
#[lang = \"panic_const_div_by_zero\"]\n\
pub const fn panic_const_div_by_zero() -> ! {{ loop {{}} }}\n\
pub fn div_u8(x: u8) -> u8 {{ x / 16u8 }}\n"
    ));
    let (output, dir) =
        div_assert.capture("core", &["--select=div_u8", "--stdlib-crate=core"]);
    assert_refused(&output, &dir, "unsupported", "without overflow checks or Assert terminators");

    // A crate named `core` that loads the sysroot's `core` is not
    // self-contained, so the capability does not apply to it.
    let mut linked = Fixture::new("#![no_std]\npub fn selected(x: u8) -> u8 { x }\n");
    let (output, dir) = linked.capture("core", &["--select=selected", "--stdlib-crate=core"]);
    assert_refused(&output, &dir, "unsupported", "loads no other crate");
}

#[test]
fn stdlib_capability_validates_a_local_ordering_lang_item_shape() {
    let mut pinned = Fixture::new(&format!("{NO_CORE}{ORDERING_PINNED}"));
    let (output, _) = pinned.capture("core", &["--select=selected", "--stdlib-crate=core"]);
    assert!(output.status.success(), "{output:?}");

    let mut forged = Fixture::new(&format!("{NO_CORE}{ORDERING_FORGED}"));
    let (output, dir) = forged.capture("core", &["--select=selected", "--stdlib-crate=core"]);
    assert_refused(&output, &dir, "unsupported", "does not have the modeled shape");
}

#[test]
fn stdlib_capability_keeps_the_declared_source_namespace_closed() {
    // An undeclared `..` module outside the declared tree stays a hard
    // refusal under both normal captures and `--stdlib-crate=core`.
    let mut plain = Fixture::new(
        "#[path = \"../outside/m.rs\"]\npub mod outside;\npub fn selected(x: u8) -> u8 { x }\n",
    );
    let plain_outside = plain.directory.path().canonicalize().unwrap().join("outside/m.rs");
    std::fs::create_dir_all(plain_outside.parent().unwrap()).unwrap();
    std::fs::write(&plain_outside, "pub fn other() {}\n").unwrap();
    let (output, dir) = plain.capture("core", &["--select=selected"]);
    assert_refused(&output, &dir, "unsupported", "undeclared compiler read");

    let mut fixture =
        Fixture::new(&format!("{NO_CORE}#[path = \"../outside/m.rs\"]\npub mod outside;\n"));
    let outside = fixture.directory.path().canonicalize().unwrap().join("outside/m.rs");
    std::fs::create_dir_all(outside.parent().unwrap()).unwrap();
    std::fs::write(&outside, "pub fn other() {}\n").unwrap();
    let (output, dir) = fixture.capture("core", &["--select=selected", "--stdlib-crate=core"]);
    assert_refused(&output, &dir, "unsupported", "undeclared compiler read");
    // Declaring the file admits the same `..` path (the loader resolves it
    // through declared ancestors), and the read is bound in the manifest.
    fixture.sources.push(outside.clone());
    let (output, dir) = fixture.capture("core", &["--select=selected", "--stdlib-crate=core"]);
    assert!(output.status.success(), "{output:?}");
    let reads = manifest(&dir)["source_files"].as_array().unwrap().clone();
    assert!(reads.iter().any(|read| read["path"] == outside.to_str().unwrap()), "{reads:?}");
}

#[test]
fn imported_sysroot_snippet_probes_do_not_mask_compiler_diagnostics() {
    // Rendering this error's "function defined here" note re-reads `core`'s
    // source from the sysroot. That probe must not become an undeclared-read
    // refusal that hides the compiler's own failure.
    let mut fixture =
        Fixture::new("pub fn selected() -> u64 { 0 }\npub fn bad() { core::mem::drop(); }\n");
    let (output, dir) = fixture.capture("session", &["--select=selected"]);
    assert_refused(&output, &dir, "compiler_failed", "rustc rejected the compilation");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("undeclared compiler read"), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stderr).contains("E0061"), "{output:?}");
}

/// Recursively copy every file of `from` into `to`, recording each copy.
///
/// Symlinks are followed: Anneal's Nix `symlinkJoin` test sysroot
/// (`anneal/flake.nix`) is a tree of real directories whose files are
/// symlinks into the store. A symlink may therefore resolve outside `from`;
/// copying its target's contents keeps every staged path a regular file
/// under `to`. A directory that resolves to one of its own ancestors would
/// recurse forever, so it is refused, as are dangling links and special
/// files, rather than silently staging an incomplete tree.
fn stage_tree(from: &Path, to: &Path, staged: &mut Vec<PathBuf>) {
    stage_dir(from, to, staged, &mut Vec::new());
}

fn stage_dir(from: &Path, to: &Path, staged: &mut Vec<PathBuf>, ancestors: &mut Vec<PathBuf>) {
    let resolved = from.canonicalize().unwrap();
    assert!(!ancestors.contains(&resolved), "symlink cycle at {}", from.display());
    ancestors.push(resolved);
    std::fs::create_dir_all(to).unwrap();
    let mut entries: Vec<_> = std::fs::read_dir(from).unwrap().map(|e| e.unwrap()).collect();
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        // Unlike `DirEntry::file_type`, `fs::metadata` follows symlinks.
        let kind = std::fs::metadata(&path)
            .unwrap_or_else(|e| panic!("cannot stage {}: {e}", path.display()))
            .file_type();
        let target = to.join(entry.file_name());
        if kind.is_dir() {
            stage_dir(&path, &target, staged, ancestors);
        } else if kind.is_file() {
            std::fs::copy(&path, &target).unwrap();
            staged.push(target);
        } else {
            panic!("cannot stage special file {}", path.display());
        }
    }
    ancestors.pop();
}

#[test]
fn stage_tree_copies_through_symlinked_files_and_directories() {
    use std::os::unix::fs::symlink;

    // A `symlinkJoin`-style tree: real directories, a file symlink, and a
    // directory symlink, both resolving outside the staged root.
    let store = tempfile::tempdir().unwrap();
    std::fs::write(store.path().join("lib.rs"), "lib").unwrap();
    std::fs::create_dir(store.path().join("dir")).unwrap();
    std::fs::write(store.path().join("dir/nested.rs"), "nested").unwrap();
    let tree = tempfile::tempdir().unwrap();
    let src = tree.path().join("src");
    std::fs::create_dir(&src).unwrap();
    symlink(store.path().join("lib.rs"), src.join("lib.rs")).unwrap();
    symlink(store.path().join("dir"), src.join("linked")).unwrap();
    std::fs::write(src.join("plain.rs"), "plain").unwrap();

    let out = tempfile::tempdir().unwrap();
    let to = out.path().join("staged");
    let mut staged = Vec::new();
    stage_tree(tree.path(), &to, &mut staged);

    let expected: Vec<(PathBuf, &str)> = vec![
        (to.join("src/lib.rs"), "lib"),
        (to.join("src/linked/nested.rs"), "nested"),
        (to.join("src/plain.rs"), "plain"),
    ];
    let paths: Vec<&PathBuf> = expected.iter().map(|(path, _)| path).collect();
    assert_eq!(staged.iter().collect::<Vec<_>>(), paths);
    for (path, contents) in &expected {
        assert!(std::fs::symlink_metadata(path).unwrap().is_file(), "{path:?}");
        assert_eq!(std::fs::read_to_string(path).unwrap(), *contents);
    }
    assert!(std::fs::symlink_metadata(to.join("src/linked")).unwrap().is_dir());
}

#[test]
#[should_panic(expected = "symlink cycle")]
fn stage_tree_refuses_symlink_cycles() {
    let tree = tempfile::tempdir().unwrap();
    std::fs::create_dir(tree.path().join("a")).unwrap();
    std::os::unix::fs::symlink(tree.path(), tree.path().join("a/loop")).unwrap();
    let out = tempfile::tempdir().unwrap();
    stage_tree(tree.path(), &out.path().join("staged"), &mut Vec::new());
}

#[test]
fn verbatim_sysroot_core_captures_selected_scalar_functions() {
    let library = sysroot().join("lib/rustlib/src/rust/library");
    if !library.join("core/src/lib.rs").is_file() {
        // `rust-src` is optional: the packaged omnibus archive omits
        // `lib/rustlib/src`, and a rustup sysroot may lack the component.
        // Set `ANNEAL_TEST_REQUIRE_RUST_SRC=1` or `ANNEAL_CI_STRICT=1` to
        // fail closed instead of silently skipping.
        let env_truthy =
            |name: &str| std::env::var_os(name).is_some_and(|v| !v.is_empty() && v != "0");
        let required = env_truthy("ANNEAL_TEST_REQUIRE_RUST_SRC") || env_truthy("ANNEAL_CI_STRICT");
        assert!(
            !required,
            "the selected sysroot {} lacks the `rust-src` tree \
             (fail-closed under ANNEAL_TEST_REQUIRE_RUST_SRC / ANNEAL_CI_STRICT)",
            sysroot().display()
        );
        eprintln!("skipping: sysroot {} lacks the `rust-src` tree", sysroot().display());
        return;
    }
    // Stage `core` and the sibling trees it mounts through `#[path]` and
    // `include_str!` (`../../stdarch/...`, `../../portable-simd/...`) under
    // one declared `library/` root, unmodified.
    let directory = tempfile::tempdir().unwrap();
    let staged_library = directory.path().canonicalize().unwrap().join("library");
    let mut sources = Vec::new();
    for tree in ["core", "stdarch/crates/core_arch", "portable-simd/crates/core_simd"] {
        stage_tree(&library.join(tree), &staged_library.join(tree), &mut sources);
    }
    let output_dir = directory.path().join("output");
    let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
    command
        .current_dir(directory.path())
        .arg("capture")
        .arg("--crate-root")
        .arg(staged_library.join("core/src/lib.rs"))
        .args([
            "--crate-name=core",
            "--edition=2024",
            "--target=x86_64-unknown-linux-gnu",
            "--stdlib-crate=core",
            "--select=str::validations::utf8_is_cont_byte",
            "--select=str::validations::utf8_first_byte",
        ])
        .arg("--out-dir")
        .arg(&output_dir)
        .arg("--sysroot")
        .arg(sysroot());
    for source in &sources {
        command.arg("--source-file").arg(source);
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");

    let captured = manifest(&output_dir);
    assert_eq!(captured["configuration"]["stdlib_crate"], "core");
    let selected: Vec<&str> = captured["selected"]
        .as_array()
        .unwrap()
        .iter()
        .map(|body| body["path"].as_str().unwrap())
        .collect();
    assert_eq!(
        selected,
        ["str::validations::utf8_first_byte", "str::validations::utf8_is_cont_byte"]
    );
    // Every read is a staged file under `library/`, and reads cross into the
    // sibling `stdarch` tree through `core`'s own relative `#[path]`s.
    let reads = captured["source_files"].as_array().unwrap();
    for read in reads {
        let path = Path::new(read["path"].as_str().unwrap());
        assert!(path.starts_with(&staged_library), "{path:?}");
    }
    assert!(
        reads.iter().any(|read| {
            Path::new(read["path"].as_str().unwrap())
                .starts_with(staged_library.join("stdarch/crates/core_arch"))
        }),
        "no stdarch read"
    );
}
