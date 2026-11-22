// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared integration test cases for `anneal_audit::check_cargo_boundary`,
//! exercised by both `boundary_audit` and `cargo_boundary_audit`.

#[cfg(unix)]
use std::os::unix::fs::symlink;
use std::{
    fs,
    path::{Path, PathBuf},
};

use anneal_audit::{Checker, check_cargo_boundary};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_path_buf()
}

/// Minimal synthetic Cargo workspace under a fresh temporary directory with
/// `trusted/rustc-capture` as its default library member (`doctest = false`).
struct CargoFixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
}

impl CargoFixture {
    fn new() -> Self {
        let dir = tempfile::Builder::new().prefix("anneal-cargo-boundary-").tempdir().unwrap();
        let root = dir.path().to_path_buf();
        fs::create_dir_all(root.join("trusted/rustc-capture/src")).unwrap();
        fs::write(
            root.join("Cargo.toml"),
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\n",
        )
        .unwrap();
        fs::write(
            root.join("trusted/rustc-capture/Cargo.toml"),
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        )
        .unwrap();
        fs::write(root.join("trusted/rustc-capture/src/lib.rs"), b"pub fn ok() -> u32 { 0 }\n")
            .unwrap();
        Self { _dir: dir, root }
    }

    fn write(&self, rel: &str, bytes: &[u8]) {
        let path = self.root.join(rel);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, bytes).unwrap();
    }

    fn assert_rejected(&self, expected_substring: &str) {
        let err = check_cargo_boundary(&self.root).unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit code 1, got: {err}");
        assert_eq!(err.phase, "cargo-boundary", "unexpected phase: {err}");
        assert!(
            err.message.contains(expected_substring),
            "expected diagnostic containing {expected_substring:?}, got: {err}"
        );
    }

    fn assert_checker_rejected(&self, expected_substring: &str) {
        let mut checker = Checker::new(&self.root, None).unwrap();
        checker.set_require_mir_wp(false);
        let err = checker.run().unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit code 1, got: {err}");
        assert_eq!(err.phase, "cargo-boundary", "unexpected phase: {err}");
        assert!(
            err.message.contains(expected_substring),
            "expected diagnostic containing {expected_substring:?}, got: {err}"
        );
        assert!(!checker.execution_began());
    }
}

pub fn assert_accepts_real_repository() {
    check_cargo_boundary(&repo_root()).unwrap();
}

pub fn assert_accepts_valid_explicit_implicit_targets_and_in_member_rust_closure() {
    let fix = CargoFixture::new();
    fix.write(
        "Cargo.toml",
        b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/helper\",\n    \"trusted/bin-only\",\n]\nexclude = [\"trusted/excluded-dir\"]\n",
    );
    fix.write("trusted/excluded-dir/README.md", b"ignored\n");
    fix.write("trusted/lean/lean-toolchain", b"leanprover/lean4:v4.34.1\n");
    fix.write(
        "trusted/bin-only/Cargo.toml",
        b"[package]\nname = \"bin-only\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    fix.write(
        "trusted/bin-only/src/main.rs",
        "// Non-ASCII in comments (caf\u{00e9}), strings, and char literals is allowed.\n\
         const _UTF8: &str = \"caf\u{00e9}\";\n\
         const _RAW_UTF8: &str = r#\"caf\u{00e9}\"#;\n\
         const _CHAR_UTF8: char = '\u{03bb}';\n\
         fn main() {}\n"
            .as_bytes(),
    );
    fix.write(
        "trusted/helper/Cargo.toml",
        b"[package]\nname = \"helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\nautobins = true\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"custom\"\npath = \"custom/sub/main.rs\"\n",
    );
    fix.write(
        "trusted/rustc-capture/src/lib.rs",
        b"#![feature(normalize_lexically, rustc_private)]\npub fn ok() -> u32 { 0 }\n",
    );
    fix.write(
        "trusted/helper/src/lib.rs",
        br#"
pub mod extra;
exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: ["anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
    };
}
exocrate::parse_remote_archive! {
    const REMOTE_ARCHIVE: RemoteArchive = "Cargo.toml";
}
"#,
    );
    fix.write("trusted/helper/src/extra.rs", b"pub fn x() -> u8 { 1 }\n");
    fix.write("trusted/helper/src/bin/tool.rs", b"fn main() {}\n");
    fix.write("trusted/helper/examples/ex.rs", b"fn main() {}\n");
    fix.write("trusted/helper/benches/bn.rs", b"fn main() {}\n");
    fix.write("trusted/helper/data/note.txt", b"hello\n");
    fix.write("trusted/helper/custom/sub/main.rs", b"fn main() {}\n");
    fix.write("trusted/helper/tests/support/mod.rs", b"pub fn helper() -> u8 { 1 }\n");
    // Uncompiled test-subject fixture data under `src/fixtures/` or
    // `tests/fixtures/` may contain negative-test Rust syntax
    // (`#![feature(core_intrinsics)]`, `macro_rules!`, relative
    // `include_str!("../Cargo.toml")`) without failing compiled host-source
    // scanning while remaining subject to whole-member filesystem hygiene.
    fix.write(
        "trusted/helper/src/fixtures/case.rs",
        b"#![feature(core_intrinsics)]\nmacro_rules! fixture_only { () => {}; }\n",
    );
    fix.write(
        "trusted/helper/tests/fixtures/id.rs",
        b"#![feature(core_intrinsics)]\nconst _: &str = include_str!(\"../Cargo.toml\");\n",
    );
    fix.write(
        "trusted/helper/tests/t.rs",
        br####"
#[path = "../src/extra.rs"]
pub mod extra;
mod support;

// Comments and strings containing decoy directives must not trigger rejections:
// #[path = "../../../theory/evil.rs"] mod evil;
/* outer /* #[path = "../../../theory/evil.rs"] include!("../../../evil.rs") */ */
const DECOY_STR: &str = "#[path = \"../../../theory/evil.rs\"] include_str!(\"../../../x\")";
const DECOY_RAW: &str = r#"include!("../../../theory/evil.rs")"#;
const ESCAPED_QUOTE: char = '\'';
const BYTE_QUOTE: u8 = b'\'';
const NOTE: &str = include_str!("../data/note.txt");
const BYTES: &[u8] = include_bytes!("../data/note.txt");
const FIXTURE_EMBED: &str = concat!("```rust\n", include_str!("fixtures/id.rs"), "```");
#[doc = include_str!("../data/note.txt")]
pub fn lifetime_user<'a>(s: &'a str) -> &'a str { s }
"####,
    );

    check_cargo_boundary(&fix.root).unwrap();

    // `autolib = false` (with no `[lib]`), explicit `[lib] path = ...`, and
    // `autotests = false` / `autobins = false` leave uncompiled files in
    // `src/lib.rs`, `tests/`, and `src/bin/` unseeded (covered by filesystem
    // hygiene) while explicit pathless targets are still resolved and scanned.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\nautolib = false\nautotests = false\nautobins = false\n\n[[bin]]\nname = \"anneal-rustc-capture\"\n\n[[test]]\nname = \"active\"\n",
        );
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"macro_rules! uncompiled_lib_fixture { () => {}; }\n",
        );
        fix.write("trusted/rustc-capture/src/main.rs", b"fn main() {}\n");
        fix.write("trusted/rustc-capture/tests/active.rs", b"fn ok() {}\n");
        fix.write(
            "trusted/rustc-capture/tests/inactive.rs",
            b"#![feature(core_intrinsics)]\nmacro_rules! inactive_fixture { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/bin/unused.rs",
            b"macro_rules! unused_bin_fixture { () => {}; }\n",
        );
        check_cargo_boundary(&fix.root).unwrap();
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\npath = \"src/custom.rs\"\n",
        );
        fix.write("trusted/rustc-capture/src/custom.rs", b"pub fn custom() {}\n");
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"#![feature(core_intrinsics)]\nmacro_rules! stale_lib { () => {}; }\n",
        );
        check_cargo_boundary(&fix.root).unwrap();
    }

    // Bare `asm` / `global_asm` / `naked_asm` / `debugger_visualizer` identifiers
    // (without `!`, `use`, or attribute placement) are permitted, and
    // `StemSubdir` `#[path]` inside inline `mod`s follows `rustc`'s
    // `DirOwnership` rules: top-level inline `mod`s (even with nested `fn`
    // bodies) resolve under `foo/<mod>/`, an outer non-module block (`fn f()
    // { ... }`) drops the `foo/` stem permanently inside that block (ignoring
    // decoys on the uncompiled path, even across nested macros), and top-level
    // macros scan both candidates.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"mod foo;\npub trait UseExt { fn r#use<T>(&self, v: T) -> T { v } }\nimpl UseExt for () {}\npub fn use_asm_idents() -> usize { let asm = 0; let global_asm = 1; let naked_asm = 2; let debugger_visualizer = 3; let macro_rules = 4; let r#macro = 5; let toml_const = 6; let macro_util = 7; ().r#use::<usize>(asm + global_asm + naked_asm + debugger_visualizer + macro_rules + r#macro + toml_const + macro_util) }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/foo.rs",
            b"pub mod outer {\n    #[path = \"x.rs\"]\n    pub mod x;\n    pub fn owned_fn() {\n        #[path = \"y.rs\"]\n        pub mod y;\n    }\n}\npub fn block_disowned() {\n    pub mod blk {\n        #[path = \"z.rs\"]\n        pub mod z;\n    }\n    #[path = \"w.rs\"]\n    pub mod w;\n    cfg_if::cfg_if! {\n        if #[cfg(all())] {\n            pub mod blk_mac {\n                #[path = \"u.rs\"]\n                pub mod u;\n            }\n        }\n    }\n}\n",
        );
        fix.write(
            "trusted/rustc-capture/src/foo/outer/x.rs",
            b"pub fn valid_nested_i() -> u32 { 42 }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/foo/outer/y.rs",
            b"pub fn valid_nested_ii() -> u32 { 43 }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/blk/z.rs",
            b"pub fn valid_block_iii() -> u32 { 44 }\n",
        );
        fix.write("trusted/rustc-capture/src/w.rs", b"pub fn valid_block_iv() -> u32 { 45 }\n");
        fix.write(
            "trusted/rustc-capture/src/blk_mac/u.rs",
            b"pub fn valid_block_macro() -> u32 { 46 }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/outer/x.rs",
            b"macro_rules! uncompiled_sibling_outer { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/foo/blk/z.rs",
            b"macro_rules! uncompiled_stem_inside_block { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/foo/blk_mac/u.rs",
            b"macro_rules! uncompiled_stem_inside_block_macro { () => {}; }\n",
        );
        check_cargo_boundary(&fix.root).unwrap();
    }

    // Items disabled by statically false `#[cfg(...)]` predicates (`false`,
    // `any()`, `not(all())`, `all(false, unix)`, or `#[cfg_attr(all(),
    // cfg(false))]`) skip enqueuing external module files (including any
    // sibling `#[path = "..."]`, in either order, across `pub(...)`) and skip
    // scanning balanced inline `mod { ... }` bodies; unconditionally stripped
    // `#[cfg_attr(false, ...)]` inner attributes are ignored; and `path` inside
    // attribute arguments or `cfg` predicates (`#[cfg(path)]`,
    // `#[cfg(not(path))]`, `#[allow(path)]`, `#[arg(value_name = "path")]`,
    // `#[cfg_attr(path, allow(dead_code))]`) is accepted cleanly without
    // misinterpreting `path` as `#[path]`.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            br#"
#[cfg(any())]
mod disabled_fixture;

#[cfg(false)]
#[path = "../../../theory/evil.rs"]
pub(crate) mod disabled_p;

#[path = "../../../theory/evil.rs"]
#[cfg(all(false, unix))]
pub mod disabled_p_rev;

#[cfg_attr(all(), cfg(false))]
mod disabled_via_cfg_attr;

#[cfg(not(all()))]
mod disabled_inline {
    mod inner;
    #[path = "disabled_path.rs"]
    mod nested;
    macro_rules! uncompiled_inline { () => {}; }
    fn helper() { let _ = (1 + 2); }
}

#[cfg_attr(false, path = "../../../theory/evil.rs", feature(core_intrinsics))]
mod active_after_stripped_cfg_attr;

mod active_sibling;

#[cfg(any())]
include!("missing_disabled.rs");

#[cfg(false)]
::core::include!("disabled_macro_fixture.rs");

#[cfg(not(all()))]
const _: &str = {
    #[cfg(any())]
    ::std::include_str!("missing_disabled.txt");
    #[cfg_attr(all(), cfg(false))]
    include_bytes!("missing_disabled.bin");
    "ok"
};

#[cfg_attr(all(), cfg(false))]
exocrate::config! {
    const DISABLED_CFG: Config = Config {
        rel_dir_path: ["anneal", "toolchain"],
        versioned_files: &["../../../outside_disabled"],
    };
}

#[cfg(any())]
exocrate::parse_remote_archive! {
    const DISABLED_ARCHIVE: RemoteArchive = "missing_disabled.toml";
}

#[cfg(any())]
cfg_if::cfg_if! {
    if #[cfg(all())] {
        mod nonexistent_inside_disabled_macro;
    }
}

#[cfg(path)]
pub fn cfg_path_ok() {}

#[cfg(not(path))]
pub fn cfg_not_path_ok() {}

#[allow(path)]
pub fn allow_path_ok() {}

#[arg(value_name = "path")]
pub fn arg_value_name_path_ok() {}

#[cfg_attr(path, allow(dead_code))]
pub fn cfg_attr_path_pred_ok() {}

include!("generated.inc");

#[path = "module.inc"]
mod inc_mod;
"#,
        );
        fix.write(
            "trusted/rustc-capture/src/disabled_macro_fixture.rs",
            b"macro_rules! uncompiled_disabled_include { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/generated.inc",
            b"pub fn generated_inc_ok() -> u8 { 3 }\n",
        );
        fix.write("trusted/rustc-capture/src/module.inc", b"pub fn module_inc_ok() -> u8 { 4 }\n");
        fix.write(
            "trusted/rustc-capture/src/disabled_fixture.rs",
            b"macro_rules! uncompiled_cfg_any { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/disabled_path.rs",
            b"macro_rules! uncompiled_cfg_false_path { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/disabled_path_rev.rs",
            b"macro_rules! uncompiled_cfg_all_false_rev { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/disabled_via_cfg_attr.rs",
            b"macro_rules! uncompiled_cfg_attr_false { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/disabled_inline/inner.rs",
            b"macro_rules! uncompiled_inline_child { () => {}; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/active_after_stripped_cfg_attr.rs",
            b"pub fn active_stripped() -> u8 { 1 }\n",
        );
        fix.write("trusted/rustc-capture/src/active_sibling.rs", b"pub fn active() -> u8 { 2 }\n");
        check_cargo_boundary(&fix.root).unwrap();
    }

    // Inline `#[path = "..."] mod <ident> { ... }` resolves nested external
    // `mod` declarations from the overridden directory at both root
    // (`lib.rs`) and nested/non-root (`foo.rs`) levels while honoring
    // statically disabled `#[cfg(any())]`.
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/sub_ok/local.rs", b"pub fn ok() {}\n");
        fix.write("trusted/rustc-capture/src/custom_dir/local.rs", b"pub fn custom_ok() {}\n");
        fix.write(
            "trusted/rustc-capture/src/parent_stem.rs",
            b"#[path = \"custom_dir\"] pub mod thread { pub mod local; }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/outer_root.rs",
            b"pub mod outer { #[path = \"leaf_sub\"] pub mod inner { pub mod leaf; } }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/outer_root/outer/leaf_sub/leaf.rs",
            b"pub fn leaf_ok() {}\n",
        );
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            br#"
#[path = "sub_ok"]
pub mod thread {
    pub mod local;
}
pub mod parent_stem;
pub mod outer_root;
#[cfg(any())]
#[path = "../../../outside"]
pub mod disabled_inline_path {
    pub mod missing;
}
"#,
        );
        check_cargo_boundary(&fix.root).unwrap();
    }
}

#[cfg(unix)]
pub fn assert_rejects_symlinked_and_hardlinked_directories_and_files() {
    // 1. Symlinked `trusted/` directory redirecting outside the checkout.
    {
        let fix = CargoFixture::new();
        let outside = tempfile::tempdir().unwrap();
        fs::create_dir_all(outside.path().join("rustc-capture/src")).unwrap();
        fs::write(
            outside.path().join("rustc-capture/Cargo.toml"),
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        )
        .unwrap();
        fs::write(outside.path().join("rustc-capture/src/lib.rs"), b"").unwrap();
        fs::remove_dir_all(fix.root.join("trusted")).unwrap();
        symlink(outside.path(), fix.root.join("trusted")).unwrap();
        fix.assert_rejected("trusted directory must be a regular directory");
    }

    // 2. Symlinked `trusted/rustc-capture` member directory.
    {
        let fix = CargoFixture::new();
        let outside = tempfile::tempdir().unwrap();
        fs::create_dir_all(outside.path().join("src")).unwrap();
        fs::write(
            outside.path().join("Cargo.toml"),
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        )
        .unwrap();
        fs::write(outside.path().join("src/lib.rs"), b"").unwrap();
        fs::remove_dir_all(fix.root.join("trusted/rustc-capture")).unwrap();
        symlink(outside.path(), fix.root.join("trusted/rustc-capture")).unwrap();
        fix.assert_rejected("workspace member trusted/rustc-capture must be a regular directory");
    }

    // 3. Symlinked intermediate parent directory along a nested member path.
    {
        let fix = CargoFixture::new();
        let outside = tempfile::tempdir().unwrap();
        fs::create_dir_all(outside.path().join("subcrate/src")).unwrap();
        fs::write(
            outside.path().join("subcrate/Cargo.toml"),
            b"[package]\nname = \"subcrate\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        )
        .unwrap();
        fs::write(outside.path().join("subcrate/src/lib.rs"), b"").unwrap();
        symlink(outside.path(), fix.root.join("trusted/nested")).unwrap();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/nested/subcrate\",\n]\n",
        );
        fix.assert_rejected("workspace member trusted/nested/subcrate must be a regular directory");
    }

    // 3b. Symlinked member directory pointing at another crate inside
    // `trusted/`.
    {
        let fix = CargoFixture::new();
        symlink(fix.root.join("trusted/rustc-capture"), fix.root.join("trusted/member-alias"))
            .unwrap();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/member-alias\",\n]\n",
        );
        fix.assert_rejected("workspace member trusted/member-alias must be a regular directory");
    }

    // 4. Symlink traversed by a member's `path = "..."` dependency.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/helper/Cargo.toml",
            b"[package]\nname = \"helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        );
        fix.write("trusted/helper/src/lib.rs", b"");
        symlink(fix.root.join("trusted/helper"), fix.root.join("trusted/helper-link")).unwrap();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/helper\",\n]\n",
        );
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[dependencies]\nhelper = { path = \"../helper-link\" }\n",
        );
        fix.assert_rejected("path dependency traverses symlink");
    }

    // 5. Hard-linked member Rust source sharing an inode with an external file
    // outside `trusted/` (direct and end-to-end `Checker::run()`).
    {
        let fix = CargoFixture::new();
        fix.write("theory/shared.rs", b"pub fn ok() -> u32 { 0 }\n");
        fs::remove_file(fix.root.join("trusted/rustc-capture/src/lib.rs")).unwrap();
        fs::hard_link(
            fix.root.join("theory/shared.rs"),
            fix.root.join("trusted/rustc-capture/src/lib.rs"),
        )
        .unwrap();
        fix.assert_rejected("must not be hard-linked");
        fix.assert_checker_rejected("must not be hard-linked");
    }

    // 6. Hard-linked explicit `[[bin]] path = "custom/main.rs"` target file.
    {
        let fix = CargoFixture::new();
        fix.write("theory/shared_bin.rs", b"fn main() {}\n");
        fs::create_dir_all(fix.root.join("trusted/rustc-capture/custom")).unwrap();
        fs::hard_link(
            fix.root.join("theory/shared_bin.rs"),
            fix.root.join("trusted/rustc-capture/custom/main.rs"),
        )
        .unwrap();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"custom\"\npath = \"custom/main.rs\"\n",
        );
        fix.assert_rejected("must not be hard-linked");
    }

    // 7. Hard-linked root `Cargo.toml`, `Cargo.lock`, and member `Cargo.toml`.
    {
        let fix = CargoFixture::new();
        fs::hard_link(fix.root.join("Cargo.toml"), fix.root.join("Cargo.toml.link")).unwrap();
        fix.assert_rejected("root Cargo.toml must not be hard-linked");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.lock",
            b"version = 4\n\n[[package]]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\n",
        );
        fs::hard_link(fix.root.join("Cargo.lock"), fix.root.join("Cargo.lock.link")).unwrap();
        fix.assert_rejected("Cargo.lock must not be hard-linked");
    }
    {
        let fix = CargoFixture::new();
        fs::hard_link(
            fix.root.join("trusted/rustc-capture/Cargo.toml"),
            fix.root.join("member_manifest_link.toml"),
        )
        .unwrap();
        fix.assert_rejected("must not be hard-linked");
    }

    // 8. Symlink or hardlink placed inside uncompiled `src/fixtures/` or
    // `tests/fixtures/` is still rejected by whole-member filesystem hygiene.
    for fixture_dir in ["src/fixtures", "tests/fixtures"] {
        {
            let fix = CargoFixture::new();
            fix.write("theory/outside.rs", b"pub fn evil() {}\n");
            let dir = fix.root.join("trusted/rustc-capture").join(fixture_dir);
            fs::create_dir_all(&dir).unwrap();
            symlink(fix.root.join("theory/outside.rs"), dir.join("link.rs")).unwrap();
            fix.assert_rejected("symlink forbidden in workspace member trusted/rustc-capture");
        }
        {
            let fix = CargoFixture::new();
            fix.write("theory/outside.rs", b"pub fn evil() {}\n");
            let dir = fix.root.join("trusted/rustc-capture").join(fixture_dir);
            fs::create_dir_all(&dir).unwrap();
            fs::hard_link(fix.root.join("theory/outside.rs"), dir.join("hardlink.rs")).unwrap();
            fix.assert_rejected("must not be hard-linked");
            fix.assert_checker_rejected("must not be hard-linked");
        }
    }
}

pub fn assert_distinguishes_workspace_members_from_workspace_exclude() {
    // 1. Moving `trusted/rustc-capture` into `workspace.exclude` fails.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/other/Cargo.toml",
            b"[package]\nname = \"other\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        );
        fix.write("trusted/other/src/lib.rs", b"");
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/other\"]\nexclude = [\"trusted/rustc-capture\"]\n",
        );
        fix.assert_rejected("trusted/rustc-capture missing from workspace.members");
    }

    // 2. Listing a member in both `workspace.members` and `workspace.exclude`
    // fails.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/rustc-capture\"]\n",
        );
        fix.assert_rejected("workspace.exclude overlaps workspace.members: trusted/rustc-capture");
    }

    // 3. Depending on an excluded crate via `path` fails as a non-member crate.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/excluded/Cargo.toml",
            b"[package]\nname = \"excluded\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        );
        fix.write("trusted/excluded/src/lib.rs", b"");
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded\"]\n",
        );
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[dependencies]\nexcluded = { path = \"../excluded\" }\n",
        );
        fix.assert_rejected("path dependency points to non-member crate: trusted/excluded");
    }

    // 4. An excluded crate cannot appear as a source-less local package in
    // `Cargo.lock`.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/excluded/Cargo.toml",
            b"[package]\nname = \"excluded\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        );
        fix.write("trusted/excluded/src/lib.rs", b"");
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded\"]\n",
        );
        fix.write(
            "Cargo.lock",
            b"version = 4\n\n[[package]]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\n\n[[package]]\nname = \"excluded\"\nversion = \"0.1.0\"\n",
        );
        fix.assert_rejected("untrusted local package without source in Cargo.lock: excluded");
    }

    // 5. Glob patterns in `workspace.members` are rejected.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/*\"]\n",
        );
        fix.assert_rejected("workspace member outside trusted/: trusted/*");
    }

    // 6. `workspace.exclude` entries outside `trusted/` are rejected.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"theory\"]\n",
        );
        fix.assert_rejected("workspace.exclude outside trusted/");
    }

    // 7. Symlinked `workspace.exclude` directory under `trusted/` is rejected.
    #[cfg(unix)]
    {
        let fix = CargoFixture::new();
        let outside = tempfile::tempdir().unwrap();
        symlink(outside.path(), fix.root.join("trusted/excluded-link")).unwrap();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded-link\"]\n",
        );
        fix.assert_rejected("workspace.exclude trusted/excluded-link must be a regular directory");
    }

    // 8. Nested overrides inside `workspace.exclude` trees and ancestors are rejected.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded\"]\n",
        );
        fix.write(
            "trusted/excluded/.cargo/config.toml",
            b"[build]\nrustc-wrapper = \"/bin/false\"\n",
        );
        fix.assert_rejected("forbidden Cargo/toolchain override in workspace.exclude");
        fix.assert_checker_rejected("forbidden Cargo/toolchain override in workspace.exclude");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/sub/excluded\"]\n",
        );
        fix.write("trusted/sub/.cargo/config.toml", b"[build]\nrustc-wrapper = \"/bin/false\"\n");
        fix.assert_rejected("forbidden Cargo/toolchain override in trusted/sub/");
    }
    #[cfg(unix)]
    {
        let fix = CargoFixture::new();
        let outside = tempfile::tempdir().unwrap();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded\"]\n",
        );
        fix.write("trusted/excluded/README.md", b"ignored\n");
        symlink(outside.path(), fix.root.join("trusted/excluded/escape")).unwrap();
        fix.assert_rejected("symlink forbidden in workspace.exclude");
    }
    #[cfg(unix)]
    {
        let outside = tempfile::tempdir().unwrap();
        let external = outside.path().join("ext.lean");
        fs::write(&external, b"def x : Nat := 1\n").unwrap();
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded\"]\n",
        );
        fix.write("trusted/excluded/README.md", b"ignored\n");
        fs::hard_link(&external, fix.root.join("trusted/excluded/hard.lean")).unwrap();
        fix.assert_rejected("must not be hard-linked");
        fix.assert_checker_rejected("must not be hard-linked");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded\"]\n",
        );
        fix.write("trusted/excluded/notes.txt", "hidden \u{202E} text\n".as_bytes());
        fix.assert_rejected("disallowed bidi or invisible control character");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/excluded\"]\n",
        );
        fix.write("trusted/excluded/bad.lean", b"\xff\xfe");
        fix.assert_rejected("non-UTF-8 file forbidden in workspace.exclude");
    }
}

#[cfg(unix)]
pub fn assert_rejects_symlinked_implicit_and_explicit_target_sources() {
    let outside = tempfile::tempdir().unwrap();
    let outside_rs = outside.path().join("evil.rs");
    fs::write(&outside_rs, b"pub fn evil() {}\n").unwrap();
    let outside_dir = outside.path().join("dir");
    fs::create_dir_all(&outside_dir).unwrap();
    fs::write(outside_dir.join("lib.rs"), b"pub fn evil() {}\n").unwrap();
    fs::write(outside_dir.join("main.rs"), b"fn main() {}\n").unwrap();

    // 1. Symlinked `src/` directory.
    {
        let fix = CargoFixture::new();
        fs::remove_dir_all(fix.root.join("trusted/rustc-capture/src")).unwrap();
        symlink(&outside_dir, fix.root.join("trusted/rustc-capture/src")).unwrap();
        fix.assert_rejected("symlink forbidden in workspace member trusted/rustc-capture");
    }

    // 2. Symlinked implicit `src/lib.rs`.
    {
        let fix = CargoFixture::new();
        fs::remove_file(fix.root.join("trusted/rustc-capture/src/lib.rs")).unwrap();
        symlink(&outside_rs, fix.root.join("trusted/rustc-capture/src/lib.rs")).unwrap();
        fix.assert_rejected("symlink forbidden in workspace member trusted/rustc-capture");
    }

    // 2b. Symlinked file pointing at another regular file inside the same
    // member.
    {
        let fix = CargoFixture::new();
        symlink(
            fix.root.join("trusted/rustc-capture/src/lib.rs"),
            fix.root.join("trusted/rustc-capture/src/alias.rs"),
        )
        .unwrap();
        fix.assert_rejected("symlink forbidden in workspace member trusted/rustc-capture");
    }

    // 3. Symlinked implicit `src/bin/b.rs`.
    {
        let fix = CargoFixture::new();
        fs::create_dir_all(fix.root.join("trusted/rustc-capture/src/bin")).unwrap();
        symlink(&outside_rs, fix.root.join("trusted/rustc-capture/src/bin/b.rs")).unwrap();
        fix.assert_rejected("symlink forbidden in workspace member trusted/rustc-capture");
    }

    // 4. Symlinked implicit `tests/t.rs` and `tests/helper/mod.rs`.
    for rel in [
        "trusted/rustc-capture/tests/t.rs",
        "trusted/rustc-capture/tests/helper/mod.rs",
        "trusted/rustc-capture/examples/e.rs",
        "trusted/rustc-capture/benches/b.rs",
    ] {
        let fix = CargoFixture::new();
        let target = fix.root.join(rel);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        symlink(&outside_rs, &target).unwrap();
        fix.assert_rejected("symlink forbidden in workspace member trusted/rustc-capture");
    }

    // 5. Symlinked parent directory of explicit
    // `[[bin]] path = "custom/sub/main.rs"`.
    {
        let fix = CargoFixture::new();
        fs::create_dir_all(fix.root.join("trusted/rustc-capture/custom")).unwrap();
        symlink(&outside_dir, fix.root.join("trusted/rustc-capture/custom/sub")).unwrap();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"custom\"\npath = \"custom/sub/main.rs\"\n",
        );
        fix.assert_rejected("target bin.path must be a regular directory");
    }

    // 6. Symlinked leaf file of explicit `[[bin]] path = "custom/sub/main.rs"`.
    {
        let fix = CargoFixture::new();
        fs::create_dir_all(fix.root.join("trusted/rustc-capture/custom/sub")).unwrap();
        symlink(&outside_rs, fix.root.join("trusted/rustc-capture/custom/sub/main.rs")).unwrap();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"custom\"\npath = \"custom/sub/main.rs\"\n",
        );
        fix.assert_rejected("target bin.path must be a regular file");
    }

    // 7. Symlinked `[lib] path` target.
    {
        let fix = CargoFixture::new();
        fs::create_dir_all(fix.root.join("trusted/rustc-capture/alt")).unwrap();
        symlink(&outside_rs, fix.root.join("trusted/rustc-capture/alt/lib.rs")).unwrap();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\npath = \"alt/lib.rs\"\n",
        );
        fix.assert_rejected("target lib.path must be a regular file");
    }

    // 8. End-to-end `Checker::run()` fails before Lean execution on symlinked
    // target.
    {
        let fix = CargoFixture::new();
        fs::remove_file(fix.root.join("trusted/rustc-capture/src/lib.rs")).unwrap();
        symlink(&outside_rs, fix.root.join("trusted/rustc-capture/src/lib.rs")).unwrap();
        fix.assert_checker_rejected("symlink forbidden in workspace member trusted/rustc-capture");
    }
}

pub fn assert_rejects_manifest_targets_edition_doctest_proc_macros_dep_renames_and_auto_fields() {
    // 1. Explicit target using `..`, leading `/`, Windows backslash, or Windows
    // drive prefix.
    for path in [
        "../outside.rs",
        "/tmp/outside.rs",
        r#"..\outside.rs"#,
        "C:/evil.rs",
        r#"C:\Windows\win.ini"#,
    ] {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"esc\"\npath = '{path}'\n"
            )
            .as_bytes(),
        );
        fix.assert_rejected("target bin.path escapes member directory");
    }

    // 2. `[lib] proc-macro = true` and `crate-type = ["proc-macro"]`.
    for lib_section in [
        "[lib]\ndoctest = false\nproc-macro = true\n",
        "[lib]\ndoctest = false\nproc_macro = true\n",
        "[lib]\ndoctest = false\ncrate-type = [\"proc-macro\"]\n",
        "[lib]\ndoctest = false\ncrate_type = [\"proc-macro\"]\n",
    ] {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n{lib_section}"
            )
            .as_bytes(),
        );
        fix.assert_rejected("disallowed proc-macro");
    }

    // 3. Nested `[workspace]` table inside a member manifest.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[workspace]\n",
        );
        fix.assert_rejected("disallowed package.build or package.workspace");
    }

    // 4. Non-boolean `package.autobins`.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\nautobins = \"yes\"\n\n[lib]\ndoctest = false\n",
        );
        fix.assert_rejected("invalid package.autobins");
    }

    // 5. Missing explicit target file.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"missing\"\npath = \"custom/missing.rs\"\n",
        );
        fix.assert_rejected("target bin.path does not exist");
    }

    // 6. Explicit non-`.rs` target file still undergoes Rust source-closure
    // scan.
    {
        let fix = CargoFixture::new();
        fix.write("theory/evil.rs", b"pub fn evil() {}\n");
        fix.write(
            "trusted/rustc-capture/custom/main.txt",
            b"include!(\"../../../theory/evil.rs\");\n",
        );
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"custom\"\npath = \"custom/main.txt\"\n",
        );
        fix.assert_rejected("escapes member directory");
    }

    // 7. Missing or non-2024 `package.edition` (N1: prevents 2015/2018
    // `cr"\" /*"` lexer desync).
    for manifest in [
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\n\n[lib]\ndoctest = false\n",
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2018\"\n\n[lib]\ndoctest = false\n",
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\ndoctest = false\n",
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition.workspace = true\n\n[lib]\ndoctest = false\n",
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/Cargo.toml", manifest.as_bytes());
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"const _: &str = stringify!(cr\"\\\" /*\");\n#[path = \"../../../theory/evil.rs\"] pub mod evil;\n// */\n",
        );
        fix.assert_rejected("package.edition must be \"2024\"");
    }

    // 8. Target-level `edition` overrides on `[lib]`, `[[bin]]`, `[[example]]`,
    // `[[test]]`, and `[[bench]]` (N1).
    for target_section in [
        "[lib]\ndoctest = false\nedition = \"2018\"\n",
        "[lib]\ndoctest = false\n\n[[bin]]\nname = \"b\"\npath = \"src/lib.rs\"\nedition = \"2018\"\n",
        "[lib]\ndoctest = false\n\n[[example]]\nname = \"e\"\npath = \"src/lib.rs\"\nedition = \"2018\"\n",
        "[lib]\ndoctest = false\n\n[[test]]\nname = \"t\"\npath = \"src/lib.rs\"\nedition = \"2018\"\n",
        "[lib]\ndoctest = false\n\n[[bench]]\nname = \"bn\"\npath = \"src/lib.rs\"\nedition = \"2018\"\n",
    ] {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n{target_section}"
            )
            .as_bytes(),
        );
        fix.assert_rejected("disallowed target-level edition override");
    }

    // 9. Library targets must explicitly set `[lib] doctest = false` so
    // `cargo test --workspace` cannot compile unchecked doc-comment code
    // blocks.
    for manifest in [
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\n",
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = true\n",
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = \"false\"\n",
        "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\nautolib = false\n\n[lib]\npath = \"src/lib.rs\"\n",
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/Cargo.toml", manifest.as_bytes());
        fix.assert_rejected("must set [lib] doctest = false");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        );
        fix.assert_checker_rejected("must set [lib] doctest = false");
    }

    // 10. Cargo dependency renaming (`package = "..."`) is forbidden across all
    // dependency tables so crates like `exocrate` cannot be hidden behind a
    // Cargo alias.
    for dep_section in [
        "[dependencies]\nexo = { package = \"exocrate\", version = \"0.3.0\" }\n",
        "[dev-dependencies]\nexo = { package = \"exocrate\", version = \"0.3.0\" }\n",
        "[build-dependencies]\nexo = { package = \"exocrate\", version = \"0.3.0\" }\n",
        "[target.'cfg(unix)'.dependencies]\nexo = { package = \"exocrate\", version = \"0.3.0\" }\n",
    ] {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n{dep_section}"
            )
            .as_bytes(),
        );
        fix.assert_rejected("disallowed renamed dependency (package = ...)");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[dependencies]\nexo = { package = \"exocrate\", version = \"0.3.0\" }\n",
        );
        fix.assert_checker_rejected("disallowed renamed dependency (package = ...)");
    }

    // 11. Closed-world Cargo manifest and dependency schemas reject workspace
    // dependency inheritance, `cargo-features`, `package.metabuild`,
    // `package.links`, and unknown manifest/package/target/dependency keys.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/helper\"]\n\n[workspace.dependencies]\nhelper = { path = \"trusted/helper\" }\n",
        );
        fix.write(
            "trusted/helper/Cargo.toml",
            b"[package]\nname = \"helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        );
        fix.write("trusted/helper/src/lib.rs", b"");
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[dependencies]\nhelper = { workspace = true }\n",
        );
        fix.assert_rejected("root Cargo.toml may contain only [workspace]");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[dependencies]\nhelper = { workspace = true }\n",
        );
        fix.assert_rejected("disallowed workspace dependency inheritance");
        fix.assert_checker_rejected("disallowed workspace dependency inheritance");
    }
    for (manifest, expected_diag) in [
        (
            "cargo-features = [\"metabuild\"]\n\n[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
            "disallowed cargo-features",
        ),
        (
            "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\nmetabuild = [\"helper\"]\n\n[lib]\ndoctest = false\n",
            "disallowed package.metabuild",
        ),
        (
            "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\nlinks = \"foo\"\n\n[lib]\ndoctest = false\n",
            "disallowed package.links",
        ),
        (
            "[package]\nname = \"anneal-rustc-capture\"\nversion.workspace = true\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
            "disallowed workspace inheritance on package.version",
        ),
        (
            "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[lints]\n",
            "malformed member Cargo.toml",
        ),
        (
            "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[target.'cfg(unix)']\nrunner = \"x\"\n",
            "malformed member Cargo.toml",
        ),
        (
            "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\nextra = true\n",
            "malformed member Cargo.toml",
        ),
        (
            "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[dependencies]\nexo = { version = \"0.3.0\", artifact = \"bin\" }\n",
            "disallowed dependency key 'artifact'",
        ),
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/Cargo.toml", manifest.as_bytes());
        fix.assert_rejected(expected_diag);
    }

    // 12. Explicit pathless targets are still scanned when `auto* = false` and
    // fail closed if missing or ambiguous.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\nautotests = false\n\n[lib]\ndoctest = false\n\n[[test]]\nname = \"active\"\n",
        );
        fix.write("trusted/rustc-capture/tests/active.rs", b"macro_rules! sneaky { () => {}; }\n");
        fix.write("trusted/rustc-capture/tests/inactive.rs", b"pub fn ok() {}\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\nautobins = false\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = \"anneal-rustc-capture\"\n",
        );
        fix.write(
            "trusted/rustc-capture/src/main.rs",
            b"macro_rules! sneaky { () => {}; }\nfn main() {}\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n\n[[test]]\nname = \"dup\"\n",
        );
        fix.write("trusted/rustc-capture/tests/dup.rs", b"");
        fix.write("trusted/rustc-capture/tests/dup/main.rs", b"");
        fix.assert_rejected("ambiguous source files for pathless [[test]] 'dup'");
    }

    // 10. Nested Cargo/toolchain/ambient override entries inside `trusted/`,
    // intermediate member ancestors, or workspace member subdirectories are
    // rejected (direct and via `Checker::run()`).
    for (rel_path, expected_diag) in [
        ("trusted/.cargo/config.toml", "forbidden Cargo/toolchain override in trusted/: .cargo"),
        (
            "trusted/rust-toolchain.toml",
            "forbidden Cargo/toolchain override in trusted/: rust-toolchain.toml",
        ),
        (
            "trusted/rustc-capture/.cargo/config.toml",
            "forbidden Cargo/toolchain override in workspace member trusted/rustc-capture: .cargo",
        ),
        (
            "trusted/rustc-capture/src/.cargo/config.toml",
            "forbidden Cargo/toolchain override in workspace member trusted/rustc-capture: src/.cargo",
        ),
        (
            "trusted/rustc-capture/rust-toolchain.toml",
            "forbidden Cargo/toolchain override in workspace member trusted/rustc-capture: rust-toolchain.toml",
        ),
        (
            "trusted/rustc-capture/.envrc",
            "forbidden Cargo/toolchain override in workspace member trusted/rustc-capture: .envrc",
        ),
        (
            "trusted/rustc-capture/.gitattributes",
            "forbidden Cargo/toolchain override in workspace member trusted/rustc-capture: .gitattributes",
        ),
        (
            "trusted/rustc-capture/AGENTS.override.md",
            "forbidden Cargo/toolchain override in workspace member trusted/rustc-capture: AGENTS.override.md",
        ),
        (
            "trusted/rustc-capture/lean-toolchain",
            "forbidden Cargo/toolchain override in workspace member trusted/rustc-capture: lean-toolchain",
        ),
        (".envrc", "forbidden Cargo/toolchain override at repository root: .envrc"),
        ("lean-toolchain", "forbidden Cargo/toolchain override at repository root: lean-toolchain"),
    ] {
        let fix = CargoFixture::new();
        fix.write(rel_path, b"[build]\nrustc-wrapper = \"evil\"\n");
        fix.assert_rejected(expected_diag);
        fix.assert_checker_rejected(expected_diag);
    }
    // Intermediate ancestor directory between `trusted/` and a nested member
    // (`trusted/nested/.cargo/config.toml` for member `trusted/nested/pkg`).
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/nested/pkg\"]\n",
        );
        fix.write(
            "trusted/nested/pkg/Cargo.toml",
            b"[package]\nname = \"pkg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        );
        fix.write("trusted/nested/pkg/src/lib.rs", b"");
        fix.write("trusted/nested/.cargo/config.toml", b"[build]\nrustc-wrapper = \"evil\"\n");
        fix.assert_rejected("forbidden Cargo/toolchain override in trusted/nested/: .cargo");
        fix.assert_checker_rejected(
            "forbidden Cargo/toolchain override in trusted/nested/: .cargo",
        );
    }
}

pub fn assert_rejects_rust_source_closure_escapes_and_smuggling() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "direct #[path] escape",
            "#[path = \"../../../theory/evil.rs\"]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "raw string #[path] escape",
            "#[path = r#\"../../../theory/evil.rs\"#]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "hex-escaped #[path] escape",
            "#[path = \"\\x2e\\x2e/\\x2e\\x2e/\\x2e\\x2e/theory/evil.rs\"]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "raw-ident #[r#path] escape",
            "#[r#path = \"../../../theory/evil.rs\"]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "inline mod #[path] directory escape",
            "#[path = \"../..\"]\nmod outer {\n    mod inner;\n}\n",
            "escapes member directory",
        ),
        (
            "#[path] on non-mod item",
            "#[path = \"sub\"]\nfn f() {}\n",
            "#[path] attribute is permitted only on 'mod <name>' declarations",
        ),
        (
            "Windows trailing-dot #[path] alias",
            "#[cfg(windows)]\n#[path = \"payload.rs.\"]\nmod payload;\n",
            "non-portable Windows path syntax",
        ),
        (
            "Windows trailing-space include! alias",
            "include!(\"payload.rs \");\n",
            "non-portable Windows path syntax",
        ),
        (
            "Windows trailing-dot parent directory include_str! alias",
            "const S: &str = include_str!(\"sub./evil.txt\");\n",
            "non-portable Windows path syntax",
        ),
        (
            "inner #![path] attribute",
            "#![path = \"../src/lib.rs\"]\n",
            "inner #![path] attribute forbidden",
        ),
        (
            "cfg_attr path smuggling",
            "#[cfg_attr(all(), path = \"../../../theory/evil.rs\")]\nmod evil;\n",
            "unsupported or non-literal path attribute",
        ),
        (
            "cfg_attr unknown predicate path smuggling",
            "#[cfg_attr(unix, path = \"evil.rs\")]\nmod m;\n",
            "unsupported or non-literal path attribute",
        ),
        (
            "nested cfg_attr path smuggling",
            "#[cfg_attr(all(), cfg_attr(unix, path = \"evil.rs\"))]\nmod m2;\n",
            "unsupported or non-literal path attribute",
        ),
        (
            "qualified non-literal path attribute",
            "#[foo::path = \"evil.rs\"]\nmod m4;\n",
            "unsupported or non-literal path attribute",
        ),
        (
            "computed #[path = concat!(...)]",
            "#[path = concat!(\"../../..\", \"/theory/evil.rs\")]\nmod evil;\n",
            "unsupported or non-literal path attribute",
        ),
        (
            "direct include! escape",
            "include!(\"../../../theory/evil.rs\");\n",
            "escapes member directory",
        ),
        (
            "direct include_str! escape",
            "const S: &str = include_str!(\"../../../theory/evil.txt\");\n",
            "escapes member directory",
        ),
        (
            "direct include_bytes! escape",
            "const B: &[u8] = include_bytes!(\"../../../theory/evil.bin\");\n",
            "escapes member directory",
        ),
        (
            "doc attribute include_str! escape",
            "#[doc = include_str!(\"../../../theory/evil.md\")]\npub fn f() {}\n",
            "escapes member directory",
        ),
        (
            "include! after escaped-quote char literal",
            "const Q: char = '\\'';\ninclude!(\"../../../theory/evil.rs\");\n",
            "escapes member directory",
        ),
        (
            "Windows backslash #[path] under #[cfg(windows)]",
            "#[cfg(windows)]\n#[path = r#\"..\\..\\..\\theory\\evil.rs\"#]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "Windows backslash #[path]",
            "#[path = r#\"..\\..\\..\\theory\\evil.rs\"#]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "Windows drive prefix forward-slash #[path]",
            "#[path = \"C:/evil.rs\"]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "leading slash #[path]",
            "#[path = \"/etc/passwd.rs\"]\nmod evil;\n",
            "escapes member directory",
        ),
        (
            "Windows backslash include!",
            "include!(r#\"..\\evil.rs\"#);\n",
            "escapes member directory",
        ),
        (
            "Windows drive prefix include_str!",
            "const S: &str = include_str!(r#\"C:\\Windows\\win.ini\"#);\n",
            "escapes member directory",
        ),
        (
            "Windows drive prefix include_bytes!",
            "const B: &[u8] = include_bytes!(r#\"C:\\Windows\\win.ini\"#);\n",
            "escapes member directory",
        ),
        (
            "Windows backslash exocrate::config! versioned_files",
            "exocrate::config! {\n    const C: Config = Config {\n        versioned_files: &[r#\"..\\Cargo.toml\"#],\n    };\n}\n",
            "escapes member directory",
        ),
        (
            "Windows backslash exocrate::parse_remote_archive!",
            "exocrate::parse_remote_archive! {\n    const R: RemoteArchive = r#\"foo\\Cargo.toml\"#;\n}\n",
            "escapes member directory",
        ),
        (
            "include_str! canceling nonexistent directory",
            "const S: &str = include_str!(\"missing/../../../theory/evil.txt\");\n",
            "escapes member directory",
        ),
        (
            "computed include!(concat!(...))",
            "include!(concat!(\"../../..\", \"/theory/evil.rs\"));\n",
            "must take a single string literal path",
        ),
        (
            "aliased use core::include_str",
            "use core::include_str as sneak;\nconst S: &str = sneak!(\"../../../theory/evil.txt\");\n",
            "disallowed import of path-reading macro or crate 'include_str'",
        ),
        (
            "non-invocation reference to include_str",
            "fn f() { let _ = include_str; }\n",
            "disallowed non-invocation reference to include_str",
        ),
        (
            "macro_rules! definition (F1/F2 root cause)",
            "macro_rules! wrap { ($($t:tt)*) => { #[$($t)*] mod evil; }; }\n",
            "macro_rules! definitions are forbidden",
        ),
        (
            "doc-comment-to-#[path] macro_rules! synthesis (F2)",
            "macro_rules! p { ($h:tt $d:tt) => { $h [path=\"../../../theory/evil.rs\"] pub mod evil; }; }\np!(/// x);\n",
            "macro_rules! definitions are forbidden",
        ),
        (
            "declarative macro 2.0 definition",
            "pub macro sneaky() {}\n",
            "declarative macro definitions are forbidden",
        ),
        (
            "metavariable '$' inside attribute",
            "#[foo($x)]\nfn f() {}\n",
            "metavariable '$' forbidden inside attribute",
        ),
        ("standalone '#' token", "fn f() { # }\n", "standalone '#' token forbidden"),
        (
            "crate_type proc-macro attribute",
            "#![crate_type = \"proc-macro\"]\n",
            "disallowed crate_type attribute",
        ),
        (
            "macro_export attribute",
            "#[macro_export]\nfn f() {}\n",
            "disallowed macro_export attribute",
        ),
        (
            "nested inline mod #[path] escape",
            "mod inner {\n    #[path = \"../../../theory/evil.rs\"]\n    pub mod evil;\n}\n",
            "escapes member directory",
        ),
        (
            "concat_idents feature gate",
            "#![feature(concat_idents)]\n",
            "disallowed unstable feature(concat_idents)",
        ),
        (
            "frontmatter feature gate (F3)",
            "#![feature(frontmatter)]\n",
            "disallowed unstable feature(frontmatter)",
        ),
        (
            "cfg_attr frontmatter feature gate (F3)",
            "#[cfg_attr(all(), feature(frontmatter))]\n",
            "disallowed unstable feature(frontmatter)",
        ),
        (
            "frontmatter comment-shadow lexer desync (F3)",
            "---\n/*\n---\n#![feature(frontmatter)]\n#[path = \"../../../theory/evil.rs\"]\nmod evil;\n// */\n",
            "frontmatter '---' forbidden",
        ),
        ("shebang line", "#!/usr/bin/env rustc\nfn main() {}\n", "shebang '#!' forbidden"),
        ("UTF-8 BOM prefix", "\u{feff}pub fn f() {}\n", "UTF-8 BOM forbidden"),
        (
            "exocrate::config! escaping versioned_files (F4)",
            "exocrate::config! {\n    const C: Config = Config {\n        rel_dir_path: [\"a\"],\n        versioned_files: &[\"../../../theory/evil.rs\"],\n    };\n}\n",
            "escapes member directory",
        ),
        (
            "exocrate::config! non-literal versioned_files (F4)",
            "exocrate::config! {\n    const C: Config = Config {\n        rel_dir_path: [\"a\"],\n        versioned_files: &[concat!(\"../\", \"Cargo.toml\")],\n    };\n}\n",
            "must contain only string literals",
        ),
        (
            "exocrate::parse_remote_archive! escaping manifest (F4)",
            "exocrate::parse_remote_archive! {\n    const R: RemoteArchive = \"../../theory/evil.toml\";\n}\n",
            "escapes member directory",
        ),
        (
            "use exocrate alias smuggling (F4)",
            "use exocrate::parse_remote_archive as p;\np! { const R: RemoteArchive = \"../../theory/evil.toml\"; }\n",
            "disallowed import of path-reading macro or crate 'exocrate'",
        ),
        (
            "braced use exocrate alias smuggling",
            "use {exocrate as e};\n",
            "disallowed import of path-reading macro or crate 'exocrate'",
        ),
        (
            "use renamed-crate parse_remote_archive smuggling",
            "use exo::parse_remote_archive as p;\np! { const R: RemoteArchive = \"../../theory/evil.toml\"; }\n",
            "disallowed import of path-reading macro or crate 'parse_remote_archive'",
        ),
        (
            "extern crate exocrate alias smuggling (F4)",
            "extern crate exocrate as exo;\nexo::parse_remote_archive! { const R: RemoteArchive = \"../../theory/evil.toml\"; }\n",
            "disallowed extern crate alias",
        ),
        (
            "extern crate general alias smuggling",
            "extern crate core as c;\n",
            "disallowed extern crate alias",
        ),
        (
            "exocrate::macro_util::toml_const smuggling (F4)",
            "exocrate::macro_util::toml_const::toml_const! { const M: \"../../theory/evil.toml\"; }\n",
            "disallowed exocrate internal macro reference",
        ),
        (
            "unqualified parse_remote_archive! invocation (F4)",
            "parse_remote_archive! { const R: RemoteArchive = \"Cargo.toml\"; }\n",
            "unqualified or aliased parse_remote_archive! macro invocation forbidden",
        ),
        (
            "malformed \\x escape before multi-byte UTF-8 char (P3-a)",
            "const S: &str = \"\\x1\u{00e9}\";\n",
            "invalid \\x escape",
        ),
        (
            "debugger_visualizer gdb_script_file file read (N2)",
            "#![debugger_visualizer(gdb_script_file = \"../../../theory/evil.py\")]\n",
            "disallowed compile-time file-reading construct 'debugger_visualizer'",
        ),
        (
            "cfg_attr debugger_visualizer file read (N2)",
            "#[cfg_attr(all(), debugger_visualizer(natvis_file = \"../../../theory/evil.natvis\"))]\npub fn f() {}\n",
            "disallowed compile-time file-reading construct 'debugger_visualizer'",
        ),
        (
            "global_asm! .incbin file read (N2)",
            "core::arch::global_asm!(\".incbin \\\"../../../theory/evil.txt\\\"\");\n",
            "disallowed compile-time file-reading construct 'global_asm'",
        ),
        (
            "aliased use global_asm! .incbin file read (N2)",
            "use core::arch::global_asm as g;\ng!(\".incbin \\\"../../../theory/evil.txt\\\"\");\n",
            "disallowed import of compile-time file-reading construct 'global_asm'",
        ),
        (
            "asm! .incbin file read (N2)",
            "pub unsafe fn f() { core::arch::asm!(\".incbin \\\"../../../theory/evil.txt\\\"\"); }\n",
            "disallowed compile-time file-reading construct 'asm'",
        ),
        (
            "naked_asm! .incbin file read (N2)",
            "pub unsafe extern \"C\" fn f() { core::arch::naked_asm!(\".incbin \\\"../../../theory/evil.txt\\\"\"); }\n",
            "disallowed compile-time file-reading construct 'naked_asm'",
        ),
        (
            "unqualified asm! macro invocation",
            "pub unsafe fn f() { asm!(\"nop\"); }\n",
            "disallowed compile-time file-reading construct 'asm'",
        ),
        (
            "use aliased core::arch::asm",
            "use core::arch::asm as my_asm;\npub unsafe fn f() { my_asm!(\"nop\"); }\n",
            "disallowed import of compile-time file-reading construct 'asm'",
        ),
        (
            "attribute #[naked_asm]",
            "#[naked_asm]\npub fn f() {}\n",
            "disallowed compile-time file-reading construct 'naked_asm'",
        ),
        (
            "outer #[debugger_visualizer]",
            "#[debugger_visualizer(natvis_file = \"../../../theory/evil.natvis\")]\npub fn f() {}\n",
            "disallowed compile-time file-reading construct 'debugger_visualizer'",
        ),
        (
            "use core::debugger_visualizer",
            "use core::debugger_visualizer;\npub fn f() {}\n",
            "disallowed import of compile-time file-reading construct 'debugger_visualizer'",
        ),
    ];

    for (label, source, expected) in cases {
        let fix = CargoFixture::new();
        fix.write("theory/evil.rs", b"pub fn evil() {}\n");
        fix.write("theory/evil.txt", b"evil\n");
        fix.write("theory/evil.bin", b"evil\n");
        fix.write("theory/evil.md", b"evil\n");
        fix.write("theory/evil.toml", b"[package]\nname = \"evil\"\n");
        fix.write("trusted/rustc-capture/src/lib.rs", source.as_bytes());
        let err = check_cargo_boundary(&fix.root)
            .expect_err(&format!("expected rejection for case: {label}"));
        assert_eq!(err.code, 1, "case {label}: expected code 1, got {err}");
        assert_eq!(err.phase, "cargo-boundary", "case {label}: unexpected phase: {err}");
        assert!(
            err.message.contains(expected),
            "case {label}: expected diagnostic containing {expected:?}, got: {err}"
        );
    }

    for def_src in [
        &b"macro_rules! sneaky_braces { () => {}; }\n"[..],
        &b"macro_rules! sneaky_parens ( () => {}; );\n"[..],
        &b"macro_rules! sneaky_brackets [ () => {}; ];\n"[..],
        &b"macro_rules! r#type { () => {}; }\n"[..],
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", def_src);
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }

    // Raw-identifier `r#use` method calls do not swallow subsequent macros,
    // and exocrate internal identifiers remain rejected in path/use/macro form.
    {
        let fix = CargoFixture::new();
        fix.write("outside.toml", b"[package]\nname = \"out\"\n");
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"pub trait U { fn r#use<T>(&self, v: T) -> T { v } }\nimpl U for () {}\npub fn f() { ().r#use::<()>(exocrate::config! { const C: Config = Config { rel_dir_path: [\"a\"], versioned_files: &[\"../../../outside.toml\"] }; }); }\n",
        );
        fix.assert_rejected("escapes member directory");
    }
    for (src, expected) in [
        (
            "pub fn f() { exocrate::macro_util::toml_const!(\"bad\"); }\n",
            "disallowed exocrate internal macro reference 'macro_util'",
        ),
        (
            "use crate::macro_util;\npub fn f() {}\n",
            "disallowed import of path-reading macro or crate 'macro_util'",
        ),
        (
            "#[path = \"thread_files\"]\nmod thread { mod escape; }\n",
            "macro_rules! definitions are forbidden",
        ),
        (
            "#[path = \"thread_files\"]\nmod thread { #[path = \"../../../theory/evil.rs\"] mod bad; }\n",
            "escapes member directory",
        ),
    ] {
        let fix = CargoFixture::new();
        fix.write("theory/evil.rs", b"pub fn evil() {}\n");
        fix.write(
            "trusted/rustc-capture/src/thread_files/escape.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        fix.assert_rejected(expected);
    }
    // Trailing dot in Cargo target path fails closed for cross-platform safety.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\npath = \"src/lib.rs.\"\n",
        );
        fix.assert_rejected("escapes member directory");
    }

    // F1 cross-directory macro_rules! repro: macro defined in deeper submodule
    // (`src/a/b/defs.rs`) and invoked from `src/lib.rs`.
    {
        let fix = CargoFixture::new();
        fix.write("theory/evil.rs", b"pub fn evil() {}\n");
        fix.write(
            "trusted/rustc-capture/src/a/b/defs.rs",
            b"macro_rules! load_evil { () => { include!(\"../../../theory/evil.rs\"); }; }\n",
        );
        fix.write("trusted/rustc-capture/src/lib.rs", b"mod a { mod b { mod defs; } }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }

    // F4 symlinked `exocrate::parse_remote_archive!` manifest target inside
    // member.
    #[cfg(unix)]
    {
        let fix = CargoFixture::new();
        let outside = tempfile::tempdir().unwrap();
        let evil_toml = outside.path().join("evil.toml");
        fs::write(&evil_toml, b"[package]\nname = \"evil\"\n").unwrap();
        symlink(&evil_toml, fix.root.join("trusted/rustc-capture/link.toml")).unwrap();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"exocrate::parse_remote_archive! { const R: RemoteArchive = \"link.toml\"; }\n",
        );
        fix.assert_rejected("symlink forbidden in workspace member trusted/rustc-capture");
    }

    // N3: `#![feature(rustc_private)]` and `#![feature(normalize_lexically)]`
    // are restricted strictly to `trusted/rustc-capture` and rejected in other
    // workspace members.
    for (src, expected) in [
        ("#![feature(rustc_private)]\n", "disallowed unstable feature(rustc_private)"),
        ("#![feature(normalize_lexically)]\n", "disallowed unstable feature(normalize_lexically)"),
        (
            "#![cfg_attr(all(), feature(rustc_private))]\n",
            "disallowed unstable feature(rustc_private)",
        ),
    ] {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/helper\",\n]\n",
        );
        fix.write(
            "trusted/helper/Cargo.toml",
            b"[package]\nname = \"helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\ndoctest = false\n",
        );
        fix.write("trusted/helper/src/lib.rs", src.as_bytes());
        fix.assert_rejected(expected);
    }

    // Out-of-line module reachability from Cargo target roots:
    // (a) `tests/t.rs` -> `mod support;` -> `tests/support/mod.rs` with
    // `macro_rules!`.
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/tests/t.rs", b"mod support;\n");
        fix.write(
            "trusted/rustc-capture/tests/support/mod.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }

    // (b) Nested `tests/t.rs` -> `mod support;` -> `tests/support/mod.rs` ->
    // `mod helper;` -> `tests/support/helper.rs` with escaping `include_str!`.
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/tests/t.rs", b"mod support;\n");
        fix.write("trusted/rustc-capture/tests/support/mod.rs", b"mod helper;\n");
        fix.write(
            "trusted/rustc-capture/tests/support/helper.rs",
            b"const S: &str = include_str!(\"../../../../Cargo.toml\");\n",
        );
        fix.assert_rejected("escapes member directory");
    }

    // (c) Non-root `StemSubdir` resolution: both pure non-target submodule
    // chains (`tests/t.rs` -> `tests/support/mod.rs` ->
    // `tests/support/nested.rs` -> `tests/support/nested/deep.rs`) and
    // dual-mode `tests/sub.rs` -> `tests/sub/child.rs`.
    {
        let fix = CargoFixture::new();
        fix.write("theory/evil.rs", b"pub fn evil() {}\n");
        fix.write("trusted/rustc-capture/tests/t.rs", b"mod support;\n");
        fix.write("trusted/rustc-capture/tests/support/mod.rs", b"mod nested;\n");
        fix.write("trusted/rustc-capture/tests/support/nested.rs", b"mod deep;\n");
        fix.write(
            "trusted/rustc-capture/tests/support/nested/deep.rs",
            b"include!(\"../../../../../theory/evil.rs\");\n",
        );
        fix.assert_rejected("escapes member directory");
    }
    {
        let fix = CargoFixture::new();
        fix.write("theory/evil.rs", b"pub fn evil() {}\n");
        fix.write("trusted/rustc-capture/tests/t.rs", b"mod sub;\n");
        fix.write("trusted/rustc-capture/tests/sub.rs", b"mod child;\n");
        fix.write(
            "trusted/rustc-capture/tests/sub/child.rs",
            b"include!(\"../../../../theory/evil.rs\");\n",
        );
        fix.assert_rejected("escapes member directory");
    }

    // (d) Inline `mod outer { mod inner; }` -> `tests/outer/inner.rs`.
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/tests/t.rs", b"mod outer { mod inner; }\n");
        fix.write(
            "trusted/rustc-capture/tests/outer/inner.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }

    // (e) Inline `mod outer { #[path = "inner.rs"] mod m; }` ->
    // `tests/outer/inner.rs`.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/tests/t.rs",
            b"mod outer { #[path = \"inner.rs\"] mod m; }\n",
        );
        fix.write(
            "trusted/rustc-capture/tests/outer/inner.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }

    // (f) Auto-discovered `tests/sub/main.rs` and `src/bin/tool/main.rs` ->
    // `mod helper;` target roots.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/tests/sub/main.rs",
            b"macro_rules! sneaky { () => {}; }\nfn main() {}\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/bin/tool/main.rs", b"mod helper;\nfn main() {}\n");
        fix.write(
            "trusted/rustc-capture/src/bin/tool/helper.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }

    // (g) Compiling a `src/fixtures/` or `tests/fixtures/` file via `include!`
    // or `#[path]` scans it as compiled host Rust and rejects disallowed
    // features.
    for loader in
        ["include!(\"fixtures/case.rs\");\n", "#[path = \"fixtures/case.rs\"]\nmod case;\n"]
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/fixtures/case.rs", b"#![feature(core_intrinsics)]\n");
        fix.write("trusted/rustc-capture/src/lib.rs", loader.as_bytes());
        fix.assert_rejected("disallowed unstable feature(core_intrinsics)");
    }
    for loader in ["include!(\"fixtures/id.rs\");\n", "#[path = \"fixtures/id.rs\"]\nmod evil;\n"] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/tests/fixtures/id.rs", b"#![feature(core_intrinsics)]\n");
        fix.write("trusted/rustc-capture/tests/t.rs", loader.as_bytes());
        fix.assert_rejected("disallowed unstable feature(core_intrinsics)");
    }

    // (h) Non-ASCII identifiers, combining marks (such as `mod a\u{0301}`
    // which rustc NFC-normalizes), raw non-ASCII identifiers, non-ASCII
    // lifetimes, and non-ASCII whitespace outside comments and string/char
    // literals fail closed.
    for (label, src) in [
        ("combining-mark inline mod", "mod a\u{0301} { mod payload; }\n"),
        ("non-ASCII fn ident", "pub fn caf\u{00e9}() {}\n"),
        ("non-ASCII raw ident", "pub fn r#caf\u{00e9}() {}\n"),
        ("non-ASCII lifetime", "pub fn f<'\u{00e9}>(s: &'\u{00e9} str) -> &'\u{00e9} str { s }\n"),
        ("non-ASCII whitespace", "pub\u{00a0}fn f() {}\n"),
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        let err =
            check_cargo_boundary(&fix.root).expect_err(&format!("{label}: expected rejection"));
        assert_eq!(err.code, 1, "{label}: expected code 1, got: {err}");
        assert_eq!(err.phase, "cargo-boundary", "{label}: got: {err}");
        assert!(
            err.message.contains("non-ASCII token or identifier forbidden in trusted Rust source"),
            "{label}: unexpected diagnostic: {err}"
        );
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            "mod a\u{0301} { mod payload; }\n".as_bytes(),
        );
        fix.assert_checker_rejected(
            "non-ASCII token or identifier forbidden in trusted Rust source",
        );
    }

    // (i) Bidi and invisible control characters fail closed before comment and
    // literal stripping across Rust source, Cargo.toml manifests, and member
    // relative paths.
    for (label, src) in [
        (
            "bidi RLO inside allowed comment",
            "#![allow(text_direction_codepoint_in_comment)]\n// \u{202E} hidden\npub fn f() {}\n",
        ),
        ("zero-width space inside comment", "// hi\u{200B}den\npub fn f() {}\n"),
        ("LRI bidi isolate inside string literal", "const S: &str = \"a\u{2066}b\";\n"),
        ("interior BOM inside string literal", "const S: &str = \"a\u{feff}b\";\n"),
        ("Arabic letter mark inside comment", "// \u{061C}\npub fn f() {}\n"),
        ("soft hyphen U+00AD inside string literal", "const S: &str = \"a\u{00AD}b\";\n"),
        ("function application U+2061 inside comment", "// a\u{2061}b\npub fn f() {}\n"),
        ("DEL control inside comment", "// \u{007F}\npub fn f() {}\n"),
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        let err =
            check_cargo_boundary(&fix.root).expect_err(&format!("{label}: expected rejection"));
        assert_eq!(err.code, 1, "{label}: expected code 1, got: {err}");
        assert_eq!(err.phase, "cargo-boundary", "{label}: got: {err}");
        assert!(
            err.message.contains("disallowed bidi or invisible control character"),
            "{label}: unexpected diagnostic: {err}"
        );
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            "#![allow(text_direction_codepoint_in_comment)]\n// \u{202E} hidden\npub fn f() {}\n"
                .as_bytes(),
        );
        fix.assert_checker_rejected("disallowed bidi or invisible control character");
    }
    for comment_char in [
        "\u{202E}",
        "\u{00AD}",
        "\u{2061}",
        "\u{FFF0}",
        "\u{FFF8}",
        "\u{E0000}",
        "\u{E0002}",
        "\u{E0080}",
        "\u{E01F0}",
    ] {
        let fix = CargoFixture::new();
        let toml = format!(
            "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n# {comment_char}\n\n[lib]\ndoctest = false\n"
        );
        fix.write("trusted/rustc-capture/Cargo.toml", toml.as_bytes());
        fix.assert_rejected("disallowed bidi or invisible control character");
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            format!("// {comment_char}\npub fn f() {{}}\n").as_bytes(),
        );
        fix.assert_rejected("disallowed bidi or invisible control character");
        fix.write(
            "trusted/rustc-capture/README.md",
            format!("text {comment_char} end\n").as_bytes(),
        );
        fix.assert_rejected("disallowed bidi or invisible control character");
    }
    for rel in ["trusted/rustc-capture/README.md", "trusted/rustc-capture/src/fixtures/case.rs"] {
        let fix = CargoFixture::new();
        fix.write(rel, "hidden \u{202E} text\n".as_bytes());
        fix.assert_rejected("disallowed bidi or invisible control character");
        fix.assert_checker_rejected("disallowed bidi or invisible control character");
    }
    // Binary resources (such as PNGs/archives consumed via `include_bytes!`)
    // are permitted when path, single-link, and containment checks pass, while
    // mandatory text extensions (like `.rs`) and NUL-free UTF-8 files still
    // enforce UTF-8 and invisible-control checks.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"pub const RAW: &[u8] = include_bytes!(\"../data/raw.bin\");\n",
        );
        fix.write("trusted/rustc-capture/data/raw.bin", b"\x89PNG\r\n\x1a\n\x00\xff\xfe");
        fix.write("trusted/rustc-capture/data/nul.bin", b"\x00\x01\x02\x03");
        check_cargo_boundary(&fix.root).unwrap();
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/fixtures/bad.rs", b"\xff\xfe");
        fix.assert_rejected("non-UTF-8 file forbidden");
    }
    // Workspace member and exclude roots must pass canonical printable-ASCII,
    // override, and global case-collision checks before walking contents.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/Foo\", \"trusted/foo\"]\n",
        );
        for (dir, pkg) in [("trusted/Foo", "foo"), ("trusted/foo", "foo_two")] {
            fix.write(
                &format!("{dir}/Cargo.toml"),
                format!("[package]\nname = \"{pkg}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n")
                    .as_bytes(),
            );
            fix.write(&format!("{dir}/src/main.rs"), b"fn main() {}\n");
        }
        fix.assert_rejected("case-colliding workspace paths");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/Sub/pkg-one\", \"trusted/sub/pkg-two\"]\n",
        );
        for (dir, pkg) in [("trusted/Sub/pkg-one", "pkg_one"), ("trusted/sub/pkg-two", "pkg_two")] {
            fix.write(
                &format!("{dir}/Cargo.toml"),
                format!("[package]\nname = \"{pkg}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n")
                    .as_bytes(),
            );
            fix.write(&format!("{dir}/src/main.rs"), b"fn main() {}\n");
        }
        fix.assert_rejected("case-colliding workspace paths");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/Rustc-Capture\"]\n",
        );
        fix.write("trusted/Rustc-Capture/README.md", b"ignored\n");
        fix.assert_rejected("case-colliding workspace paths");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            "[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/caf\u{00E9}\"]\n"
                .as_bytes(),
        );
        fix.write(
            "trusted/caf\u{00E9}/Cargo.toml",
            b"[package]\nname = \"cafe\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        );
        fix.write("trusted/caf\u{00E9}/src/main.rs", b"fn main() {}\n");
        fix.assert_rejected("non-ASCII, or uses glob");
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/data/zw\u{200B}s.txt", b"hi\n");
        fix.assert_rejected("disallowed bidi or invisible control character");
    }
    // Non-mandatory-extension NUL-free UTF-8 fallback still rejects bidi/control.
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/data/notes.cfg", "hidden \u{202E} text\n".as_bytes());
        fix.assert_rejected("disallowed bidi or invisible control character");
        fix.assert_checker_rejected("disallowed bidi or invisible control character");
    }
    // Workspace member/exclude roots reject forbidden override segments directly.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/sub/.cargo\"]\n",
        );
        fix.write(
            "trusted/sub/.cargo/Cargo.toml",
            b"[package]\nname = \"dot_cargo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        );
        fix.write("trusted/sub/.cargo/src/main.rs", b"fn main() {}\n");
        fix.assert_rejected(
            "forbidden Cargo/toolchain override in workspace member trusted/sub/.cargo: trusted/sub/.cargo",
        );
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/x/.cargo\"]\n",
        );
        fix.write("trusted/x/.cargo/README.md", b"ignored\n");
        fix.assert_rejected(
            "forbidden Cargo/toolchain override in workspace.exclude trusted/x/.cargo: trusted/x/.cargo",
        );
    }
    // Exclude roots share global case-collision tracking with walked member files.
    {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\nexclude = [\"trusted/rustc-capture/data\"]\n",
        );
        fix.write("trusted/rustc-capture/data/README.md", b"excluded\n");
        fix.write("trusted/rustc-capture/Data/raw.bin", b"\x00\x01");
        fix.assert_rejected("case-colliding workspace paths");
    }

    // (j) StemSubdir inline `mod` `#[path]` obeys `rustc` `DirOwnership`:
    // (i) `mod outer { #[path = "x.rs"] mod x; }` -> `src/foo/outer/x.rs`,
    // (ii) `mod outer { fn f() { #[path = "x.rs"] mod x; } }` ->
    // `src/foo/outer/x.rs`,
    // (iii) `fn f()` / `const _: () = { ... }` enclosing `mod outer` ->
    // `src/outer/x.rs`,
    // (iv) `fn f() { #[path = "x.rs"] mod x; }` -> `src/x.rs`,
    // (v) top-level macro invocations (`{...}`, `(...)`, `[...]`)
    // conservatively scan both `src/foo/outer/x.rs` and `src/outer/x.rs`.
    for foo_src in [
        &b"mod outer { #[path = \"x.rs\"] mod x; }\n"[..],
        &b"mod outer { fn f() { #[path = \"x.rs\"] mod x; } }\n"[..],
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", b"mod foo;\n");
        fix.write("trusted/rustc-capture/src/foo.rs", foo_src);
        fix.write(
            "trusted/rustc-capture/src/foo/outer/x.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    for foo_src in [
        &b"fn f() { mod outer { #[path = \"x.rs\"] mod x; } }\n"[..],
        &b"const _: () = { mod outer { #[path = \"x.rs\"] mod x; } };\n"[..],
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", b"mod foo;\n");
        fix.write("trusted/rustc-capture/src/foo.rs", foo_src);
        fix.write("trusted/rustc-capture/src/outer/x.rs", b"macro_rules! sneaky { () => {}; }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", b"mod foo;\n");
        fix.write("trusted/rustc-capture/src/foo.rs", b"fn f() { #[path = \"x.rs\"] mod x; }\n");
        fix.write("trusted/rustc-capture/src/x.rs", b"macro_rules! sneaky { () => {}; }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
    }
    for foo_src in [
        &b"extern crate cfg_if;\ncfg_if::cfg_if! { if #[cfg(all())] { mod outer { #[path = \"x.rs\"] mod x; } } }\n"[..],
        &b"extern crate cfg_if;\ncfg_if::cfg_if!(if #[cfg(all())] { mod outer { #[path = \"x.rs\"] mod x; } });\n"[..],
        &b"extern crate cfg_if;\ncfg_if::cfg_if![if #[cfg(all())] { mod outer { #[path = \"x.rs\"] mod x; } }];\n"[..],
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", b"mod foo;\n");
        fix.write("trusted/rustc-capture/src/foo.rs", foo_src);
        fix.write(
            "trusted/rustc-capture/src/outer/x.rs",
            b"pub fn decoy() {}\n",
        );
        fix.write(
            "trusted/rustc-capture/src/foo/outer/x.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    for foo_src in [
        &b"wrap_block! { mod outer { #[path = \"x.rs\"] mod x; } }\n"[..],
        &b"wrap_block!(mod outer { #[path = \"x.rs\"] mod x; });\n"[..],
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", b"mod foo;\n");
        fix.write("trusted/rustc-capture/src/foo.rs", foo_src);
        fix.write("trusted/rustc-capture/src/foo/outer/x.rs", b"pub fn decoy() {}\n");
        fix.write("trusted/rustc-capture/src/outer/x.rs", b"macro_rules! sneaky { () => {}; }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }

    // (k) Non-ASCII homoglyph member paths and case-colliding member paths
    // fail closed.
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/payl\u{043e}ad.rs", b"pub fn x() {}\n");
        fix.assert_rejected("non-ASCII or non-canonical relative path forbidden");
        fix.assert_checker_rejected("non-ASCII or non-canonical relative path forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/Foo.rs", b"pub fn a() {}\n");
        fix.write("trusted/rustc-capture/src/foo.rs", b"pub fn b() {}\n");
        fix.assert_rejected("case-colliding paths forbidden");
        fix.assert_checker_rejected("case-colliding paths forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/data/Sub/a.txt", b"a\n");
        fix.write("trusted/rustc-capture/data/sub/b.txt", b"b\n");
        fix.assert_rejected("case-colliding paths forbidden");
    }

    // (l) Non-static `#[cfg(...)]` predicates (`#[cfg(unix)]`, `#[cfg(path)]`,
    // `#[cfg_attr(unix, cfg(false))]`), raw-identifier `cfg`/`cfg_attr` bypass
    // attempts (`not(r#true)`, `r#false`, `r#cfg`, `r#cfg_attr`, `r#path`),
    // `cfg`/`cfg_attr` inside macro invocations (at file level, inside `fn`,
    // and inside inline `mod`), active `#[path = "evil.rs"]`, `#[cfg(false)]`
    // attached only to a preceding `fn` before an enabled `mod`, and malformed
    // delimiters in disabled inline `mod`s fail closed.
    for src in [
        "#[cfg(unix)]\nmod evil;\n",
        "#[cfg(path)]\nmod evil;\n",
        "#[cfg(unix)]\n#[path = \"evil.rs\"]\nmod m;\n",
        "#[cfg_attr(unix, cfg(false))]\nmod evil;\n",
        "#[allow(unexpected_cfgs)]\n#[cfg(not(r#true))]\nmod evil;\n",
        "#[cfg(not(any(r#true)))]\nmod evil;\n",
        "#[cfg_attr(all(), cfg(not(r#true)))]\nmod evil;\n",
        "#[cfg(r#false)]\nmod evil;\n",
        "#[r#cfg(false)]\nmod evil;\n",
        "#[cfg_attr(all(), r#cfg(false))]\nmod evil;\n",
        "#[r#path = \"evil.rs\"]\nmod m4;\n",
        "foo::bar! { #[cfg(false)] mod evil; }\n",
        "pub fn f() { foo::bar! { #[cfg(false)] mod evil; } }\n",
        "#[cfg(false)]\nfn disabled_fn() {}\nmod evil;\n",
        "#[path = \"evil.rs\"]\nmod m3;\n",
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        fix.write("trusted/rustc-capture/src/evil.rs", b"macro_rules! sneaky { () => {}; }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"pub mod outer { foo::bar! { #[cfg(false)] mod evil; } }\n",
        );
        fix.write(
            "trusted/rustc-capture/src/outer/evil.rs",
            b"macro_rules! sneaky { () => {}; }\n",
        );
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    for src in [
        "#[cfg_attr(not(r#true), path = \"evil.rs\")]\nmod x;\n",
        "#[r#cfg_attr(false, path = \"evil.rs\")]\nmod x;\n",
        "foo::bar! { #[cfg_attr(false, path = \"evil.rs\")] mod x; }\n",
        "pub fn f() { foo::bar! { #[cfg_attr(false, path = \"evil.rs\")] mod x; } }\n",
        "pub mod outer { foo::bar! { #[cfg_attr(false, path = \"evil.rs\")] mod x; } }\n",
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        fix.write("trusted/rustc-capture/src/x.rs", b"pub fn ok() {}\n");
        fix.write("trusted/rustc-capture/src/evil.rs", b"pub fn sneaky() {}\n");
        fix.assert_rejected("unsupported or non-literal path attribute");
        fix.assert_checker_rejected("unsupported or non-literal path attribute");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"#[cfg(any())]\nmod disabled_inline {\n    ( }\n}\n",
        );
        fix.assert_rejected("mismatched closing delimiter");
        fix.assert_checker_rejected("mismatched closing delimiter");
    }

    // (m) Non-`.rs` targets in `include!` and `#[path]` are followed into the
    // Rust scanner (so `macro_rules!` inside `.inc` files is rejected),
    // Windows path separators/drive prefixes fail closed via `Checker::run()`,
    // disabled item macro invocations never leak `pending_item_cfg_disabled` to
    // subsequent items or bypass `macro_rules!` / `macro` / unbalanced
    // delimiters, and `#[cfg(Unknown)]` or macro-wrapped `#[cfg(any())]`
    // `include!` still fails closed.
    for (rel, lib_src) in [
        ("trusted/rustc-capture/src/generated.inc", b"include!(\"generated.inc\");\n".as_slice()),
        (
            "trusted/rustc-capture/src/module.inc",
            b"#[path = \"module.inc\"]\nmod module;\n".as_slice(),
        ),
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", lib_src);
        fix.write(rel, b"macro_rules! sneaky { () => {}; }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"#[cfg(windows)]\n#[path = r#\"..\\..\\..\\theory\\evil.rs\"#]\nmod evil;\n",
        );
        fix.assert_checker_rejected("escapes member directory");
    }
    for src in [
        "#[cfg(any())]\ninclude!(\"fixture.rs\");\ninclude!(\"evil.rs\");\n",
        "#[cfg(any())]\nexocrate::config! { const C: Config = Config { versioned_files: &[\"fixture.rs\"] }; }\ninclude!(\"evil.rs\");\n",
        "#[cfg(unix)]\ninclude!(\"evil.rs\");\n",
        "#[cfg(unix)]\ncore::include!(\"evil.rs\");\n",
        "#[cfg_attr(unix, cfg(false))]\ninclude!(\"evil.rs\");\n",
        "#[r#cfg(false)]\ninclude!(\"evil.rs\");\n",
        "foo::bar! { #[cfg(any())] include!(\"evil.rs\"); }\n",
        "pub fn f() { foo::bar! { #[cfg(any())] include!(\"evil.rs\"); } }\n",
        "#[cfg(any())]\nfn disabled_fn() {}\ninclude!(\"evil.rs\");\n",
        "#[cfg(any())]\nfn disabled_body() { include!(\"evil.rs\"); }\n",
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        fix.write("trusted/rustc-capture/src/fixture.rs", b"pub fn ok() {}\n");
        fix.write("trusted/rustc-capture/src/evil.rs", b"macro_rules! sneaky { () => {}; }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/rustc-capture/src/lib.rs",
            b"pub mod outer { foo::bar! { #[cfg(any())] include!(\"evil.rs\"); } }\n",
        );
        fix.write("trusted/rustc-capture/src/evil.rs", b"macro_rules! sneaky { () => {}; }\n");
        fix.assert_rejected("macro_rules! definitions are forbidden");
        fix.assert_checker_rejected("macro_rules! definitions are forbidden");
    }
    for (src, expected) in [
        (
            "#[cfg(any())]\nmacro_rules! evil { () => {}; }\n",
            "macro_rules! definitions are forbidden",
        ),
        (
            "#[cfg_attr(all(), cfg(false))]\nmacro_rules! evil { () => {}; }\n",
            "macro_rules! definitions are forbidden",
        ),
        ("#[cfg(any())]\nmacro evil() {}\n", "declarative macro definitions are forbidden"),
        ("#[cfg(any())]\npub macro evil() {}\n", "declarative macro definitions are forbidden"),
        ("#[cfg(any())]\ninclude!( ( [ ) ] );\n", "mismatched closing delimiter"),
        ("#[cfg(any())]\ninclude!( ( );\n", "unclosed delimiter"),
        (
            "#[cfg(any())]\nconst S: &str = include_str!(\"../../../theory/evil.txt\");\n",
            "escapes member directory",
        ),
    ] {
        let fix = CargoFixture::new();
        fix.write("theory/evil.txt", b"evil\n");
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        fix.assert_rejected(expected);
        fix.assert_checker_rejected(expected);
    }
}

pub fn assert_rejects_case_folded_aliases_unlisted_overrides_submodules_and_manifest_bidi() {
    // 1. Case-folded module aliases on case-sensitive Linux must still fail closed.
    for (src, file_rel) in [
        ("#[cfg(windows)] mod Payload;\n", "trusted/rustc-capture/src/payload.rs"),
        (
            "#[cfg(windows)] #[path = \"Payload.rs\"] mod p;\n",
            "trusted/rustc-capture/src/payload.rs",
        ),
        ("#[cfg(windows)] mod Payload;\n", "trusted/rustc-capture/src/payload/mod.rs"),
        ("#[cfg(windows)] mod payload;\n", "trusted/rustc-capture/src/payload/MOD.RS"),
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        fix.write(file_rel, b"pub fn hidden() {}\n");
        fix.assert_rejected("case-folded path alias forbidden");
        fix.assert_checker_rejected("case-folded path alias forbidden");
    }
    // Repro (a)-(c): case-folded module search directories (`src/A/` for `mod a;`,
    // inline `mod x { mod y; }` with `src/X/y.rs`, inline `mod x { #[path="y.rs"] }` with `src/X/y.rs`).
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", b"mod a;\n");
        fix.write("trusted/rustc-capture/src/a.rs", b"#[cfg(windows)] mod b;\n");
        fix.write("trusted/rustc-capture/src/A/b.rs", b"pub fn hidden() {}\n");
        fix.assert_rejected("case-folded path alias forbidden");
        fix.assert_checker_rejected("case-folded path alias forbidden");
    }
    for lib_src in [
        "pub mod x { #[cfg(windows)] mod y; }\n",
        "pub mod x { #[cfg(windows)] #[path = \"y.rs\"] mod y; }\n",
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", lib_src.as_bytes());
        fix.write("trusted/rustc-capture/src/X/y.rs", b"pub fn hidden() {}\n");
        fix.assert_rejected("case-folded path alias forbidden");
        fix.assert_checker_rejected("case-folded path alias forbidden");
    }
    // Repro (d): case-folded implicit Cargo target & build-script probes
    // (`Build.rs`, `src/Main.rs`, `src/Bin/x.rs`, `Tests/x.rs`, `tests/sub/Main.rs`, `Src/lib.rs`).
    for (bin_path, alias_rel) in [
        ("entry.rs", "trusted/bin-only/Build.rs"),
        ("entry.rs", "trusted/bin-only/Src/lib.rs"),
        ("entry.rs", "trusted/bin-only/src/Main.rs"),
        ("entry.rs", "trusted/bin-only/src/Bin/x.rs"),
        ("entry.rs", "trusted/bin-only/Tests/x.rs"),
        ("entry.rs", "trusted/bin-only/tests/sub/Main.rs"),
    ] {
        let fix = CargoFixture::new();
        fix.write(
            "Cargo.toml",
            b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"trusted/bin-only\"]\n",
        );
        fix.write(
            "trusted/bin-only/Cargo.toml",
            format!(
                "[package]\nname = \"bin-only\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[[bin]]\nname = \"tool\"\npath = \"{bin_path}\"\n"
            )
            .as_bytes(),
        );
        fix.write(&format!("trusted/bin-only/{bin_path}"), b"fn main() {}\n");
        fix.write(alias_rel, b"fn hidden() {}\n");
        fix.assert_rejected("case-folded path alias forbidden");
        fix.assert_checker_rejected("case-folded path alias forbidden");
    }

    // 2. Unlisted nested subtrees under `trusted/` must be walked for overrides & `.git`.
    {
        let fix = CargoFixture::new();
        fix.write(
            "trusted/tools/project/.cargo/config.toml",
            b"[build]\nrustc-wrapper = \"/tmp/evil\"\n",
        );
        fix.assert_rejected("forbidden Cargo/toolchain override");
        fix.assert_checker_rejected("forbidden Cargo/toolchain override");
    }
    #[cfg(unix)]
    {
        let fix = CargoFixture::new();
        let outside = fix.root.join("outside_tools");
        fs::create_dir_all(outside.join(".cargo")).unwrap();
        fs::write(outside.join(".cargo/config.toml"), b"[build]\n").unwrap();
        symlink(&outside, fix.root.join("trusted/tools")).unwrap();
        fix.assert_rejected("symlink forbidden in trusted tree trusted");
        fix.assert_checker_rejected("symlink forbidden in trusted tree trusted");
    }

    // 3. Nested `.git` submodule markers and `160000` gitlink index entries fail closed.
    {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/sub/.git", b"gitdir: ../../../outside\n");
        fix.assert_rejected("forbidden nested .git/submodule entry");
        fix.assert_checker_rejected("forbidden nested .git/submodule entry");
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/unlisted-sub/.git/HEAD", b"ref: refs/heads/main\n");
        fix.assert_rejected("forbidden nested .git/submodule entry");
        fix.assert_checker_rejected("forbidden nested .git/submodule entry");
    }
    {
        let fix = CargoFixture::new();
        let sub_repo = tempfile::Builder::new().prefix("anneal-subrepo-").tempdir().unwrap();
        let run_git = |cwd: &Path, args: &[&str]| {
            let out = std::process::Command::new("git")
                .args(["-c", "user.name=Test", "-c", "user.email=test@example.com"])
                .args(args)
                .current_dir(cwd)
                .output()
                .unwrap();
            assert!(
                out.status.success(),
                "git {:?} failed: {}",
                args,
                String::from_utf8_lossy(&out.stderr)
            );
        };
        run_git(sub_repo.path(), &["init"]);
        fs::write(sub_repo.path().join("lib.rs"), b"pub fn sub() {}\n").unwrap();
        run_git(sub_repo.path(), &["add", "lib.rs"]);
        run_git(sub_repo.path(), &["commit", "-m", "init sub"]);
        let rev_out = std::process::Command::new("git")
            .args(["rev-parse", "HEAD"])
            .current_dir(sub_repo.path())
            .output()
            .unwrap();
        let rev = String::from_utf8(rev_out.stdout).unwrap();
        let rev = rev.trim();

        run_git(&fix.root, &["init"]);
        run_git(&fix.root, &["add", "Cargo.toml", "trusted"]);
        run_git(
            &fix.root,
            &[
                "update-index",
                "--add",
                "--cacheinfo",
                &format!("160000,{rev},trusted/unlisted-submod"),
            ],
        );
        fix.assert_rejected("gitlink/submodule forbidden in workspace: trusted/unlisted-submod");
        fix.assert_checker_rejected(
            "gitlink/submodule forbidden in workspace: trusted/unlisted-submod",
        );
    }

    // 4. Pinned root manifests with matching digests must still scan for bidi/invisible controls.
    {
        let fix = CargoFixture::new();
        fix.write("Cargo.lock", b"version = 4\n");
        fix.write("flake.nix", "// hidden \u{202E} bidi\n{}\n".as_bytes());
        fix.write("flake.lock", b"{}\n");
        let manifest: String = ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"]
            .into_iter()
            .map(|rel| {
                let hex = cargo_anneal::sha256_file(&fix.root.join(rel), "test").unwrap();
                format!("{hex}  {rel}\n")
            })
            .collect();
        fix.write("trusted/root-manifest.sha256", manifest.as_bytes());
        fix.assert_rejected("disallowed bidi or invisible control");
        fix.assert_checker_rejected("disallowed bidi or invisible control");
    }

    // 5. NTFS alternate data streams (`::$DATA`) and Windows 8.3 short names (`~1`) fail closed on Linux too.
    for src in [
        "#[cfg(windows)] include!(\"payload.rs::$DATA\");\n",
        "#[cfg(windows)] #[path = \"payload.rs::$DATA\"] mod p;\n",
        "#[cfg(windows)] include!(\"PAYLOA~1.RS\");\n",
        "#[cfg(windows)] #[path = \"PAYLOA~1.RS\"] mod p;\n",
    ] {
        let fix = CargoFixture::new();
        fix.write("trusted/rustc-capture/src/lib.rs", src.as_bytes());
        fix.write("trusted/rustc-capture/src/payload.rs", b"macro_rules! evil { () => {}; }\n");
        fix.write(
            "trusted/rustc-capture/src/payload_source.rs",
            b"macro_rules! evil { () => {}; }\n",
        );
        fix.assert_rejected("non-portable Windows path syntax");
        fix.assert_checker_rejected("non-portable Windows path syntax");
    }

    // 6. Unlisted `trusted/` subtrees (e.g., `trusted/lean/`) enforce single-link and UTF-8/bidi hygiene.
    #[cfg(unix)]
    {
        let fix = CargoFixture::new();
        fix.write("outside_lean.lean", b"-- ok\n");
        fix.write("trusted/lean/lean-toolchain", b"leanprover/lean4:v4.34.1\n");
        fs::hard_link(
            fix.root.join("outside_lean.lean"),
            fix.root.join("trusted/lean/Hardlinked.lean"),
        )
        .unwrap();
        fix.assert_rejected("must not be hard-linked");
        fix.assert_checker_rejected("must not be hard-linked");
    }
    {
        let fix = CargoFixture::new();
        fix.write("trusted/correspondence/Bidi.lean", "-- \u{202E} hidden\n".as_bytes());
        fix.assert_rejected("disallowed bidi or invisible control");
        fix.assert_checker_rejected("disallowed bidi or invisible control");
    }

    // 7. Checked-in build/cache outputs (`target/`, `.lake/`, `/result*`, `.olean*`, `.ilean`, `.ir`, `.ir.sig`) fail closed.
    for artifact in [
        "result-build/output",
        "result",
        ".lake/build/out",
        "trusted/rustc-capture/target/debug/out",
        "trusted/rustc-capture/.lake/build/out",
        "trusted/lean/Trusted.olean",
        "trusted/lean/Trusted.olean.server",
        "trusted/lean/Trusted.olean.private",
        "trusted/lean/Trusted.ilean",
        "trusted/lean/Trusted.ir",
        "trusted/lean/Trusted.ir.sig",
    ] {
        let fix = CargoFixture::new();
        fix.write(artifact, b"stale\n");
        fix.assert_rejected("checked-in build/cache artifact forbidden");
        fix.assert_checker_rejected("checked-in build/cache artifact forbidden");
    }
}
