// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Automated 6-seam nightly pass-order sentinel and `O1a-Dual` capture suite.
//!
//! Anneal captures `optimized_mir` at `MirPhase::Runtime(PostCleanup)` on the
//! pinned nightly toolchain (`rustc 1.98.0-nightly`, commit
//! `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). These tests pin the six cospan
//! seams where a compiler upgrade could silently move a MIR pass across the
//! capture point, weaken feature/cfg gating, or drift between expansion,
//! type-checking, and extraction:
//!
//! 1. `PlaceMention` preservation via `-Zmir-preserve-ub` (and fail-closed
//!    refusal of projected `PlaceMention`, generalizing `#4042`).
//! 2. `SwitchInt` / trivial-discriminant read preservation across
//!    `Runtime(PostCleanup)`.
//! 3. `CallSource::Use` / `#![feature(ergonomic_clones)]` fail-closed refusal
//!    (generalizing `#4083`).
//! 4. Closed positive `#![feature(...)]` allowlist (empty `[]` for normal
//!    crates across unstable lang and lib features unless named by
//!    `--allow-unstable-feature`, with a non-overridable hard-ban floor;
//!    already-stabilized `ACCEPTED_LANG_FEATURES` are admitted and recorded,
//!    and inactive `#![cfg_attr(..., feature(...))]` lines other than
//!    `rustc_private`, such as `zerocopy`'s, are preserved).
//! 5. `debug_assert!` erasure under `-Cdebug-assertions=no` (even when
//!    `--overflow-checks` is enabled) and general `cfg(miri)` refusal across
//!    all crates.
//! 6. Macro expansion, `#[path]` / `include!` provenance, and
//!    primitive/type-name shadowing seams.
//!
//! The final test additionally pins `O1a-Dual` CLI-level adversarial cases:
//! ill-formed `#[repr(...)]` attributes (`E0587`, `E0690`, `E0692`) and
//! dead-branch generic post-monomorphization errors (`eval_required_consts`).

// The packaged compiler has only its native standard library. The typed
// capture profile requires the x86-64 Linux standard library.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::{
    path::PathBuf,
    process::{Command, Output},
};

use serde_json::{Value, json};

const NO_CORE_STUB: &str = r#"#![feature(no_core, lang_items)]
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

pub fn selected(x: u8) -> u8 {
    x
}
"#;

fn sysroot() -> PathBuf {
    anneal_testkit::default_rust_sysroot().expect("resolve pinned compiler sysroot")
}

struct Capture {
    directory: tempfile::TempDir,
    source: PathBuf,
    output: PathBuf,
}

impl Capture {
    fn new(source: &[u8]) -> Self {
        let directory = tempfile::tempdir().expect("create sentinel capture fixture");
        let source_path = directory.path().join("input.rs");
        std::fs::write(&source_path, source).expect("write sentinel capture fixture");
        let output = directory.path().join("output");
        Self { directory, source: source_path, output }
    }

    fn command(&self) -> Command {
        self.command_with("sentinel", true)
    }

    fn command_with(&self, crate_name: &str, declare_source: bool) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
        command
            .current_dir(self.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&self.source)
            .arg(format!("--crate-name={crate_name}"))
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&self.output)
            .arg("--sysroot")
            .arg(sysroot());
        if declare_source {
            command.arg("--source-file").arg(&self.source);
        }
        command
    }

    fn selected_command(&self) -> Command {
        let mut command = self.command();
        command.arg("--select=selected");
        command
    }

    fn lean_source(&self) -> String {
        std::fs::read_to_string(self.output.join("Captured.lean")).expect("read Captured.lean")
    }

    fn manifest(&self) -> Value {
        serde_json::from_slice(
            &std::fs::read(self.output.join("capture.json")).expect("read capture.json"),
        )
        .expect("parse capture.json")
    }

    fn assert_no_capture_artifacts(&self) {
        for name in ["capture.json", "Captured.lean"] {
            assert!(
                std::fs::symlink_metadata(self.output.join(name)).is_err(),
                "capture artifact {name} exists after failure"
            );
        }
    }
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn status(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).expect("typed capture returns one JSON status")
}

fn assert_refused(
    label: &str,
    fixture: &Capture,
    output: &Output,
    expected_status: &str,
    needle: &str,
) {
    assert_eq!(output.status.code(), Some(1), "{label}: expected exit 1, got {output:?}");
    let failure = status(output);
    assert_eq!(failure["status"], expected_status, "{label}: {failure}");
    assert!(
        failure.to_string().contains(needle),
        "{label}: expected `{needle}` in failure status, got {failure}"
    );
    fixture.assert_no_capture_artifacts();
}

/// Seam 1 (`#4042`): `-Zmir-preserve-ub` keeps `StatementKind::PlaceMention`
/// alive through `Runtime(PostCleanup)` where bare `rustc` strips it via
/// `RemovePlaceMention`, while projected `PlaceMention` fails closed.
#[test]
fn seam_1_place_mention_preserved_by_mir_preserve_ub_and_projected_refused() {
    let bare_src = b"pub fn selected(x: u8) -> u8 { let _ = x; x }\n";
    let fixture = Capture::new(bare_src);
    let output = fixture.selected_command().output().expect("capture bare PlaceMention");
    assert!(output.status.success(), "{output:?}");

    let manifest = fixture.manifest();
    assert!(
        manifest.to_string().contains("\"place_mention\""),
        "expected unprojected PlaceMention to survive capture: {manifest}"
    );
    let lean = fixture.lean_source();
    assert!(
        lean.contains("Trusted.MirAst.StatementKind.nop"),
        "expected validated unprojected PlaceMention to lower to nop: {lean}"
    );

    // Differential sentinel against the exact same pinned `rustc` WITHOUT
    // `-Zmir-preserve-ub`: `RemovePlaceMention` must strip `PlaceMention` in
    // default `-Zmir-opt-level=0` MIR so we know the flag is doing real work.
    let raw_dir = tempfile::tempdir().expect("create raw rustc dir");
    let raw_src = raw_dir.path().join("input.rs");
    std::fs::write(&raw_src, bare_src).expect("write raw input");
    let rustc_bin = sysroot().join("bin/rustc");
    let raw_out = Command::new(&rustc_bin)
        .current_dir(raw_dir.path())
        .args([
            "--crate-type=lib",
            "--crate-name=sentinel",
            "--edition=2024",
            "--emit=mir",
            "-Zmir-opt-level=0",
            "-Cdebug-assertions=no",
        ])
        .arg(&raw_src)
        .output()
        .expect("run bare rustc --emit=mir");
    assert!(raw_out.status.success(), "bare rustc failed: {raw_out:?}");
    let raw_mir =
        std::fs::read_to_string(raw_dir.path().join("sentinel.mir")).expect("read sentinel.mir");
    assert!(
        !raw_mir.contains("PlaceMention("),
        "bare rustc without -Zmir-preserve-ub unexpectedly retained PlaceMention:\n{raw_mir}"
    );

    // Projected `PlaceMention` must fail closed rather than collapsing to
    // `nop`. Note: `unsafe { let _ = *p; }` puts the place expression `*p`
    // directly on the RHS of `let _ =` (emitting `PlaceMention((*_1))`),
    // whereas `let _ = unsafe { *p };` wraps `*p` in a block value expression
    // that loads into a temporary first.
    let projected_cases: &[(&str, &[u8])] = &[
        ("raw ptr deref", b"pub unsafe fn selected(p: *const u8) { unsafe { let _ = *p; } }\n"),
        ("shared ref deref", b"pub fn selected(r: &u8) { let _ = *r; }\n"),
        ("mut ref deref", b"pub fn selected(r: &mut u8) { let _ = *r; }\n"),
    ];
    for (label, src) in projected_cases {
        let proj = Capture::new(src);
        let out = proj.selected_command().output().expect("capture projected PlaceMention");
        assert_refused(
            label,
            &proj,
            &out,
            "unsupported",
            "PlaceMention with projections is unsupported",
        );
    }
}

/// Seam 2: `SwitchInt` / trivial-discriminant reads survive
/// `Runtime(PostCleanup)` under `-Copt-level=0 -Zmir-preserve-ub` and
/// `-Zmir-opt-level=0` rather than being simplified away.
#[test]
fn seam_2_switch_int_trivial_discriminant_reads_preserved() {
    let bool_fixture = Capture::new(
        b"pub fn selected(b: bool) -> u8 {\n\
              match b {\n\
                  true => 7,\n\
                  false => 7,\n\
              }\n\
          }\n",
    );
    let bool_out = bool_fixture.selected_command().output().expect("capture trivial bool match");
    assert!(bool_out.status.success(), "{bool_out:?}");
    let bool_lean = bool_fixture.lean_source();
    assert!(
        bool_lean.contains("Trusted.MirAst.TerminatorKind.switchInt"),
        "expected trivial bool match to preserve SwitchInt:\n{bool_lean}"
    );

    let enum_fixture = Capture::new(
        b"#[repr(u8)]\n\
          pub enum Tag { A = 1, B = 2 }\n\
          pub fn selected(t: Tag) -> u8 {\n\
              match t {\n\
                  Tag::A => 9,\n\
                  Tag::B => 9,\n\
              }\n\
          }\n",
    );
    let enum_out = enum_fixture.selected_command().output().expect("capture trivial enum match");
    assert!(enum_out.status.success(), "{enum_out:?}");
    let enum_lean = enum_fixture.lean_source();
    assert!(
        enum_lean.contains("Trusted.MirAst.Rvalue.discriminant"),
        "expected trivial enum match to preserve discriminant read:\n{enum_lean}"
    );
    assert!(
        enum_lean.contains("Trusted.MirAst.TerminatorKind.switchInt"),
        "expected trivial enum match to preserve SwitchInt:\n{enum_lean}"
    );

    let multi_fixture = Capture::new(
        b"pub fn selected(x: u8) -> u8 {\n\
              match x {\n\
                  0 => 1,\n\
                  1 => 2,\n\
                  _ => 3,\n\
              }\n\
          }\n",
    );
    let multi_out = multi_fixture.selected_command().output().expect("capture integer match");
    assert!(multi_out.status.success(), "{multi_out:?}");
    let multi_lean = multi_fixture.lean_source();
    assert!(
        multi_lean.contains("Trusted.MirAst.TerminatorKind.switchInt"),
        "expected integer match to preserve SwitchInt:\n{multi_lean}"
    );
}

/// Seam 3 (`#4083`): `#![feature(ergonomic_clones)]` and `CallSource::Use`
/// (`SneakyCopy`) fail closed across normal crates, active `cfg_attr`, and
/// `--stdlib-crate=core`, while an inactive `cfg_attr` stays admitted.
#[test]
fn seam_3_ergonomic_clones_and_call_source_use_refused() {
    let cases: &[(&str, &[u8])] = &[
        (
            "plain ergonomic_clones",
            b"#![feature(ergonomic_clones)]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
        (
            "active cfg_attr ergonomic_clones",
            b"#![cfg_attr(all(), feature(ergonomic_clones))]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
        (
            "SneakyCopy .use",
            b"#![feature(ergonomic_clones)]\n\
              #[derive(Copy)]\n\
              pub struct SneakyCopy(pub u64);\n\
              impl Clone for SneakyCopy {\n\
                  fn clone(&self) -> Self { SneakyCopy(self.0.wrapping_add(1)) }\n\
              }\n\
              impl core::clone::UseCloned for SneakyCopy {}\n\
              pub fn selected(x: SneakyCopy) -> u64 {\n\
                  let y = x.use;\n\
                  y.0\n\
              }\n",
        ),
    ];
    for (label, src) in cases {
        let fixture = Capture::new(src);
        let out = fixture.selected_command().output().expect("capture ergonomic_clones case");
        assert_refused(label, &fixture, &out, "unsupported", "ergonomic_clones");
    }

    // Even under `--stdlib-crate=core`, `ergonomic_clones` is outside the
    // version-pinned `core` allowlist and fails closed.
    let core_src = format!("#![feature(ergonomic_clones)]\n{NO_CORE_STUB}");
    let core_fixture = Capture::new(core_src.as_bytes());
    let core_out = core_fixture
        .command_with("core", true)
        .args(["--select=selected", "--stdlib-crate=core"])
        .output()
        .expect("capture stdlib core ergonomic_clones");
    assert_refused(
        "stdlib core ergonomic_clones",
        &core_fixture,
        &core_out,
        "unsupported",
        "ergonomic_clones",
    );

    // Positive control: an inactive
    // `#![cfg_attr(..., feature(ergonomic_clones))]` is not enabled and must
    // not break capture.
    let inactive = Capture::new(
        b"#![cfg_attr(never_enabled_cfg, feature(ergonomic_clones))]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let inactive_out = inactive.selected_command().output().expect("capture inactive cfg_attr");
    assert!(inactive_out.status.success(), "{inactive_out:?}");
}

/// Seam 4: Closed positive `#![feature(...)]` allowlist (empty `[]` for normal
/// crates) rejects unstable lang and lib features, admits and records
/// `ACCEPTED_LANG_FEATURES` (`doc_alias`), and preserves `zerocopy`-style
/// inactive `#![cfg_attr(..., feature(...))]` lines until activated.
#[test]
fn seam_4_positive_feature_allowlist_and_accepted_features() {
    // Disallowed unstable lang features (including `f16`), unstable lib
    // features (`core_intrinsics`, `ptr_metadata`, `const_eval_select`), and
    // `doc_cfg`.
    let rejected_features: &[(&str, &str)] = &[
        (
            "rustc_attrs",
            "#![feature(rustc_attrs)]\n\
             #[rustc_inherit_overflow_checks]\n\
             pub fn selected(x: u64) -> u64 { x }\n",
        ),
        ("custom_mir", "#![feature(custom_mir)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("specialization", "#![feature(specialization)]\npub fn selected(x: u64) -> u64 { x }\n"),
        (
            "generic_const_exprs",
            "#![feature(generic_const_exprs)]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
        (
            "adt_const_params",
            "#![feature(adt_const_params)]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
        ("intrinsics", "#![feature(intrinsics)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("f16", "#![feature(f16)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("doc_cfg", "#![feature(doc_cfg)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("rustc_private", "#![feature(rustc_private)]\npub fn selected(x: u64) -> u64 { x }\n"),
        // Unstable library features (missed by lang-only checks).
        ("core_intrinsics", "#![feature(core_intrinsics)]\npub fn selected(x: u64) -> u64 { x }\n"),
        ("ptr_metadata", "#![feature(ptr_metadata)]\npub fn selected(x: u64) -> u64 { x }\n"),
        (
            "const_eval_select",
            "#![feature(const_eval_select)]\npub fn selected(x: u64) -> u64 { x }\n",
        ),
    ];

    for (feature, src) in rejected_features {
        let fixture = Capture::new(src.as_bytes());
        let out = fixture.selected_command().output().expect("capture disallowed feature");
        assert_refused(feature, &fixture, &out, "unsupported", feature);
    }

    // Non-word `#![feature(...)]` entries fail closed uniformly before
    // expansion.
    let non_word = Capture::new(
        b"#![feature(no_core = \"x\")]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let non_word_out = non_word.selected_command().output().expect("capture non-word feature");
    assert_refused(
        "non-word feature attr",
        &non_word,
        &non_word_out,
        "unsupported",
        "must list feature identifiers",
    );

    // Already-stabilized `ACCEPTED_LANG_FEATURES` (which `-Zallow-features=`
    // skips) activate nothing unstable: capture admits them untainted and
    // records them, directly or through an active `cfg_attr`.
    for src in [
        "#![feature(doc_alias)]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![cfg_attr(all(), feature(doc_alias))]\npub fn selected(x: u64) -> u64 { x }\n",
    ] {
        let fixture = Capture::new(src.as_bytes());
        let out = fixture.selected_command().output().expect("capture accepted feature");
        assert!(out.status.success(), "{src}: {out:?}");
        let configuration = &fixture.manifest()["configuration"];
        assert_eq!(configuration["stabilized_features_present"], json!(["doc_alias"]), "{src}");
        for key in [
            "allowed_unstable_features",
            "observed_unstable_features",
            "incomplete_observed_unstable_features",
        ] {
            assert!(configuration.get(key).is_none(), "{src}: unexpected {key}");
        }
    }

    // Positive control mirroring `zerocopy/src/lib.rs:318-325`: inactive
    // `#![cfg_attr(..., feature(...))]` declarations stay admitted under
    // default cfgs, and fail closed as soon as a `--cfg` activates any of them.
    let zerocopy_style = Capture::new(
        b"#![cfg_attr(doc_cfg, feature(doc_cfg))]\n\
          #![cfg_attr(feature = \"float-nightly\", feature(f16, f128))]\n\
          #![cfg_attr(coverage_nightly, feature(coverage_attribute))]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let default_out = zerocopy_style
        .selected_command()
        .output()
        .expect("capture inactive zerocopy-style cfg_attr");
    assert!(default_out.status.success(), "{default_out:?}");

    let activated_doc_cfg = Capture::new(
        b"#![cfg_attr(doc_cfg, feature(doc_cfg))]\n\
          #![cfg_attr(feature = \"float-nightly\", feature(f16, f128))]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let doc_cfg_out = activated_doc_cfg
        .selected_command()
        .arg("--cfg=doc_cfg")
        .output()
        .expect("capture activated doc_cfg");
    assert_refused("activated doc_cfg", &activated_doc_cfg, &doc_cfg_out, "unsupported", "doc_cfg");

    let activated_float = Capture::new(
        b"#![cfg_attr(doc_cfg, feature(doc_cfg))]\n\
          #![cfg_attr(feature = \"float-nightly\", feature(f16, f128))]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let float_out = activated_float
        .selected_command()
        .arg("--cfg=feature=\"float-nightly\"")
        .output()
        .expect("capture activated float-nightly");
    assert_refused(
        "activated float-nightly",
        &activated_float,
        &float_out,
        "unsupported",
        "f128, f16",
    );
}

/// Seam 4b: `--allow-unstable-feature` admits exactly the named unstable
/// features (recording what the operator allowed, what the crate enabled, and
/// which enabled features `rustc` marks incomplete), never the hard-ban floor,
/// and keeps `-Zallow-features` enforcing the allowlist under active
/// `cfg_attr`.
#[test]
fn seam_4b_operator_allowed_unstable_features() {
    let selected = "pub fn selected(x: u64) -> u64 { x }\n";

    // Allowed and enabled: recorded as allowed and observed.
    let doc_cfg = Capture::new(format!("#![feature(doc_cfg)]\n{selected}").as_bytes());
    let out = doc_cfg
        .selected_command()
        .arg("--allow-unstable-feature=doc_cfg")
        .output()
        .expect("capture allowed doc_cfg");
    assert!(out.status.success(), "{out:?}");
    let configuration = &doc_cfg.manifest()["configuration"];
    assert_eq!(configuration["allowed_unstable_features"], json!(["doc_cfg"]));
    assert_eq!(configuration["observed_unstable_features"], json!(["doc_cfg"]));
    assert!(configuration.get("incomplete_observed_unstable_features").is_none());
    assert!(configuration.get("stabilized_features_present").is_none());

    // Allowed but unused: recorded as allowed only. Repeated and
    // comma-separated flags normalize to one sorted list.
    let unused = Capture::new(selected.as_bytes());
    let out = unused
        .selected_command()
        .arg("--allow-unstable-feature=doc_cfg,allocator_api")
        .arg("--allow-unstable-feature")
        .arg("doc_cfg")
        .output()
        .expect("capture unused allowlist");
    assert!(out.status.success(), "{out:?}");
    let configuration = &unused.manifest()["configuration"];
    assert_eq!(configuration["allowed_unstable_features"], json!(["allocator_api", "doc_cfg"]));
    assert!(configuration.get("observed_unstable_features").is_none());

    // Incomplete features stay admissible but are flagged.
    let incomplete = Capture::new(format!("#![feature(specialization)]\n{selected}").as_bytes());
    let out = incomplete
        .selected_command()
        .arg("--allow-unstable-feature=specialization")
        .output()
        .expect("capture allowed specialization");
    assert!(out.status.success(), "{out:?}");
    let configuration = &incomplete.manifest()["configuration"];
    assert_eq!(configuration["observed_unstable_features"], json!(["specialization"]));
    assert_eq!(configuration["incomplete_observed_unstable_features"], json!(["specialization"]));

    // Naming an already-stabilized feature is harmless: it is allowed but
    // never observed, and the attribute is recorded as stabilized.
    let stabilized = Capture::new(format!("#![feature(doc_alias)]\n{selected}").as_bytes());
    let out = stabilized
        .selected_command()
        .arg("--allow-unstable-feature=doc_alias")
        .output()
        .expect("capture allowed stabilized feature");
    assert!(out.status.success(), "{out:?}");
    let configuration = &stabilized.manifest()["configuration"];
    assert_eq!(configuration["allowed_unstable_features"], json!(["doc_alias"]));
    assert!(configuration.get("observed_unstable_features").is_none());
    assert_eq!(configuration["stabilized_features_present"], json!(["doc_alias"]));

    // Features outside the operator's list still fail closed, including under
    // an active `cfg_attr` and for library features.
    for (label, src) in [
        ("cfg_attr allocator_api", "#![cfg_attr(all(), feature(allocator_api))]\n"),
        ("lib ptr_metadata", "#![feature(doc_cfg, ptr_metadata)]\n"),
    ] {
        let fixture = Capture::new(format!("{src}{selected}").as_bytes());
        let out = fixture
            .selected_command()
            .arg("--allow-unstable-feature=doc_cfg")
            .output()
            .expect("capture feature outside allowlist");
        let needle = if label.starts_with("lib") { "ptr_metadata" } else { "allocator_api" };
        assert_refused(label, &fixture, &out, "unsupported", needle);
    }

    // The hard-ban floor cannot be allowed, whether or not the crate enables
    // the feature.
    for banned in
        ["rustc_attrs", "rustc_private", "ergonomic_clones", "custom_mir", "core_intrinsics"]
    {
        for src in [selected.to_owned(), format!("#![feature({banned})]\n{selected}")] {
            let fixture = Capture::new(src.as_bytes());
            let out = fixture
                .selected_command()
                .arg(format!("--allow-unstable-feature=doc_cfg,{banned}"))
                .output()
                .expect("capture hard-banned feature");
            assert_refused(banned, &fixture, &out, "unsupported", "cannot be allowed");
        }
    }

    // Malformed names and `--stdlib-crate` conflicts are usage errors.
    for args in [
        vec!["--allow-unstable-feature=*"],
        vec!["--allow-unstable-feature=Doc_cfg"],
        vec!["--allow-unstable-feature=doc_cfg,"],
        vec!["--allow-unstable-feature=doc-cfg"],
        vec!["--allow-unstable-feature=doc_cfg", "--stdlib-crate=core"],
    ] {
        let fixture = Capture::new(selected.as_bytes());
        let out = fixture.selected_command().args(&args).output().expect("capture bad usage");
        assert_eq!(out.status.code(), Some(2), "{args:?}: {out:?}");
        assert_eq!(status(&out)["status"], "tool_failed", "{args:?}");
        fixture.assert_no_capture_artifacts();
    }
}

/// Seam 5: `debug_assert!` expands to a disabled `cfg!(debug_assertions)`
/// (`bool` constant `false`) guard and `#[cfg(debug_assertions)]` is erased at
/// expansion time under `-Cdebug-assertions=no` (even when `--overflow-checks`
/// is enabled), and `cfg(miri)` is refused on all normal crates (both
/// `--select` and `--scope=crate`).
#[test]
fn seam_5_debug_assert_erasure_and_general_cfg_miri_refusal() {
    let dbg_src = b"pub fn selected(x: u64) -> u64 {\n\
        debug_assert!(x != 0);\n\
        #[cfg(debug_assertions)]\n\
        let delta = 1u64;\n\
        #[cfg(not(debug_assertions))]\n\
        let delta = 2u64;\n\
        x + delta\n\
    }\n";

    // Default profile: `-Cdebug-assertions=no -Coverflow-checks=no` keeps
    // `debug_assert!` guarded by `const false` (`BitVec.ofNat 128 0`) with zero
    // `TerminatorKind.assert`, and erases `#[cfg(debug_assertions)]` (`1u64`)
    // before MIR construction so only `delta = 2u64` survives.
    let no_overflow = Capture::new(dbg_src);
    let no_overflow_out =
        no_overflow.selected_command().output().expect("capture debug_assert default");
    assert!(no_overflow_out.status.success(), "{no_overflow_out:?}");
    let no_overflow_lean = no_overflow.lean_source();
    assert!(
        !no_overflow_lean.contains("TerminatorKind.assert"),
        "expected no Assert terminators under default profile:\n{no_overflow_lean}"
    );
    assert!(
        no_overflow_lean.contains("ConstOperand.mk Trusted.MirAst.MirTy.bool (Trusted.MirAst.ConstLit.scalar (BitVec.ofNat 128 0))"),
        "expected debug_assert! cfg!(debug_assertions) guard to evaluate to false:\n{no_overflow_lean}"
    );
    assert!(
        no_overflow_lean.contains("BitVec.ofNat 128 2")
            && !no_overflow_lean.contains("BitVec.ofNat 128 1"),
        "expected #[cfg(debug_assertions)] branch erased leaving only `delta = 2`:\n{no_overflow_lean}"
    );

    // `--overflow-checks`: enables arithmetic overflow `Assert` on `x + delta`
    // without turning `debug_assertions` back on.
    let with_overflow = Capture::new(dbg_src);
    let with_overflow_out = with_overflow
        .selected_command()
        .arg("--overflow-checks")
        .output()
        .expect("capture debug_assert with overflow checks");
    assert!(with_overflow_out.status.success(), "{with_overflow_out:?}");
    let with_overflow_lean = with_overflow.lean_source();
    assert!(
        with_overflow_lean.contains("TerminatorKind.assert"),
        "expected overflow Assert under --overflow-checks:\n{with_overflow_lean}"
    );
    assert!(
        with_overflow_lean.contains("ConstOperand.mk Trusted.MirAst.MirTy.bool (Trusted.MirAst.ConstLit.scalar (BitVec.ofNat 128 0))"),
        "expected debug_assert! guard to stay false under --overflow-checks:\n{with_overflow_lean}"
    );
    assert!(
        with_overflow_lean.contains("BitVec.ofNat 128 2")
            && !with_overflow_lean.contains("BitVec.ofNat 128 1"),
        "expected #[cfg(debug_assertions)] to stay erased under --overflow-checks:\n{with_overflow_lean}"
    );

    // General `cfg(miri)` refusal across all normal crates (protecting
    // `#[cfg(miri)]` branches like `zerocopy/src/util/mod.rs:61`).
    let miri_branch_src = b"#[cfg(miri)]\n\
        pub fn selected(_x: u64) -> u64 { 0 }\n\
        #[cfg(not(miri))]\n\
        pub fn selected(x: u64) -> u64 { x.wrapping_add(1) }\n";

    let without_miri = Capture::new(miri_branch_src);
    let without_miri_out =
        without_miri.selected_command().output().expect("capture cfg(not(miri)) branch");
    assert!(without_miri_out.status.success(), "{without_miri_out:?}");
    assert!(
        without_miri.lean_source().contains("BitVec.ofNat 128 1"),
        "expected non-miri branch to be captured"
    );

    let miri_cases: &[(&str, &[&str])] = &[
        ("selected --cfg=miri", &["--select=selected", "--cfg=miri"]),
        ("whole-crate --cfg=miri", &["--scope=crate", "--cfg=miri"]),
        ("selected --cfg=miri=\"1\"", &["--select=selected", "--cfg=miri=\"1\""]),
    ];
    for (label, args) in miri_cases {
        let miri_fixture = Capture::new(miri_branch_src);
        let out = miri_fixture.command().args(*args).output().expect("capture with cfg(miri)");
        assert_refused(label, &miri_fixture, &out, "unsupported", "cfg(miri)");
    }

    // Even when the source never mentions `cfg(miri)`, passing `--cfg=miri`
    // is refused fail-closed.
    let plain_miri = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");
    let plain_miri_out = plain_miri
        .selected_command()
        .arg("--cfg=miri")
        .output()
        .expect("capture plain crate with cfg(miri)");
    assert_refused("plain --cfg=miri", &plain_miri, &plain_miri_out, "unsupported", "cfg(miri)");
}

/// Seam 6: Macro expansion, `#[path]` / `include!` provenance, and
/// primitive/type-name shadowing.
#[test]
fn seam_6_macro_expansion_path_and_shadowing() {
    // 6a. Private `macro_rules!` expansion + nested `#[cfg_attr(all(), ...)]`
    // produces the same captured MIR body as the hand-written equivalent.
    let macro_fixture = Capture::new(
        b"macro_rules! mk_fn {\n\
              ($name:ident, $k:expr) => {\n\
                  #[cfg_attr(all(), inline)]\n\
                  pub fn $name(x: u64) -> u64 { x.wrapping_add($k) }\n\
              };\n\
          }\n\
          mk_fn!(selected, 5);\n",
    );
    let plain_fixture = Capture::new(
        b"#[inline]\n\
          pub fn selected(x: u64) -> u64 { x.wrapping_add(5) }\n",
    );
    let macro_out = macro_fixture.selected_command().output().expect("capture macro-generated fn");
    let plain_out = plain_fixture.selected_command().output().expect("capture plain fn");
    assert!(macro_out.status.success(), "{macro_out:?}");
    assert!(plain_out.status.success(), "{plain_out:?}");
    assert_eq!(
        macro_fixture.manifest()["program"],
        plain_fixture.manifest()["program"],
        "macro-expanded MIR drifted from hand-written MIR"
    );

    // 6b. Macro-smuggled unmodeled codegen attrs (`#[unsafe(no_mangle)]`) and
    // `unsafe trait` items still fail closed after expansion.
    let smuggled_no_mangle = Capture::new(
        b"macro_rules! smuggle {\n\
              ($name:ident) => {\n\
                  #[unsafe(no_mangle)]\n\
                  pub fn $name(x: u64) -> u64 { x }\n\
              };\n\
          }\n\
          smuggle!(selected);\n",
    );
    let smuggled_out =
        smuggled_no_mangle.selected_command().output().expect("capture smuggled no_mangle");
    assert_refused(
        "macro-smuggled no_mangle",
        &smuggled_no_mangle,
        &smuggled_out,
        "unsupported",
        "NO_MANGLE",
    );

    let smuggled_unsafe_trait = Capture::new(
        b"macro_rules! smuggle_trait {\n\
              ($name:ident) => {\n\
                  pub unsafe trait $name {}\n\
              };\n\
          }\n\
          smuggle_trait!(HiddenUnsafe);\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let smuggled_trait_out = smuggled_unsafe_trait
        .command()
        .arg("--scope=crate")
        .output()
        .expect("capture smuggled unsafe trait");
    assert_refused(
        "macro-smuggled unsafe trait",
        &smuggled_unsafe_trait,
        &smuggled_trait_out,
        "unsupported",
        "whole-crate obligation is unsupported: Trait",
    );

    // 6c. Declared vs. undeclared `#[path = "..."]` module and `include!`.
    let path_fixture = Capture::new(
        b"#[path = \"sub.rs\"]\n\
          mod sub;\n\
          pub fn selected(x: u64) -> u64 { sub::helper(x) }\n",
    );
    let sub_path = path_fixture.directory.path().join("sub.rs");
    std::fs::write(&sub_path, b"pub fn helper(x: u64) -> u64 { x }\n").expect("write sub.rs");
    let undeclared_out =
        path_fixture.selected_command().output().expect("capture undeclared #[path]");
    assert_refused(
        "undeclared #[path]",
        &path_fixture,
        &undeclared_out,
        "unsupported",
        "undeclared compiler read",
    );
    let declared_out = path_fixture
        .selected_command()
        .arg("--source-file")
        .arg(&sub_path)
        .output()
        .expect("capture declared #[path]");
    assert!(declared_out.status.success(), "{declared_out:?}");
    let reads = path_fixture.manifest()["source_files"].as_array().unwrap().clone();
    let canon_sub = sub_path.canonicalize().expect("canonicalize sub.rs");
    assert!(
        reads.iter().any(|r| r["path"] == canon_sub.to_str().unwrap()),
        "declared #[path] file missing from manifest source_files: {reads:?}"
    );

    let include_fixture = Capture::new(b"include!(\"body.inc\");\n");
    let inc_path = include_fixture.directory.path().join("body.inc");
    std::fs::write(&inc_path, b"pub fn selected(x: u64) -> u64 { x }\n").expect("write body.inc");
    let undeclared_inc =
        include_fixture.selected_command().output().expect("capture undeclared include!");
    assert_refused(
        "undeclared include!",
        &include_fixture,
        &undeclared_inc,
        "unsupported",
        "undeclared compiler read",
    );
    let declared_inc = include_fixture
        .selected_command()
        .arg("--source-file")
        .arg(&inc_path)
        .output()
        .expect("capture declared include!");
    assert!(declared_inc.status.success(), "{declared_inc:?}");

    // 6d. Primitive / type-name shadowing (distinct from `mod core`): capture
    // reads resolved `ty::Ty`, never raw source identifiers.
    let alias_shadow = Capture::new(
        b"#[allow(non_camel_case_types)]\n\
          type usize = u16;\n\
          pub fn selected(x: usize) -> usize { x }\n",
    );
    let alias_out = alias_shadow.selected_command().output().expect("capture type usize = u16");
    assert!(alias_out.status.success(), "{alias_out:?}");
    let alias_lean = alias_shadow.lean_source();
    assert!(
        alias_lean.contains("Trusted.MirAst.IntWidth.i16")
            && !alias_lean.contains("Trusted.MirAst.IntWidth.isize"),
        "expected shadowed `type usize = u16` to capture as i16, not isize:\n{alias_lean}"
    );

    let struct_shadow = Capture::new(
        b"#[allow(non_camel_case_types)]\n\
          pub struct u8(pub u16);\n\
          pub fn selected(x: u8) -> u16 { x.0 }\n",
    );
    let struct_out = struct_shadow.selected_command().output().expect("capture struct u8");
    assert_refused(
        "struct shadowing primitive u8",
        &struct_shadow,
        &struct_out,
        "unsupported",
        "unsupported type",
    );

    let enum_shadow = Capture::new(
        b"#[allow(non_camel_case_types)]\n\
          #[repr(u8)]\n\
          pub enum usize { A = 0, B = 1 }\n\
          pub fn selected(x: usize) -> usize { x }\n",
    );
    let enum_out = enum_shadow.selected_command().output().expect("capture enum usize");
    assert!(enum_out.status.success(), "{enum_out:?}");
    let enum_lean = enum_shadow.lean_source();
    assert!(
        enum_lean.contains("Trusted.MirAst.MirTy.enum")
            && !enum_lean.contains("Trusted.MirAst.IntWidth.isize"),
        "expected shadowed `enum usize` to capture as MirTy.enum, not isize:\n{enum_lean}"
    );
}

/// `O1a-Dual` CLI-level ill-formedness and dead-branch PME tests: conflicting
/// `#[repr(...)]` attributes fail compilation with the expected rustc error
/// codes and zero artifacts, and instantiated dead-branch `SizeEq` PMEs fail
/// closed during capture (`eval_required_consts`).
#[test]
fn o1a_dual_ill_formed_repr_and_dead_branch_pme_refused() {
    let repr_cases: &[(&str, &[u8], &str)] = &[
        (
            "repr(C, packed) + align conflict",
            b"#[repr(C, packed)]\n\
              #[repr(align(8))]\n\
              pub struct Bad { pub x: u32 }\n\
              pub fn selected(x: u64) -> u64 { x }\n",
            "E0587",
        ),
        (
            "duplicate repr(transparent)",
            b"#[repr(transparent, transparent)]\n\
              pub struct Dup(pub u32);\n\
              pub fn selected(x: u64) -> u64 { x }\n",
            "E0692",
        ),
        (
            "multi-field repr(transparent)",
            b"#[repr(transparent)]\n\
              pub struct Multi { pub a: u32, pub b: u32 }\n\
              pub fn selected(x: u64) -> u64 { x }\n",
            "E0690",
        ),
    ];

    for (label, src, code) in repr_cases {
        let fixture = Capture::new(src);
        let out = fixture.command().arg("--scope=crate").output().expect("capture ill-formed repr");
        assert_refused(label, &fixture, &out, "compiler_failed", "rustc rejected the compilation");
        let err = stderr(&out);
        assert!(
            err.contains(code),
            "{label}: expected rustc error code {code} in stderr, got:\n{err}"
        );
    }

    // Dead-branch generic `SizeEq` PME (`if false { ... }`): even though the
    // const assertion sits in a dead branch, instantiating `bad::<u8, u16>`
    // must fail closed via `eval_required_consts` during capture.
    let pme_src = b"pub fn bad<T, U>(x: u64) -> u64 {\n\
        if false {\n\
            const { assert!(core::mem::size_of::<T>() == core::mem::size_of::<U>()) }\n\
        }\n\
        x\n\
    }\n";
    let pme_ok = Capture::new(pme_src);
    let pme_ok_out = pme_ok
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"bad","args":["u16","u16"]}"#)
        .output()
        .expect("capture matching dead-branch PME instantiation");
    assert!(pme_ok_out.status.success(), "{pme_ok_out:?}");

    let pme_fail = Capture::new(pme_src);
    let pme_fail_out = pme_fail
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"bad","args":["u8","u16"]}"#)
        .output()
        .expect("capture failing dead-branch PME instantiation");
    assert_eq!(pme_fail_out.status.code(), Some(1), "{pme_fail_out:?}");
    let pme_status = status(&pme_fail_out);
    assert!(
        matches!(pme_status["status"].as_str(), Some("compiler_failed") | Some("unsupported")),
        "expected failing dead-branch PME to fail closed, got {pme_status}"
    );
    pme_fail.assert_no_capture_artifacts();
}
