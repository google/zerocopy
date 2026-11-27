// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Seams 1-3: `PlaceMention` preservation, `SwitchInt` discriminant reads,
//! and `CallSource::Use` refusal across `Runtime(PostCleanup)`.

use super::*;

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
