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

#[path = "pass_order_sentinel/cfg_expansion_and_o1a_dual.rs"]
mod cfg_expansion_and_o1a_dual;
#[path = "pass_order_sentinel/feature_allowlist.rs"]
mod feature_allowlist;
#[path = "pass_order_sentinel/mir_pass_seams.rs"]
mod mir_pass_seams;
