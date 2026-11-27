// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end `cargo-anneal verify` & `inspect` coverage for structured
//! `MirEnvelopeSpec` verification (`rustc --spec-closure` with companion
//! `.spec-closure.golden`, `verify --request`, fatal envelope lint, NDJSON
//! route refusal, `inspect` Tier-A diffing, and real unmodified `zerocopy`).

use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::OnceLock,
};

use anneal_testkit::{
    SharedOleanCache, ToolchainEnv, ToolchainMode, VerifyReceipt, assert_rejected,
    assert_verified_untainted, sha256_hex,
};
use serde_json::{Value, json};
use tempfile::TempDir;

const ZEROCOPY_SOURCE_FILES: &[&str] = &[
    "byte_slice.rs",
    "byteorder.rs",
    "deprecated.rs",
    "error.rs",
    "impls.rs",
    "layout.rs",
    "lib.rs",
    "macros.rs",
    "pointer/inner.rs",
    "pointer/invariant.rs",
    "pointer/mod.rs",
    "pointer/ptr.rs",
    "pointer/transmute.rs",
    "ref.rs",
    "split_at.rs",
    "util/macro_util.rs",
    "util/macros.rs",
    "util/mod.rs",
    "wrappers.rs",
];

fn tools() -> &'static ToolchainEnv {
    static TOOLS: OnceLock<ToolchainEnv> = OnceLock::new();
    TOOLS.get_or_init(|| {
        ToolchainEnv::resolve(ToolchainMode::WorkspaceBuild {
            cli_bin: Some(PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"))),
            capture_bin: None,
            auditor_bin: None,
        })
        .expect("resolve spec-envelope e2e toolchain")
    })
}

fn shared_cache() -> &'static SharedOleanCache {
    static CACHE: OnceLock<SharedOleanCache> = OnceLock::new();
    CACHE.get_or_init(|| SharedOleanCache::shared().expect("shared OleanCache"))
}

fn spec_module_golden(module: &str, content: &str) -> Value {
    let trailing_newline = content.ends_with('\n');
    let body = content.strip_suffix('\n').unwrap_or(content);
    let lines: Vec<String> =
        if content.is_empty() { Vec::new() } else { body.split('\n').map(str::to_owned).collect() };
    json!({
        "module": module,
        "sha256": sha256_hex(content.as_bytes()),
        "trailing_newline": trailing_newline,
        "lines": lines,
    })
}

fn run_cli(cwd: &Path, args: &[&OsStr]) -> Output {
    let tools = tools();
    let cache = shared_cache();
    let cli = tools.cli.as_deref().expect("workspace cargo-anneal binary");
    Command::new(cli)
        .current_dir(cwd)
        .env("HOME", cache.home_dir())
        .env("XDG_CACHE_HOME", cache.xdg_cache_home())
        .args(args)
        .output()
        .expect("spawn cargo-anneal")
}

fn run_verify(cwd: &Path, args: &[&OsStr]) -> (Output, VerifyReceipt) {
    let tools = tools();
    let capture = tools.capture.as_deref().expect("workspace capture binary");
    let mut full: Vec<&OsStr> = vec![
        OsStr::new("verify"),
        OsStr::new("--format"),
        OsStr::new("json"),
        OsStr::new("--capture"),
        capture.as_os_str(),
        OsStr::new("--lean"),
        tools.lean.as_os_str(),
        OsStr::new("--sysroot"),
        tools.sysroot.as_os_str(),
    ];
    full.extend_from_slice(args);
    let out = run_cli(cwd, &full);
    let receipt = VerifyReceipt::from_json_slice(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "invalid Schema v3 receipt: {e}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )
    });
    (out, receipt)
}

#[test]
fn rustc_spec_closure_with_companion_golden_verifies_inspects_and_rejects_tampers() {
    let dir = TempDir::new().unwrap();
    let work = dir.path();

    let rust_path = work.join("lib.rs");
    fs::write(&rust_path, "pub fn zero() {}\n").unwrap();

    let helper_src = "\
prelude
import Init.NotationExtra
namespace SpecHelper
def helperLawProp : Prop := (1 : Nat) = 1
end SpecHelper
";
    let spec_src = "\
prelude
import Init.NotationExtra
import SpecHelper
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def zeroLawProp : Prop := SpecHelper.helperLawProp
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"rust-path-v1::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := defaultMirDownstreamGaps
  laws := [zeroLawProp]
}
end Spec
";
    let proof_src = "\
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
import Anneal.MirWp
import Anneal.Framework
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework Anneal.MirWp Anneal.Framework
theorem verify : Expected.claim := by
  dsimp only [Expected.claim, MirEnvelopeHolds, EnvelopeTheorem, mkEnvelope, AllSpecLaws,
    NoDupStrings, List.map, List.append]
  refine ⟨rfl, (fun h => by cases h),
      ⟨⟨ne_string_of_len_beq_false rfl, rfl, ?_, rfl,
          fun h => Bool.noConfusion h, nonEmpty_oracle_id, ?_, fun _ h => h⟩,
        ?_, ?_, ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩,
      ⟨rfl, True.intro⟩, True.intro⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      rfl
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, Captured.body_0, rfl, rfl, rfl, rfl, absurd_mem_nil, ?_, ?_, ?_⟩
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            exact (spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 10)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg (fuel := 10) rfl)).1
          | cons _ _ => exact Bool.noConfusion hDom.1
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            have hSpec := spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 10)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg (fuel := 10) rfl)
            refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
            · intro r m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              injection hMap with hR hM
              subst hR hM
              exact ⟨⟨rfl, rfl⟩, rfl⟩
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
          | cons _ _ => exact Bool.noConfusion hDom.1
      · exact Or.inl ⟨rfl, Or.inl ⟨{ args := [] }, ⟨rfl, rfl⟩,
          ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
    | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
end Proof
";

    fs::write(work.join("SpecHelper.lean"), helper_src).unwrap();
    fs::write(work.join("Spec.lean"), spec_src).unwrap();
    fs::write(work.join("Proof.lean"), proof_src).unwrap();

    let helper_golden = spec_module_golden("SpecHelper", helper_src);
    fs::write(
        work.join("SpecHelper.spec-closure.golden"),
        serde_json::to_vec_pretty(&helper_golden).unwrap(),
    )
    .unwrap();

    let golden = json!({
        "root_spec_module": spec_module_golden("Spec", spec_src),
        "imported_spec_modules": {
            "SpecHelper": {
                "sha256": sha256_hex(helper_src.as_bytes()),
                "source_path": "SpecHelper.lean",
                "golden_path": "SpecHelper.spec-closure.golden"
            }
        },
        "user_declarations": [
            { "module": "Spec", "name": "Spec.specs", "kind": "def" },
            { "module": "Spec", "name": "Spec.zeroLawProp", "kind": "def" },
            { "module": "SpecHelper", "name": "SpecHelper.helperLawProp", "kind": "def" }
        ],
        "envelope_summary": {
            "entries": [{
                "identity": "rust-path-v1::zero",
                "is_unsafe": false,
                "terminates": true,
                "no_unwind": true,
                "no_abort": true,
                "require_inhabited": true
            }],
            "stubs": [],
            "refutations": [],
            "claim_shapes": ["forallSafety", "termination"],
            "gaps": [
                "unverifiedDownstream(rustc_mir_opt)",
                "unverifiedDownstream(llvm_codegen)",
                "unverifiedDownstream(linker)",
                "unverifiedDownstream(microarch_timing)"
            ],
            "law_heads": [{ "head": "Eq", "target_const": "Nat" }],
            "has_step_bounds": false
        }
    });
    let sc_bytes = serde_json::to_vec_pretty(&golden).unwrap();
    let sc_sha = sha256_hex(&sc_bytes);
    let sc_path = work.join("spec-closure.golden");
    fs::write(&sc_path, &sc_bytes).unwrap();

    let art_dir = work.join("artifacts");
    let receipt_path = work.join("receipt.json");
    let (out, receipt) = run_verify(
        work,
        &[
            OsStr::new("--artifacts"),
            art_dir.as_os_str(),
            OsStr::new("--receipt-out"),
            receipt_path.as_os_str(),
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            sc_path.as_os_str(),
        ],
    );
    assert_eq!(
        out.status.code(),
        Some(0),
        "rustc --spec-closure failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let verified = assert_verified_untainted(&receipt).unwrap();
    assert_eq!(verified.status, "crate_verified");
    assert_eq!(verified.spec_closure_sha256.as_deref(), Some(sc_sha.as_str()));
    assert!(verified.candidate_features.contains(&"refinement".to_owned()));
    assert_eq!(verified.audit["canonicalRoot"], "Trusted.Framework.CrateMirEnvelopeTheoremV1");

    // `cargo-anneal inspect` passes strictly with `--require-exact-artifacts`.
    for (fmt, substr) in [
        ("ledger", &format!("digest.spec_closure_sha256={sc_sha}")),
        ("markdown", &format!("| Spec Closure Digest | `{}` |", &sc_sha[..12])),
    ] {
        let insp = run_cli(
            work,
            &[
                OsStr::new("inspect"),
                receipt_path.as_os_str(),
                OsStr::new("--verify-artifacts"),
                art_dir.as_os_str(),
                OsStr::new("--require-exact-artifacts"),
                OsStr::new("--check"),
                OsStr::new("--require-untainted"),
                OsStr::new("--unknown-fields"),
                OsStr::new("deny"),
                OsStr::new("--format"),
                OsStr::new(fmt),
            ],
        );
        assert_eq!(
            insp.status.code(),
            Some(0),
            "inspect fmt={fmt}\nstderr: {}",
            String::from_utf8_lossy(&insp.stderr)
        );
        let stdout = String::from_utf8_lossy(&insp.stdout);
        assert!(stdout.contains(substr), "fmt={fmt}\n{stdout}");
    }

    // `inspect --diff --require-unchanged-specs` classifies changed
    // `spec_closure_sha256` as Tier A (exit 1).
    let mut modified_receipt: Value =
        serde_json::from_slice(&fs::read(&receipt_path).unwrap()).unwrap();
    modified_receipt["spec_closure_sha256"] = json!("f".repeat(64));
    let mod_receipt_path = work.join("receipt_modified.json");
    fs::write(&mod_receipt_path, serde_json::to_vec(&modified_receipt).unwrap()).unwrap();
    let diff_out = run_cli(
        work,
        &[
            OsStr::new("inspect"),
            OsStr::new("--diff"),
            receipt_path.as_os_str(),
            mod_receipt_path.as_os_str(),
            OsStr::new("--require-unchanged-specs"),
            OsStr::new("--format"),
            OsStr::new("json"),
        ],
    );
    assert_eq!(
        diff_out.status.code(),
        Some(1),
        "inspect --diff stderr: {}",
        String::from_utf8_lossy(&diff_out.stderr)
    );
    let diff_json: Value = serde_json::from_slice(&diff_out.stdout).unwrap();
    assert_eq!(diff_json["has_regressions"], true, "{diff_json}");
    assert!(
        diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "spec_closure_sha256" && c["tier"] == "tier_a"),
        "expected Tier A spec_closure_sha256 change: {diff_json}"
    );

    // Negative: omitting `--spec-closure` fails closed (`Expected.claim`
    // expects `CrateTheorem`).
    let (out_no_sc, rec_no_sc) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
        ],
    );
    assert_eq!(out_no_sc.status.code(), Some(1));
    assert_rejected(&rec_no_sc, "proof_failed", None, "").unwrap();

    // Negative: non-CODEOWNERS-gated filename is rejected fail-closed.
    let bad_name_path = work.join("bad_name.json");
    fs::write(&bad_name_path, &sc_bytes).unwrap();
    let (out_bad_name, rec_bad_name) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            bad_name_path.as_os_str(),
        ],
    );
    assert_eq!(out_bad_name.status.code(), Some(1));
    assert_rejected(&rec_bad_name, "unsupported", Some("spec"), "spec-closure.golden").unwrap();

    // Negative: tampered root sha256, self-consistent root lines mismatch,
    // mismatched `user_declarations`, mismatched `envelope_summary`, or
    // tampered companion `.spec-closure.golden` content fails closed.
    let mut bad_sha = golden.clone();
    bad_sha["root_spec_module"]["sha256"] = json!("0".repeat(64));
    let bad_sha_path = work.join("bad_sha.spec-closure.golden");
    fs::write(&bad_sha_path, serde_json::to_vec(&bad_sha).unwrap()).unwrap();
    let (out_bad_sha, rec_bad_sha) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            bad_sha_path.as_os_str(),
        ],
    );
    assert_eq!(out_bad_sha.status.code(), Some(1));
    assert_rejected(&rec_bad_sha, "proof_failed", Some("spec"), "digest mismatch").unwrap();

    let mut bad_root_lines = golden.clone();
    bad_root_lines["root_spec_module"] = spec_module_golden("Spec", "-- different\n");
    let bad_root_lines_path = work.join("bad_root_lines.spec-closure.golden");
    fs::write(&bad_root_lines_path, serde_json::to_vec(&bad_root_lines).unwrap()).unwrap();
    let (out_bad_lines, rec_bad_lines) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            bad_root_lines_path.as_os_str(),
        ],
    );
    assert_eq!(out_bad_lines.status.code(), Some(1));
    assert_rejected(
        &rec_bad_lines,
        "proof_failed",
        Some("spec"),
        "root_spec_module lines do not match",
    )
    .unwrap();

    let mut bad_decls = golden.clone();
    bad_decls["user_declarations"] =
        json!([{ "module": "Spec", "name": "Spec.specs", "kind": "def" }]);
    let bad_decls_path = work.join("bad_decls.spec-closure.golden");
    fs::write(&bad_decls_path, serde_json::to_vec(&bad_decls).unwrap()).unwrap();
    let (out_bad_decls, rec_bad_decls) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            bad_decls_path.as_os_str(),
        ],
    );
    assert_eq!(out_bad_decls.status.code(), Some(1));
    assert_rejected(&rec_bad_decls, "proof_failed", Some("spec"), "user_declarations").unwrap();

    let mut bad_summary = golden.clone();
    bad_summary["envelope_summary"]["claim_shapes"] = json!(["forallSafety"]);
    let bad_summary_path = work.join("bad_summary.spec-closure.golden");
    fs::write(&bad_summary_path, serde_json::to_vec(&bad_summary).unwrap()).unwrap();
    let (out_bad_sum, rec_bad_sum) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            bad_summary_path.as_os_str(),
        ],
    );
    assert_eq!(out_bad_sum.status.code(), Some(1));
    assert_rejected(&rec_bad_sum, "proof_failed", Some("spec"), "envelope_summary").unwrap();

    let tampered_helper_src = format!("{helper_src}-- tampered\n");
    let tampered_comp_path = work.join("TamperedHelper.spec-closure.golden");
    fs::write(
        &tampered_comp_path,
        serde_json::to_vec_pretty(&spec_module_golden("SpecHelper", &tampered_helper_src)).unwrap(),
    )
    .unwrap();
    let mut bad_comp = golden.clone();
    bad_comp["imported_spec_modules"]["SpecHelper"] = json!({
        "sha256": sha256_hex(tampered_helper_src.as_bytes()),
        "source_path": "SpecHelper.lean",
        "golden_path": "TamperedHelper.spec-closure.golden"
    });
    let bad_comp_path = work.join("bad_comp.spec-closure.golden");
    fs::write(&bad_comp_path, serde_json::to_vec(&bad_comp).unwrap()).unwrap();
    let (out_bad_comp, rec_bad_comp) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--spec-file"),
            OsStr::new("SpecHelper=SpecHelper.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            bad_comp_path.as_os_str(),
        ],
    );
    assert_eq!(out_bad_comp.status.code(), Some(1));
    assert_rejected(&rec_bad_comp, "proof_failed", Some("spec"), "imported module `SpecHelper`")
        .unwrap();
}

#[test]
fn fatal_envelope_spec_warning_fails_closed_as_proof_failed() {
    let dir = TempDir::new().unwrap();
    let work = dir.path();

    let rust_path = work.join("lib.rs");
    fs::write(&rust_path, "pub fn zero() {}\n").unwrap();

    // `unusedArgHelper` triggers Gate G4 `unused_spec_binding` which is fatal
    // on envelope roots.
    let spec_src = "\
prelude
import Init.NotationExtra
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def unusedArgHelper (unused_arg : Nat) : Nat := 0
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := \"rust-path-v1::zero\"
    sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
    contract := {
      postReturn := fun _ r _ => r = .unit
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := defaultMirDownstreamGaps
  laws := []
}
end Spec
";
    let proof_src = "\
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
import Anneal.MirWp
import Anneal.Framework
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework Anneal.MirWp Anneal.Framework
theorem verify : Expected.claim := by
  dsimp only [Expected.claim, MirEnvelopeHolds, EnvelopeTheorem, mkEnvelope, AllSpecLaws,
    NoDupStrings, List.map, List.append]
  refine ⟨rfl, (fun h => by cases h),
      ⟨⟨ne_string_of_len_beq_false rfl, rfl, ?_, rfl,
          fun h => Bool.noConfusion h, nonEmpty_oracle_id, ?_, fun _ h => h⟩,
        ?_, ?_, ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩,
      True.intro, True.intro⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      rfl
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, Captured.body_0, rfl, rfl, rfl, rfl, absurd_mem_nil, ?_, ?_, ?_⟩
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            exact (spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 10)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg (fuel := 10) rfl)).1
          | cons _ _ => exact Bool.noConfusion hDom.1
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          dsimp at hDom
          rw [hDom.2]
          cases args with
          | nil =>
            have hSpec := spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [] }) (fuel := 10)
              (out := .returned ⟨.unit, ⟨[]⟩⟩)
              (wpProg_of_execProg (fuel := 10) rfl)
            refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
            · intro r m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              injection hMap with hR hM
              subst hR hM
              exact ⟨⟨rfl, rfl⟩, rfl⟩
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
            · intro m ⟨out, hBehOut, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBehOut
              subst hEq
              cases hMap
          | cons _ _ => exact Bool.noConfusion hDom.1
      · exact Or.inl ⟨rfl, Or.inl ⟨{ args := [] }, ⟨rfl, rfl⟩,
          ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
    | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
end Proof
";
    fs::write(work.join("Spec.lean"), spec_src).unwrap();
    fs::write(work.join("Proof.lean"), proof_src).unwrap();

    let golden = json!({
        "root_spec_module": spec_module_golden("Spec", spec_src),
        "imported_spec_modules": {},
        "user_declarations": [
            { "module": "Spec", "name": "Spec.specs", "kind": "def" },
            { "module": "Spec", "name": "Spec.unusedArgHelper", "kind": "def" }
        ],
        "envelope_summary": {
            "entries": [{
                "identity": "rust-path-v1::zero",
                "is_unsafe": false,
                "terminates": true,
                "no_unwind": true,
                "no_abort": true,
                "require_inhabited": true
            }],
            "stubs": [],
            "refutations": [],
            "claim_shapes": ["forallSafety", "termination"],
            "gaps": [
                "unverifiedDownstream(rustc_mir_opt)",
                "unverifiedDownstream(llvm_codegen)",
                "unverifiedDownstream(linker)",
                "unverifiedDownstream(microarch_timing)"
            ],
            "law_heads": [],
            "has_step_bounds": false
        }
    });
    let sc_path = work.join("spec-closure.golden");
    fs::write(&sc_path, serde_json::to_vec_pretty(&golden).unwrap()).unwrap();

    let (out, receipt) = run_verify(
        work,
        &[
            OsStr::new("rustc"),
            rust_path.as_os_str(),
            OsStr::new("--crate-name"),
            OsStr::new("demo"),
            OsStr::new("--spec-file"),
            OsStr::new("Spec=Spec.lean"),
            OsStr::new("--proof-file"),
            OsStr::new("Proof=Proof.lean"),
            OsStr::new("--spec-closure"),
            sc_path.as_os_str(),
        ],
    );
    assert_eq!(out.status.code(), Some(1));
    assert_rejected(&receipt, "proof_failed", Some("audit"), "unused_spec_binding").unwrap();
}

#[test]
fn real_zerocopy_split_at_unchecked_verifies_unit_mir_envelope_theorem_v2() {
    let dir = TempDir::new().unwrap();
    let work = dir.path();
    let lean_dir = work.join("lean");
    fs::create_dir_all(&lean_dir).unwrap();

    let zc_src =
        fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../zerocopy/src"))
            .expect("resolve unmodified zerocopy/src");

    let spec_src = "\
prelude
import Trusted.Framework.Bridge
namespace Spec
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
def splitAtSharedIdentity : String :=
  \"rust-path-v1::<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked\"
def splitAtSafety (q : Query) : Prop :=
  match q.args with
  | [.slicePtr _ len, .scalar mid] => mid.bits.toNat ≤ len.toNat
  | _ => False
def splitAtPostReturn (q : Query) (r : Val) (m : CallerMemory) : Prop :=
  match q.args with
  | [.slicePtr ptr len, .scalar mid] =>
    let pR :=
      match ptr.allocId with
      | none => ptr
      | some _ =>
        { ptr with
          offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + mid.bits.toNat) }
    let lenL := UInt64.ofNat mid.bits.toNat
    let lenR := UInt64.ofNat (len.toNat - mid.bits.toNat)
    m = q.callerMem ∧
    r = .tuple [.slicePtr ptr lenL, .slicePtr pR lenR] ∧
    lenL.toNat + lenR.toNat = len.toNat
  | _ => False
def specs : MirEnvelopeSpec := {
  entries := [{
    identity := splitAtSharedIdentity
    sig := {
      isUnsafe := true
      abi := .rust
      params := [.ref .shared (.slice (.int .i8 false)), .int .isize false]
      ret := .tuple [
        .ref .shared (.slice (.int .i8 false)),
        .ref .shared (.slice (.int .i8 false))
      ]
    }
    contract := {
      safetyPre := splitAtSafety
      postReturn := splitAtPostReturn
      effects := { terminates := true, noUnwind := true, noAbort := true }
    }
  }]
  claimShapes := [.forallSafety, .termination]
  gaps := .selectedUnitScope ::
          .unbridgedSemantics \"mir_profile_v2\" ::
          .callerMemoryThreadIsolation \"mir_profile_v2\" ::
          .callerRawPtrAliasing \"mir_profile_v2\" ::
          defaultMirDownstreamGaps
  laws := []
}
end Spec
";

    let base_proof = include_str!("fixtures/profile_v2_zerocopy/Proof.lean");
    let (prefix, _) =
        base_proof.split_once("theorem verify : Expected.claim := by").expect("split Proof.lean");
    let patched_prefix = prefix
        .replace("import Anneal.MirWp.V2Memory", "import Anneal.MirWp.V2Memory\nimport Anneal.Framework")
        .replace(
            "      WellFormedV2 (entryProgForBody Captured.program 0) q ∧\n      (∃ out : TerminalOut,\n        BehaviorV2 (entryProgForBody Captured.program 0) q out ∧\n        out = TerminalOut.returned\n          ⟨.tuple [.slicePtr ptr lenL, .slicePtr pR lenR], q.callerMem⟩ ∧\n        lenL.toNat + lenR.toNat = len.toNat)",
            "      WellFormedV2 (entryProgForBody Captured.program 0) q ∧\n      ¬ DivergesV2 (entryProgForBody Captured.program 0) q ∧\n      (∀ out : TerminalOut,\n        BehaviorV2 (entryProgForBody Captured.program 0) q out →\n        out = TerminalOut.returned\n          ⟨.tuple [.slicePtr ptr lenL, .slicePtr pR lenR], q.callerMem⟩) ∧\n      lenL.toNat + lenR.toNat = len.toNat ∧\n      Trusted.Framework.ValidMirReturnValV2 Captured.body_0\n        (.tuple [.slicePtr ptr lenL, .slicePtr pR lenR]) q.callerMem",
        )
        .replace(
            "    have hRes := spec_and_behaviorV2_of_exec_eq hExec\n    rw [← hQ] at hRes\n    rw [hArgs]\n    refine ⟨hRes.1, expectedOut, hRes.2.1, ?_, hSumLen⟩\n    dsimp only [expectedOut]\n    rw [hPRSpecEq]",
            "    have hRes := spec_and_behaviorV2_of_exec_eq hExec\n    have hRetValid : Trusted.Framework.ValidMirReturnValV2 Captured.body_0\n        (.tuple [.slicePtr ptr lenL, .slicePtr pR lenR]) q.callerMem := by\n      dsimp only [Trusted.Framework.ValidMirReturnValV2, Captured.body_0,\n        Trusted.MirSemantics.getElem?]\n      refine ⟨?_, hCM, hStay, ?_, hDisjOut⟩\n      · dsimp only [checkValV2, checkValV2List]; rw [hPRW]; rfl\n      · dsimp only [refsValidInMem, refsValidInMemList]\n        rw [hRefValidL, hRefValidR]\n        rfl\n    have hRes' : WellFormedV2 (entryProgForBody Captured.program 0)\n        ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ ∧\n        ¬ DivergesV2 (entryProgForBody Captured.program 0)\n          ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ ∧\n        ∀ out : TerminalOut,\n          BehaviorV2 (entryProgForBody Captured.program 0)\n            ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ out →\n          out = expectedOut := by\n      exact ⟨hRes.1, hRes.2.2.1, fun out hB =>\n        (hRes.2.2.2 (fun o => o = expectedOut) rfl).2 out hB⟩\n    rw [← hQ] at hRes'\n    rw [hArgs]\n    refine ⟨hRes'.1, hRes'.2.1, (fun out hB => ?_), hSumLen, ?_⟩\n    · have hEq := hRes'.2.2 out hB\n      rw [hEq]\n      dsimp only [expectedOut]\n      rw [hPRSpecEq]\n    · rw [← hPRSpecEq]\n      exact hRetValid",
        );
    let proof_src = format!(
        "{patched_prefix}\
open Trusted.Framework Anneal.Framework in
theorem verify : Expected.claim := by
  dsimp only [Expected.claim, MirEnvelopeHolds, EnvelopeTheorem, mkEnvelope, AllSpecLaws,
    NoDupStrings, List.map, List.append]
  refine ⟨rfl, (fun _ => List.Mem.head _),
      ⟨⟨nonEmpty_profile_v2_id, rfl, ?_, rfl, fun _ => List.Mem.head _,
          ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩, ?_,
          fun g hg => List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ hg)))⟩,
        ?_, ?_, ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩,
      True.intro, True.intro⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      rfl
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, Captured.body_0, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · intro g hg
        dsimp only [MirProfileV2] at hg
        unfold mirProfileV2RequiredGaps at hg
        cases hRaw : bodyHasRawPtrLocalV2 Captured.body_0 with
        | false =>
          rw [hRaw] at hg
          cases hg with
          | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
          | tail _ hNil => cases hNil
        | true =>
          rw [hRaw] at hg
          cases hg with
          | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
          | tail _ h2 =>
            cases h2 with
            | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hNil => cases hNil
      · intro q hDom hSafe
        have hSafePre : Spec.splitAtSafety q := hSafe rfl
        have hCor := split_at_shared_correct q hDom hSafePre
        let ⟨_, _, _, hArgs, _, _⟩ := checkArgsMatchV2_slice_u8_isize_inv hDom.2.1
        rw [hArgs] at hCor
        exact hCor.1
      · intro q hDom hBeh
        have hSafePre : Spec.splitAtSafety q := hBeh.1 rfl
        have hCor := split_at_shared_correct q hDom hSafePre
        let ⟨ptr, len, midBits, hArgs, _, _⟩ := checkArgsMatchV2_slice_u8_isize_inv hDom.2.1
        rw [hArgs] at hCor
        let ⟨_, hNoDiv, hUniq, hSumLen, hRetValid⟩ := hCor
        refine ⟨fun _ => hNoDiv, ?_, ?_, ?_⟩
        · intro r m ⟨out, hBehOut, hMap⟩
          have hEq := hUniq out hBehOut
          subst hEq
          injection hMap with hR hM
          subst hR hM
          refine ⟨hRetValid, ?_⟩
          dsimp only [Spec.splitAtPostReturn]
          rw [hArgs]
          dsimp only
          exact ⟨rfl, rfl, hSumLen⟩
        · intro m ⟨out, hBehOut, hMap⟩
          have hEq := hUniq out hBehOut
          subst hEq
          cases hMap
        · intro m ⟨out, hBehOut, hMap⟩
          have hEq := hUniq out hBehOut
          subst hEq
          cases hMap
      · refine Or.inl ⟨rfl, Or.inl ⟨{{
            args := [.slicePtr ⟨none, 1, .isize⟩ 0, .scalar ⟨.isize, false, 0⟩],
            callerMem := ⟨[]⟩ }}, ?_, ⟨fun _ => Nat.le_refl 0, True.intro⟩⟩⟩
        refine ⟨rfl, rfl, ?_, rfl⟩
        have hTys : List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals) =
            [.ref .shared (.slice (.int .i8 false)), .int .isize false] := by rfl
        rw [hTys]
        change refsValidInMem (entryMemoryWithCaller ⟨[]⟩)
          (.ref .shared (.slice (.int .i8 false))) (.slicePtr ⟨none, 1, .isize⟩ 0) &&
          (refsValidInMem (entryMemoryWithCaller ⟨[]⟩) (.int .isize false)
            (.scalar ⟨.isize, false, 0⟩) && true) = true
        unfold refsValidInMem refValidInMem
        dsimp only
        rw [ite_bool_false (by decide : (!isSizedNoRefV2Ty (.int .i8 false)) = false),
          show layoutOfTyV2 (.int .i8 false) = some ⟨1, 0⟩ from rfl]
        dsimp only
        unfold sliceFromRawPartsCheck sliceRefRawCheck
        rw [ite_bool_false (by decide : (!Nat.blt ((0 : UInt64).toNat * 1) isizeMaxBytes) = false)]
        dsimp only
        rw [ite_bool_false (by decide :
          (Nat.beq ((1 : UInt64).toNat) 0 || Nat.blt 0 ((0 : UInt64).toNat * 1)) = false)]
        rw [ite_bool_false (by decide :
          (!Nat.beq (Nat.mod ((1 : UInt64).toNat) (Nat.pow 2 0)) 0) = false)]
        rfl
    | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
end Proof
"
    );

    fs::write(lean_dir.join("Spec.lean"), spec_src).unwrap();
    fs::write(lean_dir.join("Proof.lean"), &proof_src).unwrap();

    let golden = json!({
        "root_spec_module": spec_module_golden("Spec", spec_src),
        "imported_spec_modules": {},
        "user_declarations": [
            { "module": "Spec", "name": "Spec.specs", "kind": "def" },
            { "module": "Spec", "name": "Spec.splitAtPostReturn", "kind": "def" },
            { "module": "Spec", "name": "Spec.splitAtSafety", "kind": "def" },
            { "module": "Spec", "name": "Spec.splitAtSharedIdentity", "kind": "def" }
        ],
        "envelope_summary": {
            "entries": [{
                "identity": "rust-path-v1::<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked",
                "is_unsafe": true,
                "terminates": true,
                "no_unwind": true,
                "no_abort": true,
                "require_inhabited": true
            }],
            "stubs": [],
            "refutations": [],
            "claim_shapes": ["forallSafety", "termination"],
            "gaps": [
                "selectedUnitScope",
                "unbridgedSemantics(mir_profile_v2)",
                "callerMemoryThreadIsolation(mir_profile_v2)",
                "callerRawPtrAliasing(mir_profile_v2)",
                "unverifiedDownstream(rustc_mir_opt)",
                "unverifiedDownstream(llvm_codegen)",
                "unverifiedDownstream(linker)",
                "unverifiedDownstream(microarch_timing)"
            ],
            "law_heads": [],
            "has_step_bounds": false
        }
    });
    let sc_bytes = serde_json::to_vec_pretty(&golden).unwrap();
    let sc_sha = sha256_hex(&sc_bytes);
    fs::write(lean_dir.join("spec-closure.golden"), &sc_bytes).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": zc_src,
            "crate_root": "lib.rs",
            "crate_name": "zerocopy",
            "crate_type": "lib",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": ["no_zerocopy_allocator_api_1_100_0"],
            "env": {"CARGO_PKG_VERSION": "0.8.64"},
            "source_files": ZEROCOPY_SOURCE_FILES
        },
        "scope": {
            "kind": "selected_unit",
            "roots": ["<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked"]
        },
        "proof": {
            "source_root": lean_dir,
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "spec_closure": "spec-closure.golden",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let req_path = work.join("request.json");
    fs::write(&req_path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
    let art_dir = work.join("artifacts");
    let receipt_path = work.join("zc_receipt.json");
    let (out, receipt) = run_verify(
        work,
        &[
            OsStr::new("--request"),
            req_path.as_os_str(),
            OsStr::new("--artifacts"),
            art_dir.as_os_str(),
            OsStr::new("--receipt-out"),
            receipt_path.as_os_str(),
        ],
    );
    assert_eq!(
        out.status.code(),
        Some(0),
        "zerocopy UnitMirEnvelopeTheoremV2 failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let verified = assert_verified_untainted(&receipt).unwrap();
    assert_eq!(verified.status, "selected_unit_verified");
    assert_eq!(verified.spec_closure_sha256.as_deref(), Some(sc_sha.as_str()));
    assert_eq!(verified.audit["canonicalRoot"], "Trusted.Framework.UnitMirEnvelopeTheoremV2");

    let insp = run_cli(
        work,
        &[
            OsStr::new("inspect"),
            receipt_path.as_os_str(),
            OsStr::new("--verify-artifacts"),
            art_dir.as_os_str(),
            OsStr::new("--require-exact-artifacts"),
            OsStr::new("--check"),
            OsStr::new("--require-untainted"),
            OsStr::new("--unknown-fields"),
            OsStr::new("deny"),
            OsStr::new("--format"),
            OsStr::new("json"),
        ],
    );
    assert_eq!(
        insp.status.code(),
        Some(0),
        "inspect zerocopy failed:\nstderr: {}",
        String::from_utf8_lossy(&insp.stderr)
    );
}

#[test]
fn unpinned_ndjson_route_refuses_envelope_root_fail_closed() {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let dir = TempDir::new().unwrap();
        let root = dir.path();

        let rust_path = root.join("lib.rs");
        fs::write(&rust_path, "pub fn id() {}\n").unwrap();
        let spec_src = "prelude\ndef Spec.specs : Nat := 0\n";
        let proof_src = "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := rfl\n";
        fs::write(root.join("Spec.lean"), spec_src).unwrap();
        fs::write(root.join("Proof.lean"), proof_src).unwrap();

        let golden = json!({
            "root_spec_module": spec_module_golden("Spec", spec_src),
            "imported_spec_modules": {},
            "user_declarations": [{ "module": "Spec", "name": "Spec.specs", "kind": "def" }],
            "envelope_summary": {
                "entries": [],
                "stubs": [],
                "refutations": [],
                "claim_shapes": [],
                "gaps": [],
                "law_heads": [],
                "has_step_bounds": false
            }
        });
        let sc_path = root.join("spec-closure.golden");
        fs::write(&sc_path, serde_json::to_vec(&golden).unwrap()).unwrap();

        let sysroot = root.join("sysroot");
        fs::create_dir_all(sysroot.join("lib")).unwrap();

        // Fake Lean v4.35.0+ toolchain exposing NDJSON comparator tools
        // alongside `lean` so `--allow-unpinned-lean` hits the NDJSON
        // comparator gate.
        let lean_prefix = root.join("lean-prefix");
        let lean_bin_dir = lean_prefix.join("bin");
        let lean_lib_dir = lean_prefix.join("lib/lean");
        fs::create_dir_all(&lean_bin_dir).unwrap();
        fs::create_dir_all(lean_lib_dir.join("Init")).unwrap();
        fs::write(lean_lib_dir.join("libleanshared.so"), b"stub").unwrap();
        fs::write(lean_lib_dir.join("Init.olean"), b"olean\x02init").unwrap();
        for m in ["Coe", "Core", "Notation", "Prelude", "SizeOf", "Tactics"] {
            fs::write(lean_lib_dir.join(format!("Init/{m}.olean")), b"olean\x02fnd").unwrap();
        }
        for tool_name in ["leanexport", "nanoda_bin", "con-ron"] {
            let p = lean_bin_dir.join(tool_name);
            fs::write(&p, b"#!/bin/sh\nexit 0\n").unwrap();
            fs::set_permissions(&p, fs::Permissions::from_mode(0o755)).unwrap();
        }
        let fake_lean = lean_bin_dir.join("lean");
        let lean_script = format!(
            "#!/bin/sh\n\
             set -eu\n\
             if [ \"${{1:-}}\" = '--version' ]; then\n\
               printf 'Lean (version 4.35.0)\\n'\n\
               exit 0\n\
             fi\n\
             if [ \"${{1:-}}\" = '--print-prefix' ]; then\n\
               printf '%s\\n' {prefix:?}\n\
               exit 0\n\
             fi\n\
             out_olean=''\n\
             run_mode=0\n\
             prev=''\n\
             last=''\n\
             while [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in\n\
                 -o)\n\
                   shift\n\
                   out_olean=\"$1\"\n\
                   ;;\n\
                 --run)\n\
                   run_mode=1\n\
                   ;;\n\
               esac\n\
               prev=\"$last\"\n\
               last=\"$1\"\n\
               shift\n\
             done\n\
             if [ \"$run_mode\" -eq 1 ]; then\n\
               /usr/bin/python3 -c 'import json, sys; req = json.load(open(sys.argv[1])); m = req[\"mode\"]; fnd = [\"Init.Coe\", \"Init.Core\", \"Init.Notation\", \"Init.Prelude\", \"Init.SizeOf\", \"Init.Tactics\"]; res = {{\"headers\": [{{\"module\": n, \"imports\": [], \"isModule\": False}} for n, _ in req[\"sources\"]]}} if m == \"headers\" else ({{\"checked\": [n for n, _ in req[\"sources\"]]}} if m == \"spec-preflight\" else ({{\"graph\": {{k: ([{{\"module\": d, \"importAll\": False, \"isExported\": True, \"isMeta\": False}} for d in fnd if d != k] if k == \"Init.Core\" else []) for k in fnd}}}} if m == \"resolve-imports\" else {{}})); json.dump({{\"ok\": True, \"result\": res}}, open(sys.argv[2], \"w\"))' \"$prev\" \"$last\"\n\
               exit 0\n\
             fi\n\
             if [ -n \"$out_olean\" ]; then\n\
               printf 'olean\\002stub' > \"$out_olean\"\n\
               exit 0\n\
             fi\n\
             exit 0\n",
            prefix = lean_prefix.display()
        );
        fs::write(&fake_lean, lean_script).unwrap();
        fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_capture = root.join("fake-capture");
        let cap_script = "#!/bin/sh\n\
            set -eu\n\
            out_dir=''\n\
            while [ \"$#\" -gt 0 ]; do\n\
              if [ \"$1\" = '--out-dir' ]; then shift; out_dir=\"$1\"; fi\n\
              shift\n\
            done\n\
            mkdir -p \"$out_dir\"\n\
            cat > \"$out_dir/capture.json\" <<'JSON'\n\
            {\n\
              \"schema_version\": 5,\n\
              \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
              \"configuration\": {\n\
                \"crate_root\": \"lib.rs\",\n\
                \"crate_name\": \"demo\",\n\
                \"crate_type\": \"lib\",\n\
                \"panic\": \"unwind\",\n\
                \"overflow_checks\": false,\n\
                \"target\": \"x86_64-unknown-linux-gnu\",\n\
                \"edition\": \"2024\",\n\
                \"cfg\": [],\n\
                \"env\": {}\n\
              },\n\
              \"source_files\": [],\n\
              \"census\": [],\n\
              \"selected\": [],\n\
              \"program\": {\"scope\": {\"kind\": \"crate\"}, \"bodies\": []}\n\
            }\n\
            JSON\n\
            printf -- '-- captured\\n' > \"$out_dir/Captured.lean\"\n\
            printf '{\"status\":\"captured\"}\\n'\n";
        fs::write(&fake_capture, cap_script).unwrap();
        fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

        let out = run_cli(
            root,
            &[
                OsStr::new("verify"),
                OsStr::new("--format"),
                OsStr::new("json"),
                OsStr::new("--no-cache"),
                OsStr::new("--allow-unpinned-lean"),
                OsStr::new("--allow-unsandboxed-elaboration"),
                OsStr::new("--capture"),
                fake_capture.as_os_str(),
                OsStr::new("--sysroot"),
                sysroot.as_os_str(),
                OsStr::new("--lean"),
                fake_lean.as_os_str(),
                OsStr::new("rustc"),
                rust_path.as_os_str(),
                OsStr::new("--crate-name"),
                OsStr::new("demo"),
                OsStr::new("--spec-file"),
                OsStr::new("Spec=Spec.lean"),
                OsStr::new("--proof-file"),
                OsStr::new("Proof=Proof.lean"),
                OsStr::new("--spec-closure"),
                sc_path.as_os_str(),
            ],
        );
        assert_ne!(out.status.code(), Some(0));
        let rec: Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(rec["status"], "unsupported", "{rec}");
        assert!(
            rec["detail"].as_str().unwrap_or("").contains("NDJSON comparator"),
            "expected ndjson rejection detail: {rec}"
        );
    }
}
