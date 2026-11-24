// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end Profile v2 (`mirProfileVersion = 2`) verification regressions.
//!
//! Exercises real `cargo-anneal verify` with `anneal-rustc-capture` and the
//! pinned Lean toolchain across:
//! 1. Verbatim `zerocopy/src/byte_slice.rs`
//!    `<&[u8] as SplitByteSlice>::split_at_unchecked` under `UnitTheoremV2`
//!    with non-vacuous `SpecsV2.safety` and functional `SpecsV2.property`.
//! 2. Raw pointer `*const u32` aligned load and `*mut u8` store updating
//!    `out.callerMem` under `CrateTheoremV2`.
//! 3. Fail-closed negative cases: proofs rejected for unsound caller
//!    preconditions (omitted `mid <= len`, missing alignment, null pointer,
//!    read-only write), and capture refusing bodies that mix reference and
//!    raw-pointer locals, which Profile v2 cannot check without an aliasing
//!    model (verbatim `<&mut [u8] as SplitByteSlice>::split_at_unchecked`,
//!    `from_raw_parts`, and a returned reference to a stack local).

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use serde_json::{Value, json};
use tempfile::TempDir;

const ZEROCOPY_SPEC: &str = include_str!("fixtures/profile_v2_zerocopy/Spec.lean");
const ZEROCOPY_PROOF: &str = include_str!("fixtures/profile_v2_zerocopy/Proof.lean");
const RAW_PTR_LIB: &str = include_str!("fixtures/profile_v2_raw_ptr/lib.rs");
const RAW_PTR_SPEC: &str = include_str!("fixtures/profile_v2_raw_ptr/Spec.lean");
const RAW_PTR_PROOF: &str = include_str!("fixtures/profile_v2_raw_ptr/Proof.lean");

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

struct Tools {
    cli: PathBuf,
    capture: PathBuf,
    lean: PathBuf,
    sysroot: PathBuf,
}

impl Tools {
    fn discover() -> Self {
        let install_root = override_path("ANNEAL_TEST_INSTALL_ROOT");
        let cli = first_override(&["ANNEAL_CLI"])
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal-test-bin")));
        let cli = required_file(cli, "cargo-anneal", "ANNEAL_CLI");
        let capture = first_override(&["ANNEAL_CAPTURE"])
            .or_else(|| {
                ["anneal-rustc-capture", "anneal-rustc-capture-test-bin"]
                    .into_iter()
                    .map(|name| cli.with_file_name(name))
                    .find(|sibling| sibling.is_file())
            })
            .or_else(|| install_root.as_ref().map(|root| root.join("bin/anneal-rustc-capture")))
            .unwrap_or_else(|| cli.with_file_name("anneal-rustc-capture"));
        let capture = required_file(
            capture,
            "anneal-rustc-capture; build it before running this test",
            "ANNEAL_CAPTURE",
        );
        let lean = first_override(&["ANNEAL_LEAN"])
            .or_else(|| install_root.as_ref().map(|root| root.join("lean/bin/lean")))
            .unwrap_or_else(cargo_anneal::default_lean_path);
        let lean = required_file(lean, "the pinned Lean executable", "ANNEAL_LEAN");
        let sysroot = first_override(&["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"])
            .or_else(|| install_root.as_ref().map(|root| root.join("rust")))
            .unwrap_or_else(|| {
                let output = Command::new("rustup")
                    .args(["run", "nightly-2026-05-31", "rustc", "--print", "sysroot"])
                    .output()
                    .expect("install the pinned compiler or set ANNEAL_SYSROOT");
                assert!(
                    output.status.success(),
                    "cannot find the pinned compiler sysroot; set ANNEAL_SYSROOT:\n{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                PathBuf::from(
                    String::from_utf8(output.stdout).expect("rustc sysroot must be UTF-8").trim(),
                )
            });
        assert!(
            sysroot.join("lib").is_dir(),
            "missing compiler sysroot {}; set ANNEAL_SYSROOT",
            sysroot.display()
        );
        let sysroot = fs::canonicalize(sysroot).expect("resolve test sysroot path");
        Self { cli, capture, lean, sysroot }
    }

    fn verify_command(&self) -> Command {
        let mut command = Command::new(&self.cli);
        command
            .arg("verify")
            .arg("--capture")
            .arg(&self.capture)
            .arg("--lean")
            .arg(&self.lean)
            .arg("--sysroot")
            .arg(&self.sysroot);
        command
    }
}

fn override_path(name: &str) -> Option<PathBuf> {
    std::env::var_os(name).filter(|value| !value.is_empty()).map(PathBuf::from)
}

fn first_override(names: &[&str]) -> Option<PathBuf> {
    names.iter().find_map(|name| override_path(name))
}

fn required_file(path: PathBuf, what: &str, variable: &str) -> PathBuf {
    assert!(path.is_file(), "missing {what} at {}; set {variable}", path.display());
    fs::canonicalize(path).expect("resolve test tool path")
}

struct Receipt {
    name: String,
    value: Value,
    output: Output,
}

impl Receipt {
    fn expect_ok(&self, status: &str) {
        assert_eq!(
            self.output.status.code(),
            Some(0),
            "{} failed unexpectedly:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(self.value["schema_version"], 3, "{}: {}", self.name, self.value);
        assert!(self.value.get("tainted").is_none(), "{}: {}", self.name, self.value);
        assert_eq!(self.value["status"], status, "{}: {}", self.name, self.value);
        assert_eq!(self.value["audit"]["exactType"], true, "{}: {}", self.name, self.value);
        assert_eq!(self.value["audit"]["replay"], true, "{}: {}", self.name, self.value);
        assert_eq!(
            self.value["audit"]["axioms"],
            json!(["propext"]),
            "{}: {}",
            self.name,
            self.value
        );
    }

    fn expect_proof_failed(&self) {
        assert_eq!(
            self.output.status.code(),
            Some(1),
            "{} must fail closed:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(self.value["schema_version"], 3, "{}: {}", self.name, self.value);
        assert_eq!(self.value["status"], "proof_failed", "{}: {}", self.name, self.value);
        assert_eq!(self.value["phase"], "audit", "{}: {}", self.name, self.value);
    }

    fn expect_capture_refused(&self, needle: &str) {
        assert_eq!(
            self.output.status.code(),
            Some(1),
            "{} must fail closed:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(self.value["status"], "unsupported", "{}: {}", self.name, self.value);
        assert_eq!(self.value["phase"], "capture", "{}: {}", self.name, self.value);
        let detail = self.value["detail"].as_str().unwrap_or_default();
        assert!(detail.contains(needle), "{}: {}", self.name, self.value);
    }
}

/// Capture refusal for bodies mixing reference and raw-pointer locals.
const MIXED_REFS_AND_RAW_PTRS: &str = "body mixes reference and raw-pointer locals";

fn run_request(tools: &Tools, dir: &Path, name: &str, request: &Value) -> Receipt {
    let req_path = dir.join(format!("{name}.json"));
    fs::write(&req_path, serde_json::to_vec_pretty(request).unwrap()).unwrap();
    let artifacts = dir.join(format!("artifacts-{name}"));
    let output = tools
        .verify_command()
        .current_dir(dir)
        .arg("--request")
        .arg(&req_path)
        .arg("--artifacts")
        .arg(&artifacts)
        .output()
        .unwrap_or_else(|e| panic!("failed to run {name}: {e}"));
    let value = serde_json::from_slice(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "{name} did not emit JSON receipt: {e}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    Receipt { name: name.to_owned(), value, output }
}

/// Verifies the unmodified `zerocopy/src/byte_slice.rs` `split_at_unchecked`
/// implementation for `&[u8]` end-to-end under `UnitTheoremV2` (`["propext"]`,
/// zero taint), confirms that omitting the `mid <= len` safety precondition is
/// rejected fail-closed, and confirms that capture refuses the `&mut [u8]`
/// implementation, which derives references from raw pointers.
#[test]
fn verifies_verbatim_zerocopy_split_at_unchecked_and_rejects_missing_bounds() {
    let tools = Tools::discover();
    let dir = TempDir::new().unwrap();
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(lean_dir.join("Spec.lean"), ZEROCOPY_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ZEROCOPY_PROOF).unwrap();

    let zc_src = fs::canonicalize(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../zerocopy/src"),
    )
    .expect("locate unmodified zerocopy/src");
    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": zc_src.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "zerocopy",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": ["no_zerocopy_allocator_api_1_100_0"],
            "env": {"CARGO_PKG_VERSION": "0.8.64"},
            "source_files": ZEROCOPY_SOURCE_FILES
        },
        "scope": {
            "kind": "selected_unit",
            "roots": [
                "<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked"
            ]
        },
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let ok = run_request(&tools, dir.path(), "zerocopy-split-at-ok", &request);
    ok.expect_ok("selected_unit_verified");
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-zerocopy-split-at-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");

    // Negative 1: weaken splitAtSafety to omit `mid <= len` on verbatim zerocopy.
    let bad_spec = ZEROCOPY_SPEC.replace(
        "mid.bits.toNat ≤ len.toNat",
        "True",
    );
    assert_ne!(bad_spec, ZEROCOPY_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_spec).unwrap();
    run_request(&tools, dir.path(), "zerocopy-split-at-missing-bounds", &request)
        .expect_proof_failed();

    // Negative 2: the `&mut [u8]` implementation mixes `&mut [u8]` and
    // `*mut u8` locals, so capture refuses it until Profile v2 models
    // aliasing.
    let mut mut_request = request.clone();
    mut_request["scope"]["roots"] =
        json!(["<&mut [u8] as byte_slice::SplitByteSlice>::split_at_unchecked"]);
    run_request(&tools, dir.path(), "zerocopy-split-at-mut-refused", &mut_request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Verifies raw pointer `*const u32` load and `*mut u8` store updating
/// `out.callerMem` under `CrateTheoremV2`, confirms that proofs are rejected
/// for missing alignment, null pointers, and read-only stores, and confirms
/// that capture refuses bodies that turn raw pointers into references.
#[test]
fn verifies_raw_pointer_load_store_and_rejects_unsound_callers() {
    let tools = Tools::discover();
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), RAW_PTR_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), RAW_PTR_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), RAW_PTR_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "raw_ptr_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let ok = run_request(&tools, dir.path(), "raw-ptr-ok", &request);
    ok.expect_ok("crate_verified");
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-raw-ptr-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");

    // Negative 2: missing alignment precondition on `*const u32`.
    let no_align = RAW_PTR_SPEC.replace(
        "isAligned a pv.offsetBytes.toNat 2 = true ∧",
        "True ∧",
    );
    assert_ne!(no_align, RAW_PTR_SPEC);
    fs::write(lean_dir.join("Spec.lean"), no_align).unwrap();
    run_request(&tools, dir.path(), "raw-ptr-missing-align", &request).expect_proof_failed();

    // Negative 3: missing non-null / live allocation precondition on `*const u32`.
    let allow_null = RAW_PTR_SPEC.replacen("| none => False", "| none => True", 1);
    assert_ne!(allow_null, RAW_PTR_SPEC);
    fs::write(lean_dir.join("Spec.lean"), allow_null).unwrap();
    run_request(&tools, dir.path(), "raw-ptr-allow-null", &request).expect_proof_failed();

    // Negative 4: missing `.mut` precondition on `*mut u8` write.
    let no_mut = RAW_PTR_SPEC.replace("a.mutability = .mut ∧", "True ∧");
    assert_ne!(no_mut, RAW_PTR_SPEC);
    fs::write(lean_dir.join("Spec.lean"), no_mut).unwrap();
    run_request(&tools, dir.path(), "raw-ptr-readonly-write", &request).expect_proof_failed();

    // Negative 5: `from_raw_parts` turns a `*const u8` into a `&[u8]`, so the
    // body mixes reference and raw-pointer locals and capture refuses it.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub unsafe fn make_slice<'a>(p: *const u8, len: usize) -> &'a [u8] {\n\
             unsafe { core::slice::from_raw_parts(p, len) }\n\
         }\n",
    )
    .unwrap();
    run_request(&tools, dir.path(), "slice-from-raw-parts-refused", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);

    // Negative 6: returning a dangling stack reference `&*(&raw const x)` also
    // mixes reference and raw-pointer locals.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub unsafe fn dangling<'a>(x: u8) -> &'a u8 {\n\
             unsafe { &*(&raw const x) }\n\
         }\n",
    )
    .unwrap();
    run_request(&tools, dir.path(), "dangling-stack-ref-refused", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}

/// Verifies safe `NonZero<usize>::get` and unsafe `new_unchecked`
/// under `CrateTheoremV2`, and confirms fail-closed rejection when the
/// non-zero precondition on `new_unchecked` is omitted.
#[test]
fn verifies_nonzero_usize_and_rejects_zero_unchecked() {
    let tools = Tools::discover();
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn get_nonzero(x: core::num::NonZero<usize>) -> usize {\n\
             x.get()\n\
         }\n\n\
         pub unsafe fn make_nonzero(x: usize) -> core::num::NonZero<usize> {\n\
             unsafe { core::num::NonZero::new_unchecked(x) }\n\
         }\n",
    )
    .unwrap();

    const NONZERO_SPEC: &str = "\
prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def makeNonZeroIdentity : String := \"rust-path-v1::make_nonzero\"

def makeNonZeroSafety (q : Query) : Prop :=
  match q.args with
  | [.scalar sv] => sv.bits.toNat ≠ 0
  | _ => False

def safetyPre (identity : String) (q : Query) : Prop :=
  if identity = makeNonZeroIdentity then makeNonZeroSafety q else False

def specs : SpecsV2 := ⟨safetyPre, fun _ => True⟩

end Spec
";

    const NONZERO_PROOF: &str = "\
prelude
import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro hEq; subst hEq; rw [Nat.beq_refl] at h; cases h

private theorem beq_zero_false_of_ne {n : Nat} (h : n ≠ 0) : Nat.beq n 0 = false := by
  cases hB : Nat.beq n 0 with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hB))

private theorem readPlaceV2_copy_local {bodyLocals : List MirTy} {locals : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true) :
    readPlaceV2 bodyLocals locals mem false ⟨lid, []⟩ =
      .ok (ty, optVal, locals, mem) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [hSup]
  rw [ite_bool_false (b := !true) rfl]
  rfl

private theorem readPlaceV2_move_local {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState}
    {lid : LocalId} {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) = some locals') :
    readPlaceV2 bodyLocals locals mem true ⟨lid, []⟩ =
      .ok (ty, optVal, locals', mem) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [hSup]
  rw [ite_bool_false (b := !true) rfl]
  change (if true = true then match setElem? locals lid (liveUninitSlot ty) with
    | some locals1 => Except.ok (ty, optVal, locals1, mem)
    | none => Except.error FaultKind.unsupported else _) = _
  rw [hSet]
  rfl

private theorem writePlaceV2_immediate_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) = some locals') :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val = .ok (locals', mem) := by
  unfold writePlaceV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]

private theorem evalRvalueV2_use_copy_ok {bodyLocals : List MirTy} {locals : List LocalSlot}
    {mem : MemoryState} {dstTy : MirTy} {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some dstTy)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy dstTy = true)
    (hEq : MirTy.beq dstTy dstTy = true) :
    evalRvalueV2 bodyLocals locals mem dstTy (.use (.copy ⟨lid, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [hEq]
  rfl

private theorem evalTerminatorV2_return_scalar_ok {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : MemoryState} {callerMem : CallerMemory}
    {retTy : MirTy} {retVal : Val}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalTerminatorV2 body bb frame mem callerMem =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]

private theorem initStateV2_ok_of {p : Program} {q : Query} {body : Body}
    (hPW : Nat.beq p.pointerWidthBits 64 = true)
    (hPV : Nat.beq p.mirProfileVersion 2 = true)
    (hCM : validCallerMemory q.callerMem = true)
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hNonEmpty : body.basicBlocks.isEmpty = false)
    (hArgLt : Nat.blt body.argumentCount body.locals.length = true)
    (hSto : storageAnnotationsInBounds body = true)
    (hDiscr : discriminantTypesValid body = true)
    (hCast : castTypesValid body = true)
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hArgs : checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0, initLocalsLoop body q.args 0 body.locals⟩],
      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  unfold initStateV2
  rw [hPW, hPV, hCM, hEntry]
  dsimp only
  rw [hNonEmpty, hArgLt, hSto, hDiscr, hCast, hLocs]
  rw [hArgs, hRefs, hDisj]
  rfl

private theorem execCoreCallOp_nonZeroGet_isize_ok {m : MemoryState} {sv : ScalarVal}
    (hWf : sv.wf = true) (hW : sv.width = .isize) (hS : sv.signed = false)
    (hNz : sv.bits.toNat ≠ 0) :
    execCoreCallOp m .nonZeroGet [(.nonZero .isize false, .nonZero sv)]
      (.int .isize false) = .ok (.scalar sv) := by
  unfold execCoreCallOp
  dsimp only
  have hBad : (!MirTy.beq (.int .isize false) (.int .isize false) || !sv.wf ||
      !IntWidth.beq sv.width .isize || !(sv.signed == false)) = false := by
    rw [hWf, hW, hS]; rfl
  rw [ite_bool_false hBad]
  rw [ite_bool_false (beq_zero_false_of_ne hNz)]

private theorem execCoreCallOp_nonZeroNewUnchecked_isize_ok {m : MemoryState} {sv : ScalarVal}
    (hWf : sv.wf = true) (hW : sv.width = .isize) (hS : sv.signed = false)
    (hNz : sv.bits.toNat ≠ 0) :
    execCoreCallOp m .nonZeroNewUnchecked [(.int .isize false, .scalar sv)]
      (.nonZero .isize false) = .ok (.nonZero sv) := by
  unfold execCoreCallOp
  dsimp only
  have hBad : (!MirTy.beq (.nonZero .isize false) (.nonZero .isize false) || !sv.wf ||
      !IntWidth.beq sv.width .isize || !(sv.signed == false)) = false := by
    rw [hWf, hW, hS]; rfl
  rw [ite_bool_false hBad]
  rw [ite_bool_false (beq_zero_false_of_ne hNz)]

private theorem checkValV2_isize_inv {v : Val}
    (h : checkValV2 v (.int .isize false) = true) :
    ∃ sv : ScalarVal,
      v = .scalar sv ∧ sv.wf = true ∧ sv.width = .isize ∧ sv.signed = false := by
  cases v with
  | scalar sv =>
    have hCV : checkVal (.scalar sv) (.int .isize false) = true := h
    let ⟨bits, hEq, hTrunc⟩ := checkVal_int_iff.mp hCV
    have hWf : ScalarVal.wf ⟨.isize, false, bits⟩ = true := by
      unfold ScalarVal.wf
      dsimp only
      rw [hTrunc]
      exact beq_self_eq_true bits
    cases hEq
    exact ⟨⟨.isize, false, bits⟩, rfl, hWf, rfl, rfl⟩
  | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | nonZero _ | bool _ | char _
  | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ => cases h

private theorem checkValV2_nonZero_isize_inv {v : Val}
    (h : checkValV2 v (.nonZero .isize false) = true) :
    ∃ sv : ScalarVal,
      v = .nonZero sv ∧ sv.wf = true ∧ sv.width = .isize ∧ sv.signed = false ∧
      sv.bits.toNat ≠ 0 := by
  cases v with
  | nonZero sv =>
    unfold checkValV2 at h
    cases hWf : sv.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [hWf] at h
      cases hW : IntWidth.beq sv.width .isize with
      | false => rw [hW] at h; cases h
      | true =>
        rw [hW] at h
        cases hS : (sv.signed == false) with
        | false => rw [hS] at h; cases h
        | true =>
          rw [hS] at h
          cases hNz : Nat.beq sv.bits.toNat 0 with
          | true => rw [hNz] at h; cases h
          | false =>
            exact ⟨sv, rfl, hWf, IntWidth.beq_iff.mp hW, eq_of_beq hS, ne_of_beq_false hNz⟩
  | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _ | char _
  | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ => cases h

private theorem args_one_nonZero_inv {args : List Val}
    (h : checkArgsMatchV2 args [.nonZero .isize false] = true) :
    ∃ sv : ScalarVal,
      args = [.nonZero sv] ∧ sv.wf = true ∧ sv.width = .isize ∧ sv.signed = false ∧
      sv.bits.toNat ≠ 0 := by
  cases args with
  | nil => cases h
  | cons v rest =>
    cases rest with
    | cons _ _ =>
      dsimp only [checkArgsMatchV2] at h
      cases hV : checkValV2 v (.nonZero .isize false) <;> rw [hV] at h <;> cases h
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV : checkValV2 v (.nonZero .isize false) with
      | false => rw [hV] at h; cases h
      | true =>
        let ⟨sv, hEq, hWf, hW, hS, hNz⟩ := checkValV2_nonZero_isize_inv hV
        exact ⟨sv, by rw [hEq], hWf, hW, hS, hNz⟩

private theorem args_one_isize_inv {args : List Val}
    (h : checkArgsMatchV2 args [.int .isize false] = true) :
    ∃ sv : ScalarVal,
      args = [.scalar sv] ∧ sv.wf = true ∧ sv.width = .isize ∧ sv.signed = false := by
  cases args with
  | nil => cases h
  | cons v rest =>
    cases rest with
    | cons _ _ =>
      dsimp only [checkArgsMatchV2] at h
      cases hV : checkValV2 v (.int .isize false) <;> rw [hV] at h <;> cases h
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV : checkValV2 v (.int .isize false) with
      | false => rw [hV] at h; cases h
      | true =>
        let ⟨sv, hEq, hWf, hW, hS⟩ := checkValV2_isize_inv hV
        exact ⟨sv, by rw [hEq], hWf, hW, hS⟩

private theorem execOutcomeStateV2_step {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : execOutcomeStateV2 p onDone onFault fuel s') :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hNext

private theorem execOutcomeStateV2_done {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out) (hDone : onDone out) :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hDone

private def execV2 (p : Program) (post : TerminalOut → Prop)
    (fuel : Nat) (s : State) : Prop :=
  execOutcomeStateV2 p post (fun _ => False) fuel s

private theorem execV2_step {p : Program} {post : TerminalOut → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : execV2 p post fuel s') :
    execV2 p post (fuel + 1) s :=
  execOutcomeStateV2_step hStep hNext

private theorem execV2_done {p : Program} {post : TerminalOut → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out) (hDone : post out) :
    execV2 p post (fuel + 1) s :=
  execOutcomeStateV2_done hStep hDone

private theorem execV2_to_execProgV2 {p : Program} {q : Query}
    {fuel : Nat} {s₀ : State} {post : TerminalOut → Prop}
    (hInit : initStateV2 p q = .ok s₀)
    (hExec : execV2 p post fuel s₀) :
    execProgV2 p fuel q post := by
  unfold execProgV2
  rw [hInit]
  exact hExec

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, trivial⟩
  intro id b hb
  cases id with
  | zero =>
    change some Captured.body_0 = some b at hb
    cases hb
    refine ⟨rfl, by decide, fun q hValid _ => ?_⟩
    let ⟨sv, hArgs, hWf, hW, hS, hNz⟩ := args_one_nonZero_inv hValid.2.1
    have hZ := beq_zero_false_of_ne hNz
    have hInit : initStateV2 (entryProgForBody Captured.program 0) q =
        .ok ⟨[⟨0, 0, 0, [.immediate none, .immediate (some (.nonZero sv)), .dead]⟩],
          q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
      have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 0)
        (q := q) (body := Captured.body_0)
        rfl rfl hValid.1 rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hValid.2.1 hValid.2.2.1 hValid.2.2.2
      rw [h0, hArgs]; rfl
    let expectedOut : TerminalOut :=
      .returned ⟨.scalar sv, extractCallerMemory q.callerMem (entryMemoryWithCaller q.callerMem)⟩
    have hExec : execProgV2 (entryProgForBody Captured.program 0) 6 q
        (fun o => o = expectedOut) := by
      apply execV2_to_execProgV2 hInit
      apply execV2_step (by rfl)
      apply execV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, placeStaticTyV2, Trusted.MirSemantics.getElem?]
        rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [writePlaceV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hWf, hW, hS, hZ]; rfl)
          (by rfl) (by rfl)])
      apply execV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalArgOperandsV2, evalOperandToSlotV2,
          Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [execCoreCallOp_nonZeroGet_isize_ok hWf hW hS hNz]
        dsimp only
        rw [writePlaceV2_immediate_ok
          (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hWf, hW, hS]; rfl)
          (by rfl) (by rfl)]
        rfl)
      apply execV2_step (by rfl)
      apply execV2_done (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          Trusted.MirSemantics.getElem?]
        rw [ite_bool_true (b := Nat.beq (0 + 1) [StatementKind.storageDead 2].length) rfl]
        rw [evalTerminatorV2_return_scalar_ok (by rfl) (by rfl) (by rfl) (by rfl)
          (by rfl) (by rfl) (by rfl)])
      rfl
    exact (spec_and_behaviorV2_of_exec_eq hExec).1
  | succ d =>
    cases d with
    | zero =>
      change some Captured.body_1 = some b at hb
      cases hb
      refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
      let ⟨sv, hArgs, hWf, hW, hS⟩ := args_one_isize_inv hValid.2.1
      have hSafe1 : sv.bits.toNat ≠ 0 := by
        have hId1 : Captured.body_1.identity = Spec.makeNonZeroIdentity := by decide
        have hS0 := hSafe (by decide)
        change Spec.safetyPre Captured.body_1.identity q at hS0
        unfold Spec.safetyPre at hS0
        rw [hId1, ite_prop_true (rfl : Spec.makeNonZeroIdentity = Spec.makeNonZeroIdentity)] at hS0
        dsimp only [Spec.makeNonZeroSafety] at hS0
        rw [hArgs] at hS0
        exact hS0
      have hZ := beq_zero_false_of_ne hSafe1
      have hInit : initStateV2 (entryProgForBody Captured.program 1) q =
          .ok ⟨[⟨1, 0, 0, [.immediate none, .immediate (some (.scalar sv)), .dead]⟩],
            q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
        have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 1)
          (q := q) (body := Captured.body_1)
          rfl rfl hValid.1 rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          hValid.2.1 hValid.2.2.1 hValid.2.2.2
        rw [h0, hArgs]; rfl
      let expectedOut : TerminalOut :=
        .returned ⟨.nonZero sv, extractCallerMemory q.callerMem (entryMemoryWithCaller q.callerMem)⟩
      have hExec : execProgV2 (entryProgForBody Captured.program 1) 6 q
          (fun o => o = expectedOut) := by
        apply execV2_to_execProgV2 hInit
        apply execV2_step (by rfl)
        apply execV2_step (by
          dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
            evalStatementV2, placeStaticTyV2, Trusted.MirSemantics.getElem?]
          rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl) (by rfl)]
          dsimp only
          rw [writePlaceV2_immediate_ok
            (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hWf, hW, hS]; rfl)
            (by rfl) (by rfl)])
        apply execV2_step (by
          dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
            evalTerminatorV2, evalArgOperandsV2, evalOperandToSlotV2,
            Trusted.MirSemantics.getElem?]
          rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
          dsimp only
          rw [execCoreCallOp_nonZeroNewUnchecked_isize_ok hWf hW hS hSafe1]
          dsimp only
          rw [writePlaceV2_immediate_ok
            (by dsimp only [checkValV2]; rw [hWf, hW, hS, hZ]; rfl)
            (by rfl) (by rfl)]
          rfl)
        apply execV2_step (by rfl)
        apply execV2_done (by
          dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
            Trusted.MirSemantics.getElem?]
          rw [ite_bool_true (b := Nat.beq (0 + 1) [StatementKind.storageDead 2].length) rfl]
          rw [evalTerminatorV2_return_scalar_ok (by rfl) (by rfl) (by rfl) (by rfl)
            (by rfl) (by rfl) (by rfl)])
        rfl
      exact (spec_and_behaviorV2_of_exec_eq hExec).1
    | succ _ =>
      change none = some b at hb
      cases hb

end Proof
";

    fs::write(lean_dir.join("Spec.lean"), NONZERO_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), NONZERO_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "nonzero_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let ok = run_request(&tools, dir.path(), "nonzero-ok", &request);
    ok.expect_ok("crate_verified");
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-nonzero-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");

    // Negative: weaken `makeNonZeroSafety` to omit `sv.bits.toNat ≠ 0`.
    let missing_nonzero = NONZERO_SPEC.replace("sv.bits.toNat ≠ 0", "True");
    assert_ne!(missing_nonzero, NONZERO_SPEC);
    fs::write(lean_dir.join("Spec.lean"), missing_nonzero).unwrap();
    run_request(&tools, dir.path(), "nonzero-missing-pre", &request).expect_proof_failed();
}
