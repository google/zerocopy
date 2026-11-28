// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--panic abort` `div_ceil`, rejected under `--panic unwind`.

use super::*;

/// Verifies safe `safe_div_ceil` and `write_then_div` under `--panic abort`
/// (`SafeContractV2` covering both `{ allowAbort := true }` abort on `b = 0`—
/// including pre-abort `&mut` mutation visibility in `postAbort`—and
/// `noAbort` when `b != 0`), and confirms `--panic unwind`, omitted panic
/// strategy (defaulting to unwind), and weakened `EffectMaskV2.noAbort`
/// preconditions fail closed.
#[test]
fn verifies_panic_abort_div_ceil_and_rejects_panic_unwind() {
    let tools = tools();
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), PANIC_ABORT_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), PANIC_ABORT_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), PANIC_ABORT_PROOF).unwrap();

    let base_request = |panic: Option<&str>| {
        let mut compilation = json!({
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "panic_abort_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        });
        if let Some(strategy) = panic {
            compilation["panic"] = json!(strategy);
        }
        json!({
            "schema_version": 1,
            "compilation": compilation,
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
        })
    };

    let abort_request = base_request(Some("abort"));
    let ok = run_request(dir.path(), "panic-abort-ok", &abort_request);
    ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(abort_verified) = &ok.receipt else {
        panic!("expected verified receipt, got {:?}", ok.receipt);
    };
    let abort_assumptions: Vec<&str> =
        abort_verified.assumptions.iter().map(String::as_str).collect();
    assert!(
        abort_assumptions.iter().any(|a| {
            a.starts_with(
                "--panic abort models failed non-optional safe assertions \
                 and admitted core::panicking calls as .aborted",
            )
                && a.contains("panic hooks and handlers")
                && a.contains("caller-memory effects before the panic")
                && !a.contains("overflow")
        }),
        "expected explicit --panic abort receipt assumption, got {abort_assumptions:?}"
    );
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-panic-abort-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert_eq!(capture_json["program"]["panic"], "abort", "{capture_json}");
    assert_eq!(capture_json["program"]["has_local_panic_handler"], false, "{capture_json}");

    // Negative 1: explicit `--panic unwind` fails closed on aborting paths.
    run_request(dir.path(), "panic-unwind-rejected", &base_request(Some("unwind")))
        .expect_proof_failed();

    // Negative 2: omitted panic strategy defaults to unwind and fails closed.
    run_request(dir.path(), "panic-default-rejected", &base_request(None))
        .expect_proof_failed();

    // Negative 3: weakening `divCeilNoAbort` `behaviorPre` under `noAbort`
    // fails closed even under `--panic abort`.
    let weak_spec = PANIC_ABORT_SPEC.replace("b.bits.toNat ≠ 0", "True");
    assert_ne!(weak_spec, PANIC_ABORT_SPEC);
    fs::write(lean_dir.join("Spec.lean"), weak_spec).unwrap();
    run_request(dir.path(), "panic-abort-weak-no-abort", &abort_request)
        .expect_proof_failed();

    // Negative 4: asserting entry `q.callerMem` instead of post-mutation
    // `extractCallerMemory q.callerMem mem'` in `writeThenDivSlotPost` fails
    // closed because `*slot = a` mutates caller memory before aborting.
    let stale_mem_spec = PANIC_ABORT_SPEC.replace(
        "cm = extractCallerMemory q.callerMem mem'",
        "cm = q.callerMem",
    );
    assert_ne!(stale_mem_spec, PANIC_ABORT_SPEC);
    fs::write(lean_dir.join("Spec.lean"), stale_mem_spec).unwrap();
    run_request(dir.path(), "panic-abort-stale-preabort-mem", &abort_request)
        .expect_proof_failed();

    // Check 5: optional overflow checks (`-Coverflow-checks=yes`) under
    // `--panic abort` abort cleanly like the other safe panics, because
    // `evalAssertFailure` models them as runtime panics when
    // `Program.overflowChecks` is set.
    //
    // First confirm stable `a + b` under `--panic abort --overflow-checks`
    // captures with `overflowChecks := true` and an
    // `AssertKind.overflow BinOp.add` terminator.
    let overflow_add_dir = dir.path().join("overflow-add");
    fs::create_dir_all(&overflow_add_dir).unwrap();
    let overflow_add_src = overflow_add_dir.join("lib.rs");
    fs::write(
        &overflow_add_src,
        "pub fn f(a: u8, b: u8) -> u8 {\n\
             a + b\n\
         }\n",
    )
    .unwrap();
    let overflow_add_out = dir.path().join("overflow-add-capture");
    let add_cap_out = Command::new(tools.capture.as_deref().expect("capture bin"))
        .args([
            "capture",
            "--crate-root",
            overflow_add_src.to_str().unwrap(),
            "--crate-name",
            "overflow_add_demo",
            "--crate-type",
            "lib",
            "--edition",
            "2021",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--panic",
            "abort",
            "--overflow-checks",
            "--scope",
            "crate",
            "--out-dir",
            overflow_add_out.to_str().unwrap(),
            "--sysroot",
            tools.sysroot.to_str().unwrap(),
            "--source-file",
            overflow_add_src.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        add_cap_out.status.success(),
        "overflow-add capture failed: {}",
        String::from_utf8_lossy(&add_cap_out.stdout)
    );
    let overflow_add_lean = fs::read_to_string(overflow_add_out.join("Captured.lean")).unwrap();
    assert!(
        overflow_add_lean.contains("overflowChecks := true")
            && overflow_add_lean
                .contains("Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.add"),
        "{overflow_add_lean}"
    );

    // Next kernel-check via `cargo-anneal verify` on real captured
    // `-Coverflow-checks=yes` bodies whose assert condition is a bare scalar
    // (`-a` -> `AssertKind.overflowNeg`, `a << b` ->
    // `AssertKind.overflow BinOp.shl`) that overflowing inputs reach
    // `.done (.aborted _)`. Both proofs fail to typecheck if optional overflow
    // asserts fault under `--panic abort --overflow-checks`.
    let overflow_rust_dir = dir.path().join("overflow-rust");
    let overflow_lean_dir = dir.path().join("overflow-lean");
    fs::create_dir_all(&overflow_rust_dir).unwrap();
    fs::create_dir_all(&overflow_lean_dir).unwrap();
    fs::write(
        overflow_rust_dir.join("lib.rs"),
        "pub unsafe fn f_neg(a: i8) -> i8 {\n\
             -a\n\
         }\n\
         pub unsafe fn f_shl(a: u8, b: u32) -> u8 {\n\
             a << b\n\
         }\n",
    )
    .unwrap();
    fs::write(
        overflow_lean_dir.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def qNegOverflow : Query :=
  { args := [.scalar ⟨.i8, true, BitVec.ofNat 128 128⟩] }

def qShlOverflow : Query :=
  { args := [
      .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
      .scalar ⟨.i32, false, BitVec.ofNat 128 8⟩] }

def safety (id : String) (q : Query) : Prop :=
  (id = "rust-path-v1::f_neg" ∧
    q.args = [.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩]) ∨
  (id = "rust-path-v1::f_shl" ∧
    q.args = [
      .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
      .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩])

def property (p : Program) : Prop :=
  (∃ cm, ReachesResultV2 (entryProgForBody p 0) qNegOverflow
    (.done (.aborted cm))) ∧
  (∃ cm, ReachesResultV2 (entryProgForBody p 1) qShlOverflow
    (.done (.aborted cm)))

def specs : SpecsV2 := ⟨safety, property⟩

end Spec
"#,
    )
    .unwrap();
    fs::write(
        overflow_lean_dir.join("Proof.lean"),
        r#"prelude
import Init.NotationExtra
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics

private theorem ite_bool_false {α : Type u} {b : Bool} {t e : α}
    (h : b = false) : (if b = true then t else e) = e := by
  rw [h]; rfl

private def mkS (defId bb st : Nat) (locs : List LocalSlot)
    (cm : CallerMemory) (mem : MemoryState) : State :=
  ⟨[⟨defId, bb, st, locs, none, none, none⟩], cm, mem⟩

private inductive DetTerminates (p : Program) : State → Prop where
  | done {s : State} {out : TerminalOut} :
      evalStepV2Choice p 0 s = .done out → DetTerminates p s
  | step {s s' : State} :
      evalStepV2Choice p 0 s = .step s' →
      DetTerminates p s' →
      DetTerminates p s

private theorem det_step_eq {p : Program} {s : State}
    {r₁ r₂ : StepResult State TerminalOut}
    (h₁ : StepV2 p s r₁) (h₂ : evalStepV2Choice p 0 s = r₂) :
    r₁ = r₂ := by
  let ⟨c, hc, heq⟩ := h₁
  have hc0 : c = 0 := hc
  rw [hc0] at heq
  rw [← heq, h₂]

private theorem detTerminates_reaches {p : Program} {s₀ s : State}
    (hR : ReachesV2 p s₀ s) (hT : DetTerminates p s₀) :
    DetTerminates p s := by
  induction hR with
  | refl => exact hT
  | tail _ hStep ih =>
    cases ih with
    | done hD => cases det_step_eq hStep hD
    | step hS hNext =>
      cases det_step_eq hStep hS
      exact hNext

private theorem wf_of_detTerminates {p : Program} {q : Query}
    {s₀ : State} (hInit : initStateV2 p q = .ok s₀)
    (hT : DetTerminates p s₀) : WellFormedV2 p q := by
  refine ⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, fun k hFault => ?_⟩
  unfold ReachesResultV2 at hFault
  rw [hInit] at hFault
  let ⟨s, hR, hSt⟩ := hFault
  cases detTerminates_reaches hR hT with
  | done hD => cases det_step_eq hSt hD
  | step hS _ => cases det_step_eq hSt hS

private theorem body0_steps (cm : CallerMemory) (mem : MemoryState) :
    DetTerminates (entryProgForBody Captured.program 0)
      (mkS 0 0 0
        [.immediate none,
         .immediate (some (.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩)),
         .dead, .immediate none] cm mem) := by
  let v1 : Val := .scalar ⟨.i8, true, BitVec.ofNat 128 1⟩
  let vm1 : Val := .scalar ⟨.i8, true, BitVec.ofNat 128 255⟩
  refine .step (s' := mkS 0 0 1 [.immediate none, .immediate (some v1), .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 2 [.immediate none, .immediate (some v1), .immediate (some v1), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 3 [.immediate none, .immediate (some v1), .immediate (some v1), .immediate (some (.bool false))] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 0 [.immediate none, .immediate (some v1), .immediate (some v1), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 1 [.immediate (some vm1), .immediate (some v1), .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 2 [.immediate (some vm1), .immediate (some v1), .dead, .immediate none] cm mem) rfl ?_
  exact .done rfl

private theorem body0_wf (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hSafe : q.args = [.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩]) :
    WellFormedV2 (entryProgForBody Captured.program 0) q := by
  cases q with
  | mk args cm =>
    dsimp only at hSafe
    subst hSafe
    let ⟨hMem, _, _, _⟩ := hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩], cm⟩ =
        .ok (mkS 0 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i8, true, BitVec.ofNat 128 1⟩)),
           .dead, .immediate none] cm (entryMemoryWithCaller cm)) := by
      unfold initStateV2 entryProgForBody Captured.program
        Trusted.MirSemantics.getElem?
      dsimp only
      have h1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
      have h2 : (!(true : Bool)) = false := rfl
      rw [ite_bool_false h1, hMem, ite_bool_false h2]
      rfl
    exact wf_of_detTerminates hInit (body0_steps cm (entryMemoryWithCaller cm))

private theorem body1_steps (cm : CallerMemory) (mem : MemoryState) :
    DetTerminates (entryProgForBody Captured.program 1)
      (mkS 1 0 0
        [.immediate none,
         .immediate (some (.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩)),
         .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 2⟩)),
         .dead, .dead, .immediate none] cm mem) := by
  let va : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩
  let vb : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩
  let vr : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 4⟩
  refine .step (s' := mkS 1 0 1 [.immediate none, .immediate (some va), .immediate (some vb), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 2 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 3 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 4 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 0 5 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate (some (.bool true))] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 0 [.immediate none, .immediate (some va), .immediate (some vb), .immediate (some va), .immediate (some vb), .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 1 [.immediate (some vr), .immediate (some va), .immediate (some vb), .immediate none, .immediate none, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 2 [.immediate (some vr), .immediate (some va), .immediate (some vb), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 1 1 3 [.immediate (some vr), .immediate (some va), .immediate (some vb), .dead, .dead, .immediate none] cm mem) rfl ?_
  exact .done rfl

private theorem body1_wf (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q)
    (hSafe : q.args = [
      .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
      .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩]) :
    WellFormedV2 (entryProgForBody Captured.program 1) q := by
  cases q with
  | mk args cm =>
    dsimp only at hSafe
    subst hSafe
    let ⟨hMem, _, _, _⟩ := hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 1)
          ⟨[.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
            .scalar ⟨.i32, false, BitVec.ofNat 128 2⟩], cm⟩ =
        .ok (mkS 1 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩)),
           .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 2⟩)),
           .dead, .dead, .immediate none] cm (entryMemoryWithCaller cm)) := by
      unfold initStateV2 entryProgForBody Captured.program
        Trusted.MirSemantics.getElem?
      dsimp only
      have h1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
      have h2 : (!(true : Bool)) = false := rfl
      rw [ite_bool_false h1, hMem, ite_bool_false h2]
      rfl
    exact wf_of_detTerminates hInit (body1_steps cm (entryMemoryWithCaller cm))

private theorem neg_overflow_aborts :
    ∃ cm, ReachesResultV2 (entryProgForBody Captured.program 0)
      Spec.qNegOverflow (.done (.aborted cm)) :=
  ⟨_, _, .tail (.tail (.tail (.refl _) ⟨0, rfl, rfl⟩)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩, ⟨0, rfl, rfl⟩⟩

private theorem shl_overflow_aborts :
    ∃ cm, ReachesResultV2 (entryProgForBody Captured.program 1)
      Spec.qShlOverflow (.done (.aborted cm)) :=
  ⟨_, _, .tail (.tail (.tail (.tail (.tail (.refl _)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩, ⟨0, rfl, rfl⟩⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
      cases hSafe rfl with
      | inl h => exact body0_wf q hValid h.2
      | inr h =>
        exact False.elim
          ((by decide : Captured.body_0.identity ≠ "rust-path-v1::f_shl") h.1)
    | succ n =>
      cases n with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        refine ⟨rfl, by decide, fun q hValid hSafe => ?_⟩
        cases hSafe rfl with
        | inl h =>
          exact False.elim
            ((by decide : Captured.body_1.identity ≠ "rust-path-v1::f_neg") h.1)
        | inr h => exact body1_wf q hValid h.2
      | succ _ =>
        change none = some body at hBody
        cases hBody
  · exact ⟨neg_overflow_aborts, shl_overflow_aborts⟩

end Proof
"#,
    )
    .unwrap();
    let overflow_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": overflow_rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "optional_overflow_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "overflow_checks": true,
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": overflow_lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let overflow_ok = run_request(
        dir.path(),
        "panic-abort-optional-overflow",
        &overflow_request,
    );
    overflow_ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(overflow_verified) = &overflow_ok.receipt else {
        panic!("expected verified receipt, got {:?}", overflow_ok.receipt);
    };
    assert!(overflow_verified.spec_warnings.is_empty(), "{overflow_verified:?}");
    let overflow_assumptions: Vec<&str> =
        overflow_verified.assumptions.iter().map(String::as_str).collect();
    assert!(
        overflow_assumptions.iter().any(|a| {
            a.starts_with(
                "--panic abort models failed non-optional safe assertions, admitted \
                 core::panicking calls, and, under --overflow-checks, failed overflow \
                 checks as .aborted",
            ) && a.contains("panic hooks and handlers")
                && a.contains("a build that elides the overflow checks wraps")
        }),
        "expected --panic abort --overflow-checks receipt assumption, got \
         {overflow_assumptions:?}"
    );
    let overflow_captured = fs::read_to_string(
        dir.path().join("artifacts-panic-abort-optional-overflow/capture/Captured.lean"),
    )
    .unwrap();
    assert!(
        overflow_captured.contains("overflowChecks := true"),
        "{overflow_captured}"
    );
    assert!(
        overflow_captured.contains("Trusted.MirAst.AssertKind.overflowNeg"),
        "{overflow_captured}"
    );
    assert!(
        overflow_captured
            .contains("Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.shl"),
        "{overflow_captured}"
    );

    // Check 6: a `#![no_std]` binary with a crate-local `#[panic_handler]`
    // compiled with `--panic abort` keeps failing safe `Assert`s fail-closed
    // as `.fault .unsupported` (and omits the default-runtime `.aborted`
    // receipt assumption).
    let local_handler_rust = dir.path().join("local-handler-rust");
    let local_handler_lean = dir.path().join("local-handler-lean");
    fs::create_dir_all(&local_handler_rust).unwrap();
    fs::create_dir_all(&local_handler_lean).unwrap();
    fs::write(
        local_handler_rust.join("main.rs"),
        "#![no_std]\n\
         #![no_main]\n\
         use core::panic::PanicInfo;\n\
         #[panic_handler]\n\
         fn panic(_info: &PanicInfo<'_>) -> ! {\n\
             loop {}\n\
         }\n\
         pub unsafe fn div_u64(a: u64, b: u64, _tag: (u8, u8, u8)) -> u64 {\n\
             a / b\n\
         }\n",
    )
    .unwrap();
    fs::write(
        local_handler_lean.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def vTag : Val :=
  .tuple [
    .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩,
    .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩,
    .scalar ⟨.i8, false, BitVec.ofNat 128 0⟩]

def qDivZero : Query :=
  { args := [
      .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
      .scalar ⟨.i64, false, BitVec.ofNat 128 0⟩,
      vTag] }

def safety (_id : String) (q : Query) : Prop :=
  q.args = [
    .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
    .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩,
    vTag]

def property (p : Program) : Prop :=
  ReachesResultV2 (entryProgForBody p 0) qDivZero (.fault .unsupported) ∧
  ¬ WellFormedV2 (entryProgForBody p 0) qDivZero

def specs : SpecsV2 := {
  safety := safety
  property := property
}

end Spec
"#,
    )
    .unwrap();
    fs::write(
        local_handler_lean.join("Proof.lean"),
        r#"prelude
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics

private theorem ite_bool_false {α : Type u} {b : Bool} {t e : α}
    (h : b = false) : (if b = true then t else e) = e := by
  rw [h]; rfl

private def mkS (defId bb st : Nat) (locs : List LocalSlot)
    (cm : CallerMemory) (mem : MemoryState) : State :=
  ⟨[⟨defId, bb, st, locs, none, none, none⟩], cm, mem⟩

private inductive DetTerminates (p : Program) : State → Prop where
  | done {s : State} {out : TerminalOut} :
      evalStepV2Choice p 0 s = .done out → DetTerminates p s
  | step {s s' : State} :
      evalStepV2Choice p 0 s = .step s' →
      DetTerminates p s' →
      DetTerminates p s

private theorem det_step_eq {p : Program} {s : State}
    {r₁ r₂ : StepResult State TerminalOut}
    (h₁ : StepV2 p s r₁) (h₂ : evalStepV2Choice p 0 s = r₂) :
    r₁ = r₂ := by
  let ⟨c, hc, heq⟩ := h₁
  have hc0 : c = 0 := hc
  rw [hc0] at heq
  rw [← heq, h₂]

private theorem detTerminates_reaches {p : Program} {s₀ s : State}
    (hR : ReachesV2 p s₀ s) (hT : DetTerminates p s₀) :
    DetTerminates p s := by
  induction hR with
  | refl => exact hT
  | tail _ hStep ih =>
    cases ih with
    | done hD => cases det_step_eq hStep hD
    | step hS hNext =>
      cases det_step_eq hStep hS
      exact hNext

private theorem wf_of_detTerminates {p : Program} {q : Query}
    {s₀ : State} (hInit : initStateV2 p q = .ok s₀)
    (hT : DetTerminates p s₀) : WellFormedV2 p q := by
  refine ⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, fun k hFault => ?_⟩
  unfold ReachesResultV2 at hFault
  rw [hInit] at hFault
  let ⟨s, hR, hSt⟩ := hFault
  cases detTerminates_reaches hR hT with
  | done hD => cases det_step_eq hSt hD
  | step hS _ => cases det_step_eq hSt hS

private theorem div_steps (cm : CallerMemory) (mem : MemoryState) :
    DetTerminates (entryProgForBody Captured.program 0)
      (mkS 0 0 0
        [.immediate none,
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩)),
         .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩)),
         .immediate (some Spec.vTag),
         .dead, .dead, .immediate none] cm mem) := by
  let va : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩
  let vb : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩
  let vt : Val := Spec.vTag
  refine .step (s' := mkS 0 0 1
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 2
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 3
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate none,
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 4
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate (some vb),
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 0 5
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate (some vb),
     .immediate (some (.bool false))] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 0
    [.immediate none, .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate (some va), .immediate (some vb),
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 1
    [.immediate (some va), .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate none, .immediate none,
     .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 2
    [.immediate (some va), .immediate (some va), .immediate (some vb),
     .immediate (some vt), .immediate none, .dead, .immediate none] cm mem) rfl ?_
  refine .step (s' := mkS 0 1 3
    [.immediate (some va), .immediate (some va), .immediate (some vb),
     .immediate (some vt), .dead, .dead, .immediate none] cm mem) rfl ?_
  exact .done rfl

private theorem div_ok_wf (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hArgs : q.args = [
      .scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
      .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩,
      Spec.vTag]) :
    WellFormedV2 (entryProgForBody Captured.program 0) q := by
  cases q with
  | mk args cm =>
    dsimp only at hArgs
    subst hArgs
    let ⟨hMem, _, _, _⟩ := hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩,
            .scalar ⟨.i64, false, BitVec.ofNat 128 1⟩,
            Spec.vTag], cm⟩ =
        .ok (mkS 0 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩)),
           .immediate (some (.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩)),
           .immediate (some Spec.vTag),
           .dead, .dead, .immediate none] cm (entryMemoryWithCaller cm)) := by
      unfold initStateV2 entryProgForBody Captured.program
        Trusted.MirSemantics.getElem?
      dsimp only
      have h1 : (!Nat.beq 64 64 || !Nat.beq 2 2) = false := rfl
      have h2 : (!(true : Bool)) = false := rfl
      rw [ite_bool_false h1, hMem, ite_bool_false h2]
      rfl
    exact wf_of_detTerminates hInit (div_steps cm (entryMemoryWithCaller cm))

private theorem div_zero_unsupported :
    ReachesResultV2 (entryProgForBody Captured.program 0) Spec.qDivZero
      (.fault .unsupported) :=
  ⟨_, .tail (.tail (.tail (.tail (.tail (.refl _) ⟨0, rfl, rfl⟩)
    ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩,
    ⟨0, rfl, rfl⟩⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid hSafe => div_ok_wf q hValid (hSafe rfl)⟩
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · exact ⟨div_zero_unsupported,
      fun hWf => hWf.2 .unsupported div_zero_unsupported⟩

end Proof
"#,
    )
    .unwrap();
    let local_handler_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": local_handler_rust.to_str().unwrap(),
            "crate_root": "main.rs",
            "crate_name": "local_handler_demo",
            "crate_type": "bin",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "cfg": [],
            "source_files": ["main.rs"]
        },
        "scope": {"kind": "selected_unit", "roots": ["div_u64"]},
        "proof": {
            "source_root": local_handler_lean.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let lh_ok = run_request(
        dir.path(),
        "panic-abort-local-handler",
        &local_handler_request,
    );
    lh_ok.expect_ok("selected_unit_verified");
    let lh_capture: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-panic-abort-local-handler/capture/capture.json"))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(lh_capture["program"]["panic"], "abort", "{lh_capture}");
    assert_eq!(lh_capture["program"]["has_local_panic_handler"], true, "{lh_capture}");
    let VerifyReceipt::Verified(lh_verified) = &lh_ok.receipt else {
        panic!("expected verified receipt, got {:?}", lh_ok.receipt);
    };
    let lh_assumptions: Vec<&str> =
        lh_verified.assumptions.iter().map(String::as_str).collect();
    assert!(
        !lh_assumptions.iter().any(|a| a.contains("as .aborted")),
        "local #[panic_handler] receipt must not claim .aborted modeling: {lh_assumptions:?}"
    );
}
