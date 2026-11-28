// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `-Coverflow-checks=yes` captures, and arrays with unsound specs rejected.

use super::*;

/// Stages `fixtures/profile_v2_overflow` with the given specification and
/// proof, returning the request for `roots` captured under `panic`, with or
/// without `-Coverflow-checks=yes`. Both `buggy_add_u8` requests also capture
/// `zero_pair`, whose tuple keeps the program on Profile v2 when
/// `buggy_add_u8` has no `Assert`.
fn stage_overflow_case(
    spec: &str,
    proof: &str,
    roots: &[&str],
    panic: &str,
    overflow_checks: bool,
) -> (TempDir, Value) {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(rust_dir.join("lib.rs"), OVERFLOW_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), spec).unwrap();
    fs::write(lean_dir.join("Proof.lean"), proof).unwrap();
    fs::write(lean_dir.join("StepLemmas.lean"), OVERFLOW_STEPS).unwrap();
    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "overflow_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"],
            "panic": panic,
            "overflow_checks": overflow_checks
        },
        "scope": {"kind": "selected_unit", "roots": roots},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "StepLemmas", "path": "StepLemmas.lean", "role": "proof"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    (dir, request)
}

/// Reads the `capture.json` and `Captured.lean` that request `name` wrote.
fn captured_overflow_case(dir: &Path, name: &str) -> (Value, String) {
    let capture = dir.join(format!("artifacts-{name}/capture"));
    let capture_json: Value =
        serde_json::from_slice(&fs::read(capture.join("capture.json")).unwrap()).unwrap();
    let lean = fs::read_to_string(capture.join("Captured.lean")).unwrap();
    (capture_json, lean)
}

const OVERFLOW_ADD_ASSERT: &str = "AssertKind.overflow Trusted.MirAst.BinOp.add";
const WRAPPING_ROOTS: &[&str] = &["buggy_add_u8", "zero_pair"];

/// Verifies `guarded_add_u8` captured with `-Coverflow-checks=yes` under
/// `panic`: the saturating result and normal return with no divergence or
/// fault, so its `AddWithOverflow` `Assert` never fails.
fn verify_overflow_checked_guarded_add(panic: &str) {
    let name = format!("guarded-add-overflow-checks-{panic}");
    let (dir, request) =
        stage_overflow_case(GUARDED_SPEC, GUARDED_PROOF, &["guarded_add_u8"], panic, true);
    let ok = run_request(dir.path(), &name, &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let (capture_json, lean) = captured_overflow_case(dir.path(), &name);
    assert_eq!(capture_json["configuration"]["overflow_checks"], true, "{capture_json}");
    assert_eq!(capture_json["configuration"]["panic"], panic, "{capture_json}");
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert!(lean.contains("overflowChecks := true"), "{name}:\n{lean}");
    assert!(lean.contains(OVERFLOW_ADD_ASSERT), "{name}:\n{lean}");
}

#[test]
fn verifies_overflow_checked_guarded_add_under_panic_abort() {
    verify_overflow_checked_guarded_add("abort");
}

#[test]
fn verifies_overflow_checked_guarded_add_under_panic_unwind() {
    verify_overflow_checked_guarded_add("unwind");
}

/// Without overflow checks, `buggy_add_u8`'s `x + 1` is a wrapping `Add`, and
/// a proof that it returns `(x + 1) % 256` verifies.
#[test]
fn verifies_wrapping_add_without_overflow_checks() {
    let name = "wrapping-add-no-overflow-checks";
    let (dir, request) =
        stage_overflow_case(WRAPPING_SPEC, WRAPPING_PROOF, WRAPPING_ROOTS, "abort", false);
    let ok = run_request(dir.path(), name, &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let (capture_json, lean) = captured_overflow_case(dir.path(), name);
    assert_eq!(capture_json["configuration"]["overflow_checks"], false, "{capture_json}");
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert!(lean.contains("overflowChecks := false"), "{lean}");
    assert!(!lean.contains("AssertKind.overflow"), "{lean}");
}

/// With overflow checks, the same specification and proof are rejected,
/// because `x = 255` fails the overflow `Assert`.
#[test]
fn rejects_wrapping_add_proof_with_overflow_checks() {
    let name = "wrapping-add-overflow-checks";
    let (dir, request) =
        stage_overflow_case(WRAPPING_SPEC, WRAPPING_PROOF, WRAPPING_ROOTS, "abort", true);
    run_request(dir.path(), name, &request).expect_proof_failed();
    let (capture_json, lean) = captured_overflow_case(dir.path(), name);
    assert_eq!(capture_json["configuration"]["overflow_checks"], true, "{capture_json}");
    assert!(lean.contains(OVERFLOW_ADD_ASSERT), "{lean}");
}

/// Verifies fixed-size arrays `[T; N]`, `Repeat`, `ConstantIndex`, `Unsize`
/// (`&[u8; 3] -> &[u8]`), `.rodata` array constants, projected
/// `Rvalue::Discriminant` (`discriminant(*a)`), `int::to_le_bytes`, and
/// `<[u8; 4] as PartialEq>::eq` under `UnitTheoremV2` (`["propext"]`, zero
/// taint), plus four functional spec mismatch rejections and a capture-level
/// rejection for dynamic array indexing.
#[test]
fn verifies_profile_v2_arrays_and_rejects_unsound_specs() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), ARRAYS_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), ARRAYS_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ARRAYS_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "profile_v2_arrays",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {
            "kind": "selected_unit",
            "roots": [
                "pack_le_rev",
                "repeat_unsize_len",
                "tag_eq",
                "matches_pattern"
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

    let ok = run_request(dir.path(), "arrays-ok", &request);
    ok.expect_ok("selected_unit_verified");
    ok.expect_profile_v2_assumptions();
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-arrays-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");

    // Negative 1: wrong byte order in `pack_le_rev` spec.
    let bad_pack = ARRAYS_SPEC.replace(
        "⟨.array [.scalar ⟨.i8, false, hi⟩, .scalar ⟨.i8, false, lo⟩], q.callerMem⟩",
        "⟨.array [.scalar ⟨.i8, false, lo⟩, .scalar ⟨.i8, false, hi⟩], q.callerMem⟩",
    );
    assert_ne!(bad_pack, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_pack).unwrap();
    run_request(dir.path(), "arrays-wrong-le-order", &request).expect_proof_failed();

    // Negative 2: wrong slice length in `repeat_unsize_len` spec.
    let bad_len = ARRAYS_SPEC.replace(
        "⟨.scalar ⟨.isize, false, BitVec.ofNat 128 3⟩, q.callerMem⟩",
        "⟨.scalar ⟨.isize, false, BitVec.ofNat 128 4⟩, q.callerMem⟩",
    );
    assert_ne!(bad_len, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_len).unwrap();
    run_request(dir.path(), "arrays-wrong-repeat-len", &request).expect_proof_failed();

    // Negative 3: inverted boolean result in `tag_eq` spec.
    let bad_tag = ARRAYS_SPEC.replace(
        "⟨.bool (Nat.beq ba.toNat bb.toNat), q.callerMem⟩",
        "⟨.bool (!(Nat.beq ba.toNat bb.toNat)), q.callerMem⟩",
    );
    assert_ne!(bad_tag, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_tag).unwrap();
    run_request(dir.path(), "arrays-wrong-tag-eq", &request).expect_proof_failed();

    // Negative 4: wrong `.rodata` pattern byte in `matches_pattern` spec.
    let bad_pat = ARRAYS_SPEC.replace(
        "Nat.beq b3.toNat 4",
        "Nat.beq b3.toNat 5",
    );
    assert_ne!(bad_pat, ARRAYS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_pat).unwrap();
    run_request(dir.path(), "arrays-wrong-rodata-pattern", &request)
        .expect_proof_failed();

    // Negative 5 (capture): dynamic array indexing (`PlaceElem::Index`) is
    // refused fail-closed at capture time.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn dyn_idx(a: &[u8; 4], i: usize) -> u8 { a[i] }\n",
    )
    .unwrap();
    let bad_req = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "profile_v2_arrays",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {
            "kind": "selected_unit",
            "roots": ["dyn_idx"]
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
    run_request(dir.path(), "arrays-dyn-index-refused", &bad_req)
        .expect_capture_refused("unsupported place projection `Index(");
}
