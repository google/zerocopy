// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `Vec` and `Box` allocation contracts under `--panic abort`.

use super::*;

/// Verifies `Vec<u8>`, `Box<[u8]>`, and `Box<u64>` allocation contracts under
/// `CrateTheoremV2` with `"panic": "abort"` (`["propext"]`, zero taint),
/// including the heap buffers visible to `post` on return and
/// `push_one(&mut Vec<u8>)` over every valid caller `Vec` that cannot
/// overflow its capacity, and
/// confirms fail-closed rejections for both weakening `Vec::with_capacity`'s
/// `isize::MAX` bound and omitting `"panic": "abort"` (`--panic unwind`).
#[test]
fn verifies_profile_v2_vec_and_box_contracts_and_rejects_missing_cap_bound() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), ALLOC_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), ALLOC_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), ALLOC_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "alloc_demo",
            "panic": "abort",
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

    let ok = run_request(dir.path(), "alloc-ok", &request);
    ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(verified) = &ok.receipt else {
        panic!("alloc-ok: expected verified receipt, got {:?}", ok.receipt);
    };
    assert_eq!(verified.configuration["panic"], "abort", "{:?}", verified.configuration);
    let capture_json: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-alloc-ok/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    assert_eq!(capture_json["configuration"]["panic"], "abort", "{capture_json}");
    let identities: Vec<&str> = capture_json["program"]["bodies"]
        .as_array()
        .unwrap()
        .iter()
        .map(|b| b["identity"].as_str().unwrap())
        .collect();
    assert_eq!(
        identities,
        vec![
            "rust-path-v1::vec_and_box_slice",
            "rust-path-v1::box_new_and_deref",
            "rust-path-v1::vec_with_cap_arg",
            "rust-path-v1::read_slice_and_box_len",
            "rust-path-v1::push_one",
        ],
        "{capture_json}"
    );
    let captured_lean =
        fs::read_to_string(dir.path().join("artifacts-alloc-ok/capture/Captured.lean")).unwrap();
    assert!(captured_lean.contains("CastKind.boxAsRef"), "{captured_lean}");

    // Negative 7: weaken `vecWithCapSafety` to omit `< isizeMaxBytes`.
    let bad_spec = ALLOC_SPEC.replace("capSv.bits.toNat < isizeMaxBytes", "True");
    assert_ne!(bad_spec, ALLOC_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_spec).unwrap();
    run_request(dir.path(), "alloc-missing-cap-bound", &request).expect_proof_failed();

    // Negative 8: restore valid `Spec.lean`, omit `"panic": "abort"`
    // (`--panic unwind` default), and confirm fail-closed capture rejection.
    fs::write(lean_dir.join("Spec.lean"), ALLOC_SPEC).unwrap();
    let mut unwind_request = request.clone();
    unwind_request["compilation"].as_object_mut().unwrap().remove("panic");
    let unwind = run_request(dir.path(), "alloc-unwind-rejected", &unwind_request);
    assert!(
        !unwind.output.status.success(),
        "alloc-unwind-rejected must fail closed:\n{:?}\nstderr:\n{}",
        unwind.receipt,
        String::from_utf8_lossy(&unwind.output.stderr)
    );
    let VerifyReceipt::Failed(failure) = &unwind.receipt else {
        panic!("alloc-unwind-rejected must fail closed: {:?}", unwind.receipt);
    };
    assert_eq!(failure.schema_version, 3, "{failure:?}");
    assert_ne!(failure.status, "crate_verified", "{failure:?}");
    assert_eq!(failure.phase, "capture", "{failure:?}");

    // Negative 9: a function mixing `&[u8]` / `&Box<u64>` with a genuine
    // `*const u64` raw pointer still fails closed in capture.
    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn mixed(s: &[u8], b: &Box<u64>) -> (usize, *const u64) {\n\
             (s.len(), &**b as *const u64)\n\
         }\n",
    )
    .unwrap();
    run_request(dir.path(), "alloc-mixed-raw-ptr-rejected", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}
