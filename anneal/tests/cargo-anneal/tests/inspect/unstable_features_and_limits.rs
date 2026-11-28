// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The allowed-unstable-features gate and the receipt size limit.

use super::*;

#[test]
fn allowed_unstable_features_gate_admits_only_the_exact_feature_taint() {
    let tmp = tempfile::tempdir().unwrap();
    let (clean, ..) = sample_receipt_bundle(&tmp.path().join("artifacts"));
    let clean_path = tmp.path().join("clean.json");
    fs::write(&clean_path, serde_json::to_vec(&clean).unwrap()).unwrap();

    let mut tainted = clean.clone();
    tainted["status"] = json!("tainted_crate_verified");
    tainted["taint_reasons"] = json!(["unmodeled_unstable_features"]);
    tainted["unstable_features"] = json!({
        "allowed": ["doc_cfg", "specialization"],
        "observed": ["specialization"],
        "incomplete_observed": ["specialization"],
    });
    tainted["configuration"]["allowed_unstable_features"] = json!(["doc_cfg", "specialization"]);
    tainted["configuration"]["observed_unstable_features"] = json!(["specialization"]);
    tainted["configuration"]["incomplete_observed_unstable_features"] = json!(["specialization"]);
    tainted["assumptions"].as_array_mut().unwrap().push(json!(
        "unmodeled unstable rustc features allowed by operator (see unstable_features); \
         non-interference with captured MIR semantics is unverified"
    ));
    let path = tmp.path().join("tainted.json");
    fs::write(&path, serde_json::to_vec(&tainted).unwrap()).unwrap();
    let p = path.to_str().unwrap();

    let code = |args: &[&str]| run_inspect(args, None).status.code();
    // Bare validation rejects every tainted receipt.
    assert_eq!(code(&[p]), Some(1));
    // The exact feature set (or a superset) admits it, alongside other gates.
    assert_eq!(
        code(&[
            p,
            "--allowed-unstable-features",
            "doc_cfg,specialization",
            "--require-containment"
        ]),
        Some(0)
    );
    assert_eq!(
        code(&[
            p,
            "--allowed-unstable-features",
            "allocator_api",
            "--allowed-unstable-features",
            "doc_cfg,specialization",
        ]),
        Some(0)
    );
    // Drift outside the locked set, or any incomplete feature under
    // `--forbid-incomplete-unstable-features`, fails.
    assert_eq!(code(&[p, "--allowed-unstable-features", "specialization"]), Some(1));
    assert_eq!(
        code(&[
            p,
            "--allowed-unstable-features",
            "doc_cfg,specialization",
            "--forbid-incomplete-unstable-features",
        ]),
        Some(1)
    );
    // Clean receipts pass the gate unchanged.
    assert_eq!(
        code(&[clean_path.to_str().unwrap(), "--allowed-unstable-features", "doc_cfg"]),
        Some(0)
    );

    // Malformed names and contradictory gates are usage errors.
    for bad in [
        vec![p, "--allowed-unstable-features", "*"],
        vec![p, "--allowed-unstable-features", "doc_cfg", "--require-untainted"],
        vec![p, "--allowed-unstable-features", "doc_cfg", "--passive"],
        vec![p, "--forbid-incomplete-unstable-features", "--passive"],
    ] {
        assert_eq!(code(&bad), Some(2), "{bad:?}");
    }

    // A clean-to-tainted diff is a Tier A regression.
    let diff = run_inspect(&["--diff", clean_path.to_str().unwrap(), p, "--no-regressions"], None);
    assert_eq!(diff.status.code(), Some(1), "{diff:?}");
    let stdout = String::from_utf8_lossy(&diff.stdout);
    assert!(stdout.contains("unstable_features.allowed"), "{stdout}");
}

#[test]
fn max_receipt_bytes_toggle_enforces_default_accepts_large_receipts_and_rejects_invalid() {
    let tmp = tempfile::tempdir().unwrap();
    let (clean, ..) = sample_receipt_bundle(&tmp.path().join("artifacts"));
    let clean_bytes = serde_json::to_vec(&clean).unwrap();
    let clean_path = tmp.path().join("clean.json");
    fs::write(&clean_path, &clean_bytes).unwrap();
    let clean_p = clean_path.to_str().unwrap();

    // Help mentions `--max-receipt-bytes`, and out-of-range values fail usage.
    let help = run_inspect(&["--help"], None);
    assert_eq!(help.status.code(), Some(0));
    assert!(
        String::from_utf8_lossy(&help.stdout).contains("--max-receipt-bytes"),
        "{}",
        String::from_utf8_lossy(&help.stdout)
    );
    for bad in ["0", "1073741825", "-1", "abc"] {
        let flag = format!("--max-receipt-bytes={bad}");
        let out = run_inspect(&[clean_p, &flag], None);
        assert_eq!(out.status.code(), Some(2), "bad={bad}: {out:?}");
        assert!(out.stdout.is_empty(), "bad={bad} wrote stdout");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.contains("max-receipt-bytes"), "bad={bad}: {stderr}");
    }

    // Explicit lower cap rejects a normal clean receipt, while a compact
    // stdout receipt (`<= --max-receipt-bytes`) whose pretty/padded retained
    // `result.json` or `capture/capture_shards.json` exceeds
    // `--max-receipt-bytes` (within the 128 MiB artifact ceiling) still passes
    // `--verify-artifacts --require-exact-artifacts`.
    let too_small = run_inspect(&[clean_p, "--max-receipt-bytes", "64"], None);
    assert_eq!(too_small.status.code(), Some(2), "{too_small:?}");
    assert!(
        String::from_utf8_lossy(&too_small.stderr).contains("exceeds"),
        "{}",
        String::from_utf8_lossy(&too_small.stderr)
    );

    let shard0_lean = b"-- captured shard 0\n";
    let proof_shard0_lean = b"-- authored proof shard 0\n";
    let id_tree_lean = b"-- generated Proof.IdTree\n";
    let shard0_sha = sha256_hex(shard0_lean);
    let proof_shard0_sha = sha256_hex(proof_shard0_lean);
    let id_tree_sha = sha256_hex(id_tree_lean);
    let art_dir = tmp.path().join("artifacts");
    fs::create_dir_all(art_dir.join("capture/Captured")).unwrap();
    fs::create_dir_all(art_dir.join("authored/Proof")).unwrap();
    fs::create_dir_all(art_dir.join("generated/Proof")).unwrap();
    fs::write(art_dir.join("capture/Captured/Shard_000.lean"), shard0_lean).unwrap();
    fs::write(art_dir.join("authored/Proof/Shard_000.lean"), proof_shard0_lean).unwrap();
    fs::write(art_dir.join("generated/Proof/IdTree.lean"), id_tree_lean).unwrap();

    let shards_manifest = json!({
        "schema_version": 1,
        "scope": "crate",
        "total_bodies": 1,
        "total_sccs": 1,
        "cyclic_sccs": 0,
        "total_shards": 1,
        "is_lean_module": true,
        "id_tree_sha256": id_tree_sha,
        "shards": [{
            "shard_idx": 0,
            "capture_module": "Captured.Shard_000",
            "proof_module": "Proof.Shard_000",
            "capture_sha256": shard0_sha,
            "num_bodies": 1,
            "ast_nodes": 5,
            "has_cycle": false,
            "oversized_scc": false,
            "scc_ids": [0],
            "callee_shards": [],
            "global_def_id_range": [0, 0],
            "identities": ["rust-path-v1::zero"]
        }]
    });
    let mut padded_shards = vec![b' '; 16384];
    padded_shards.extend_from_slice(&serde_json::to_vec_pretty(&shards_manifest).unwrap());
    fs::write(art_dir.join("capture/capture_shards.json"), &padded_shards).unwrap();

    let mut stage_sharded = clean.clone();
    stage_sharded.as_object_mut().unwrap().remove("artifacts");
    stage_sharded["capture_shards_sha256"] = json!(sha256_hex(&padded_shards));
    stage_sharded["shards"] = shards_manifest;
    let sources = stage_sharded["audit"]["sources"].as_array_mut().unwrap();
    sources.push(json!({
        "module": "Captured.Shard_000",
        "role": "capture",
        "sourceSha256": shard0_sha
    }));
    sources.push(json!({
        "module": "Proof.IdTree",
        "role": "proof",
        "sourceSha256": id_tree_sha
    }));
    sources.push(json!({
        "module": "Proof.Shard_000",
        "role": "proof",
        "sourceSha256": proof_shard0_sha
    }));
    let mut padded_sharded_retained = vec![b' '; 16384];
    padded_sharded_retained.extend_from_slice(&serde_json::to_vec_pretty(&stage_sharded).unwrap());
    fs::write(art_dir.join("result.json"), &padded_sharded_retained).unwrap();

    let mut compact_stdout = stage_sharded;
    compact_stdout["artifacts"] = json!(art_dir.to_str().unwrap());
    let compact_stdout_bytes = serde_json::to_vec(&compact_stdout).unwrap();
    assert!(compact_stdout_bytes.len() < 8192, "compact len={}", compact_stdout_bytes.len());
    assert!(padded_shards.len() > 8192 && padded_sharded_retained.len() > 8192);
    let compact_stdout_path = tmp.path().join("compact_stdout.json");
    fs::write(&compact_stdout_path, &compact_stdout_bytes).unwrap();
    let retained_parity_ok = run_inspect(
        &[
            compact_stdout_path.to_str().unwrap(),
            "--max-receipt-bytes",
            "8192",
            "--unknown-fields",
            "deny",
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--require-exact-artifacts",
            "--check",
        ],
        None,
    );
    assert_eq!(
        retained_parity_ok.status.code(),
        Some(0),
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&retained_parity_ok.stdout),
        String::from_utf8_lossy(&retained_parity_ok.stderr)
    );

    // Build a valid receipt strictly larger than the 64 MiB default via leading
    // JSON whitespace.
    let over_64_mib_len = 64 * 1024 * 1024 + 64;
    let pad_len = over_64_mib_len - clean_bytes.len();
    let large_path = tmp.path().join("large_clean.json");
    {
        use std::io::Write;
        let mut f = fs::File::create(&large_path).unwrap();
        let chunk = [b' '; 65536];
        let mut remaining = pad_len;
        while remaining > 0 {
            let n = remaining.min(chunk.len());
            f.write_all(&chunk[..n]).unwrap();
            remaining -= n;
        }
        f.write_all(&clean_bytes).unwrap();
    }
    let large_p = large_path.to_str().unwrap();

    // Stock default (64 MiB) rejects the >64 MiB receipt with exit 2 and hints
    // `--max-receipt-bytes`.
    let rejected = run_inspect(&[large_p, "--unknown-fields", "deny"], None);
    assert_eq!(rejected.status.code(), Some(2), "{rejected:?}");
    let err = String::from_utf8_lossy(&rejected.stderr);
    assert!(err.contains("exceeds") && err.contains("--max-receipt-bytes"), "{err}");

    // Raising `--max-receipt-bytes` accepts the >64 MiB receipt from file,
    // `--diff`, and stdin (`-`) with `--unknown-fields deny`.
    let raised = run_inspect(
        &[large_p, "--max-receipt-bytes", "134217728", "--unknown-fields", "deny"],
        None,
    );
    assert_eq!(raised.status.code(), Some(0), "{raised:?}");

    let diff = run_inspect(
        &[
            "--diff",
            large_p,
            clean_p,
            "--max-receipt-bytes",
            "134217728",
            "--unknown-fields",
            "deny",
        ],
        None,
    );
    assert_eq!(diff.status.code(), Some(0), "{diff:?}");

    let mut large_stdin = vec![b' '; over_64_mib_len];
    large_stdin[pad_len..].copy_from_slice(&clean_bytes);
    let stdin_ok = run_inspect(
        &["-", "--max-receipt-bytes", "134217728", "--unknown-fields", "deny"],
        Some(&large_stdin),
    );
    assert_eq!(stdin_ok.status.code(), Some(0), "{stdin_ok:?}");

    // Also verify `--verify-artifacts --require-exact-artifacts` scales above
    // the 128 MiB retained-artifact ceiling when `--max-receipt-bytes` exceeds
    // 128 MiB (using a >128 MiB padded valid failure receipt).
    let fail_json = serde_json::to_vec(&json!({
        "schema_version": 3,
        "status": "proof_failed",
        "taint_reasons": [],
        "phase": "audit",
        "detail": "boom",
    }))
    .unwrap();
    let over_128_mib_len = 128 * 1024 * 1024 + 64;
    let fail_pad = over_128_mib_len - fail_json.len();
    let fail_dir = tmp.path().join("fail_artifacts");
    fs::create_dir_all(&fail_dir).unwrap();
    let fail_receipt = tmp.path().join("large_fail.json");
    let fail_retained = fail_dir.join("result.json");
    for target in [&fail_receipt, &fail_retained] {
        use std::io::Write;
        let mut f = fs::File::create(target).unwrap();
        let chunk = [b' '; 65536];
        let mut remaining = fail_pad;
        while remaining > 0 {
            let n = remaining.min(chunk.len());
            f.write_all(&chunk[..n]).unwrap();
            remaining -= n;
        }
        f.write_all(&fail_json).unwrap();
    }
    let fail_artifacts_passive_ok = run_inspect(
        &[
            fail_receipt.to_str().unwrap(),
            "--passive",
            "--unknown-fields",
            "deny",
            "--verify-artifacts",
            fail_dir.to_str().unwrap(),
            "--max-receipt-bytes",
            "268435456",
        ],
        None,
    );
    assert_eq!(fail_artifacts_passive_ok.status.code(), Some(0), "{fail_artifacts_passive_ok:?}");

    let fail_artifacts_exact = run_inspect(
        &[
            fail_receipt.to_str().unwrap(),
            "--unknown-fields",
            "deny",
            "--verify-artifacts",
            fail_dir.to_str().unwrap(),
            "--require-exact-artifacts",
            "--max-receipt-bytes",
            "268435456",
        ],
        None,
    );
    // Exits `1` due to `proof_failed`, with clean retained-artifact check
    // (no SHA mismatch or 128 MiB artifact cap failure).
    assert_eq!(fail_artifacts_exact.status.code(), Some(1), "{fail_artifacts_exact:?}");
    let exact_stdout = String::from_utf8_lossy(&fail_artifacts_exact.stdout);
    assert!(
        !exact_stdout.contains("exceeds") && !exact_stdout.contains("mismatch"),
        "{exact_stdout}"
    );
}
