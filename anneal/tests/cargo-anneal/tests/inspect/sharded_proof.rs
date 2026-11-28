// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--verify-artifacts` with a sharded proof ID tree and capture shards.

use super::*;

#[test]
fn verify_artifacts_supports_sharded_proof_id_tree_and_capture_shards_json() {
    let tmp = tempfile::tempdir().unwrap();
    let art_dir = tmp.path().join("artifacts");
    let (mut receipt, _, _, _, _) = sample_receipt_bundle(&art_dir);

    let shard0_lean = b"-- captured shard 0\n";
    let proof_shard0_lean = b"-- authored proof shard 0\n";
    let id_tree_lean = b"-- generated Proof.IdTree\n";
    let shard0_sha = sha256_hex(shard0_lean);
    let proof_shard0_sha = sha256_hex(proof_shard0_lean);
    let id_tree_sha = sha256_hex(id_tree_lean);

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
    let shards_bytes = serde_json::to_vec_pretty(&shards_manifest).unwrap();
    let shards_sha = sha256_hex(&shards_bytes);
    fs::write(art_dir.join("capture/capture_shards.json"), &shards_bytes).unwrap();

    receipt["capture_shards_sha256"] = json!(shards_sha);
    receipt["shards"] = shards_manifest.clone();
    let sources = receipt["audit"]["sources"].as_array_mut().unwrap();
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

    let receipt_bytes = serde_json::to_vec_pretty(&receipt).unwrap();
    fs::write(art_dir.join("result.json"), &receipt_bytes).unwrap();
    let receipt_path = tmp.path().join("sharded_receipt.json");
    fs::write(&receipt_path, &receipt_bytes).unwrap();

    // 1. Sharded receipt + retained artifacts pass strictly under
    //    `--unknown-fields=deny --verify-artifacts --require-exact-artifacts`.
    for fmt in ["human", "ledger", "markdown", "json"] {
        let out = run_inspect(
            &[
                receipt_path.to_str().unwrap(),
                "--verify-artifacts",
                art_dir.to_str().unwrap(),
                "--require-exact-artifacts",
                "--unknown-fields",
                "deny",
                "--format",
                fmt,
                "--color",
                "never",
            ],
            None,
        );
        assert_eq!(
            out.status.code(),
            Some(0),
            "sharded inspect ({fmt}) failed: stdout={}\nstderr={}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }

    // 2. Tampering `generated/Proof/IdTree.lean` fails `--verify-artifacts`.
    fs::write(art_dir.join("generated/Proof/IdTree.lean"), b"-- tampered id tree\n").unwrap();
    let bad_id_tree = run_inspect(
        &[
            receipt_path.to_str().unwrap(),
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--unknown-fields",
            "deny",
        ],
        None,
    );
    assert_eq!(bad_id_tree.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&bad_id_tree.stdout).contains("generated/Proof/IdTree.lean"),
        "{}",
        String::from_utf8_lossy(&bad_id_tree.stdout)
    );
    fs::write(art_dir.join("generated/Proof/IdTree.lean"), id_tree_lean).unwrap();

    // 3. Tampering `capture/capture_shards.json` fails `--verify-artifacts`.
    fs::write(art_dir.join("capture/capture_shards.json"), b"{\"tampered\":true}").unwrap();
    let bad_shards = run_inspect(
        &[
            receipt_path.to_str().unwrap(),
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--unknown-fields",
            "deny",
        ],
        None,
    );
    assert_eq!(bad_shards.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&bad_shards.stdout).contains("capture/capture_shards.json"),
        "{}",
        String::from_utf8_lossy(&bad_shards.stdout)
    );

    // 4. Split-brain: `capture_shards_sha256` updated to match mutated disk
    //    `capture_shards.json` while receipt `shards` stays unchanged fails.
    let mut alt_manifest = shards_manifest.clone();
    alt_manifest["shards"][0]["ast_nodes"] = json!(999);
    let alt_bytes = serde_json::to_vec_pretty(&alt_manifest).unwrap();
    fs::write(art_dir.join("capture/capture_shards.json"), &alt_bytes).unwrap();
    let mut split_receipt = receipt.clone();
    split_receipt["capture_shards_sha256"] = json!(sha256_hex(&alt_bytes));
    let split_path = tmp.path().join("split_receipt.json");
    fs::write(&split_path, serde_json::to_vec_pretty(&split_receipt).unwrap()).unwrap();
    let split_out = run_inspect(
        &[
            split_path.to_str().unwrap(),
            "--verify-artifacts",
            art_dir.to_str().unwrap(),
            "--unknown-fields",
            "deny",
        ],
        None,
    );
    assert_eq!(split_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&split_out.stdout).contains("differ from receipt `shards`"),
        "{}",
        String::from_utf8_lossy(&split_out.stdout)
    );
}
