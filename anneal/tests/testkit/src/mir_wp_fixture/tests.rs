// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{fs, path::Path};

use super::*;
use crate::toolchain::ToolchainEnv;

/// Extract the `def verifyMirWpCoreTheorems` function body from
/// `TrustedBoundary.lean`.
fn extract_verify_mir_wp_body(source: &str) -> &str {
    let start = source
        .find("def verifyMirWpCoreTheorems")
        .expect("verifyMirWpCoreTheorems must exist in TrustedBoundary.lean");
    let tail = &source[start..];
    let end = tail[1..]
        .find("\n/-- ")
        .or_else(|| tail[1..].find("\ndef "))
        .map(|offset| offset + 1)
        .unwrap_or(tail.len());
    &tail[..end]
}

/// Scan every backtick-quoted Lean name (`Foo.Bar.baz`) inside `text`.
fn backtick_names(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut names = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'`' {
            let start = i + 1;
            let mut end = start;
            while end < bytes.len()
                && (bytes[end].is_ascii_alphanumeric() || matches!(bytes[end], b'.' | b'_'))
            {
                end += 1;
            }
            if end > start {
                names.push(&text[start..end]);
            }
            i = end;
        } else {
            i += 1;
        }
    }
    names
}

/// Return `true` iff `expr` contains `ident` as a whole Lean identifier
/// token (delimited by non-identifier characters, not a mere substring).
fn contains_lean_ident_token(expr: &str, ident: &str) -> bool {
    expr.split(|c: char| !(c.is_ascii_alphanumeric() || matches!(c, '_' | '.')))
        .any(|tok| tok == ident)
}

/// Parse every core `requireClaimProof` call preceding the canary loop in
/// `body`, returning `(claim, wp_param, proof, reqs)`.
fn parse_core_require_claim_proofs(body: &str) -> Vec<(String, String, String, Vec<String>)> {
    let core_end = body.find("let posClaim").expect("canary section marker `let posClaim`");
    let core = &body[..core_end];
    let mut results = Vec::new();
    let mut idx = 0;
    while let Some(rel) = core[idx..].find("requireClaimProof ") {
        let start = idx + rel;
        let tail = &core[start..];
        let next_stmt =
            tail[1..].find("requireClaimProof ").map(|off| off + 1).unwrap_or(tail.len());
        let call = &tail[..next_stmt];
        let open_b = call.find('[').unwrap_or_else(|| panic!("missing reqConsts `[` in {call}"));
        let close_b = call.find(']').unwrap_or_else(|| panic!("missing reqConsts `]` in {call}"));
        let header = &call[..open_b];
        let header_names = backtick_names(header);
        assert_eq!(
            header_names.len(),
            3,
            "expected (claim, wp_param, proof) before reqConsts: {call}"
        );
        let claim = header_names[0]
            .strip_prefix("Trusted.MirSemantics.")
            .unwrap_or_else(|| panic!("unexpected core claim: {}", header_names[0]))
            .to_string();
        let wp_param = header_names[1]
            .strip_prefix("Anneal.MirWp.")
            .unwrap_or_else(|| panic!("unexpected core param: {}", header_names[1]))
            .to_string();
        let proof = header_names[2]
            .strip_prefix("Anneal.MirWp.")
            .unwrap_or_else(|| panic!("unexpected core proof: {}", header_names[2]))
            .to_string();
        let reqs = backtick_names(&call[open_b + 1..close_b])
            .into_iter()
            .map(|name| name.strip_prefix("Trusted.MirSemantics.").unwrap_or(name).to_string())
            .collect();
        results.push((claim, wp_param, proof, reqs));
        idx = start + next_stmt;
    }
    results
}

#[test]
fn synthetic_mir_wp_fixture_matches_trusted_boundary_lean_100_percent() {
    let repo_root = ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))
        .expect("resolve anneal repo root");
    let tb_path = repo_root.join("trusted/audit/TrustedBoundary.lean");
    let source =
        fs::read_to_string(&tb_path).unwrap_or_else(|e| panic!("read {}: {e}", tb_path.display()));
    let body = extract_verify_mir_wp_body(&source);

    // 1. Parse the canary `(claim, proof, reqConsts)` list inside
    //    `for (claimName, proofName, reqConsts) in [ ... ] do`.
    let list_marker = "for (claimName, proofName, reqConsts) in [";
    let list_start =
        body.find(list_marker).expect("canary loop in verifyMirWpCoreTheorems") + list_marker.len();
    let list_end = body[list_start..].find("] do").expect("closing `] do` for canary loop");
    let canary_block = &body[list_start..list_start + list_end];

    let mut parsed_canaries: Vec<(String, String, Vec<String>)> = Vec::new();
    let mut idx = 0;
    while let Some(open_rel) = canary_block[idx..].find('(') {
        let start = idx + open_rel;
        let mut depth = 0usize;
        let mut end = None;
        for (off, ch) in canary_block[start..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(start + off + 1);
                        break;
                    }
                }
                _ => {}
            }
        }
        let end = end.expect("balanced tuple in canary list");
        let tuple = &canary_block[start..end];
        let names = backtick_names(tuple);
        assert!(names.len() >= 2, "expected (claim, proof, reqConsts) tuple, got: {tuple}");
        let claim = names[0]
            .strip_prefix("Trusted.MirSemantics.")
            .unwrap_or_else(|| panic!("unexpected claim name: {}", names[0]))
            .to_string();
        let proof = names[1]
            .strip_prefix("Anneal.MirWp.")
            .unwrap_or_else(|| panic!("unexpected proof name: {}", names[1]))
            .to_string();

        // Collect required constants (expanding `posClaim`/`negClaim`/
        // `widthClaim` shorthands).
        let bracket_start =
            tuple.find('[').unwrap_or_else(|| panic!("missing reqConsts in {tuple}"));
        let bracket_end =
            tuple.rfind(']').unwrap_or_else(|| panic!("missing closing `]` in {tuple}"));
        let req_slice = &tuple[bracket_start + 1..bracket_end];
        let mut reqs = Vec::new();
        for token in req_slice.split(',') {
            let tok = token.trim();
            if tok.is_empty() {
                continue;
            }
            let mapped = match tok {
                "posClaim" => "PositiveCanaryClaim".to_string(),
                "negClaim" => "NegativeCanaryClaim".to_string(),
                "widthClaim" => "IntWidthBoundaryCanary".to_string(),
                other => {
                    let stripped = other
                        .strip_prefix('`')
                        .unwrap_or_else(|| panic!("unexpected reqConst token: {other}"));
                    stripped.strip_prefix("Trusted.MirSemantics.").unwrap_or(stripped).to_string()
                }
            };
            reqs.push(mapped);
        }
        parsed_canaries.push((claim, proof, reqs));
        idx = end;
    }

    // Exact 1:1 parity on canary count, order, claim names, proof names,
    // and whole-token required constant references in every synthetic body.
    assert_eq!(
        parsed_canaries.len(),
        SYNTHETIC_CANARIES.len(),
        "SYNTHETIC_CANARIES count drifted from TrustedBoundary.lean"
    );
    for ((tb_claim, tb_proof, tb_reqs), fixture_canary) in
        parsed_canaries.iter().zip(SYNTHETIC_CANARIES.iter())
    {
        assert_eq!(
            tb_claim.as_str(),
            fixture_canary.claim,
            "canary claim mismatch against TrustedBoundary.lean"
        );
        assert_eq!(tb_proof.as_str(), fixture_canary.proof, "canary proof mismatch for {tb_claim}");
        for req in tb_reqs {
            assert!(
                contains_lean_ident_token(fixture_canary.body, req),
                "synthetic body for {tb_claim} missing required constant \
                 token {req:?}: {}",
                fixture_canary.body
            );
        }
    }

    // 2. Verify all three core WP / Profile v2 soundness
    //    `requireClaimProof` calls and their required constants against
    //    `MirWpFixtureSpec::valid()`.
    let spec = MirWpFixtureSpec::valid();
    let parsed_core = parse_core_require_claim_proofs(body);
    assert_eq!(
        parsed_core.len(),
        CORE_WP_CLAIMS.len(),
        "CORE_WP_CLAIMS count drifted from TrustedBoundary.lean"
    );
    let core_claim_bodies = [
        spec.wp_soundness_claim.as_deref().unwrap(),
        spec.wp_fault_soundness_claim.as_deref().unwrap(),
        spec.exec_soundness_claim_v2.as_deref().unwrap(),
        spec.safe_contract_soundness_claim_v2.as_deref().unwrap(),
    ];
    let core_proof_bodies = [
        spec.wp_soundness_proof.as_deref().unwrap(),
        spec.wp_fault_soundness_proof.as_deref().unwrap(),
        spec.exec_soundness_proof_v2.as_deref().unwrap(),
        spec.safe_contract_soundness_proof_v2.as_deref().unwrap(),
    ];
    for (((tb_claim, tb_param, tb_proof, tb_reqs), &(c, p, pr)), idx) in
        parsed_core.iter().zip(CORE_WP_CLAIMS.iter()).zip(0usize..)
    {
        assert_eq!((tb_claim.as_str(), tb_param.as_str(), tb_proof.as_str()), (c, p, pr));
        assert!(
            contains_lean_ident_token(core_claim_bodies[idx], c),
            "core claim decl missing {c}: {}",
            core_claim_bodies[idx]
        );
        for req in tb_reqs {
            assert!(
                contains_lean_ident_token(core_claim_bodies[idx], req),
                "core claim {c} missing required constant token {req:?}: {}",
                core_claim_bodies[idx]
            );
        }
        assert!(
            contains_lean_ident_token(core_proof_bodies[idx], pr),
            "core proof decl missing {pr}: {}",
            core_proof_bodies[idx]
        );
        assert!(
            contains_lean_ident_token(core_proof_bodies[idx], &format!("Anneal.MirWp.{p}")),
            "core proof decl missing Anneal.MirWp.{p}: {}",
            core_proof_bodies[idx]
        );
    }

    // 3. Verify public aliases (`Trusted.Crate`, `Trusted.CrateTheorem`,
    //    `Trusted.UnitTheorem`, `Trusted.CrateV2`,
    //    `Trusted.CrateTheoremV2`, `Trusted.UnitTheoremV2`).
    let alias_marker = "for (aliasName, targetName) in [";
    let alias_start = body.find(alias_marker).expect("alias loop in verifyMirWpCoreTheorems")
        + alias_marker.len();
    let alias_end = body[alias_start..].find("] do").expect("closing `] do` for alias loop");
    let alias_names = backtick_names(&body[alias_start..alias_start + alias_end]);
    let parsed_aliases: Vec<(&str, &str)> = alias_names
        .chunks_exact(2)
        .map(|pair| {
            (
                pair[0].strip_prefix("Trusted.").unwrap(),
                pair[1].strip_prefix("Trusted.MirSemantics.").unwrap(),
            )
        })
        .collect();
    assert_eq!(
        parsed_aliases, PUBLIC_MIR_ALIASES,
        "PUBLIC_MIR_ALIASES drifted from TrustedBoundary.lean"
    );

    // 4. Smoke-check rendering and materialization of both standard and
    //    `module`-syntax baseline specs.
    assert!(spec.render_mir_semantics().contains("ExecSoundnessClaimV2"));
    assert!(spec.render_mir_semantics().contains("CrateTheoremV2"));
    assert!(spec.render_mir_wp().contains("def execProgV2 : Nat := 0"));
    for candidate in [spec, MirWpFixtureSpec::valid_module_style()] {
        let fix =
            candidate.materialize(&repo_root, "test-mir-wp-", OleanCachePolicy::Isolated).unwrap();
        assert!(fix.root().join("trusted/lean/Trusted/MirAst.lean").is_file());
        assert!(fix.root().join("trusted/lean/Trusted/MirSemantics.lean").is_file());
        assert!(fix.root().join("theory/Anneal/MirWp.lean").is_file());
        assert!(fix.root().join("theory/Anneal/MirWp/Canaries.lean").is_file());
        assert!(fix.root().join("theory/Anneal/Wp.lean").is_file());
        assert!(!fix.root().join("theory/Anneal.lean").exists());
    }
    let mod_spec = MirWpFixtureSpec::valid_module_style();
    assert!(mod_spec.render_mir_ast().contains("\nmodule\n"));
    assert!(!mod_spec.render_mir_ast().contains("placeholder"));
    assert!(MirWpFixtureSpec::valid().render_mir_ast().contains("def placeholder : Nat := 0"));
    assert!(mod_spec.render_mir_semantics().contains("ExecSoundnessClaimV2"));
    assert!(mod_spec.render_mir_semantics().contains("CrateTheoremV2"));
    assert!(mod_spec.render_mir_wp().contains("@[expose] def execProgV2"));
}

#[test]
fn theory_umbrella_module_supports_domain_umbrella_and_rejects_invalid_names() {
    let repo_root = ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))
        .expect("resolve anneal repo root");

    let default_spec = MirWpFixtureSpec::valid();
    assert_eq!(
        default_spec.theory_umbrella_rel_path().unwrap(),
        Path::new("theory/Anneal/Wp.lean")
    );
    assert_eq!(default_spec.render_theory_umbrella_import().unwrap(), "import Anneal.Wp\n");

    let wp_mod_spec = MirWpFixtureSpec::valid_module_style();
    assert_eq!(wp_mod_spec.theory_umbrella_rel_path().unwrap(), Path::new("theory/Anneal/Wp.lean"));
    assert_eq!(wp_mod_spec.render_theory_umbrella_import().unwrap(), "public import Anneal.Wp\n");
    assert_eq!(
        wp_mod_spec.render_anneal(),
        "module\n\
         prelude\n\
         public import Init.NotationExtra\n\
         public import Trusted\n\
         public import Anneal.MirWp\n"
    );
    let fix = wp_mod_spec
        .materialize(&repo_root, "test-mir-wp-domain-", OleanCachePolicy::Isolated)
        .expect("materialize domain umbrella fixture");
    assert!(fix.root().join("theory/Anneal/Wp.lean").is_file());
    assert!(!fix.root().join("theory/Anneal.lean").exists());

    let mut legacy_spec = MirWpFixtureSpec::valid();
    legacy_spec.theory_umbrella_module = "Anneal".to_string();
    assert_eq!(legacy_spec.theory_umbrella_rel_path().unwrap(), Path::new("theory/Anneal.lean"));
    assert_eq!(legacy_spec.render_theory_umbrella_import().unwrap(), "import Anneal\n");
    let legacy_fix = legacy_spec
        .materialize(&repo_root, "test-mir-wp-legacy-", OleanCachePolicy::Isolated)
        .expect("materialize legacy synthetic umbrella fixture");
    assert!(legacy_fix.root().join("theory/Anneal.lean").is_file());
    assert!(!legacy_fix.root().join("theory/Anneal/Wp.lean").exists());

    for bad in [
        "",
        "Other",
        "Anneal.",
        "Anneal..Wp",
        "Anneal/Wp",
        "../Escape",
        "Anneal.1bad",
        "Anneal.MirWp",
        "Anneal.MirWp.Canaries",
    ] {
        let mut invalid = MirWpFixtureSpec::valid();
        invalid.theory_umbrella_module = bad.to_string();
        assert!(
            invalid.theory_umbrella_rel_path().is_err(),
            "expected invalid theory_umbrella_module {bad:?} to fail closed"
        );
        assert!(invalid.render_theory_umbrella_import().is_err());
    }
}
