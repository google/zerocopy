// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Forged `.olean` keys, duplicate declarations, replay invariants, and
//! foundation axiom hijacking.

use super::*;

/// Verifies Pass-1 and Pass-2 `.olean` replay-key, intra-module duplicate,
/// anonymous declaration, `_unsafe_rec` header parity, `validateReplayMap`
/// (`hasNoDuplicateNames`, missing peers, ctor mismatch),
/// `checkSysrootAlternates`, and `.foundation` `sorryAx` subsumption defenses.
#[test]
fn rejects_forged_olean_keys_dups_replay_invariants_and_foundation_axiom_hijack() {
    use anneal_audit::ImportEdge;

    let fix = TempFixture::new(None);
    fs::create_dir_all(fix.root.join("theory")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n",
    )
    .unwrap();
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let lib_dir = stage.join("lib");
    let forged_lib = stage.join("forged-pass1-lib");
    fs::create_dir_all(forged_lib.join("Anneal")).unwrap();
    fs::create_dir_all(forged_lib.join("Trusted")).unwrap();
    let orig_arts = checker.admitted().unwrap().artifacts.clone();
    let orig_graph = checker.admitted().unwrap().graph.clone();
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];

    let inspect_pass1_mod = |checker: &mut Checker,
                             mod_name: &str,
                             olean_path: &Path,
                             is_trusted: bool,
                             edge: Vec<ImportEdge>| {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts = orig_arts.clone();
        adm.graph = orig_graph.clone();
        let avail = BTreeMap::from([("olean", olean_path.to_string_lossy().into_owned())]);
        let arts = ModuleArtifacts::from_available(&avail, "test", String::new).unwrap();
        adm.artifacts.insert(mod_name.to_string(), arts);
        adm.graph.insert(mod_name.to_string(), edge);
        let (trusted, theory, tiers) = if is_trusted {
            (
                vec!["Trusted".to_string(), mod_name.to_string()],
                vec!["Anneal".to_string()],
                BTreeMap::from([
                    ("Trusted".to_string(), TrustTier::Vetted),
                    (mod_name.to_string(), TrustTier::Vetted),
                ]),
            )
        } else {
            (
                vec!["Trusted".to_string()],
                vec!["Anneal".to_string(), mod_name.to_string()],
                BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            )
        };
        checker
            .inspect(InspectorRequest::Audit { trusted, theory, module_tiers: tiers })
            .unwrap_err()
    };

    let checker = pass1_replay_invariants::rejects_forged_keys_headers_and_replay_maps(
        checker,
        stage.clone(),
        forged_lib,
        core_edge.clone(),
        &inspect_pass1_mod,
    );
    let checker = foundation_alternates::rejects_axiom_hijack_and_forged_alternates(
        checker,
        stage.clone(),
        lib_dir.clone(),
        orig_arts.clone(),
        orig_graph.clone(),
        core_edge,
        &inspect_pass1_mod,
    );
    let checker = sysroot_and_vendor_origins::rejects_forged_vendor_and_sysroot_origins(
        checker,
        stage.clone(),
        lib_dir,
    );
    sysroot_alternate_order::checks_sysroot_alternate_order(checker, stage);
}

#[path = "forged_olean_replay/foundation_alternates.rs"]
mod foundation_alternates;
#[path = "forged_olean_replay/pass1_replay_invariants.rs"]
mod pass1_replay_invariants;
#[path = "forged_olean_replay/sysroot_alternate_order.rs"]
mod sysroot_alternate_order;
#[path = "forged_olean_replay/sysroot_and_vendor_origins.rs"]
mod sysroot_and_vendor_origins;
