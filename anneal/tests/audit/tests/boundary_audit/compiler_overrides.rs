// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Repository and proof compiler override entries.

use super::*;

/// Verifies that compiled repository `.olean` checks in Pass 1 `"audit"`,
/// Pass 2 `"correspondence-audit"`, and `"target-export"` <-> `"target-audit"`
/// fail closed on authored compiler overrides (`@[implemented_by]`,
/// `@[extern]`, `@[csimp]`, `@[export]`, `@[init]`, `@[builtin_init]`,
/// `@[cpass]`, `ConstantFold.folderExt`, and `postponedCompileDeclsExt`),
/// including `module`-mode `.olean.private`, `.olean` (`.exported`), and
/// `.olean.server` companion parts.
#[test]
fn rejects_repo_and_proof_compiler_override_entries() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let theory_lib = stage.join("theory-lib");
    let src_dir = stage.join("src/override-neg");
    fs::create_dir_all(&theory_lib).unwrap();

    let (checker, postponed_olean) = repo_passes::audit_rejects_forged_overrides(
        checker,
        stage.clone(),
        theory_lib.clone(),
        src_dir.clone(),
    );
    let checker = repo_passes::correspondence_audit_rejects_forged_overrides(
        checker,
        stage.clone(),
        theory_lib.clone(),
        src_dir.clone(),
    );
    let (checker, target_dir, inputs, cpass_olean) =
        target_splices::target_audit_rejects_spliced_overrides(
            checker,
            checkout,
            stage.clone(),
            theory_lib.clone(),
            postponed_olean,
        );
    let checker = module_parts::repo_passes_reject_overrides_in_module_parts(
        checker,
        stage.clone(),
        theory_lib,
        src_dir,
        cpass_olean.clone(),
    );
    target_module_parts::target_audit_rejects_overrides_in_module_parts(
        checker,
        stage,
        target_dir,
        inputs,
        cpass_olean,
    );
}

#[path = "compiler_overrides/module_parts.rs"]
mod module_parts;
#[path = "compiler_overrides/repo_passes.rs"]
mod repo_passes;
#[path = "compiler_overrides/target_module_parts.rs"]
mod target_module_parts;
#[path = "compiler_overrides/target_splices.rs"]
mod target_splices;
