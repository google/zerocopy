// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Specification-vacuity compiler-helper exclusion regressions
//! (`isCompilerGeneratedSpecDef` and `inspectSpecVacuity` structural /
//! well-founded / structure helpers).

use super::*;

const SIMPLE_PROOF: &str = "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
                            theorem Proof.verify : Expected.claim :=\n  \
                              And.intro rfl BitVec.and_self\n";

fn unused_spec_binding_decls(report: &Json) -> BTreeSet<String> {
    report["specWarnings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|w| w["code"] == "unused_spec_binding")
        .map(|w| w["declaration"].as_str().unwrap().to_owned())
        .collect()
}

#[path = "spec_g4_vacuity/positive.rs"]
mod positive;
#[path = "spec_g4_vacuity/spoofs.rs"]
mod spoofs;
#[path = "spec_g4_vacuity/wf_and_forged.rs"]
mod wf_and_forged;
