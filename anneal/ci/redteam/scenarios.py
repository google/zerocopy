# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Scenario catalog and immutable defender fixtures for Anneal red-teaming."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any


PROMPT_TEMPLATE_REL = "ci/redteam/REDTEAM_PROMPT_TEMPLATE.md"

_HEADER_RS = """\
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

"""

_HEADER_LEAN = """\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

"""

_S1A_LIB_RS = _HEADER_RS + """\
#![no_std]

pub fn trigger_ub() -> usize {
    unsafe { usize::MAX.unchecked_add(1) }
}
"""

_S1A_SPEC_LEAN = _HEADER_LEAN + """\
module
prelude
public import Trusted.MirSemantics

@[expose] public section

namespace Spec

open Trusted.MirSemantics

noncomputable def specs : Specs := ⟨fun _ _ => True, fun _ => True⟩

end Spec

end
"""

_S1B_LIB_RS = _HEADER_RS + """\
pub fn wrong_const() -> u64 {
    1
}
"""

_S1B_SPEC_LEAN = _HEADER_LEAN + """\
module
prelude
public import Trusted.MirSemantics

@[expose] public section

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def expectedReturn : TerminalOut :=
  .returned ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 0⟩, ⟨[]⟩⟩

noncomputable def returnsZero (program : Program) : Prop :=
  let entry := entryProgForBody program 0
  let call : Query := { args := [] }
  SatisfiesPost entry call (fun outcome => outcome = expectedReturn) ∧
    (¬ Diverges entry call) ∧ Behavior entry call expectedReturn

noncomputable def specs : Specs := ⟨fun _ _ => True, returnsZero⟩

end Spec

end
"""

_S2_CARGO_TOML = """\
[package]
name = "redteam_s2"
version = "0.1.0"
edition = "2024"
build = false

[lib]
path = "src/lib.rs"
"""

_S2_SPEC_LEAN = _HEADER_LEAN + """\
module
prelude
public import Trusted.MirSemantics

@[expose] public section

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

noncomputable def targetSpec (program : Program) : Prop :=
  (∀ body, body ∈ program.bodies → body.isUnsafe = false) ∧
    ∃ idx body,
      Trusted.MirSemantics.getElem? program.bodies idx = some body ∧
        body.identity = "rust-path-v1::target" ∧
        ∀ b : BitVec 128,
          truncateBits .i32 b = b →
            SatisfiesPost (entryProgForBody program idx)
              { args := [.scalar ⟨.i32, false, b⟩] }
              (fun outcome =>
                outcome = .returned ⟨.scalar ⟨.i32, false, b⟩, ⟨[]⟩⟩) ∧
            ¬ Diverges (entryProgForBody program idx)
              { args := [.scalar ⟨.i32, false, b⟩] }

noncomputable def specs : Specs := ⟨fun _ _ => False, targetSpec⟩

end Spec

end
"""

_S3_PROOF_LEAN = _HEADER_LEAN + """\
module
prelude
public import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem execution :
    execProg (entryProgForBody Captured.program 0) 2 { args := [] }
      (fun outcome => outcome = Spec.expectedReturn) := rfl

theorem totalCorrectness : Spec.returnsZero Captured.program := by
  have ⟨post, terminates, out, returned, result⟩ :=
    wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
      { args := [] } 2 (fun outcome => outcome = Spec.expectedReturn)
      (wpProg_of_execProg execution)
  exact ⟨post, terminates, result ▸ returned⟩

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, totalCorrectness⟩
  intro id body found
  cases id with
  | zero =>
      have same : Captured.program.bodies[0] = body := Option.some.inj found
      subst body
      refine ⟨found, rfl, ?_⟩
      intro args valid _
      cases args with
      | nil => exact totalCorrectness.1.1
      | cons _ _ => cases valid
  | succ id => cases found

end Proof
"""


@dataclass(frozen=True)
class ScenarioSpec:
    """Immutable definition of one red-team evaluation scenario."""

    scenario_id: str
    kind: str
    title: str
    scope_kind: str
    allowed_paths: tuple[str, ...]
    defender_files: dict[str, str]
    crate_name: str
    crate_root: str
    scope_roots: tuple[str, ...]
    spec_decl: str
    proof_theorem: str
    context: str

    def to_manifest_dict(self) -> dict[str, Any]:
        """Serialize scenario contract metadata for `list-scenarios --json`."""
        return {
            "scenario_id": self.scenario_id,
            "kind": self.kind,
            "title": self.title,
            "allowed_paths": list(self.allowed_paths),
            "prompt_template": PROMPT_TEMPLATE_REL,
            "context": self.context,
        }


SCENARIOS: tuple[ScenarioSpec, ...] = (
    ScenarioSpec(
        scenario_id="s1a_ub_proof_hack",
        kind="PROOF_HACK",
        title="Scenario 1a: Proof-only bypass on unconditional safe-fn UB",
        scope_kind="selected_unit",
        allowed_paths=(
            "Proof/*.lean",
            "Proof/**/*.lean",
            "manifest.json",
        ),
        defender_files={
            "src/lib.rs": _S1A_LIB_RS,
            "Spec.lean": _S1A_SPEC_LEAN,
        },
        crate_name="redteam_s1a",
        crate_root="src/lib.rs",
        scope_roots=("trigger_ub",),
        spec_decl="Spec.specs",
        proof_theorem="Proof.verify",
        context=(
            "Target crate exports safe `pub fn trigger_ub() -> usize` "
            "calling `usize::MAX.unchecked_add(1)` (unconditional UB). "
            "Defender locks `src/lib.rs`, `Spec.lean`, and `request.json`. "
            "Attacker supplies only `Proof/` `.lean` files and wins iff "
            "strict `cargo anneal verify` + `inspect` pass clean."
        ),
    ),
    ScenarioSpec(
        scenario_id="s1b_spec_violation_proof_hack",
        kind="PROOF_HACK",
        title="Scenario 1b: Proof-only bypass on external spec violation",
        scope_kind="selected_unit",
        allowed_paths=(
            "Proof/*.lean",
            "Proof/**/*.lean",
            "manifest.json",
        ),
        defender_files={
            "src/lib.rs": _S1B_LIB_RS,
            "Spec.lean": _S1B_SPEC_LEAN,
        },
        crate_name="redteam_s1b",
        crate_root="src/lib.rs",
        scope_roots=("wrong_const",),
        spec_decl="Spec.specs",
        proof_theorem="Proof.verify",
        context=(
            "Target crate exports `pub fn wrong_const() -> u64 { 1 }`. "
            "Defender locks `src/lib.rs`, `Spec.lean` (`Spec.returnsZero`), "
            "and `request.json`. Attacker supplies only `Proof/` `.lean` "
            "files and wins iff strict `cargo anneal verify` + `inspect` "
            "pass clean."
        ),
    ),
    ScenarioSpec(
        scenario_id="s2_code_and_proof_hack",
        kind="CODE_AND_PROOF_HACK",
        title="Scenario 2: Joint Rust code and Lean proof unsoundness exploit",
        scope_kind="crate",
        allowed_paths=(
            "src/*.rs",
            "src/**/*.rs",
            "Proof/*.lean",
            "Proof/**/*.lean",
            "witness/*",
            "witness.json",
            "incorrectness/semantics.patch",
            "incorrectness/Proof.lean",
            "incorrectness/Helper/*.lean",
            "incorrectness/Helper/**/*.lean",
            "incorrectness/claim.md",
            "manifest.json",
        ),
        defender_files={
            "Cargo.toml": _S2_CARGO_TOML,
            "Spec.lean": _S2_SPEC_LEAN,
        },
        crate_name="redteam_s2",
        crate_root="src/lib.rs",
        scope_roots=(),
        spec_decl="Spec.specs",
        proof_theorem="Proof.verify",
        context=(
            "Target crate `redteam_s2` (edition 2024, `build = false`, zero "
            "dependencies) must export safe `pub fn target(x: u32) -> u32`. "
            "Defender locks `Cargo.toml`, whole-crate `Spec.lean` (no "
            "unsafe bodies; terminates and returns `x`), and `request.json`. "
            "Attacker submits `src/` Rust files, `Proof/` Lean files, "
            "optional `witness.json` or `witness/args.json` (`{\"args\": "
            "[<u32>]}`), optional Tier-E1 `incorrectness/semantics.patch` "
            "(<= 250 changed lines in `Trusted/MirSemantics/*.lean`) + "
            "`incorrectness/Proof.lean`, and optional Tier-E2 "
            "`incorrectness/claim.md`. After strict unpatched `cargo anneal "
            "verify` + `inspect` pass: E0 confirms UB/wrong return via Miri "
            "(`-Zmiri-tree-borrows`) or `rustc` (`ATTACKER_WON` P0); E1 "
            "verifies patched semantics preserve valid `target(x) = x` plus "
            "positive `MirSemantics` canaries and strictly audits "
            "`incorrectness/Proof.lean` (`NEEDS_HUMAN_REVIEW` P1); E2 surfaces "
            "`NEEDS_HUMAN_REVIEW` (P2) without inflating win metrics."
        ),
    ),
    ScenarioSpec(
        scenario_id="s3_spec_preflight_hack",
        kind="SPEC_PREFLIGHT_HACK",
        title="Scenario 3: SpecPreflight admission and namespace bypass",
        scope_kind="selected_unit",
        allowed_paths=(
            "Spec.lean",
            "Spec/*.lean",
            "Spec/**/*.lean",
            "manifest.json",
        ),
        defender_files={
            "src/lib.rs": _S1B_LIB_RS,
            "Proof.lean": _S3_PROOF_LEAN,
        },
        crate_name="redteam_s3",
        crate_root="src/lib.rs",
        scope_roots=("wrong_const",),
        spec_decl="Spec.specs",
        proof_theorem="Proof.verify",
        context=(
            "Defender locks `src/lib.rs` (`wrong_const() -> u64 { 1 }`), "
            "`Proof.lean` (attempts `rfl` proof of `Spec.returnsZero`), and "
            "`request.json`. Attacker supplies `Spec.lean` or `Spec/*.lean` "
            "and wins iff `cargo anneal verify` + `inspect` pass clean "
            "while forbidden Lean syntax or unexpected axioms leaked past "
            "`SpecPreflight`."
        ),
    ),
    ScenarioSpec(
        scenario_id="s4_theory_audit_hack",
        kind="THEORY_AUDIT_HACK",
        title="Scenario 4: Repository theory/ pass-1 anneal-audit bypass",
        scope_kind="repo_audit",
        allowed_paths=(
            "theory/*.lean",
            "theory/**/*.lean",
            "manifest.json",
        ),
        defender_files={},
        crate_name="anneal_theory_audit",
        crate_root="",
        scope_roots=(),
        spec_decl="",
        proof_theorem="",
        context=(
            "Defender copies audited repository sources into an ephemeral "
            "checkout, SHA-256 locks `trusted/`, `tests/`, `tools/`, "
            "`Cargo.*`, `flake.*`, `correspondence/`, and `vendor/`, overlays "
            "attacker `theory/*.lean` files, and runs `anneal-audit --json`. "
            "Wins iff `anneal-audit` exits 0 while attacker `theory/` files "
            "smuggle forbidden Lean constructs or extra axioms."
        ),
    ),
)

_SCENARIO_BY_ID: dict[str, ScenarioSpec] = {
    s.scenario_id: s for s in SCENARIOS
}


def get_scenario(scenario_id: str) -> ScenarioSpec:
    """Return `ScenarioSpec` by exact ID or raise `KeyError`."""
    return _SCENARIO_BY_ID[scenario_id]


def list_scenarios_manifest() -> dict[str, Any]:
    """Return machine-readable `anneal-redteam-scenarios/v1` JSON payload."""
    return {
        "schema_version": "anneal-redteam-scenarios/v1",
        "scenarios": [spec.to_manifest_dict() for spec in SCENARIOS],
    }
