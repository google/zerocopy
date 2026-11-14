-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore

namespace Anneal.QuarantineProto

/-- Parameterized interface firewall for any HybridTrace optimization rule family. -/
structure VerifiedOptRule where
  familyId : Nat
  name : String
  rewrite : CoreStmt → CoreStmt
  rewrite_sound : ∀ (s : CoreStmt) (st : MachState), evalStmt (rewrite s) st = evalStmt s st

/-- Soundness Quarantine combinator: when `quarantined = true` (or a candidate rule is
disabled in the registry), falls back to the identity rewrite `s` with zero `sorryAx`. -/
def applyWithQuarantine (quarantined : Bool) (rule : Option VerifiedOptRule) (s : CoreStmt) : CoreStmt :=
  match quarantined, rule with
  | false, some r => r.rewrite s
  | _, _ => s

theorem applyWithQuarantine_sound (quarantined : Bool) (rule : Option VerifiedOptRule) (s : CoreStmt) :
    StmtDeriv s (applyWithQuarantine quarantined rule s) := by
  refine ⟨fun st => ?_⟩
  cases quarantined with
  | false =>
    cases rule with
    | none => rfl
    | some r => exact r.rewrite_sound s st
  | true => rfl

end Anneal.QuarantineProto
