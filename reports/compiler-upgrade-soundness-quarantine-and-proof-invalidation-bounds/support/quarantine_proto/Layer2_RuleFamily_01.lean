-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore
import Layer2_RuleInterface

namespace Anneal.QuarantineProto

def ruleFamily_01_rewrite (s : CoreStmt) : CoreStmt :=
  match s with
  | .nop => .nop
  | .assign dst rhs => .assign dst rhs

theorem ruleFamily_01_sound (s : CoreStmt) (st : MachState) :
    evalStmt (ruleFamily_01_rewrite s) st = evalStmt s st := by
  cases s <;> rfl

def ruleFamily_01 : VerifiedOptRule := {
  familyId := 1,
  name := "AddZeroFold",
  rewrite := ruleFamily_01_rewrite,
  rewrite_sound := ruleFamily_01_sound
}

end Anneal.QuarantineProto
