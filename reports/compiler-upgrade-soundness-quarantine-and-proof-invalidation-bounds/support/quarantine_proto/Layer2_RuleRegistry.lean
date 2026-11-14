-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore
import Layer2_RuleInterface
import Layer2_RuleFamily_01
import Layer2_RuleFamily_02
import Layer2_RuleFamily_03
import Layer2_RuleFamily_04
import Layer2_RuleFamily_05
import Layer2_RuleFamily_06
import Layer2_RuleFamily_07
import Layer2_RuleFamily_08

namespace Anneal.QuarantineProto

def lookupRuleFamily (fid : Nat) : Option VerifiedOptRule :=
  match fid with
  | 1 => some ruleFamily_01
  | 2 => some ruleFamily_02
  | 3 => some ruleFamily_03
  | 4 => some ruleFamily_04
  | 5 => some ruleFamily_05
  | 6 => some ruleFamily_06
  | 7 => some ruleFamily_07
  | 8 => some ruleFamily_08
  | _ => none

def runRegisteredRule (quarantined : Bool) (fid : Nat) (s : CoreStmt) : CoreStmt :=
  applyWithQuarantine quarantined (lookupRuleFamily fid) s

theorem runRegisteredRule_sound (quarantined : Bool) (fid : Nat) (s : CoreStmt) :
    StmtDeriv s (runRegisteredRule quarantined fid s) :=
  applyWithQuarantine_sound quarantined (lookupRuleFamily fid) s

end Anneal.QuarantineProto
