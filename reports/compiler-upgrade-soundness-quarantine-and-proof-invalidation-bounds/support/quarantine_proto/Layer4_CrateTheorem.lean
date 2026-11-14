-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore
import Layer1_Adapter_1991
import Layer1_Adapter_1100
import Layer2_RuleRegistry
import Layer3_Target_x86_64
import Layer3_Target_aarch64
import Layer3_Target_i686

namespace Anneal.QuarantineProto

theorem end_to_end_productive_compiles_x86_64
    (quarantined : Bool) (fid : Nat) (fs : FrontendStmt1100) :
    ProductiveCompiles targetSpec_x86_64 (adapt1100 fs) (runRegisteredRule quarantined fid (adapt1100 fs)) :=
  ⟨targetSpec_x86_64_valid, runRegisteredRule_sound quarantined fid (adapt1100 fs)⟩

theorem end_to_end_productive_compiles_i686
    (quarantined : Bool) (fid : Nat) (fs : FrontendStmt1100) :
    ProductiveCompiles targetSpec_i686 (adapt1100 fs) (runRegisteredRule quarantined fid (adapt1100 fs)) :=
  ⟨targetSpec_i686_valid, runRegisteredRule_sound quarantined fid (adapt1100 fs)⟩

#print axioms end_to_end_productive_compiles_x86_64
#print axioms end_to_end_productive_compiles_i686

end Anneal.QuarantineProto
