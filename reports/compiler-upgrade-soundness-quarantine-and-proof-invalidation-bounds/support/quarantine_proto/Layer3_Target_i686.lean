-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore

namespace Anneal.QuarantineProto

def targetSpec_i686 : TargetAbiSpec := {
  triple := "i686-unknown-linux-gnu",
  intArgRegs := 3,
  floatInVectorRegs := false
}

theorem targetSpec_i686_valid : targetSpec_i686.intArgRegs > 0 := by decide

end Anneal.QuarantineProto
