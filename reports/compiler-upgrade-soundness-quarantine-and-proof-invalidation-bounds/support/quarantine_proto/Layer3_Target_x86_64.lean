-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore

namespace Anneal.QuarantineProto

def targetSpec_x86_64 : TargetAbiSpec := {
  triple := "x86_64-unknown-linux-gnu",
  intArgRegs := 6,
  floatInVectorRegs := true
}

theorem targetSpec_x86_64_valid : targetSpec_x86_64.intArgRegs > 0 := by decide

end Anneal.QuarantineProto
