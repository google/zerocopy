-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted
import Anneal.NatBitwise
import Anneal.BitVec
import Anneal.LeBytes
import Anneal.ListChunks
import Anneal.MirWp
import Anneal.PureLift

namespace Anneal

/-!
# Anneal Theory Umbrella

Umbrella module for Anneal's untrusted proof theory (`theory/`), re-exporting
`Trusted`, the reusable 3-axiom proof libraries (`Anneal.BitVec`,
`Anneal.LeBytes`, and `Anneal.ListChunks`), the fuel-bounded MIR
weakest-precondition machinery (`Anneal.MirWp`), and `Anneal.PureLift`.
-/

end Anneal
