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
import Anneal.BitVecArith
import Anneal.LeBytes
import Anneal.ListChunks
import Anneal.MirWp
import Anneal.LoopInv
import Anneal.LinearArith
import Anneal.SpineForce
import Anneal.PTree
import Anneal.BitTrieLrat
import Anneal.InitLemmas
import Anneal.ClassicalEm
import Anneal.MirTotal
import Anneal.Core
import Anneal.ByteSubLens
import Anneal.PureLift

namespace Anneal

/-!
# Anneal Theory Umbrella

Umbrella module for Anneal's untrusted proof theory (`theory/`), re-exporting
`Trusted`, the reusable 3-axiom proof libraries (`Anneal.NatBitwise`,
`Anneal.BitVec`, `Anneal.BitVecArith`, `Anneal.LeBytes`, `Anneal.ListChunks`,
`Anneal.LoopInv`, `Anneal.LinearArith`, `Anneal.SpineForce`, `Anneal.PTree`,
`Anneal.BitTrieLrat`, `Anneal.InitLemmas`, and `Anneal.ClassicalEm`), the
fuel-bounded MIR weakest-precondition machinery (`Anneal.MirWp`), the computable
MIR step mirrors and unbounded-depth bridges (`Anneal.MirTotal`), the
block-tree, separation-logic, and stage-cut core (`Anneal.Core`), lawful
sub-allocation byte lenses and `&mut` method call summaries
(`Anneal.ByteSubLens`), and `Anneal.PureLift`.
-/

end Anneal
