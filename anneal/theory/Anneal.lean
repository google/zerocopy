-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Trusted
public import Anneal.NatBitwise
public import Anneal.BitVec
public import Anneal.BitVecArith
public import Anneal.LeBytes
public import Anneal.ListChunks
public import Anneal.MirWp
public import Anneal.LoopInv
public import Anneal.LinearArith
public import Anneal.SpineForce
public import Anneal.PTree
public import Anneal.BitTrieLrat
public import Anneal.InitLemmas
public import Anneal.ClassicalEm
public import Anneal.Firewall

public section

namespace Anneal

/-!
# Anneal Theory Umbrella

Umbrella module for Anneal's untrusted proof theory (`theory/`), re-exporting
`Trusted`, the reusable 3-axiom proof libraries (`Anneal.NatBitwise`,
`Anneal.BitVec`, `Anneal.BitVecArith`, `Anneal.LeBytes`, `Anneal.ListChunks`,
`Anneal.LoopInv`, `Anneal.LinearArith`, `Anneal.SpineForce`, `Anneal.PTree`,
`Anneal.BitTrieLrat`, `Anneal.InitLemmas`, `Anneal.ClassicalEm`, and
`Anneal.Firewall`), and the fuel-bounded MIR weakest-precondition machinery
(`Anneal.MirWp`).
-/

end Anneal

end
