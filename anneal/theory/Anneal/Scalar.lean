-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.BitVec
public import Anneal.BitVecArith
public import Anneal.InitLemmas
public import Anneal.LeBytes
public import Anneal.LinearArith
public import Anneal.ListChunks
public import Anneal.NatBitwise

-- Domain-scoped umbrella for pure constructive scalar, bitwise, bitvector,
-- endian byte-layout, chunking, linear-arithmetic, and foundation lemmas
-- (excluding `Trusted.*`, MIR weakest-precondition machinery, and classical
-- choice).
