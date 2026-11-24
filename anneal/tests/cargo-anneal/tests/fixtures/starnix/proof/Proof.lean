-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Expected
import ProductionClaims

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Endianness ProductionReduction ProductionClaims

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      have same : sourceBody = body := Option.some.inj found
      subst body
      exact baseline _
    | succ id => cases found
  · exact ⟨sourceBody, rfl, bigEndian_exact, littleEndian_exact,
      bigEndian_involutive⟩

end Proof
