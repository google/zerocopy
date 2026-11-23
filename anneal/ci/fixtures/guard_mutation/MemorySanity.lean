-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Memory

/-!
# Positive Memory Sanity Check for Guard-Mutation CI

Confirms that ordinary in-bounds, aligned, live, mutable stack allocation,
write, read, and deallocation continue to succeed on every single-guard mutant
of `Trusted/MirSemantics/Memory.lean`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

theorem positive_sanity_memory_roundtrip :
    (let (m1, p) := allocateStack MemoryState.empty ⟨4, 2⟩
     let bs : List AllocByte :=
       [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
     match writeBytes m1 p 2 bs with
     | .error _ => False
     | .ok m2 =>
       match readBytes m2 p 4 2 with
       | .error _ => False
       | .ok got =>
         match deallocateStack m2 p with
         | .error _ => False
         | .ok _ => got = bs) :=
  rfl

end GuardMutation
