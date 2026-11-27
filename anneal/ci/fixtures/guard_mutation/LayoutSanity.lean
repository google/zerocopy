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
import Trusted.MirSemantics.Bytes

/-!
# Positive Layout Sanity Check for Guard-Mutation CI

Confirms that aligned indirect `storeIndirect` / `loadIndirect` roundtrips for
integers, `char`, and overflow pairs continue to succeed on every single-guard
mutant of `Trusted/MirSemantics/Layout.lean`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Live mutable 32-byte, 16-byte-aligned (`alignLog2 = 4`) zero-initialized
memory containing allocation id `1`. -/
noncomputable def layoutSanityMem : MemoryState :=
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 4
      mutability := .mut
      bytes := List.replicate 32 (.init 0 none)
      live := true
    }] }

theorem positive_sanity_layout_roundtrips :
    (match storeIndirect layoutSanityMem (.int .i32 false) ⟨1, 0⟩
        (.scalar ⟨.i32, false, BitVec.ofNat 128 42⟩) with
     | .error _ => False
     | .ok m1 =>
       match loadIndirect m1 (.int .i32 false) ⟨1, 0⟩ with
       | .ok (some (.scalar ⟨.i32, false, bits⟩)) => bits == BitVec.ofNat 128 42
       | _ => False) ∧
    (match loadIndirect layoutSanityMem .char ⟨1, 0⟩ with
     | .ok (some (.char _)) => True
     | _ => False) ∧
    (match loadIndirect layoutSanityMem (.tuple [.int .i32 false, .bool])
        ⟨1, 0⟩ with
     | .ok (some (.tuple [_, .bool false])) => True
     | _ => False) :=
  ⟨rfl, trivial, trivial⟩

end GuardMutation
