-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def u32Val (x : BitVec 32) : Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 x.toNat⟩

def u64Val (x : BitVec 64) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 x.toNat⟩

/-- Totality and block-identity injectivity of Fuchsia's
`fuchsia_merkle_core::make_identity(length, level, offset) -> [u8; 12]`:
1. `make_identity` terminates cleanly for all `(length, level, offset)`.
2. For any two 8192-byte-aligned offsets (`offset % 8192 = 0`) and bounded
   tree levels (`level < 8192`), equal 12-byte outputs force equal
   `(length, level, offset)` triples. -/
noncomputable def makeIdentitySpec (program : Program) : Prop :=
  (∀ (length : BitVec 32) (level offset : BitVec 64),
    ∃ out : Val, ∃ cm : CallerMemory,
      Behavior (entryProgForBody program 0)
        { args := [u32Val length, u64Val level, u64Val offset] }
        (.returned ⟨out, cm⟩)) ∧
  (∀ (len₁ len₂ : BitVec 32) (lvl₁ lvl₂ off₁ off₂ : BitVec 64)
     (out : Val) (cm₁ cm₂ : CallerMemory),
    off₁.toNat % 8192 = 0 →
    off₂.toNat % 8192 = 0 →
    lvl₁.toNat < 8192 →
    lvl₂.toNat < 8192 →
    Behavior (entryProgForBody program 0)
      { args := [u32Val len₁, u64Val lvl₁, u64Val off₁] }
      (.returned ⟨out, cm₁⟩) →
    Behavior (entryProgForBody program 0)
      { args := [u32Val len₂, u64Val lvl₂, u64Val off₂] }
      (.returned ⟨out, cm₂⟩) →
    len₁ = len₂ ∧ lvl₁ = lvl₂ ∧ off₁ = off₂)

noncomputable def specs : Specs := ⟨fun _ _ => False, makeIdentitySpec⟩

end Spec
