-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics
import Endianness

namespace Spec

open Trusted.MirAst Trusted.MirSemantics Endianness

/-- Call `program` at entry body `0` on `args` and reach normal return `ret`
with empty caller memory. -/
noncomputable def ReturnsVal (program : Program) (args : List Val)
    (ret : Val) : Prop :=
  Behavior (entryProgForBody program 0) { args := args } (.returned ⟨ret, ⟨[]⟩⟩)

/-- The selected function returns the reversed bytes within its chosen width. -/
noncomputable def exactReversal (program : Program) (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
    ReturnsVal program (bodyEndianArgs body true width.val value)
      (u64Val output) ∧
    ByteReversal (8 * 2 ^ width.val) value output

/-- Little-endian conversion on this target keeps exactly the chosen width. -/
noncomputable def exactLittleEndian (program : Program) (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
    ReturnsVal program (bodyEndianArgs body false width.val value)
      (u64Val output) ∧
    output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1)

/-- Two completed big-endian conversions recover the masked input. -/
noncomputable def involution (program : Program) (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ first second : Word,
    ReturnsVal program (bodyEndianArgs body true width.val value)
      (u64Val first) ∧
    ReturnsVal program (bodyEndianArgs body true width.val first)
      (u64Val second) ∧
    second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1)

noncomputable def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program => ∃ body, program.bodies = [body] ∧
      exactReversal program body ∧
      exactLittleEndian program body ∧
      involution program body }

end Spec
