-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Data.BitVec.BasicAux
public import Trusted.MirSemantics

@[expose] public section

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

abbrev UsizeWord := BitVec 64

def usizeVal (n : UsizeWord) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n.toNat⟩

def fromElemCountId : String :=
  "rust-path-v1::<() as PointerMetadata>::from_elem_count"

def toElemCountId : String :=
  "rust-path-v1::<() as PointerMetadata>::to_elem_count"

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous caller domain precondition admitting all `usize` counts for
`<() as PointerMetadata>::from_elem_count` and `()` for `to_elem_count`. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  (identity = fromElemCountId ∧ ∃ n : UsizeWord, args = [usizeVal n]) ∨
  (identity = toElemCountId ∧ args = [.unit])

/-- Functional specification derived from `PointerMetadata` docs (`lib.rs`)
and `Ref::{new_sized_unchecked, new_unchecked, pointer_metadata}` (`ref.rs`):
1. Exact two-body unit containing `<() as PointerMetadata>::{from,to}_elem_count`
   as safe functions (`isUnsafe = false`);
2. `from_elem_count(n) = ()` universally for all `2^64` `usize` inputs;
3. `to_elem_count(()) = 0usize`;
4. Round-trip invariants (`from(to(())) = ()` and `to(from(n)) = 0usize`). -/
noncomputable def pointerMetadataUnitSpec (program : Program) : Prop :=
  program.bodies.length = 2 ∧
  ∃ defFrom bodyFrom defTo bodyTo,
    getElem? program.bodies defFrom = some bodyFrom ∧
    bodyFrom.identity = fromElemCountId ∧
    bodyFrom.isUnsafe = false ∧
    getElem? program.bodies defTo = some bodyTo ∧
    bodyTo.identity = toElemCountId ∧
    bodyTo.isUnsafe = false ∧
    (∀ n : UsizeWord,
      ReturnsTotal program defFrom [usizeVal n] .unit) ∧
    ReturnsTotal program defTo [.unit] (usizeVal 0) ∧
    (ReturnsTotal program defTo [.unit] (usizeVal 0) ∧
      ReturnsTotal program defFrom [usizeVal 0] .unit) ∧
    (∀ n : UsizeWord,
      ReturnsTotal program defFrom [usizeVal n] .unit ∧
      ReturnsTotal program defTo [.unit] (usizeVal 0))

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, pointerMetadataUnitSpec⟩

end Spec

end
