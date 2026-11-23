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
  "rust-path-v1::<usize as PointerMetadata>::from_elem_count"

def toElemCountId : String :=
  "rust-path-v1::<usize as PointerMetadata>::to_elem_count"

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous caller domain precondition admitting every `usize` word on
the two `<usize as PointerMetadata>` methods and excluding extraneous paths or
argument shapes. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  (identity = fromElemCountId ∨ identity = toElemCountId) ∧
  ∃ n : UsizeWord, args = [usizeVal n]

/-- Functional specification derived from `PointerMetadata` docs (`lib.rs`)
and `Ref::{new_unchecked, pointer_metadata}` invariants (`ref.rs`):
1. Exact two-body unit containing
   `<usize as PointerMetadata>::{from,to}_elem_count` as safe functions
   (`isUnsafe = false`);
2. `from_elem_count(n) = n` universally over all `2^64` `usize` inputs;
3. `to_elem_count(m) = m` universally over all `2^64` `usize` inputs;
4. Two-way round-trip bijection (`to(from(n)) = n` and `from(to(m)) = m`). -/
noncomputable def pointerMetadataUsizeSpec (program : Program) : Prop :=
  program.bodies.length = 2 ∧
  ∃ defFrom bodyFrom defTo bodyTo,
    getElem? program.bodies defFrom = some bodyFrom ∧
    bodyFrom.identity = fromElemCountId ∧
    bodyFrom.isUnsafe = false ∧
    getElem? program.bodies defTo = some bodyTo ∧
    bodyTo.identity = toElemCountId ∧
    bodyTo.isUnsafe = false ∧
    (∀ n : UsizeWord,
      ReturnsTotal program defFrom [usizeVal n] (usizeVal n)) ∧
    (∀ m : UsizeWord,
      ReturnsTotal program defTo [usizeVal m] (usizeVal m)) ∧
    (∀ n : UsizeWord,
      ∃ mid : UsizeWord,
        ReturnsTotal program defFrom [usizeVal n] (usizeVal mid) ∧
        ReturnsTotal program defTo [usizeVal mid] (usizeVal n)) ∧
    (∀ m : UsizeWord,
      ∃ count : UsizeWord,
        ReturnsTotal program defTo [usizeVal m] (usizeVal count) ∧
        ReturnsTotal program defFrom [usizeVal count] (usizeVal m))

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, pointerMetadataUsizeSpec⟩

end Spec

end
