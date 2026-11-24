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

/-- The MIR value of the `usize` word `n` (an unsigned `isize`-width scalar).
-/
def usizeVal (n : UsizeWord) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n.toNat⟩

def addScaledMetadataId : String :=
  "rust-path-v1::layout::add_scaled_metadata"

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Caller safety precondition of `unsafe fn add_scaled_metadata(base:
usize, metadata: usize, multiple: usize) -> usize` (`layout.rs`), whose
`# Safety` section reads: "`base + metadata * multiple`, evaluated over the
mathematical nonnegative integers, must not exceed `usize::MAX`." Callers
invoke exactly `layout::add_scaled_metadata` with three `usize` words `b`,
`m`, and `k` whose natural-number value `b + m * k` is below `2^64` (that is,
at most `usize::MAX` on the 64-bit target). The
precondition is non-vacuous: `b = m = k = 0` satisfies it. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  identity = addScaledMetadataId ∧
  ∃ b m k : UsizeWord,
    args = [usizeVal b, usizeVal m, usizeVal k] ∧
    b.toNat + m.toNat * k.toNat < 2 ^ 64

/-- Functional specification of `layout::add_scaled_metadata` ("Computes
the affine destination-metadata map", `layout.rs`), matching its Kani
contract, which `ensures` that `metadata.checked_mul(multiple).and_then(
|scaled| base.checked_add(scaled)) == Some(result)` whenever the `requires`
clause holds:
1. The unit holds exactly one body, `layout::add_scaled_metadata`;
2. The body is an `unsafe fn` (`isUnsafe = true`) of three arguments;
3. For every `base`, `metadata`, and `multiple` satisfying the safety
   precondition (`base + metadata * multiple < 2^64`), the call terminates
   (`¬ Diverges`), never faults or hits undefined behavior (`SatisfiesPost`,
   which includes `WellFormed`), and returns the exact `usize` word
   `base + metadata * multiple`. -/
noncomputable def addScaledMetadataSpec (program : Program) : Prop :=
  program.bodies.length = 1 ∧
  ∃ defId body,
    getElem? program.bodies defId = some body ∧
    body.identity = addScaledMetadataId ∧
    body.isUnsafe = true ∧
    body.argumentCount = 3 ∧
    ∀ b m k : UsizeWord,
      b.toNat + m.toNat * k.toNat < 2 ^ 64 →
      ReturnsTotal program defId [usizeVal b, usizeVal m, usizeVal k]
        (usizeVal (BitVec.ofNat 64 (b.toNat + m.toNat * k.toNat)))

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, addScaledMetadataSpec⟩

end Spec

end
