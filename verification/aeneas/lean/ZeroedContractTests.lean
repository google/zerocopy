/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Zeroed
public import Proofs.FromBytes
public import RequiredModelContracts.Zeroed
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- The independent expectation rejects failure, divergence, and a valid Boolean
-- with the wrong value. These are model tests, not executions of invalid Rust.
example : Obligations.new_zeroed_spec := by
  intro Self meaning
  exact required_new_zeroed Self (FromZeros.new_zeroed.default Self)
    (new_zeroed_spec Self)

example : ¬ @Obligations.new_zeroed_spec_contract Bool modelBool (.fail .undef) := by
  intro expected
  obtain ⟨raw, _, _, executed, _⟩ := expected Bool.Insts.ZerocopyFromZeros
  simp at executed

example : ¬ @Obligations.new_zeroed_spec_contract Bool modelBool .div := by
  intro expected
  obtain ⟨raw, _, _, executed, _⟩ := expected Bool.Insts.ZerocopyFromZeros
  simp at executed

example : ¬ @Obligations.new_zeroed_spec_contract Bool modelBool (.ok true) := by
  intro expected
  obtain ⟨raw, _, decoder, executed, available, physical, _⟩ :=
    expected Bool.Insts.ZerocopyFromZeros
  have same : raw = true := by simpa using executed.symm
  subst raw
  change some Rust.Storage.boolDecoder = some decoder at available
  cases Option.some.inj available
  change some false = some true at physical
  contradiction

end Zerocopy.Proofs
