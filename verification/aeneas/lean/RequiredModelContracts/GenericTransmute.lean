/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import Obligations.GenericTransmute
public import RequiredContracts
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

/-- Expand the authored byte relation for the same arbitrary outcome. This
adapter does not use the native helper's correctness theorem. -/
@[contract_simps] theorem required_transmute_copy (Src Dst : Type)
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst] (run : Result Dst)
    (provided : Specs.transmute_copy_spec_contract Src Dst source destination src run) :
    Obligations.transmute_copy_spec_contract Src Dst source destination src ms md run := by
  intro sourceLaw destinationLaw zeroLaw mathSrc decoded sameSize
  obtain ⟨raw, executed, math, admitted, related⟩ :=
    (WP.spec_equiv_exists run _).mp (provided mathSrc decoded sameSize)
  obtain ⟨bytes, sourcePhysical, destinationPhysical⟩ := related
  cases hs : ms.representation with
  | none => simp [RustModel.represented, hs] at sourcePhysical
  | some sd =>
    cases hd : md.representation with
    | none => simp [RustModel.represented, hd] at destinationPhysical
    | some dd =>
      exact ⟨raw, math, executed, admitted, bytes, sd, dd, rfl, rfl,
        by simpa only [RustModel.represented, hs] using sourcePhysical,
        by simpa only [RustModel.represented, hd] using destinationPhysical⟩

@[contract_simps] theorem required_transmute_copy_caller (Src Dst : Type)
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst] (run : Result Dst)
    (provided : Specs.transmute_copy_caller_spec_contract Src Dst source destination src run) :
    Obligations.transmute_copy_caller_spec_contract Src Dst source destination src ms md run := by
  exact required_transmute_copy Src Dst source destination src run provided

end Zerocopy.Proofs
