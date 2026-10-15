/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import TraitLaws
public import TransmuteModel
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.Obligations

/-- The independent domain spells out size-query success and its agreement
with both physical widths. The result must decode from the source's same bytes.
Neither the domain nor the postcondition depends on the implementation. -/
def transmute_copy_spec_contract (Src Dst : Type)
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    (ms : RustModel Src) (md : RustModel Dst) (run : Result Dst) : Prop :=
  ∀ [_sourceLaw : @TraitLaws.into_bytes_initialized Src source ms]
    [_destinationLaw : @TraitLaws.from_bytes_valid Dst destination md]
    [_zeroLaw : @TraitLaws.from_zeros_valid Dst destination.FromZerosInst md]
    (mathSrc : ms.Model), ms.decode src = some mathSrc →
    (∃ width : Usize, core.mem.size_of Src = .ok width ∧ core.mem.size_of Dst = .ok width ∧
      ms.representation.map (·.byteSize) = some width.val ∧
      md.representation.map (·.byteSize) = some width.val) →
    ∃ raw math, run = .ok raw ∧ md.decode raw = some math ∧
      ∃ (bytes : List AMByte) (sd : BitDecoder Src) (dd : BitDecoder Dst),
        ms.representation = some sd ∧ md.representation = some dd ∧
        sd.run bytes = some src ∧ dd.run bytes = some raw

def transmute_copy_spec : Prop :=
  ∀ (Src Dst : Type) (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst],
    @transmute_copy_spec_contract Src Dst source destination src ms md
      (@util.macro_util.transmute_copy Src Dst source destination src ms md)

/-- Both APIs promise the same relation for an arbitrary supplied outcome. -/
def transmute_copy_caller_spec_contract (Src Dst : Type)
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    (ms : RustModel Src) (md : RustModel Dst) (run : Result Dst) : Prop :=
  @transmute_copy_spec_contract Src Dst source destination src ms md run

def transmute_copy_caller_spec : Prop :=
  ∀ (Src Dst : Type) (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst],
    @transmute_copy_caller_spec_contract Src Dst source destination src ms md
      (@util.generic_transmute.transmute_copy_caller Src Dst source destination src ms md)

end Zerocopy.Obligations
