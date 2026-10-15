/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredModelContracts.GenericTransmute
public import Proofs.GenericTransmute
import all Proofs.GenericTransmute
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.Proofs

check_contract Obligations.transmute_copy_spec using transmute_copy_spec
check_contract Obligations.transmute_copy_caller_spec using transmute_copy_caller_spec

section
variable {Src Dst : Type} (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
  [ms : RustModel Src] [md : RustModel Dst]
  [sourceLaw : @TraitLaws.into_bytes_initialized Src source ms]
  [destinationLaw : @TraitLaws.from_bytes_valid Dst destination md]
  [zeroLaw : @TraitLaws.from_zeros_valid Dst destination.FromZerosInst md]
  (mathSrc : ms.Model) (decoded : ms.decode src = some mathSrc)
  (width : Usize) (sourceSize : core.mem.size_of Src = .ok width)
  (destinationSize : core.mem.size_of Dst = .ok width)
  (sourceWidth : ms.representation.map (·.byteSize) = some width.val)
  (destinationWidth : md.representation.map (·.byteSize) = some width.val)

example (error : Error) :
    ¬ Obligations.transmute_copy_spec_contract Src Dst source destination src ms md (.fail error) := by
  intro expected
  obtain ⟨raw, _, executed, _⟩ := expected mathSrc decoded
    ⟨width, sourceSize, destinationSize, sourceWidth, destinationWidth⟩
  simp at executed

example :
    ¬ Obligations.transmute_copy_caller_spec_contract Src Dst source destination src ms md .div := by
  intro expected
  obtain ⟨raw, _, executed, _⟩ := expected mathSrc decoded
    ⟨width, sourceSize, destinationSize, sourceWidth, destinationWidth⟩
  simp at executed

-- Even an admitted output is insufficient when it cannot share source bytes.
example (wrong : Dst) (mathWrong : md.Model) (_admitted : md.decode wrong = some mathWrong)
    (noShared : ∀ (bytes : List AMByte) (sd : BitDecoder Src) (dd : BitDecoder Dst),
      ms.representation = some sd → md.representation = some dd →
      sd.run bytes = some src → dd.run bytes ≠ some wrong) :
    ¬ Obligations.transmute_copy_spec_contract Src Dst source destination src ms md (.ok wrong) := by
  intro expected
  obtain ⟨raw, _, executed, _, bytes, sd, dd, hs, hd, sourcePhysical, destinationPhysical⟩ :=
    expected mathSrc decoded ⟨width, sourceSize, destinationSize, sourceWidth, destinationWidth⟩
  have equal : wrong = raw := by simpa using executed
  subst raw
  exact noShared bytes sd dd hs hd sourcePhysical destinationPhysical
end

end Zerocopy.Proofs
