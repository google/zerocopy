/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import TraitLaws
public import RustRepresentation
@[expose] public section

/-!
Each law names an actual extracted implementation dictionary and retains its
canonical mathematical provider. Primitive laws use the shared representation
proofs. Arrays preserve the original type, length, and element dictionary, then
use that element's provider and trait laws. These are representation-admission
proofs; Rust layout correspondence and method-body correctness are separate
obligations.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

@[instance] theorem Tuple.Insts.ZerocopyFromZeros_law :
    TraitLaws.from_zeros_valid Unit Zerocopy.Tuple.Insts.ZerocopyFromZeros :=
  ⟨zeroUnit⟩

@[instance] theorem Tuple.Insts.ZerocopyFromBytes_law :
    TraitLaws.from_bytes_valid Unit Zerocopy.Tuple.Insts.ZerocopyFromBytes :=
  ⟨completeUnit⟩

@[instance] theorem U8.Insts.ZerocopyFromZeros_law :
    TraitLaws.from_zeros_valid U8 Zerocopy.U8.Insts.ZerocopyFromZeros :=
  ⟨zeroUScalar .U8⟩

@[instance] theorem U8.Insts.ZerocopyFromBytes_law :
    TraitLaws.from_bytes_valid U8 Zerocopy.U8.Insts.ZerocopyFromBytes :=
  ⟨completeUScalar .U8⟩

@[instance] theorem U32.Insts.ZerocopyFromZeros_law :
    TraitLaws.from_zeros_valid U32 Zerocopy.U32.Insts.ZerocopyFromZeros :=
  ⟨zeroUScalar .U32⟩

@[instance] theorem U32.Insts.ZerocopyFromBytes_law :
    TraitLaws.from_bytes_valid U32 Zerocopy.U32.Insts.ZerocopyFromBytes :=
  ⟨completeUScalar .U32⟩

@[instance] theorem Bool.Insts.ZerocopyFromZeros_law :
    TraitLaws.from_zeros_valid Bool Zerocopy.Bool.Insts.ZerocopyFromZeros :=
  ⟨zeroBool⟩

@[instance] theorem Array.Insts.ZerocopyFromZeros_law
    {T : Type} (N : Usize) (dictionary : FromZeros T) [meaning : RustModel T]
    [law : TraitLaws.from_zeros_valid T dictionary] :
    TraitLaws.from_zeros_valid (Aeneas.Std.Array T N)
      (Zerocopy.Array.Insts.ZerocopyFromZeros N dictionary) :=
  ⟨RustModel.zero_array T N
    (@TraitLaws.from_zeros_valid.holds T dictionary meaning law)⟩

-- FromBytes also supplies its actual FromZeros parent dictionary's law. The
-- complete array proof uses the stronger element admission promise, while the
-- theorem retains both premises required by that native trait bound.
@[instance] theorem Array.Insts.ZerocopyFromBytes_law
    {T : Type} (N : Usize) (dictionary : FromBytes T) [meaning : RustModel T]
    [law : TraitLaws.from_bytes_valid T dictionary]
    [_parentLaw : TraitLaws.from_zeros_valid T dictionary.FromZerosInst] :
    TraitLaws.from_bytes_valid (Aeneas.Std.Array T N)
      (Zerocopy.Array.Insts.ZerocopyFromBytes N dictionary) :=
  ⟨RustModel.complete_array T N
    (@TraitLaws.from_bytes_valid.holds T dictionary meaning law)⟩

end Zerocopy.Proofs
