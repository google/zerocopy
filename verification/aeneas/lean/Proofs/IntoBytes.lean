/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/


module
public import Specs
public import TraitLaws
public import Proofs.TraitChecks
@[expose] public section

/-!
Each theorem names the actual extracted implementation dictionary. The final
audit checks its complete generic inputs and rejects additional assumptions.
The shared decoder lemmas supply the representation facts; these declarations
attach those facts to the unsafe impls visible in Rust. They do not assert that
every IntoBytes method body or every compilation configuration is verified.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

@[instance] theorem I8.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized I8 Zerocopy.I8.Insts.ZerocopyIntoBytes :=
  ⟨initializedIScalar .I8⟩

@[instance] theorem U16.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized U16 Zerocopy.U16.Insts.ZerocopyIntoBytes :=
  ⟨initializedUScalar .U16⟩

@[instance] theorem I16.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized I16 Zerocopy.I16.Insts.ZerocopyIntoBytes :=
  ⟨initializedIScalar .I16⟩

@[instance] theorem U32.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized U32 Zerocopy.U32.Insts.ZerocopyIntoBytes :=
  ⟨initializedUScalar .U32⟩

@[instance] theorem I32.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized I32 Zerocopy.I32.Insts.ZerocopyIntoBytes :=
  ⟨initializedIScalar .I32⟩

@[instance] theorem U64.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized U64 Zerocopy.U64.Insts.ZerocopyIntoBytes :=
  ⟨initializedUScalar .U64⟩

@[instance] theorem I64.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized I64 Zerocopy.I64.Insts.ZerocopyIntoBytes :=
  ⟨initializedIScalar .I64⟩

@[instance] theorem U128.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized U128 Zerocopy.U128.Insts.ZerocopyIntoBytes :=
  ⟨initializedUScalar .U128⟩

@[instance] theorem I128.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized I128 Zerocopy.I128.Insts.ZerocopyIntoBytes :=
  ⟨initializedIScalar .I128⟩

@[instance] theorem Usize.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized Usize Zerocopy.Usize.Insts.ZerocopyIntoBytes :=
  ⟨initializedUScalar .Usize⟩

@[instance] theorem Isize.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized Isize Zerocopy.Isize.Insts.ZerocopyIntoBytes :=
  ⟨initializedIScalar .Isize⟩

@[instance] theorem Char.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized Char Zerocopy.Char.Insts.ZerocopyIntoBytes :=
  ⟨Rust.Storage.BitDecoder.filterMap_initialized _ _
    (Rust.Storage.integerDecoder_initialized 4 .little)⟩

-- Zero rejects NonZero construction; for Option it denotes a successfully
-- decoded None. Initialization follows the same full integer carrier.

@[instance] theorem core.num.nonzero.NonZeroU8NonZeroU8Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero U8 core.num.niche_types.NonZeroU8Inner)
      Zerocopy.core.num.nonzero.NonZeroU8NonZeroU8Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroUScalar .U8 core.num.niche_types.NonZeroU8Inner⟩

@[instance] theorem core.num.nonzero.NonZeroI8NonZeroI8Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero I8 core.num.niche_types.NonZeroI8Inner)
      Zerocopy.core.num.nonzero.NonZeroI8NonZeroI8Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroIScalar .I8 core.num.niche_types.NonZeroI8Inner⟩

@[instance] theorem core.num.nonzero.NonZeroU16NonZeroU16Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero U16 core.num.niche_types.NonZeroU16Inner)
      Zerocopy.core.num.nonzero.NonZeroU16NonZeroU16Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroUScalar .U16 core.num.niche_types.NonZeroU16Inner⟩

@[instance] theorem core.num.nonzero.NonZeroI16NonZeroI16Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero I16 core.num.niche_types.NonZeroI16Inner)
      Zerocopy.core.num.nonzero.NonZeroI16NonZeroI16Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroIScalar .I16 core.num.niche_types.NonZeroI16Inner⟩

@[instance] theorem core.num.nonzero.NonZeroU32NonZeroU32Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner)
      Zerocopy.core.num.nonzero.NonZeroU32NonZeroU32Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroUScalar .U32 core.num.niche_types.NonZeroU32Inner⟩

@[instance] theorem core.num.nonzero.NonZeroI32NonZeroI32Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero I32 core.num.niche_types.NonZeroI32Inner)
      Zerocopy.core.num.nonzero.NonZeroI32NonZeroI32Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroIScalar .I32 core.num.niche_types.NonZeroI32Inner⟩

@[instance] theorem core.num.nonzero.NonZeroU64NonZeroU64Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero U64 core.num.niche_types.NonZeroU64Inner)
      Zerocopy.core.num.nonzero.NonZeroU64NonZeroU64Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroUScalar .U64 core.num.niche_types.NonZeroU64Inner⟩

@[instance] theorem core.num.nonzero.NonZeroI64NonZeroI64Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero I64 core.num.niche_types.NonZeroI64Inner)
      Zerocopy.core.num.nonzero.NonZeroI64NonZeroI64Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroIScalar .I64 core.num.niche_types.NonZeroI64Inner⟩

@[instance] theorem core.num.nonzero.NonZeroU128NonZeroU128Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero U128 core.num.niche_types.NonZeroU128Inner)
      Zerocopy.core.num.nonzero.NonZeroU128NonZeroU128Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroUScalar .U128 core.num.niche_types.NonZeroU128Inner⟩

@[instance] theorem core.num.nonzero.NonZeroI128NonZeroI128Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero I128 core.num.niche_types.NonZeroI128Inner)
      Zerocopy.core.num.nonzero.NonZeroI128NonZeroI128Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroIScalar .I128 core.num.niche_types.NonZeroI128Inner⟩

@[instance] theorem core.num.nonzero.NonZeroUsizeNonZeroUsizeInner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner)
      Zerocopy.core.num.nonzero.NonZeroUsizeNonZeroUsizeInner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroUScalar .Usize core.num.niche_types.NonZeroUsizeInner⟩

@[instance] theorem core.num.nonzero.NonZeroIsizeNonZeroIsizeInner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (core.num.nonzero.NonZero Isize core.num.niche_types.NonZeroIsizeInner)
      Zerocopy.core.num.nonzero.NonZeroIsizeNonZeroIsizeInner.Insts.ZerocopyIntoBytes :=
  ⟨initializedNonZeroIScalar .Isize core.num.niche_types.NonZeroIsizeInner⟩

-- Zero rejects NonZero construction; for Option it denotes a successfully
-- decoded None. Initialization follows the same full integer carrier.

@[instance] theorem core.option.OptionNonZeroU8NonZeroU8Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero U8 core.num.niche_types.NonZeroU8Inner))
      Zerocopy.core.option.OptionNonZeroU8NonZeroU8Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroUScalar .U8 core.num.niche_types.NonZeroU8Inner⟩

@[instance] theorem core.option.OptionNonZeroI8NonZeroI8Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero I8 core.num.niche_types.NonZeroI8Inner))
      Zerocopy.core.option.OptionNonZeroI8NonZeroI8Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroIScalar .I8 core.num.niche_types.NonZeroI8Inner⟩

@[instance] theorem core.option.OptionNonZeroU16NonZeroU16Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero U16 core.num.niche_types.NonZeroU16Inner))
      Zerocopy.core.option.OptionNonZeroU16NonZeroU16Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroUScalar .U16 core.num.niche_types.NonZeroU16Inner⟩

@[instance] theorem core.option.OptionNonZeroI16NonZeroI16Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero I16 core.num.niche_types.NonZeroI16Inner))
      Zerocopy.core.option.OptionNonZeroI16NonZeroI16Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroIScalar .I16 core.num.niche_types.NonZeroI16Inner⟩

@[instance] theorem core.option.OptionNonZeroU32NonZeroU32Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero U32 core.num.niche_types.NonZeroU32Inner))
      Zerocopy.core.option.OptionNonZeroU32NonZeroU32Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroUScalar .U32 core.num.niche_types.NonZeroU32Inner⟩

@[instance] theorem core.option.OptionNonZeroI32NonZeroI32Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero I32 core.num.niche_types.NonZeroI32Inner))
      Zerocopy.core.option.OptionNonZeroI32NonZeroI32Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroIScalar .I32 core.num.niche_types.NonZeroI32Inner⟩

@[instance] theorem core.option.OptionNonZeroU64NonZeroU64Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero U64 core.num.niche_types.NonZeroU64Inner))
      Zerocopy.core.option.OptionNonZeroU64NonZeroU64Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroUScalar .U64 core.num.niche_types.NonZeroU64Inner⟩

@[instance] theorem core.option.OptionNonZeroI64NonZeroI64Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero I64 core.num.niche_types.NonZeroI64Inner))
      Zerocopy.core.option.OptionNonZeroI64NonZeroI64Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroIScalar .I64 core.num.niche_types.NonZeroI64Inner⟩

@[instance] theorem core.option.OptionNonZeroU128NonZeroU128Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero U128 core.num.niche_types.NonZeroU128Inner))
      Zerocopy.core.option.OptionNonZeroU128NonZeroU128Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroUScalar .U128 core.num.niche_types.NonZeroU128Inner⟩

@[instance] theorem core.option.OptionNonZeroI128NonZeroI128Inner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero I128 core.num.niche_types.NonZeroI128Inner))
      Zerocopy.core.option.OptionNonZeroI128NonZeroI128Inner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroIScalar .I128 core.num.niche_types.NonZeroI128Inner⟩

@[instance] theorem core.option.OptionNonZeroUsizeNonZeroUsizeInner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner))
      Zerocopy.core.option.OptionNonZeroUsizeNonZeroUsizeInner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroUScalar .Usize core.num.niche_types.NonZeroUsizeInner⟩

@[instance] theorem core.option.OptionNonZeroIsizeNonZeroIsizeInner.Insts.ZerocopyIntoBytes_law :
    TraitLaws.into_bytes_initialized (Option (core.num.nonzero.NonZero Isize core.num.niche_types.NonZeroIsizeInner))
      Zerocopy.core.option.OptionNonZeroIsizeNonZeroIsizeInner.Insts.ZerocopyIntoBytes :=
  ⟨initializedOptionNonZeroIScalar .Isize core.num.niche_types.NonZeroIsizeInner⟩

-- No value of T is stored in PhantomData, so this law needs no model or
-- trait promise for T, including when T is uninhabited.
@[instance] theorem core.marker.PhantomData.Insts.ZerocopyIntoBytes_law (T : Type) :
    TraitLaws.into_bytes_initialized (Zerocopy.core.marker.PhantomData T)
      (Zerocopy.core.marker.PhantomData.Insts.ZerocopyIntoBytes T) :=
  ⟨Rust.Storage.emptyDecoder_initialized _⟩

end Zerocopy.Proofs
