/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustRealizability
public import Models
import all RustModel
import all ModelPrelude
@[expose] public section

open Aeneas.Std Rust.Storage
namespace AeneasSpecs

/-- Generated providers retain their mathematical admission checks. A wrapper
may restrict admission further, but must still admit its stored child. -/
theorem realizableUnalign (T : Type) [ma : RustModel T]
    (child : RustModel.realizableRepresentation T) :
    RustModel.realizableRepresentation (Zerocopy.wrappers.Unalign T) := by
  apply RustModel.realizable_of_wrapper Zerocopy.wrappers.Unalign.mk (·._0)
    (by intro raw; rfl) (by rintro ⟨raw⟩; rfl) rfl ?_ child
  intro raw valid
  obtain ⟨value, accepted⟩ := valid
  cases decoded : ma.decode raw._0 with
  | none => simp [RustModel.decode, Zerocopy.wrappers.Unalign.decode, decoded] at accepted
  | some value => exact ⟨value, decoded⟩

theorem realizableReadOnly (T : Type) [ma : RustModel T]
    (child : RustModel.realizableRepresentation T) :
    RustModel.realizableRepresentation (Zerocopy.wrappers.read_only_def.ReadOnly T) := by
  apply RustModel.realizable_of_wrapper Zerocopy.wrappers.read_only_def.ReadOnly.mk (·.inner)
    (by intro raw; rfl) (by rintro ⟨raw⟩; rfl) rfl ?_ child
  intro raw valid
  obtain ⟨value, accepted⟩ := valid
  cases decoded : ma.decode raw.inner with
  | none => simp [RustModel.decode, Zerocopy.wrappers.read_only_def.ReadOnly.decode, decoded] at accepted
  | some value => exact ⟨value, decoded⟩

theorem realizableByteorderU16 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.U16 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.U16.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (2#usize) (realizableUScalar .U8))

theorem realizableByteorderU32 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.U32 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.U32.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (4#usize) (realizableUScalar .U8))

theorem realizableByteorderU64 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.U64 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.U64.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (8#usize) (realizableUScalar .U8))

theorem realizableByteorderU128 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.U128 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.U128.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (16#usize) (realizableUScalar .U8))

theorem realizableByteorderUsize (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.Usize O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.Usize.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (8#usize) (realizableUScalar .U8))

theorem realizableByteorderI16 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.I16 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.I16.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (2#usize) (realizableUScalar .U8))

theorem realizableByteorderI32 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.I32 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.I32.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (4#usize) (realizableUScalar .U8))

theorem realizableByteorderI64 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.I64 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.I64.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (8#usize) (realizableUScalar .U8))

theorem realizableByteorderI128 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.I128 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.I128.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (16#usize) (realizableUScalar .U8))

theorem realizableByteorderIsize (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.Isize O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.Isize.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (8#usize) (realizableUScalar .U8))

theorem realizableByteorderF32 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.F32 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.F32.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (4#usize) (realizableUScalar .U8))

theorem realizableByteorderF64 (O : Type) [RustModel O] :
    RustModel.realizableRepresentation (Zerocopy.byteorder.F64 O) := by
  apply RustModel.realizable_of_wrapper
    (fun raw => Zerocopy.byteorder.F64.mk raw Zerocopy.core.marker.PhantomData.mk)
    (·._0) (by intro raw; rfl) (by rintro ⟨raw, phantom⟩; cases phantom; rfl) rfl
    (fun raw _ => RustModel.valid_array raw._0 (fun _ _ => ⟨_, rfl⟩))
    (RustModel.realizable_array U8 (8#usize) (realizableUScalar .U8))

end AeneasSpecs
