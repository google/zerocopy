/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Types
public import ModelPrelude
@[expose] public section
open Aeneas Aeneas.Std
open Zerocopy

-- External semantic models: Clone copies the value; NonZero::get returns its
-- stored integer without failure. Their correspondence to Rust is part of the
-- trusted boundary described in ../../README.md, not a theorem of this package.
def core.num.niche_types.NonZeroUsizeInner.Insts.CoreCloneClone.clone
    (x : core.num.niche_types.NonZeroUsizeInner) :
    Result core.num.niche_types.NonZeroUsizeInner := .ok x

-- A forbidden execution cannot be accepted as an ordinary Rust panic. The
-- backend's existing undef tag also marks unsupported models, so it means
-- "no permitted execution claim", not necessarily that the Rust code has UB.
-- Total and partial contracts both reject it. Future recovery models must
-- propagate it rather than turn it into a successful return or divergence.
def Zerocopy.forbiddenExecution {α : Type} : Result α := .fail .undef

-- The native default constructor retains this interpretation's model provider
-- as an implicit semantic parameter. Decoding must succeed before a typed
-- result is returned; neither an absent decoder nor a rejected bit pattern
-- supplies a default value. The physical decoder's Rust correspondence is an
-- explicit premise, checked against the supported native layout profiles.
noncomputable def core.mem.zeroed (T : Type) [model : AeneasSpecs.RustModel T] : Result T :=
  model.zeroedResult

-- These required validator fields carry their actual native signatures. Their
-- pointer-based implementations have no admitted execution semantics yet.
-- Keeping a field is not permission to call it: admission rejects every such
-- call, and the compiled audit requires these whole definitions to return
-- undef. They let representation laws mention real FromZeros/FromBytes
-- dictionaries without asserting anything about TryFromBytes validation.
def Zerocopy.Tuple.Insts.ZerocopyTryFromBytes.is_safe
    {Alignment : Type} (_alignment : pointer.invariant.Alignment Alignment)
    (_candidate : pointer.ptr.def.Ptr (wrappers.read_only_def.ReadOnly Unit)
      (pointer.invariant.Shared × Alignment × pointer.invariant.Initialized)
      pointer.invariant.Shared Alignment pointer.invariant.Initialized) : Result Bool :=
  .fail .undef

def Zerocopy.U8.Insts.ZerocopyTryFromBytes.is_safe
    {Alignment : Type} (_alignment : pointer.invariant.Alignment Alignment)
    (_candidate : pointer.ptr.def.Ptr (wrappers.read_only_def.ReadOnly U8)
      (pointer.invariant.Shared × Alignment × pointer.invariant.Initialized)
      pointer.invariant.Shared Alignment pointer.invariant.Initialized) : Result Bool :=
  .fail .undef

def Zerocopy.U32.Insts.ZerocopyTryFromBytes.is_safe
    {Alignment : Type} (_alignment : pointer.invariant.Alignment Alignment)
    (_candidate : pointer.ptr.def.Ptr (wrappers.read_only_def.ReadOnly U32)
      (pointer.invariant.Shared × Alignment × pointer.invariant.Initialized)
      pointer.invariant.Shared Alignment pointer.invariant.Initialized) : Result Bool :=
  .fail .undef

def Zerocopy.Bool.Insts.ZerocopyTryFromBytes.is_safe
    {Alignment : Type} (_alignment : pointer.invariant.Alignment Alignment)
    (_candidate : pointer.ptr.def.Ptr (wrappers.read_only_def.ReadOnly Bool)
      (pointer.invariant.Shared × Alignment × pointer.invariant.Initialized)
      pointer.invariant.Shared Alignment pointer.invariant.Initialized) : Result Bool :=
  .fail .undef

def Zerocopy.Array.Insts.ZerocopyTryFromBytes.is_safe
    {T Alignment : Type} {N : Usize} (_element : TryFromBytes T)
    (_alignment : pointer.invariant.Alignment Alignment)
    (_candidate : pointer.ptr.def.Ptr (wrappers.read_only_def.ReadOnly (Aeneas.Std.Array T N))
      (pointer.invariant.Shared × Alignment × pointer.invariant.Initialized)
      pointer.invariant.Shared Alignment pointer.invariant.Initialized) : Result Bool :=
  .fail .undef

-- This is an interpretation of the whole Rust helper, whose raw-pointer body
-- is deliberately opaque to extraction. Valid input references supply separate
-- readable source and exclusive destination regions. The additional length
-- guard belongs to execution: violating it must fail even if the caller ignores
-- the result. Payload bytes have no padding or invalid bit patterns.
def util.copy_unchecked (src dst : Slice U8) : Result (Slice U8) :=
  if h : src.val.length ≤ dst.val.length then
    .ok (Slice.from (src.val ++ dst.val.drop src.val.length) (by
      have := dst.property
      simp only [List.length_append, List.length_drop]
      omega))
  else forbiddenExecution

-- The offset copy has the same reference premises. Check bounds before
-- constructing a subslice, and preserve BOTH untouched regions. A start past
-- the end panics at Rust's checked subslicing; an oversized copy is forbidden.
-- FIXME: Pinned SliceIndexRangeFromUsizeSlice.get_mut reconstructs its output
-- incorrectly (ca282ec, Aeneas/Std/Slice.lean). Do not admit that builtin until
-- its prefix-preservation law has been repaired and checked independently.
def util.copy_unchecked_at (src dst : Slice U8) (start : Usize) : Result (Slice U8) :=
  if start.val ≤ dst.val.length then
    if h : src.val.length ≤ dst.val.length - start.val then
      .ok (Slice.from
        (dst.val.take start.val ++ src.val ++ dst.val.drop (start.val + src.val.length)) (by
          have := dst.property
          simp only [List.length_append, List.length_take, List.length_drop]
          omega))
    else forbiddenExecution
  else .fail .panic

-- Reading bytes never assumes the validity of the type they might encode.
-- Bounds are checked at execution, including when the caller discards the byte.
def util.validity.read_byte (bytes : Slice U8) (index : Usize) : Result U8 :=
  if index.val < bytes.val.length then .ok bytes.val[index.val]! else .fail .panic

-- Only the u8-to-bool instantiation is supported. The admission checker also
-- checks the original Rust type arguments, before Aeneas can erase them. This
-- guard checks bit validity BEFORE creating a Bool, whose Lean carrier cannot
-- represent an invalid boolean. All other instantiations fail closed.
noncomputable def util.transmute_unchecked {Src : Type} (Dst : Type)
    (src : Src) : Result Dst := by
  classical
  exact if hs : Src = U8 then
    if hd : Dst = Bool then
      let byte := cast hs src
      if byte.val < 2 then .ok (cast hd.symm (decide (byte.val = 1)))
      else forbiddenExecution
    else forbiddenExecution
  else forbiddenExecution

-- The standard primitive uses a closed, interpretation-only provider. Original
-- Rust endpoint admission and compiled call auditing bind every reached use to
-- one of these fixed providers; no arbitrary dictionary enters a Rust root.
-- This preserves endpoint identity without testing equality of erased Types.
class Zerocopy.StdOwnedTransmute (Src Dst : Type) where
  run : Src → Result Dst

instance Zerocopy.stdTransmuteU32ToBytes :
    Zerocopy.StdOwnedTransmute U32 (Array U8 4#usize) where
  run value := .ok (core.num.U32.to_le_bytes value)

instance Zerocopy.stdTransmuteBytesToU32 :
    Zerocopy.StdOwnedTransmute (Array U8 4#usize) U32 where
  run bytes := .ok (core.num.U32.from_le_bytes bytes)

instance Zerocopy.stdTransmuteU8ToBool : Zerocopy.StdOwnedTransmute U8 Bool where
  run byte := if byte.val < 2 then .ok (decide (byte.val = 1)) else forbiddenExecution

-- The additional implicit parameter is explicitly part of the reviewed std
-- boundary, not a translated Rust trait argument. Other endpoints are rejected
-- by admission and have no registered provider. The numeric cases require the
-- independently checked little-endian compiler profile; Boolean validity does
-- not depend on byte order.
def core.intrinsics.transmute {Src : Type} (Dst : Type)
    [provider : Zerocopy.StdOwnedTransmute Src Dst] (src : Src) : Result Dst :=
  provider.run src


@[simp] def core.num.nonzero.NonZero.get
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : core.num.nonzero.NonZero T Inner) : Result T := .ok x.val

-- Aeneas erases Rust's ABI information from a generic Type parameter. These
-- two data parameters supply that information. They assert no propositions;
-- every consumer must prove its contract under explicit size/alignment inputs.
-- The axiom audit admits exactly these signatures, never arbitrary axioms.
axiom Zerocopy.RustLayout.size (T : Type) : Usize
axiom Zerocopy.RustLayout.alignInput (T : Type) : Usize

-- The byte primitive has compiler alignment one. Its native compile-time
-- assertion lives beside the Rust layout fixtures. This is a concrete external
-- interpretation, not a proof of an arbitrary ABI fact; generic types retain
-- the original unconstrained data input. Keep this one case explicit rather
-- than inferring physical layout from a Lean type's mathematical meaning.
noncomputable def Zerocopy.RustLayout.align (T : Type) : Usize := by
  classical
  exact if T = U8 then 1#usize else Zerocopy.RustLayout.alignInput T

@[simp] theorem Zerocopy.RustLayout.align_u8 :
    Zerocopy.RustLayout.align U8 = 1#usize := by
  simp [Zerocopy.RustLayout.align]

@[simp] noncomputable def core.mem.size_of (T : Type) : Result Usize := by
  classical
  exact .ok (if T = Usize then
    { bv := BitVec.ofNat _ (System.Platform.numBits / 8) }
    else Zerocopy.RustLayout.size T)

@[simp] noncomputable def core.mem.align_of (T : Type) : Result Usize :=
  .ok (Zerocopy.RustLayout.align T)

-- The extracted call sites instantiate this primitive only at Usize. Other
-- types are unsupported, so the model cannot promise a recoverable panic.
@[simp] noncomputable def core.num.nonzero.NonZero.new
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : T) : Result (Option (core.num.nonzero.NonZero T Inner)) := by
  classical
  exact if h : T = Usize then
    if (cast h x : Usize) = 0#usize then .ok none else .ok (some ⟨x⟩)
  else forbiddenExecution

-- The pinned std contract requires a nonzero argument. Guard the execution
-- before producing even a raw wrapper: zero is forbidden, including when a
-- caller discards the result. Only Usize is reviewed, and admission checks its
-- original Rust type and lifted NonZeroUsizeInner argument independently.
@[simp] noncomputable def core.num.nonzero.NonZero.new_unchecked
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : T) : Result (core.num.nonzero.NonZero T Inner) := by
  classical
  exact if h : T = Usize then
    if (cast h x : Usize) = 0#usize then forbiddenExecution else .ok ⟨x⟩
  else forbiddenExecution
