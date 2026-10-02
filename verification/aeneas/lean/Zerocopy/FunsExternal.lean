/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Types
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

@[simp] def core.num.nonzero.NonZero.get
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : core.num.nonzero.NonZero T Inner) : Result T := .ok x.val

-- Extraction uses size_of only for usize to calculate its bit width. Other
-- types remain unsupported rather than receiving arbitrary layout values.
@[simp] noncomputable def core.mem.size_of (T : Type) : Result Usize := by
  classical
  exact if T = Usize then
    .ok { bv := BitVec.ofNat _ (System.Platform.numBits / 8) }
  else .fail .panic

-- The extracted call sites instantiate this primitive only at Usize. Other
-- types are unsupported, so the model cannot promise a recoverable panic.
@[simp] noncomputable def core.num.nonzero.NonZero.new
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : T) : Result (Option (core.num.nonzero.NonZero T Inner)) := by
  classical
  exact if h : T = Usize then
    if (cast h x : Usize) = 0#usize then .ok none else .ok (some ⟨x⟩)
  else forbiddenExecution
