-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Anneal.MiniRust.Syntax

namespace Anneal.MiniRust

/-!
# MiniRust Basic Memory Model & Representation (`Anneal.MiniRust.Memory`)

Constructive Lean 4 transcription of MiniRust's `BasicMemory`
(`spec/mem/basic.md`) and little-endian type-directed representation relation
(`spec/lang/representation.md`) for upstream commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`.

Includes total allocation, deallocation, bounds/alignment/liveness-checked
`load`/`store`/`deinit`, little-endian integer/bool/tuple/array/enum `mrEncode`
and `mrDecode`, and constructive round-trip and frame lemmas.

Note on allocation addresses: `MrMemory.allocate` assigns monotonically
increasing fresh aligned addresses without reusing freed ranges or bounding
`addr + size <= 2^64` (`spec/mem/basic.md` chooses nondeterministic non-zero
in-bounds addresses and permits address reuse). In the pointer-cast-free
scalar/enum fragment covered by `Anneal.MiniRust`, concrete address magnitudes
are unobservable and divergence is preserved identically.
-/

/-- Total list lookup by index. -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Total list update by index. -/
def listSet? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match listSet? xs n v with
    | some xs' => some (x :: xs')
    | none => none

/-- A single memory allocation (`spec/mem/basic.md`: `struct Allocation`). -/
structure MrAllocation where
  allocId : AllocId
  addr : Nat
  align : Align
  live : Bool
  data : List AbstractByte

/-- Thin pointer with absolute byte address and optional provenance
(`spec/mem/pointer.md`: `ThinPointer`). -/
structure ThinPtr where
  allocId : Option AllocId
  addr : Nat

/-- Place value returned by `evalPlace`
(`spec/lang/values.md`: `struct Place`). -/
structure MrPlace where
  ptr : ThinPtr
  aligned : Bool

/-- MiniRust basic memory state (`spec/mem/basic.md`: `BasicMemory`).
Allocations are appended with consecutive `AllocId`s (`0, 1, ...`), and
`nextAddr` strictly increases to guarantee non-overlapping aligned addresses
away from `0`. -/
structure MrMemory where
  nextAddr : Nat
  allocations : List MrAllocation

/-- Empty memory starting at non-zero page-aligned base address `4096`. -/
def MrMemory.empty : MrMemory :=
  { nextAddr := 4096, allocations := [] }

/-- Round `addr` up to a multiple of `al` (preserving `addr` if `al == 0`). -/
def alignUp (addr al : Nat) : Nat :=
  if Nat.beq al 0 then addr
  else
    let rem := Nat.mod addr al
    if Nat.beq rem 0 then addr else addr + (al - rem)

/-- Check that `sz` fits in signed 64-bit `isize` (`spec/mem/basic.md`:
`T::valid_size`). -/
def validSize (sz : Size) : Bool :=
  Nat.blt sz.bytes (Nat.pow 2 63)

/-- Allocate a fresh, live, uninitialized stack allocation
(`spec/mem/basic.md`: `BasicMemory::allocate`). -/
def MrMemory.allocate (m : MrMemory) (sz : Size) (al : Align) :
    Except String (MrMemory × ThinPtr) :=
  if !validSize sz then
    .error "asking for a too large allocation"
  else if Nat.beq al.bytes 0 then
    .error "invalid zero alignment"
  else
    let base := alignUp m.nextAddr al.bytes
    let stepBytes := if Nat.beq sz.bytes 0 then 1 else sz.bytes
    let id := m.allocations.length
    let alloc : MrAllocation := {
      allocId := id
      addr := base
      align := al
      live := true
      data := List.replicate sz.bytes .uninit
    }
    let m' : MrMemory := {
      nextAddr := base + stepBytes
      allocations := m.allocations ++ [alloc]
    }
    .ok (m', ⟨some id, base⟩)

/-- Deallocate an existing live stack allocation (`spec/mem/basic.md`:
`BasicMemory::deallocate`). -/
def MrMemory.deallocate (m : MrMemory) (ptr : ThinPtr) (sz : Size)
    (al : Align) : Except String MrMemory :=
  match ptr.allocId with
  | none => .error "deallocating invalid pointer"
  | some id =>
    match listGet? m.allocations id with
    | none => .error "deallocating unknown allocation"
    | some alloc =>
      if !alloc.live then
        .error "double-free"
      else if !Nat.beq ptr.addr alloc.addr then
        .error "deallocating with pointer not to the beginning of its allocation"
      else if !Nat.beq sz.bytes alloc.data.length then
        .error "deallocating with incorrect size information"
      else if !Nat.beq al.bytes alloc.align.bytes then
        .error "deallocating with incorrect alignment information"
      else
        match listSet? m.allocations id { alloc with live := false } with
        | none => .error "deallocating unknown allocation"
        | some allocs' => .ok { m with allocations := allocs' }

/-- Check if `ptr` is dereferenceable for `len` bytes (`spec/mem/basic.md`:
`BasicMemory::check_ptr`). Zero-sized accesses return `.ok none`. -/
def MrMemory.checkPtr (m : MrMemory) (ptr : ThinPtr) (len : Size) :
    Except String (Option (AllocId × Nat)) :=
  if Nat.beq len.bytes 0 then
    .ok none
  else
    match ptr.allocId with
    | none => .error "dereferencing pointer without provenance"
    | some id =>
      match listGet? m.allocations id with
      | none => .error "dereferencing unknown allocation"
      | some alloc =>
        if !alloc.live then
          .error "dereferencing pointer to dead allocation"
        else if Nat.blt ptr.addr alloc.addr then
          .error "dereferencing pointer outside the bounds of its allocation"
        else
          let off := ptr.addr - alloc.addr
          if !Nat.ble (off + len.bytes) alloc.data.length then
            .error "dereferencing pointer outside the bounds of its allocation"
          else
            .ok (some (id, off))

/-- Subslice `[off, off + len)` of a byte list. -/
def byteSubslice (bytes : List AbstractByte) (off len : Nat) :
    List AbstractByte :=
  (bytes.drop off).take len

/-- Overwrite `[off, off + patch.length)` of `bytes` with `patch`. -/
def byteWriteSubslice (bytes : List AbstractByte) (off : Nat)
    (patch : List AbstractByte) : List AbstractByte :=
  bytes.take off ++ patch ++ bytes.drop (off + patch.length)

/-- Load `len` abstract bytes from `ptr` with alignment check `al`
(`spec/mem/basic.md`: `BasicMemory::load`). -/
def MrMemory.load (m : MrMemory) (ptr : ThinPtr) (len : Size) (al : Align) :
    Except String (List AbstractByte) :=
  if !al.isAligned ptr.addr then
    .error "load from a misaligned pointer"
  else
    match m.checkPtr ptr len with
    | .error msg => .error msg
    | .ok none => .ok []
    | .ok (some (id, off)) =>
      match listGet? m.allocations id with
      | none => .error "dereferencing unknown allocation"
      | some alloc => .ok (byteSubslice alloc.data off len.bytes)

/-- Store `bytes` at `ptr` with alignment check `al`
(`spec/mem/basic.md`: `BasicMemory::store`). -/
def MrMemory.store (m : MrMemory) (ptr : ThinPtr)
    (bytes : List AbstractByte) (al : Align) : Except String MrMemory :=
  if !al.isAligned ptr.addr then
    .error "store to a misaligned pointer"
  else
    match m.checkPtr ptr ⟨bytes.length⟩ with
    | .error msg => .error msg
    | .ok none => .ok m
    | .ok (some (id, off)) =>
      match listGet? m.allocations id with
      | none => .error "dereferencing unknown allocation"
      | some alloc =>
        let data' := byteWriteSubslice alloc.data off bytes
        match listSet? m.allocations id { alloc with data := data' } with
        | none => .error "dereferencing unknown allocation"
        | some allocs' => .ok { m with allocations := allocs' }

/-- Mark `len` bytes at `ptr` uninitialized (`spec/lang/step/statements.md`:
`ConcurrentMemory::deinit`). -/
def MrMemory.deinit (m : MrMemory) (ptr : ThinPtr) (len : Size) (al : Align) :
    Except String MrMemory :=
  m.store ptr (List.replicate len.bytes .uninit) al

/-! ## Little-Endian Byte Codecs and Type-Directed Representation Relation -/

/-- Extract the low `n` bytes of `value` in little-endian order. -/
def mrLeBytesOfNat : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, value =>
    UInt8.ofNat (Nat.mod value 256) :: mrLeBytesOfNat n (Nat.div value 256)

/-- Decode little-endian bytes to an unsigned `Nat`. -/
def mrNatOfLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * mrNatOfLeBytes rest

/-- Extract initialized raw bytes or return `none` if any byte is `.uninit`. -/
def extractInitBytes : List AbstractByte → Option (List UInt8)
  | [] => some []
  | .uninit :: _ => none
  | .init b :: rest =>
    match extractInitBytes rest with
    | some bs => some (b :: bs)
    | none => none

/-- Decode an integer of type `it` from little-endian abstract bytes
(`spec/lang/representation.md`: `Type::decode` for `Type::Int`). -/
def decodeInt (it : IntType) (bytes : List AbstractByte) : Option Int :=
  if !Nat.beq bytes.length it.size.bytes then
    none
  else
    match extractInitBytes bytes with
    | none => none
    | some raw => some (it.bringInBounds (Int.ofNat (mrNatOfLeBytes raw)))

/-- Encode a representable mathematical integer `i` at `it` as little-endian
abstract bytes (`spec/lang/representation.md`: `Type::encode` on
`Type::Int`). -/
def encodeInt (it : IntType) (i : Int) : Option (List AbstractByte) :=
  if !it.canRepresent i then
    none
  else
    let u := intEmodNat i (Nat.pow 2 it.bitWidth)
    some ((mrLeBytesOfNat it.size.bytes u).map AbstractByte.init)

mutual
  /-- Evaluate a `Discriminator` decision tree against raw enum bytes
  (`spec/lang/representation.md`: `decode_discriminant`). -/
  def decodeDiscriminant (bytes : List AbstractByte) :
      Discriminator → Option Int
    | .known val => some val
    | .invalid => none
    | .branch off valTy children fallback =>
      let sub := byteSubslice bytes off valTy.size.bytes
      match decodeInt valTy sub with
      | none => none
      | some v =>
        match decodeDiscrBranches bytes v children with
        | some res => res
        | none => decodeDiscriminant bytes fallback

  /-- Evaluate the first matching range `[lo, hi)` in `DiscrBranches`. -/
  def decodeDiscrBranches (bytes : List AbstractByte) (v : Int) :
      DiscrBranches → Option (Option Int)
    | .nil => none
    | .cons lo hi child rest =>
      if decide (lo ≤ v) && decide (v < hi) then
        some (decodeDiscriminant bytes child)
      else
        decodeDiscrBranches bytes v rest
end

/-- Apply a variant's tag writes to `bytes` (`spec/lang/representation.md`:
`encode_discriminant`). -/
def encodeDiscriminant :
    List AbstractByte → List TagWrite → Option (List AbstractByte)
  | bytes, [] => some bytes
  | bytes, tw :: rest =>
    match encodeInt tw.intTy tw.val with
    | none => none
    | some tagBytes =>
      encodeDiscriminant (byteWriteSubslice bytes tw.offset tagBytes) rest

/-- Decode `count` consecutive array elements of type `elem` starting at byte
offset `off`. -/
def mrDecodeArrayAux (decodeElem : List AbstractByte → Option MrValue)
    (elemSize : Nat) (bytes : List AbstractByte) :
    Nat → Nat → Option MrValueList
  | _, 0 => some .nil
  | off, n + 1 =>
    match decodeElem (byteSubslice bytes off elemSize) with
    | none => none
    | some v =>
      match mrDecodeArrayAux decodeElem elemSize bytes (off + elemSize) n with
      | none => none
      | some vs => some (.cons v vs)

/-- Encode array element values consecutively. -/
def mrEncodeArrayAux (encodeElem : MrValue → Option (List AbstractByte)) :
    MrValueList → Option (List AbstractByte)
  | .nil => some []
  | .cons v vs =>
    match encodeElem v, mrEncodeArrayAux encodeElem vs with
    | some bs, some rest => some (bs ++ rest)
    | _, _ => none

mutual
  /-- Type-directed byte decoding (`spec/lang/representation.md`:
  `Type::decode`). Returns `none` when `bytes` violates the language validity
  invariant (which triggers MiniRust UB on load/transmute). -/
  def mrDecode : MrType → List AbstractByte → Option MrValue
    | .int it, bytes =>
      match decodeInt it bytes with
      | some v => some (.int v)
      | none => none
    | .bool, bytes =>
      match bytes with
      | [.init b] =>
        if b == 0 then some (.bool false)
        else if b == 1 then some (.bool true)
        else none
      | _ => none
    | .tuple fields sz _, bytes =>
      if !Nat.beq bytes.length sz.bytes then
        none
      else
        match mrDecodeFields fields bytes with
        | some vs => some (.tuple vs)
        | none => none
    | .array elem count, bytes =>
      if !Nat.beq bytes.length (elem.size.bytes * count) then
        none
      else
        match mrDecodeArrayAux (mrDecode elem) elem.size.bytes bytes 0 count with
        | some vs => some (.tuple vs)
        | none => none
    | .enum variants discr _ sz _, bytes =>
      if !Nat.beq bytes.length sz.bytes then
        none
      else
        match decodeDiscriminant bytes discr with
        | none => none
        | some d =>
          match mrDecodeEnumVariant d variants bytes with
          | some dataVal => some (.variant d dataVal)
          | none => none

  /-- Decode each field of a tuple from its byte subslice. -/
  def mrDecodeFields : TupleFields → List AbstractByte → Option MrValueList
    | .nil, _ => some .nil
    | .cons off ty rest, bytes =>
      match mrDecode ty (byteSubslice bytes off ty.size.bytes) with
      | none => none
      | some v =>
        match mrDecodeFields rest bytes with
        | none => none
        | some vs => some (.cons v vs)

  /-- Lookup variant `d` in `EnumVariants` and decode its payload bytes. -/
  def mrDecodeEnumVariant (d : Int) :
      EnumVariants → List AbstractByte → Option MrValue
    | .nil, _ => none
    | .cons vd vty _ rest, bytes =>
      if vd == d then mrDecode vty bytes
      else mrDecodeEnumVariant d rest bytes
end

mutual
  /-- Type-directed value encoding (`spec/lang/representation.md`:
  `Type::encode`). Padding bytes in tuples and enums are deterministically
  `.uninit`. -/
  def mrEncode : MrType → MrValue → Option (List AbstractByte)
    | .int it, .int v => encodeInt it v
    | .bool, .bool b => some [.init (if b then 1 else 0)]
    | .tuple fields sz _, .tuple vals =>
      mrEncodeFields fields vals (List.replicate sz.bytes .uninit)
    | .array elem count, .tuple vals =>
      if !Nat.beq vals.length count then none
      else mrEncodeArrayAux (mrEncode elem) vals
    | .enum variants _ _ _ _, .variant d dataVal =>
      mrEncodeEnumVariant d dataVal variants
    | _, _ => none

  /-- Encode each tuple field into `acc` at its declared byte offset. -/
  def mrEncodeFields :
      TupleFields → MrValueList → List AbstractByte → Option (List AbstractByte)
    | .nil, .nil, acc => some acc
    | .cons off ty rest, .cons v vs, acc =>
      match mrEncode ty v with
      | none => none
      | some fbytes =>
        mrEncodeFields rest vs (byteWriteSubslice acc off fbytes)
    | _, _, _ => none

  /-- Lookup variant `d`, encode its payload, and overlay its tag writes. -/
  def mrEncodeEnumVariant (d : Int) (dataVal : MrValue) :
      EnumVariants → Option (List AbstractByte)
    | .nil => none
    | .cons vd vty tagger rest =>
      if vd == d then
        match mrEncode vty dataVal with
        | none => none
        | some baseBytes => encodeDiscriminant baseBytes tagger
      else
        mrEncodeEnumVariant d dataVal rest
end

/-! ## Core Memory and Codec Lemmas -/

theorem listGet?_set_eq {α : Type} (xs : List α) (i : Nat) (v : α)
    (xs' : List α) (h : listSet? xs i v = some xs') :
    listGet? xs' i = some v := by
  induction xs generalizing i xs' with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp only [listSet?] at h
      injection h with h1
      subst h1
      rfl
    | succ k =>
      dsimp only [listSet?] at h
      cases hset : listSet? xs k v with
      | none => rw [hset] at h; cases h
      | some ys =>
        rw [hset] at h
        injection h with h1
        subst h1
        exact ih k ys hset

theorem listGet?_set_ne {α : Type} (xs : List α) (i j : Nat) (v : α)
    (xs' : List α) (h : listSet? xs i v = some xs') (hne : i ≠ j) :
    listGet? xs' j = listGet? xs j := by
  induction xs generalizing i j xs' with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp only [listSet?] at h
      injection h with h1
      subst h1
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ m => rfl
    | succ k =>
      dsimp only [listSet?] at h
      cases hset : listSet? xs k v with
      | none => rw [hset] at h; cases h
      | some ys =>
        rw [hset] at h
        injection h with h1
        subst h1
        cases j with
        | zero => rfl
        | succ m =>
          apply ih k m ys hset
          intro heq
          apply hne
          rw [heq]

theorem listSet?_length {α : Type} (xs : List α) (i : Nat) (v : α)
    (xs' : List α) (h : listSet? xs i v = some xs') :
    xs'.length = xs.length := by
  induction xs generalizing i xs' with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp only [listSet?] at h
      injection h with h1
      subst h1
      rfl
    | succ k =>
      dsimp only [listSet?] at h
      cases hset : listSet? xs k v with
      | none => rw [hset] at h; cases h
      | some ys =>
        rw [hset] at h
        injection h with h1
        subst h1
        dsimp only [List.length]
        rw [ih k ys hset]

theorem listSet?_some_of_get?_some {α : Type} (xs : List α) (i : Nat) (v : α)
    (a : α) (h : listGet? xs i = some a) :
    ∃ xs', listSet? xs i v = some xs' := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => exact ⟨v :: xs, rfl⟩
    | succ k =>
      cases ih k h with
      | intro ys hys =>
        refine ⟨x :: ys, ?_⟩
        dsimp only [listSet?]
        rw [hys]

theorem listGet?_append_left {α : Type} (xs ys : List α) (i : Nat) (a : α)
    (h : listGet? xs i = some a) :
    listGet? (xs ++ ys) i = some a := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => exact h
    | succ k => exact ih k h

theorem listGet?_append_singleton {α : Type} (xs : List α) (a : α) :
    listGet? (xs ++ [a]) xs.length = some a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem listGet?_lt_length {α : Type} (xs : List α) (i : Nat) (a : α)
    (h : listGet? xs i = some a) : i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ k => exact Nat.succ_lt_succ (ih k h)

theorem mrLeBytesOfNat_length (n v : Nat) :
    (mrLeBytesOfNat n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ k ih =>
    dsimp only [mrLeBytesOfNat, List.length]
    rw [ih]

theorem extractInitBytes_map_init (bs : List UInt8) :
    extractInitBytes (bs.map AbstractByte.init) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    dsimp only [List.map, extractInitBytes]
    rw [ih]

theorem extractInitBytes_replicate_uninit (n : Nat) :
    extractInitBytes (List.replicate (n + 1) AbstractByte.uninit) = none := rfl

theorem alignUp_aligned (addr al : Nat) (hpos : 0 < al) :
    Align.isAligned ⟨al⟩ (alignUp addr al) = true := by
  have hne : Nat.beq al 0 = false := by
    cases al with
    | zero => cases hpos
    | succ _ => rfl
  dsimp only [Align.isAligned, alignUp]
  rw [hne]
  cases hrem : Nat.beq (Nat.mod addr al) 0 with
  | true =>
    change Nat.beq (Nat.mod addr al) 0 = true
    exact hrem
  | false =>
    change Nat.beq (Nat.mod (addr + (al - Nat.mod addr al)) al) 0 = true
    have hlt : Nat.mod addr al < al := Nat.mod_lt addr hpos
    have hsum : addr + (al - Nat.mod addr al) =
        al * (Nat.div addr al + 1) := by
      have hdiv : al * Nat.div addr al + Nat.mod addr al = addr :=
        Nat.div_add_mod addr al
      have h1 : al * (Nat.div addr al + 1) = al * Nat.div addr al + al :=
        Nat.mul_succ al (Nat.div addr al)
      have hle : Nat.mod addr al ≤ al := Nat.le_of_lt hlt
      have h2 : addr + (al - Nat.mod addr al) =
          al * Nat.div addr al + Nat.mod addr al + (al - Nat.mod addr al) := by
        rw [hdiv]
      rw [h1, h2, Nat.add_assoc, Nat.add_sub_of_le hle]
    rw [hsum]
    have hmod : Nat.mod (al * (Nat.div addr al + 1)) al = 0 :=
      Nat.mul_mod_right al (Nat.div addr al + 1)
    rw [hmod]
    rfl

theorem list_take_length {α : Type} (xs : List α) : xs.take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.length, List.take]
    rw [ih]

theorem list_drop_length {α : Type} (xs : List α) : xs.drop xs.length = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.length, List.drop]
    exact ih

theorem list_length_take_le {α : Type} (n : Nat) (xs : List α)
    (hle : n ≤ xs.length) : (xs.take n).length = n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact False.elim (Nat.not_succ_le_zero k hle)
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp only [List.take, List.length]
      rw [ih k (Nat.le_of_succ_le_succ hle)]

theorem list_length_drop {α : Type} (n : Nat) (xs : List α) :
    (xs.drop n).length = xs.length - n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact (Nat.zero_sub (k + 1)).symm
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp only [List.drop, List.length]
      rw [ih k, Nat.succ_sub_succ]

theorem byteSubslice_zero_eq (bytes : List AbstractByte) :
    byteSubslice bytes 0 bytes.length = bytes := by
  dsimp only [byteSubslice]
  exact list_take_length bytes

theorem byteWriteSubslice_zero_eq (bytes patch : List AbstractByte)
    (hlen : patch.length = bytes.length) :
    byteWriteSubslice bytes 0 patch = patch := by
  dsimp only [byteWriteSubslice]
  rw [List.take_zero, List.nil_append, Nat.zero_add, hlen, list_drop_length,
    List.append_nil]

theorem byteWriteSubslice_length (bytes patch : List AbstractByte) (off : Nat)
    (hle : off + patch.length ≤ bytes.length) :
    (byteWriteSubslice bytes off patch).length = bytes.length := by
  dsimp only [byteWriteSubslice]
  rw [List.length_append, List.length_append]
  have h1 : off ≤ bytes.length :=
    Nat.le_trans (Nat.le_add_right off patch.length) hle
  rw [list_length_take_le off bytes h1, list_length_drop (off + patch.length) bytes]
  exact Nat.add_sub_of_le hle

theorem nat_pow_add_local (a b c : Nat) :
    Nat.pow a (b + c) = Nat.pow a b * Nat.pow a c := by
  induction c with
  | zero =>
    rw [Nat.add_zero]
    exact (Nat.mul_one (Nat.pow a b)).symm
  | succ k ih =>
    rw [Nat.add_succ]
    change Nat.pow a (b + k) * a = Nat.pow a b * (Nat.pow a k * a)
    rw [ih, Nat.mul_assoc]

theorem nat_mul_add_mod_local (m q r : Nat) :
    Nat.mod (m * q + r) m = Nat.mod r m := by
  induction q with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add]
  | succ k ih =>
    have h1 : m * (k + 1) + r = m + (m * k + r) := by
      rw [Nat.mul_succ, Nat.add_comm (m * k) m, Nat.add_assoc]
    rw [h1]
    have h2 : Nat.mod (m + (m * k + r)) m = Nat.mod (m * k + r) m :=
      Nat.add_mod_left m (m * k + r)
    exact Eq.trans h2 ih

theorem nat_mod_mul_right_local (v a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Nat.mod v (a * b) = Nat.mod v a + a * Nat.mod (Nat.div v a) b := by
  have h1 : a * Nat.div v a + Nat.mod v a = v := Nat.div_add_mod v a
  have h2 : b * Nat.div (Nat.div v a) b + Nat.mod (Nat.div v a) b = Nat.div v a :=
    Nat.div_add_mod (Nat.div v a) b
  have hdecomp : v = (a * b) * Nat.div (Nat.div v a) b +
      (Nat.mod v a + a * Nat.mod (Nat.div v a) b) := by
    have hmul : a * Nat.div v a =
        (a * b) * Nat.div (Nat.div v a) b + a * Nat.mod (Nat.div v a) b := by
      have hmul2 : a * (b * Nat.div (Nat.div v a) b + Nat.mod (Nat.div v a) b) =
          a * (b * Nat.div (Nat.div v a) b) + a * Nat.mod (Nat.div v a) b :=
        Nat.mul_add a (b * Nat.div (Nat.div v a) b) (Nat.mod (Nat.div v a) b)
      rw [h2] at hmul2
      rw [hmul2, Nat.mul_assoc]
    have hstep2 : a * Nat.div v a + Nat.mod v a =
        (a * b) * Nat.div (Nat.div v a) b +
          (Nat.mod v a + a * Nat.mod (Nat.div v a) b) := by
      rw [hmul, Nat.add_assoc,
        Nat.add_comm (a * Nat.mod (Nat.div v a) b) (Nat.mod v a)]
    exact Eq.trans h1.symm hstep2
  have hlt1 : Nat.mod v a < a := Nat.mod_lt v ha
  have hlt2 : Nat.mod (Nat.div v a) b < b := Nat.mod_lt (Nat.div v a) hb
  have hbound : Nat.mod v a + a * Nat.mod (Nat.div v a) b < a * b := by
    have hs : Nat.mod (Nat.div v a) b + 1 ≤ b := hlt2
    have hm : a * (Nat.mod (Nat.div v a) b + 1) ≤ a * b :=
      Nat.mul_le_mul_left a hs
    have hlt3 : Nat.mod v a + a * Nat.mod (Nat.div v a) b <
        a + a * Nat.mod (Nat.div v a) b :=
      Nat.add_lt_add_right hlt1 (a * Nat.mod (Nat.div v a) b)
    have heq : a + a * Nat.mod (Nat.div v a) b =
        a * (Nat.mod (Nat.div v a) b + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [heq] at hlt3
    exact Nat.lt_of_lt_of_le hlt3 hm
  have hmod : Nat.mod ((a * b) * Nat.div (Nat.div v a) b +
      (Nat.mod v a + a * Nat.mod (Nat.div v a) b)) (a * b) =
      Nat.mod (Nat.mod v a + a * Nat.mod (Nat.div v a) b) (a * b) :=
    nat_mul_add_mod_local (a * b) (Nat.div (Nat.div v a) b)
      (Nat.mod v a + a * Nat.mod (Nat.div v a) b)
  have hmod2 : Nat.mod (Nat.mod v a + a * Nat.mod (Nat.div v a) b) (a * b) =
      Nat.mod v a + a * Nat.mod (Nat.div v a) b :=
    Nat.mod_eq_of_lt hbound
  rw [← hdecomp] at hmod
  exact Eq.trans hmod hmod2

theorem mrNatOfLeBytes_mrLeBytesOfNat (n v : Nat) :
    mrNatOfLeBytes (mrLeBytesOfNat n v) = Nat.mod v (Nat.pow 2 (n * 8)) := by
  induction n generalizing v with
  | zero =>
    dsimp only [mrLeBytesOfNat, mrNatOfLeBytes]
    exact (Nat.mod_one v).symm
  | succ k ih =>
    dsimp only [mrLeBytesOfNat, mrNatOfLeBytes]
    rw [ih (Nat.div v 256)]
    have hlt256 : Nat.mod v 256 < 256 := Nat.mod_lt v (by decide)
    have htoNat : (UInt8.ofNat (Nat.mod v 256)).toNat = Nat.mod v 256 := by
      dsimp only [UInt8.ofNat, UInt8.toNat, BitVec.ofNat, BitVec.toNat, Fin.ofNat]
      exact Nat.mod_eq_of_lt hlt256
    rw [htoNat]
    have hpow : Nat.pow 2 ((k + 1) * 8) = 256 * Nat.pow 2 (k * 8) := by
      rw [Nat.add_mul, Nat.one_mul, nat_pow_add_local, Nat.mul_comm]
    rw [hpow]
    have hpos : 0 < Nat.pow 2 (k * 8) := Nat.pow_pos (by decide)
    exact (nat_mod_mul_right_local v 256 (Nat.pow 2 (k * 8)) (by decide) hpos).symm

end Anneal.MiniRust
