-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirMemComp.Memory
public import Anneal.MirMemComp.Codecs

public section

/-!
# Computable MIR Memory & Codec Canaries (`Anneal.MirMemComp.Canaries`)

End-to-end universal and concrete witnesses bridging `Anneal.MirMemComp`
directly into `Trusted.MirSemantics.{allocateStack, readBytes, writeBytes,
loadIndirect, storeIndirect, deinitIndirect, deallocateStack}`:

1. `trusted_stack_u32_lifecycle_and_frame_sound` (`[propext]`): universal
   stack-slot lifecycle (`allocateStack` -> uninitialized `loadIndirect = .ok
   none` -> `storeIndirect` -> exact `loadIndirect` round-trip ->
   `deinitIndirect` -> `loadIndirect = .ok none` -> `deallocateStack` ->
   use-after-free & double-free `.error .undefined`) over arbitrary
   `MemoryState` satisfying `memAllocIdsLt`, arbitrary `u32` scalar `v < 2^32`,
   and arbitrary disjoint pre-existing allocations.
2. `canary_all_indirect_types_roundtrip_trusted` (`[propext]`): concrete
   round-trips across `bool`, `u8`, `i16`, `u32`, `u64`, `u128`, `isize`,
   `char`, `ordering`, `unit`, `(u16, bool)` overflow pairs (with `.uninit`
   padding), zero-sized and direct-tagged fieldless `.enum`s, and both
   `.little` and `.big` endian `encodeUInt`/`decodeUInt`.
3. `canary_mirMemComp_negative_fail_closed_tests` (`[propext]`): 16
   single-cause fail-closed negative scenarios (18 conjuncts) over
   `Trusted.MirSemantics`.
-/

namespace Anneal.MirMemComp

open Trusted.MirAst Trusted.MirSemantics

private theorem ite_bool_falseK {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem listMap_lengthK {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem listTake_zeroK {α : Type} (xs : List α) : xs.take 0 = [] := by
  cases xs <;> rfl

private theorem listDrop_zeroK {α : Type} (xs : List α) : xs.drop 0 = xs := by
  cases xs <;> rfl

private theorem listTake_exactK {α : Type} (xs : List α) :
    xs.take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

private theorem listDrop_exactK {α : Type} (xs : List α) :
    xs.drop xs.length = [] := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem listAppend_nil_rightK {α : Type} (xs : List α) :
    xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons hd _ ih => exact congrArg (List.cons hd) ih

private theorem execInitBytes?_map_init (bs : List UInt8) :
    execInitBytes? (bs.map (fun b => AllocByte.init b none)) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    dsimp only [execInitBytes?, List.map, List.foldr]
    change
      (match execInitBytes? (rest.map (fun b => AllocByte.init b none)) with
       | some bs' => some (b :: bs')
       | none => none) = some (b :: rest)
    rw [ih]

private theorem natMod_eq_of_ltK {x y : Nat} (h : x < y) : Nat.mod x y = x := by
  cases x with
  | zero => rfl
  | succ x' =>
    change ite (y ≤ x' + 1) (Nat.modCore (x' + 1) y) (x' + 1) = x' + 1
    cases Nat.decLe y (x' + 1) with
    | isTrue hLe => exact False.elim (Nat.not_le_of_gt h hLe)
    | isFalse _ => rfl

private theorem bv128_toNat_ofNat_lt_u32 {v : Nat} (hv : v < 4294967296) :
    (BitVec.ofNat 128 v).toNat = v := by
  have hPow : 4294967296 ≤ Nat.pow 2 128 :=
    Nat.le_of_ble_eq_true rfl
  exact natMod_eq_of_ltK (Nat.lt_of_lt_of_le hv hPow)

private theorem mirTruncateBits_i32_of_lt {v : Nat} (hv : v < 4294967296) :
    Anneal.PureLift.mirTruncateBits .i32 (BitVec.ofNat 128 v) =
      BitVec.ofNat 128 v := by
  unfold Anneal.PureLift.mirTruncateBits
  dsimp only
  rw [bv128_toNat_ofNat_lt_u32 hv]
  change BitVec.ofNat 128 (Nat.mod v 4294967296) = BitVec.ofNat 128 v
  rw [natMod_eq_of_ltK hv]

private theorem bv128_bne_self (x : BitVec 128) : (x != x) = false := by
  change (!(x == x)) = false
  have hEq : (x == x) = true := decide_eq_true rfl
  rw [hEq]
  rfl

private theorem mirCheckVal_u32_of_lt {v : Nat} (hv : v < 4294967296) :
    Anneal.PureLift.mirCheckVal (.scalar ⟨.i32, false, BitVec.ofNat 128 v⟩)
      (.int .i32 false) = true := by
  unfold Anneal.PureLift.mirCheckVal Anneal.PureLift.mirValTy?
    Anneal.PureLift.mirScalarWf
  dsimp only
  rw [mirTruncateBits_i32_of_lt hv]
  have hEq : (BitVec.ofNat 128 v == BitVec.ofNat 128 v) = true :=
    decide_eq_true rfl
  rw [hEq]
  rfl

private theorem mirEvalConstLit_u32_of_lt {v : Nat} (hv : v < 4294967296) :
    Anneal.PureLift.mirEvalConstLit (.int .i32 false)
      (.scalar (BitVec.ofNat 128 v)) =
      .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 v⟩) := by
  unfold Anneal.PureLift.mirEvalConstLit
  dsimp only
  rw [mirTruncateBits_i32_of_lt hv, bv128_bne_self, ite_bool_falseK rfl]

/-- Universal `Trusted.MirSemantics` stack `u32` lifecycle and cross-allocation
framing theorem (`[propext]`): for every `m0 : MemoryState` with
`memAllocIdsLt m0.allocations m0.nextAllocId = true`, every `u32` scalar
`v < 2^32`, and every pre-existing place `otherPlace` (`otherPlace.allocId ≠
m0.nextAllocId`), real `Trusted.MirSemantics.{allocateStack, loadIndirect,
storeIndirect, deinitIndirect, deallocateStack}` executes the full uninit ->
store -> round-trip load -> deinit -> dealloc -> use-after-free/double-free
lifecycle while preserving `readBytes` on `otherPlace`. -/
theorem trusted_stack_u32_lifecycle_and_frame_sound
    (m0 : MemoryState) (v : Nat) (otherPlace : MemPlace)
    (oSize oAlign : Nat)
    (hLt : memAllocIdsLt m0.allocations m0.nextAllocId = true)
    (hV : v < 4294967296)
    (hOther : otherPlace.allocId ≠ m0.nextAllocId) :
    let u32Ty : MirTy := .int .i32 false
    let u32Val : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 v⟩
    let res := allocateStack m0 ⟨4, 2⟩
    let m1 := res.1
    let pl := res.2
    loadIndirect m1 u32Ty pl = .ok none ∧
    (∃ m2 m3 m4 : MemoryState,
      storeIndirect m1 u32Ty pl u32Val = .ok m2 ∧
      loadIndirect m2 u32Ty pl = .ok (some u32Val) ∧
      readBytes m2 otherPlace oSize oAlign =
        readBytes m0 otherPlace oSize oAlign ∧
      deinitIndirect m2 u32Ty pl = .ok m3 ∧
      loadIndirect m3 u32Ty pl = .ok none ∧
      deallocateStack m3 pl = .ok m4 ∧
      readBytes m4 pl 4 2 = .error .undefined ∧
      deallocateStack m4 pl = .error .undefined ∧
      readBytes m4 otherPlace oSize oAlign =
        readBytes m0 otherPlace oSize oAlign) := by
  let u32Ty : MirTy := .int .i32 false
  let u32Val : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 v⟩
  let id := m0.nextAllocId
  let pl : MemPlace := ⟨id, 0⟩
  let aInit : Allocation :=
    { allocId := id, alignLog2 := 2, mutability := .mut,
      bytes := List.replicate 4 .uninit, live := true }
  let rawBytes : List UInt8 := execEncodeUInt .big 4 v
  let allocBytes : List AllocByte :=
    rawBytes.map (fun b => AllocByte.init b none)
  have hRawLen : rawBytes.length = 4 := execEncodeUInt_length .big 4 v
  have hAllocLen : allocBytes.length = 4 := by
    rw [listMap_lengthK, hRawLen]
  let aStored : Allocation := { aInit with bytes := allocBytes }
  let m1 : MemoryState :=
    { nextAllocId := id + 1, allocations := m0.allocations ++ [aInit] }
  let m2 : MemoryState :=
    { nextAllocId := id + 1, allocations := m0.allocations ++ [aStored] }
  let m3 : MemoryState := m1
  let m4 : MemoryState :=
    { nextAllocId := id + 1,
      allocations := m0.allocations ++ [{ aInit with live := false }] }
  have hFindInit :
      execFindAllocation id (m0.allocations ++ [aInit]) = some aInit :=
    execFindAllocation_append_lt m0.allocations aInit hLt
  have hFindStored :
      execFindAllocation id (m0.allocations ++ [aStored]) = some aStored :=
    execFindAllocation_append_lt m0.allocations aStored hLt
  have hRepStored :
      execReplaceAllocation aStored (m0.allocations ++ [aInit]) =
        m0.allocations ++ [aStored] :=
    execReplaceAllocation_append_lt m0.allocations aInit aStored hLt rfl
  have hRepDeinit :
      execReplaceAllocation aInit (m0.allocations ++ [aStored]) =
        m0.allocations ++ [aInit] :=
    execReplaceAllocation_append_lt m0.allocations aStored aInit hLt rfl
  have hLoadInit : loadIndirect m1 u32Ty pl = .ok none := by
    rw [← execLoadIndirect_eq]
    unfold execLoadIndirect execReadBytes
    dsimp only [u32Ty, execLayoutOfTy, execIntLayout, pl, m1]
    rw [hFindInit]
    rfl
  have hStore : storeIndirect m1 u32Ty pl u32Val = .ok m2 := by
    rw [← execStoreIndirect_eq]
    unfold execStoreIndirect execEncodeVal execWriteBytes
    dsimp only [u32Ty, u32Val, execLayoutOfTy, execIntLayout,
      execProfileTargetEndian, execByteSize]
    rw [mirCheckVal_u32_of_lt hV, Bool.not_true, ite_bool_falseK rfl,
      bv128_toNat_ofNat_lt_u32 hV]
    change
      (match execFindAllocation id m1.allocations with
       | none => Except.error FaultKind.undefined
       | some a =>
         if Nat.beq allocBytes.length 0 then
           if !execIsAligned a 0 2 then
             Except.error FaultKind.undefined
           else
             Except.ok m1
         else if !a.live || !execIsInBounds a 0 allocBytes.length ||
             !execIsAligned a 0 2 then
           Except.error FaultKind.undefined
         else
           match a.mutability with
           | .shared => Except.error FaultKind.undefined
           | .mut =>
             let bytes' :=
               a.bytes.take 0 ++ allocBytes ++
                 a.bytes.drop (0 + allocBytes.length)
             Except.ok { m1 with
               allocations :=
                 execReplaceAllocation { a with bytes := bytes' }
                   m1.allocations }) = Except.ok m2
    rw [hFindInit]
    dsimp only
    rw [hAllocLen, ite_bool_falseK (rfl : Nat.beq 4 0 = false)]
    dsimp only [aInit, execIsInBounds, execIsAligned]
    rw [listTake_zeroK]
    change
      Except.ok { m1 with
        allocations :=
          execReplaceAllocation
            { aInit with bytes := allocBytes ++ [] } m1.allocations } =
      Except.ok m2
    rw [listAppend_nil_rightK, hRepStored]
  have hLoadStored : loadIndirect m2 u32Ty pl = .ok (some u32Val) := by
    rw [← execLoadIndirect_eq]
    unfold execLoadIndirect execReadBytes
    dsimp only [u32Ty, execLayoutOfTy, execIntLayout, execProfileTargetEndian,
      pl, m2]
    rw [hFindStored]
    change
      (match
        if !Nat.ble 4 allocBytes.length then Except.error FaultKind.undefined
        else Except.ok ((allocBytes.drop 0).take 4) with
       | Except.error k => Except.error k
       | Except.ok bytes => execDecodeVal .big (.int .i32 false) bytes) =
      Except.ok (some u32Val)
    rw [hAllocLen, ite_bool_falseK (rfl : (!Nat.ble 4 4) = false)]
    dsimp only
    rw [listDrop_zeroK, ← hAllocLen, listTake_exactK]
    rw [execDecodeVal_int .big .i32 false allocBytes hAllocLen]
    rw [execInitBytes?_map_init rawBytes]
    dsimp only
    have hPow4 : Nat.pow 256 4 = 4294967296 := rfl
    have hV256 : v < Nat.pow 256 4 := by rw [hPow4]; exact hV
    rw [decodeUInt_encodeUInt_of_lt .big 4 v hV256,
      mirEvalConstLit_u32_of_lt hV]
  have hFrameM2 :
      readBytes m2 otherPlace oSize oAlign =
        readBytes m0 otherPlace oSize oAlign := by
    rw [← execReadBytes_eq, ← execReadBytes_eq]
    unfold execReadBytes
    dsimp only [m2]
    rw [execFindAllocation_append_ne m0.allocations aStored otherPlace.allocId
      hOther]
  have hDeinit : deinitIndirect m2 u32Ty pl = .ok m3 := by
    rw [← execDeinitIndirect_eq]
    unfold execDeinitIndirect execWriteUninit execWriteBytes
    dsimp only [u32Ty, execLayoutOfTy, execIntLayout, pl, m2]
    rw [hFindStored]
    change
      (if !Nat.ble 4 allocBytes.length then Except.error FaultKind.undefined
       else
         Except.ok
           ⟨id + 1,
            execReplaceAllocation
              { aStored with
                bytes := allocBytes.take 0 ++ List.replicate 4 .uninit ++
                  allocBytes.drop 4 }
              (m0.allocations ++ [aStored])⟩) =
      Except.ok m3
    rw [hAllocLen, ite_bool_falseK (rfl : (!Nat.ble 4 4) = false),
      listTake_zeroK, ← hAllocLen, listDrop_exactK, listAppend_nil_rightK]
    change
      Except.ok
        ⟨id + 1, execReplaceAllocation aInit (m0.allocations ++ [aStored])⟩ =
      Except.ok m3
    rw [hRepDeinit]
  have hDead :=
    execDeallocateStack_dead_faults { m0 with nextAllocId := id + 1 } aInit
      0 4 2 [AllocByte.init 0 none] hLt rfl rfl rfl rfl
  have hDealloc : deallocateStack m3 pl = .ok m4 := by
    rw [← execDeallocateStack_eq]
    exact hDead.1
  have hUafRead : readBytes m4 pl 4 2 = .error .undefined := by
    rw [← execReadBytes_eq]
    exact hDead.2.1
  have hDoubleFree : deallocateStack m4 pl = .error .undefined := by
    rw [← execDeallocateStack_eq]
    exact hDead.2.2.2
  have hFrameM4 :
      readBytes m4 otherPlace oSize oAlign =
        readBytes m0 otherPlace oSize oAlign := by
    rw [← execReadBytes_eq, ← execReadBytes_eq]
    unfold execReadBytes
    dsimp only [m4]
    rw [execFindAllocation_append_ne m0.allocations { aInit with live := false }
      otherPlace.allocId hOther]
  exact ⟨hLoadInit, m2, m3, m4, hStore, hLoadStored, hFrameM2, hDeinit,
    hLoadInit, hDealloc, hUafRead, hDoubleFree, hFrameM4⟩

/-- Specification predicate asserting that allocating a fresh stack slot for
`ty` via `Trusted.MirSemantics.allocateStack`, storing `v` via `storeIndirect`,
and loading via `loadIndirect` returns `.ok (some v)`. -/
@[expose] def RoundtripsIndirect (ty : MirTy) (v : Val) : Prop :=
  ∃ (lay : LayoutData) (m2 : MemoryState),
    layoutOfTy ty = some lay ∧
    storeIndirect (allocateStack MemoryState.empty lay).1 ty
      (allocateStack MemoryState.empty lay).2 v = .ok m2 ∧
    loadIndirect m2 ty (allocateStack MemoryState.empty lay).2 = .ok (some v)

/-- Computable stack-slot store/load round-trip mirror (`0` `noncomputable`).
-/
@[expose] def execRoundtripIndirect (ty : MirTy) (v : Val) :
    Except FaultKind (Option Val) :=
  match execLayoutOfTy ty with
  | none => .error .unsupported
  | some lay =>
    let (m1, pl) := execAllocateStack execMemoryEmpty lay
    match execStoreIndirect m1 ty pl v with
    | .error k => .error k
    | .ok m2 => execLoadIndirect m2 ty pl

/-- Any passing computable `execRoundtripIndirect ty v = .ok (some v)` witness
certifies `RoundtripsIndirect ty v` directly over `Trusted.MirSemantics`
(`[propext]`). -/
theorem roundtripsIndirect_of_exec (ty : MirTy) (v : Val)
    (h : execRoundtripIndirect ty v = .ok (some v)) :
    RoundtripsIndirect ty v := by
  unfold execRoundtripIndirect at h
  cases hLay : execLayoutOfTy ty with
  | none => rw [hLay] at h; cases h
  | some lay =>
    rw [hLay] at h
    dsimp only at h
    have hLayT : layoutOfTy ty = some lay := by
      rw [← execLayoutOfTy_eq]; exact hLay
    let p := execAllocateStack execMemoryEmpty lay
    have hPair : p = allocateStack MemoryState.empty lay := by
      unfold p
      rw [execMemoryEmpty_eq, execAllocateStack_eq]
    cases hSt : execStoreIndirect p.1 ty p.2 v with
    | error k =>
      change
        (match execStoreIndirect p.1 ty p.2 v with
         | Except.error k => Except.error k
         | Except.ok m2 => execLoadIndirect m2 ty p.2) =
        Except.ok (some v) at h
      rw [hSt] at h
      cases h
    | ok m2 =>
      change
        (match execStoreIndirect p.1 ty p.2 v with
         | Except.error k => Except.error k
         | Except.ok m2 => execLoadIndirect m2 ty p.2) =
        Except.ok (some v) at h
      rw [hSt] at h
      have hStT :
          storeIndirect (allocateStack MemoryState.empty lay).1 ty
            (allocateStack MemoryState.empty lay).2 v = .ok m2 := by
        rw [← hPair, ← execStoreIndirect_eq]
        exact hSt
      have hLdT :
          loadIndirect m2 ty (allocateStack MemoryState.empty lay).2 =
            .ok (some v) := by
        rw [← hPair, ← execLoadIndirect_eq]
        exact h
      exact ⟨lay, m2, hLayT, hStT, hLdT⟩

/-- Concrete round-trip canary across all supported `Trusted.MirSemantics`
indirect types (`bool`, `u8`, `i16`, `u32`, `u64`, `u128`, `isize`, `char`,
`ordering`, `unit`, `(u16, bool)` overflow pair with `.uninit` padding, and
zero-sized / direct-tagged fieldless `.enum`s) plus `.little` and `.big` endian
`encodeUInt`/`decodeUInt` (`[propext]`). -/
theorem canary_all_indirect_types_roundtrip_trusted :
    let zstEnum : EnumTy :=
      { id := 50, discrWidth := .i8, discrSigned := false,
        tagRepr := .zeroSized, discriminants := [0] }
    let tagEnum : EnumTy :=
      { id := 51, discrWidth := .i8, discrSigned := true,
        tagRepr := .scalar .i8 true, discriminants := [255, 1] }
    RoundtripsIndirect .bool (.bool true) ∧
    RoundtripsIndirect .bool (.bool false) ∧
    RoundtripsIndirect (.int .i8 false)
      (.scalar ⟨.i8, false, BitVec.ofNat 128 0xA5⟩) ∧
    RoundtripsIndirect (.int .i16 true)
      (.scalar ⟨.i16, true, BitVec.ofNat 128 0xFFFE⟩) ∧
    RoundtripsIndirect (.int .i32 false)
      (.scalar ⟨.i32, false, BitVec.ofNat 128 0xDEADBEEF⟩) ∧
    RoundtripsIndirect (.int .i64 false)
      (.scalar ⟨.i64, false, BitVec.ofNat 128 0x0123456789ABCDEF⟩) ∧
    RoundtripsIndirect (.int .i128 false)
      (.scalar ⟨.i128, false,
        BitVec.ofNat 128 0x112233445566778899AABBCCDDEEFF00⟩) ∧
    RoundtripsIndirect (.int .isize true)
      (.scalar ⟨.isize, true,
        BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩) ∧
    RoundtripsIndirect .char (.char 'A') ∧
    RoundtripsIndirect .ordering (.ordering .less) ∧
    RoundtripsIndirect .ordering (.ordering .greater) ∧
    RoundtripsIndirect .unit .unit ∧
    RoundtripsIndirect (.tuple [.int .i16 false, .bool])
      (.tuple [.scalar ⟨.i16, false, BitVec.ofNat 128 40000⟩, .bool true]) ∧
    RoundtripsIndirect (.enum zstEnum) (.enumVal zstEnum 0) ∧
    RoundtripsIndirect (.enum tagEnum) (.enumVal tagEnum 0) ∧
    RoundtripsIndirect (.enum tagEnum) (.enumVal tagEnum 1) ∧
    encodeVal .big (.tuple [.int .i16 false, .bool])
      (.tuple [.scalar ⟨.i16, false, BitVec.ofNat 128 0x1234⟩, .bool true]) =
      .ok [AllocByte.init 0x12 none, AllocByte.init 0x34 none,
           AllocByte.init 0x01 none, AllocByte.uninit] ∧
    decodeUInt .little (encodeUInt .little 4 0x01020304) = 0x01020304 ∧
    decodeUInt .big (encodeUInt .big 4 0x01020304) = 0x01020304 := by
  refine ⟨roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl,
    roundtripsIndirect_of_exec _ _ rfl, ?_, ?_, ?_⟩
  · rw [← execEncodeVal_eq]; rfl
  · rw [← execEncodeUInt_eq, ← execDecodeUInt_eq]; rfl
  · rw [← execEncodeUInt_eq, ← execDecodeUInt_eq]; rfl

/-- 8-byte mutable `MemoryState` fixture (`alignLog2 = 2`). -/
@[expose] def fixtureMut8Mem : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1, alignLog2 := 2, mutability := .mut,
         bytes := List.replicate 8 (AllocByte.init 0x55 none), live := true }] }

/-- 4-byte shared `MemoryState` fixture (`alignLog2 = 2`). -/
@[expose] def fixtureShared4Mem : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 1, alignLog2 := 2, mutability := .shared,
         bytes := List.replicate 4 (AllocByte.init 0xAA none), live := true }] }

/-- Single-cause fail-closed negative regressions directly over
`Trusted.MirSemantics` (`[propext]`): alignment, bounds, mutability, non-zero
dealloc offset, missing allocation, unsupported indirect types, `.uninit`
detection, length mismatch, and invalid `bool`/`char`/`ordering` bit patterns.
-/
theorem canary_mirMemComp_negative_fail_closed_tests :
    -- 1. Unaligned `readBytes` (offset 1, alignLog2 2) -> `.undefined`
    readBytes fixtureMut8Mem ⟨1, 1⟩ 4 2 = .error .undefined ∧
    -- 2. Out-of-bounds `readBytes` (6 + 4 > 8) -> `.undefined`
    readBytes fixtureMut8Mem ⟨1, 6⟩ 4 1 = .error .undefined ∧
    -- 3. Unaligned `writeBytes` -> `.undefined`
    writeBytes fixtureMut8Mem ⟨1, 2⟩ 2 (List.replicate 4 .uninit) =
      .error .undefined ∧
    -- 4. Writing to `.shared` allocation -> `.undefined`
    writeBytes fixtureShared4Mem ⟨1, 0⟩ 2 [AllocByte.init 1 none] =
      .error .undefined ∧
    -- 5. Deallocating `.shared` allocation -> `.undefined`
    deallocateStack fixtureShared4Mem ⟨1, 0⟩ = .error .undefined ∧
    -- 6. Deallocating at non-zero offset -> `.undefined`
    deallocateStack fixtureMut8Mem ⟨1, 4⟩ = .error .undefined ∧
    -- 7. Reading missing `allocId = 99` -> `.undefined`
    readBytes fixtureMut8Mem ⟨99, 0⟩ 4 2 = .error .undefined ∧
    -- 8. Unsupported `.ref` layout -> `none` and `loadIndirect` `.unsupported`
    layoutOfTy (.ref .shared (.int .i32 false)) = none ∧
    loadIndirect fixtureMut8Mem (.ref .shared (.int .i32 false)) ⟨1, 0⟩ =
      .error .unsupported ∧
    -- 9. Unsupported 3-tuple layout -> `none` and `storeIndirect` fails
    layoutOfTy (.tuple [.bool, .bool, .bool]) = none ∧
    storeIndirect fixtureMut8Mem (.tuple [.bool, .bool, .bool]) ⟨1, 0⟩
      (.tuple [.bool true, .bool false, .bool true]) = .error .unsupported ∧
    -- 10. `initBytes?` rejects any `.uninit` byte -> `none`
    initBytes? [AllocByte.init 1 none, AllocByte.uninit] = none ∧
    -- 11. `decodeVal` byte-length mismatch -> `.unsupported`
    decodeVal .big (.int .i32 false) [AllocByte.init 1 none] =
      .error .unsupported ∧
    -- 12. `decodeVal` invalid `bool` byte `2` -> `.undefined`
    decodeVal .big .bool [AllocByte.init 2 none] = .error .undefined ∧
    -- 13. `decodeVal` invalid `char` UTF-16 surrogate `0xD800` -> `.undefined`
    decodeVal .big .char
      [AllocByte.init 0x00 none, AllocByte.init 0x00 none,
       AllocByte.init 0xD8 none, AllocByte.init 0x00 none] =
      .error .undefined ∧
    -- 14. `decodeVal` invalid `ordering` byte `2` -> `.undefined`
    decodeVal .big .ordering [AllocByte.init 2 none] = .error .undefined ∧
    -- 15. `decodeVal` invalid `.enum` discriminant tag `7` -> `.undefined`
    decodeVal .big
      (.enum { id := 52, discrWidth := .i8, discrSigned := false,
               tagRepr := .scalar .i8 false, discriminants := [0, 1] })
      [AllocByte.init 7 none] = .error .undefined ∧
    -- 16. Non-admitted `.enum` (empty discriminants) -> `layoutOfTy = none`
    layoutOfTy
      (.enum { id := 53, discrWidth := .i8, discrSigned := false,
               tagRepr := .zeroSized, discriminants := [] }) = none := by
  rw [← execReadBytes_eq, ← execReadBytes_eq, ← execWriteBytes_eq,
    ← execWriteBytes_eq, ← execDeallocateStack_eq, ← execDeallocateStack_eq,
    ← execReadBytes_eq, ← execLayoutOfTy_eq, ← execLoadIndirect_eq,
    ← execLayoutOfTy_eq, ← execStoreIndirect_eq, ← execInitBytes?_eq,
    ← execDecodeVal_eq, ← execDecodeVal_eq, ← execDecodeVal_eq,
    ← execDecodeVal_eq, ← execDecodeVal_eq, ← execLayoutOfTy_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

end Anneal.MirMemComp

end
