-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Init.Data.UInt.BasicAux
public import Init.Data.Nat.Div.Basic
public import Init.Data.Int.Basic
public import Trusted.CppAst
public import Trusted.CppSemantics.State

@[expose] public section

namespace Trusted.CppSemantics

open Trusted.CppAst

/-!
# Rung-0 C11 Memory, Provenance, and Strict Aliasing
(`Trusted.CppSemantics.Memory`)

Tactic-free Ring-0 memory rules implementing LP64 type layout, PNVI-ae-udi
provenance/liveness/alignment/bounds checks, and strict `.uninit` scalar
detection. Programs compiled with strict aliasing are not admitted; accesses
under such a policy fail closed with `.unsupported`.
-/

/-- Pointer size in bytes from `policy` (`8` on LP64). -/
noncomputable def ptrByteSize (policy : CppLangPolicy) : Nat :=
  Nat.div policy.pointerWidthBits 8

/-- Exclusive upper bound `2^64` on LP64 addresses. -/
noncomputable def ptrAddrBound : Nat := Nat.pow 2 64

/-- Byte size of a `CppTy` (`none` for `.void` or unknown records). -/
noncomputable def cppTySize? (policy : CppLangPolicy)
    (records : List CppRecordDef) : CppTy → Option Nat
  | .void         => none
  | .bool         => some 1
  | .int w _ _    => some w.byteSize
  | .ptr _ _ _ _  => some (ptrByteSize policy)
  | .array elem n =>
    match cppTySize? policy records elem with
    | some esz => some (esz * n)
    | none     => none
  | .record rid =>
    match findRecord? records rid with
    | some r => some r.sizeBytes
    | none   => none

/-- Alignment in bytes of a `CppTy`. -/
noncomputable def cppTyAlign? (policy : CppLangPolicy)
    (records : List CppRecordDef) : CppTy → Option Nat
  | .void         => none
  | .bool         => some 1
  | .int w _ _    => some w.byteSize
  | .ptr _ _ _ _  => some (ptrByteSize policy)
  | .array elem _ => cppTyAlign? policy records elem
  | .record rid   =>
    match findRecord? records rid with
    | some r => if Nat.blt 0 r.alignBytes then some r.alignBytes else none
    | none   => none

/-- `true` iff `fields`, starting at bit `cursor`, are listed in ascending
order and cover every bit up to `endBits` exactly once, every field is named
(an unnamed bit-field is padding), every bit-field is an integer no wider than
its type, and every non-bit-field member's type satisfies `chk`. -/
noncomputable def fieldsDense (policy : CppLangPolicy)
    (records : List CppRecordDef) (chk : CppTy → Bool) (cursor endBits : Nat) :
    List CppFieldDecl → Bool
  | [] => Nat.beq cursor endBits
  | f :: fs =>
    !(f.name == "") && Nat.beq f.offsetBits cursor &&
      match f.bitWidth with
      | some w =>
        -- A `bool` bit-field, or one wider than its integer type, has
        -- padding bits (C++20 [class.bit]p1).
        (match f.ty with
         | .int fw _ _ => Nat.blt 0 w && Nat.ble w fw.bitWidth
         | _ => false) &&
          fieldsDense policy records chk (cursor + w) endBits fs
      | none =>
        chk f.ty &&
          match cppTySize? policy records f.ty with
          | some sz =>
            Nat.blt 0 sz &&
              fieldsDense policy records chk (cursor + sz * 8) endBits fs
          | none => false

/-- `true` iff every bit of a `ty` object belongs to its value representation
(no padding bytes or bits), within `fuel` levels of nesting. `bool` has seven
padding bits (C11 §6.2.6.2p1) and counts as padding-free only when `boolOk`;
unions and unknown records never do. -/
noncomputable def tyHasNoPadding (policy : CppLangPolicy)
    (records : List CppRecordDef) (boolOk : Bool) : Nat → CppTy → Bool
  | 0, _ => false
  | _ + 1, .void => false
  | _ + 1, .bool => boolOk
  | _ + 1, .int _ _ _ => true
  | _ + 1, .ptr _ _ _ _ => true
  | fuel + 1, .array elem _ => tyHasNoPadding policy records boolOk fuel elem
  | fuel + 1, .record rid =>
    match findRecord? records rid with
    | some r =>
      !r.isUnion &&
        fieldsDense policy records (tyHasNoPadding policy records boolOk fuel)
          0 (r.sizeBytes * 8) r.fields
    | none => false

/-- Look up an allocation by `allocId`. -/
noncomputable def findAlloc? (aid : Nat) : List CppAlloc → Option CppAlloc
  | [] => none
  | a :: rest =>
    if Nat.beq a.allocId aid then some a else findAlloc? aid rest

/-- Replace an allocation matching `aid` in `allocs`. -/
noncomputable def replaceAlloc? (aid : Nat) (newAlloc : CppAlloc) :
    List CppAlloc → Option (List CppAlloc)
  | [] => none
  | a :: rest =>
    if Nat.beq a.allocId aid then some (newAlloc :: rest)
    else
      match replaceAlloc? aid newAlloc rest with
      | some rest' => some (a :: rest')
      | none       => none

/-- Return `true` iff `aid` does not appear in `seen`. -/
noncomputable def allocIdNotSeen (aid : Nat) : List Nat → Bool
  | [] => true
  | x :: rest => !Nat.beq aid x && allocIdNotSeen aid rest

/-- One past the last address occupied by `a` (a zero-sized allocation
occupies one address, so distinct objects have distinct addresses). -/
noncomputable def allocEnd (a : CppAlloc) : Nat :=
  a.baseAddr + (if Nat.blt 0 a.sizeBytes then a.sizeBytes else 1)

/-- Validate `CppAlloc` list invariants (non-zero unique IDs, alignment,
non-zero aligned `baseAddr`, `bytes.length == sizeBytes`, and every allocation
below `nextAddr`, so later stack allocations cannot overlap it). -/
noncomputable def allocsValidAux (seen : List Nat) (nextId nextAddr : Nat) :
    List CppAlloc → Bool
  | [] => true
  | a :: rest =>
    Nat.blt 0 a.allocId && Nat.blt a.allocId nextId &&
    allocIdNotSeen a.allocId seen && Nat.blt 0 a.alignBytes &&
    Nat.blt 0 a.baseAddr && Nat.beq (Nat.mod a.baseAddr a.alignBytes) 0 &&
    Nat.beq a.bytes.length a.sizeBytes && Nat.ble (allocEnd a) nextAddr &&
    allocsValidAux (a.allocId :: seen) nextId nextAddr rest

/-- `true` iff `a` is dead or overlaps no live allocation in `others`. -/
noncomputable def allocDisjointFrom (a : CppAlloc) : List CppAlloc → Bool
  | [] => true
  | b :: rest =>
    (!a.live || !b.live || Nat.ble (allocEnd a) b.baseAddr ||
      Nat.ble (allocEnd b) a.baseAddr) && allocDisjointFrom a rest

/-- `true` iff the live allocations in `allocs` occupy disjoint addresses. -/
noncomputable def allocsDisjoint : List CppAlloc → Bool
  | [] => true
  | a :: rest => allocDisjointFrom a rest && allocsDisjoint rest

/-- Validate `CppMemory` well-formedness: every allocation, and so every
in-bounds or one-past-the-end address, lies below `nextAddr < 2^64`. -/
noncomputable def validCppMemory (mem : CppMemory) : Bool :=
  Nat.blt 0 mem.nextAllocId && Nat.blt 0 mem.nextAddr &&
    Nat.blt mem.nextAddr ptrAddrBound &&
    allocsValidAux [] mem.nextAllocId mem.nextAddr mem.allocs &&
    allocsDisjoint mem.allocs

/-- Align `addr` upward to a multiple of `align`. -/
noncomputable def alignUp (addr align : Nat) : Nat :=
  let rem := Nat.mod addr align
  if Nat.beq rem 0 then addr else addr + (align - rem)

/-- Allocate a live stack object initialized to `.uninit` bytes. -/
noncomputable def allocStack (mem : CppMemory) (sizeBytes alignBytes : Nat)
    (isConst : Bool) (effTy : Option CppTy) : Nat × CppMemory :=
  let align := if Nat.blt 0 alignBytes then alignBytes else 1
  let base := alignUp mem.nextAddr align
  let aid := mem.nextAllocId
  let alloc : CppAlloc := {
    allocId := aid, sizeBytes := sizeBytes, alignBytes := align,
    live := true, isConst := isConst, effectiveTy := effTy,
    bytes := cppReplicate sizeBytes .uninit, baseAddr := base
  }
  let bump := if Nat.blt 0 sizeBytes then sizeBytes else 1
  (aid, { allocs := alloc :: mem.allocs, nextAllocId := aid + 1,
          nextAddr := alignUp (base + bump) 16 })

/-- Mark allocation `aid` dead (`live := false`). -/
noncomputable def freeAlloc (mem : CppMemory) (aid : Nat) : CppMemory :=
  match findAlloc? aid mem.allocs with
  | none => mem
  | some a =>
    match replaceAlloc? aid { a with live := false } mem.allocs with
    | some allocs' => { mem with allocs := allocs' }
    | none         => mem

/-- Mark a list of stack allocations dead on function return. -/
noncomputable def freeAllocs (mem : CppMemory) : List Nat → CppMemory
  | []        => mem
  | aid :: rs => freeAllocs (freeAlloc mem aid) rs

/-- `true` iff allocation `aid` exists and is live. -/
noncomputable def ptrLive (mem : CppMemory) (aid : Nat) : Bool :=
  match findAlloc? aid mem.allocs with
  | some a => a.live
  | none   => false

/-- `true` iff `[addr, addr + len)` lies inside live allocation `aid`. -/
noncomputable def placeInBounds (mem : CppMemory) (aid : Option Nat)
    (addr len : Nat) : Bool :=
  match aid with
  | none => false
  | some id =>
    match findAlloc? id mem.allocs with
    | none => false
    | some a =>
      a.live && Nat.ble a.baseAddr addr &&
        Nat.ble (addr - a.baseAddr + len) a.sizeBytes

/-- `true` iff `[addr, addr + len)` lies inside subobject range `sr` (no
range means the whole allocation, checked separately). -/
noncomputable def subRangeContains (sr : Option (Nat × Nat))
    (addr len : Nat) : Bool :=
  match sr with
  | none          => true
  | some (lo, sz) => Nat.ble lo addr && Nat.ble (addr + len) (lo + sz)

/-- `true` iff pointer `(id, addr, sr)` points into live allocation `id` or
one past its end, and `sr` (if any) is a range inside the allocation that
contains `addr` or ends at it. -/
noncomputable def ptrInRangeOrEnd (mem : CppMemory) (id addr : Nat)
    (sr : Option (Nat × Nat)) : Bool :=
  match findAlloc? id mem.allocs with
  | none => false
  | some a =>
    a.live && Nat.ble a.baseAddr addr &&
      Nat.ble addr (a.baseAddr + a.sizeBytes) &&
      match sr with
      | none => true
      | some (lo, sz) =>
        Nat.ble a.baseAddr lo && Nat.ble (lo + sz) (a.baseAddr + a.sizeBytes) &&
          Nat.ble lo addr && Nat.ble addr (lo + sz)

/-- Structural equality on `Option (Nat × Nat)`. -/
noncomputable def optRangeBeq : Option (Nat × Nat) → Option (Nat × Nat) → Bool
  | none,          none          => true
  | some (a1, b1), some (a2, b2) => Nat.beq a1 a2 && Nat.beq b1 b2
  | _,             _             => false

/-- Encode unsigned integer `uval` into `nbytes` little-endian `CppByte`s. -/
noncomputable def encodeIntBytes (nbytes : Nat) (uval : Nat) : List CppByte :=
  match nbytes with
  | 0 => []
  | k + 1 =>
    .data (UInt8.ofNat (Nat.mod uval 256)) ::
      encodeIntBytes k (Nat.div uval 256)

/-- Decode little-endian `CppByte`s; fails (`none`) on `.uninit`/`.ptrFrag`. -/
noncomputable def decodeIntBytes : List CppByte → Option Nat
  | [] => some 0
  | .data b :: rest =>
    match decodeIntBytes rest with
    | some hi => some (b.toNat + 256 * hi)
    | none    => none
  | .uninit :: _        => none
  | .ptrFrag _ _ _ _ :: _ => none

/-- Encode pointer provenance/address/subobject range into `remaining`
`CppByte`s. -/
noncomputable def encodePtrBytesAux (aid : Option Nat) (addr : Nat)
    (sr : Option (Nat × Nat)) (idx remaining : Nat) : List CppByte :=
  match remaining with
  | 0 => []
  | k + 1 =>
    let b := match aid with
      | some id => CppByte.ptrFrag id addr sr idx
      | none    =>
        CppByte.data
          (UInt8.ofNat (Nat.mod (Nat.div addr (Nat.pow 256 idx)) 256))
    b :: encodePtrBytesAux aid addr sr (idx + 1) k

/-- Verify consecutive `ptrFrag` bytes for `(aid, addr, sr)`. -/
noncomputable def decodePtrFragsAux (aid addr : Nat) (sr : Option (Nat × Nat))
    (idx : Nat) : List CppByte → Bool
  | [] => true
  | .ptrFrag id2 a2 sr2 i2 :: rest =>
    Nat.beq aid id2 && Nat.beq addr a2 && optRangeBeq sr sr2 &&
      Nat.beq idx i2 && decodePtrFragsAux aid addr sr (idx + 1) rest
  | _ :: _ => false

/-- Decode pointer bytes; fails on `.uninit` or mixed provenance fragments. -/
noncomputable def decodePtrBytes (bs : List CppByte) : Option CppVal :=
  match bs with
  | .ptrFrag aid addr sr 0 :: rest =>
    if decodePtrFragsAux aid addr sr 1 rest then
      some (.ptr (some aid) addr sr)
    else none
  | _ =>
    match decodeIntBytes bs with
    | some addr => some (.ptr none addr none)
    | none      => none

/-- Encode a typed `CppVal` into raw `CppByte`s. -/
noncomputable def encodeValBytes (policy : CppLangPolicy)
    (records : List CppRecordDef) (v : CppVal) (ty : CppTy) :
    Option (List CppByte) :=
  match v, ty with
  | .bool b, .bool =>
    some [.data (UInt8.ofNat (if b then 1 else 0))]
  | .int w1 s1 bits, .int w2 s2 _ =>
    if CppIntWidth.beq w1 w2 && Signedness.beq s1 s2 then
      some (encodeIntBytes w1.byteSize bits)
    else none
  | .ptr aid addr sr, .ptr _ _ _ _ =>
    some (encodePtrBytesAux aid addr sr 0 (ptrByteSize policy))
  | .aggregate bs, .array elem n =>
    match cppTySize? policy records (.array elem n) with
    | some sz => if Nat.beq bs.length sz then some bs else none
    | none    => none
  | .aggregate bs, .record rid =>
    match findRecord? records rid with
    | some r => if Nat.beq bs.length r.sizeBytes then some bs else none
    | none   => none
  | _, _ => none

/-- Decode raw `CppByte`s into a typed `CppVal` (scalar `.uninit` -> `none`). -/
noncomputable def decodeValBytes (policy : CppLangPolicy)
    (records : List CppRecordDef) (bs : List CppByte) (ty : CppTy) :
    Option CppVal :=
  match ty with
  | .void => none
  | .bool =>
    match bs with
    | [.data b] =>
      if Nat.beq b.toNat 0 then some (.bool false)
      else if Nat.beq b.toNat 1 then some (.bool true)
      else none
    | _ => none
  | .int w s _ =>
    if Nat.beq bs.length w.byteSize then
      match decodeIntBytes bs with
      | some u => some (.int w s (Nat.mod u (Nat.pow 2 w.bitWidth)))
      | none   => none
    else none
  | .ptr _ _ _ _ =>
    if Nat.beq bs.length (ptrByteSize policy) then decodePtrBytes bs else none
  | .array elem n =>
    match cppTySize? policy records (.array elem n) with
    | some sz => if Nat.beq bs.length sz then some (.aggregate bs) else none
    | none    => none
  | .record rid =>
    match findRecord? records rid with
    | some r =>
      if Nat.beq bs.length r.sizeBytes then some (.aggregate bs) else none
    | none   => none

/-- `true` iff every byte is an initialized data byte (no `.uninit` and no
pointer-provenance fragment). -/
noncomputable def bytesAllData : List CppByte → Bool
  | [] => true
  | .data _ :: rest => bytesAllData rest
  | .uninit :: _ => false
  | .ptrFrag _ _ _ _ :: _ => false

/-- `true` iff `ptr (aid, addr, sr)` is a well-formed LP64 pointer value: its
address and range lie below `2^64` and a range contains or ends at `addr`;
when `mem` is given, a pointer with provenance must also point into (or one
past) its live allocation and range. -/
noncomputable def ptrValOk (memOpt : Option CppMemory) (aid : Option Nat)
    (addr : Nat) (sr : Option (Nat × Nat)) : Bool :=
  Nat.blt addr ptrAddrBound &&
    (match sr with
     | none => true
     | some (lo, sz) =>
       Nat.ble lo addr && Nat.ble addr (lo + sz) &&
         Nat.blt (lo + sz) ptrAddrBound) &&
    match memOpt, aid with
    | some mem, some id => ptrInRangeOrEnd mem id addr sr
    | _, _ => true

/-- `true` iff `n` consecutive `esz`-byte chunks of `bs` each satisfy `chk`. -/
noncomputable def aggElemsValid (chk : List CppByte → Bool) (esz : Nat) :
    Nat → List CppByte → Bool
  | 0, _ => true
  | n + 1, bs => chk (bs.take esz) && aggElemsValid chk esz n (bs.drop esz)

/-- `true` iff every field of a record in bytes `bs` holds a valid value:
members by `chk`, bit-fields by having only initialized data bytes. -/
noncomputable def aggFieldsValid (policy : CppLangPolicy)
    (records : List CppRecordDef) (chk : List CppByte → CppTy → Bool)
    (bs : List CppByte) : List CppFieldDecl → Bool
  | [] => true
  | f :: fs =>
    (match f.bitWidth with
     | some w =>
       bytesAllData
         (cppListSlice bs (Nat.div f.offsetBits 8)
           (Nat.div (f.offsetBits + w + 7) 8 - Nat.div f.offsetBits 8))
     | none =>
       match cppTySize? policy records f.ty with
       | some fsz => chk (cppListSlice bs (Nat.div f.offsetBits 8) fsz) f.ty
       | none => false) &&
      aggFieldsValid policy records chk bs fs

/-- `true` iff bytes `bs` hold a valid value of type `ty` member by member
(C++20 [conv.lval] and [basic.indet]p2: copying an aggregate reads each
member): every scalar initialized, every `bool` `0` or `1`, and every pointer
well formed (`ptrValOk`), within `fuel` levels of nesting. -/
noncomputable def aggBytesValid (policy : CppLangPolicy)
    (records : List CppRecordDef) (memOpt : Option CppMemory) :
    Nat → List CppByte → CppTy → Bool
  | 0, _, _ => false
  | _ + 1, _, .void => false
  | _ + 1, bs, .bool =>
    match bs with
    | [.data b] => Nat.beq b.toNat 0 || Nat.beq b.toNat 1
    | _ => false
  | _ + 1, bs, .int w _ _ =>
    Nat.beq bs.length w.byteSize &&
      match decodeIntBytes bs with
      | some _ => true
      | none   => false
  | _ + 1, bs, .ptr _ _ _ _ =>
    Nat.beq bs.length (ptrByteSize policy) &&
      match decodePtrBytes bs with
      | some (.ptr aid addr sr) => ptrValOk memOpt aid addr sr
      | _ => false
  | fuel + 1, bs, .array elem n =>
    match cppTySize? policy records elem with
    | some esz =>
      Nat.beq bs.length (esz * n) &&
        aggElemsValid
          (fun chunk => aggBytesValid policy records memOpt fuel chunk elem)
          esz n bs
    | none => false
  | fuel + 1, bs, .record rid =>
    match findRecord? records rid with
    | some r =>
      !r.isUnion && Nat.beq bs.length r.sizeBytes &&
        aggFieldsValid policy records (aggBytesValid policy records memOpt fuel)
          bs r.fields
    | none => false

/-- Check that `v` is a canonical value of type `ty`: integers in range,
pointers below `2^64` with well-formed ranges, and aggregates of padding-free
types whose members are all valid. -/
noncomputable def checkCppVal (policy : CppLangPolicy)
    (records : List CppRecordDef) (v : CppVal) (ty : CppTy) : Bool :=
  match v, ty with
  | .void, .void => true
  | .bool _, .bool => true
  | .int w1 s1 bits, .int w2 s2 _ =>
    CppIntWidth.beq w1 w2 && Signedness.beq s1 s2 &&
      Nat.blt bits (Nat.pow 2 w1.bitWidth)
  | .ptr aid addr sr, .ptr _ _ _ _ => ptrValOk none aid addr sr
  | .aggregate bs, .array elem n =>
    tyHasNoPadding policy records true 16 (.array elem n) &&
      aggBytesValid policy records none 16 bs (.array elem n)
  | .aggregate bs, .record rid =>
    tyHasNoPadding policy records true 16 (.record rid) &&
      aggBytesValid policy records none 16 bs (.record rid)
  | _, _ => false

/-- Check that argument values match parameter types elementwise. -/
noncomputable def checkCppArgs (policy : CppLangPolicy)
    (records : List CppRecordDef) : List CppVal → List CppTy → Bool
  | [], [] => true
  | v :: vs, t :: ts =>
    checkCppVal policy records v t && checkCppArgs policy records vs ts
  | _, _ => false

/-- `true` iff every pointer in value `v` of type `ty` (including inside an
aggregate) points into, or one past, a live allocation of `mem` (C11 §6.2.4p2:
a pointer to a dead object is indeterminate). -/
noncomputable def valLiveInMem (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) (v : CppVal) (ty : CppTy) :
    Bool :=
  match v with
  | .ptr aid addr sr => ptrValOk (some mem) aid addr sr
  | .aggregate bs => aggBytesValid policy records (some mem) 16 bs ty
  | _ => true

/-- `valLiveInMem` for every argument against its parameter type. -/
noncomputable def argsLiveInMem (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) :
    List CppVal → List CppTy → Bool
  | v :: vs, t :: ts =>
    valLiveInMem policy records mem v t &&
      argsLiveInMem policy records mem vs ts
  | _, _ => true

/-- Shared provenance, liveness, constness, alignment, and bounds guard for
`readMemory` and `writeMemory`. Fails closed with `.unsupported` under a
strict-aliasing policy (no type-based aliasing model yet), on `restrict`
pointer types, and on by-value accesses to types with padding (whose padding
bytes a copy would make indeterminate). `alignCap` lowers the required
alignment for members of packed records; `_mayAlias` is reserved for
type-based alias analysis. -/
noncomputable def validateMemAccess (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) (allocId : Option Nat)
    (addr : Nat) (accessTy : CppTy) (_mayAlias isWrite : Bool)
    (alignCap : Option Nat) :
    Except CppFaultKind (Nat × CppAlloc × Nat × Nat) :=
  if policy.strictAliasing || !CppTy.noRestrict accessTy ||
     !tyHasNoPadding policy records true 16 accessTy then
    .error .unsupported
  else
  match cppTySize? policy records accessTy,
        cppTyAlign? policy records accessTy with
  | some sz, some tyAlign =>
    let align := match alignCap with
      | some c => if Nat.blt 0 c && Nat.blt c tyAlign then c else tyAlign
      | none   => tyAlign
    match allocId with
    | none => .error .undefined
    | some aid =>
      match findAlloc? aid mem.allocs with
      | none => .error .undefined
      | some alloc =>
        if !alloc.live || (isWrite && alloc.isConst) ||
           !Nat.beq (Nat.mod addr align) 0 || Nat.blt addr alloc.baseAddr then
          .error .undefined
        else
          let off := addr - alloc.baseAddr
          if Nat.blt alloc.sizeBytes (off + sz) then .error .undefined
          else .ok (aid, alloc, off, sz)
  | _, _ => .error .unsupported

/-- Read a value of type `accessTy` from `(allocId, addr)`. Reading an
uninitialized scalar, an invalid `bool`, or a pointer to a dead allocation,
including any member of an aggregate, is `.undefined`. -/
noncomputable def readMemory (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) (allocId : Option Nat)
    (addr : Nat) (accessTy : CppTy) (mayAlias : Bool)
    (alignCap : Option Nat) : Except CppFaultKind CppVal :=
  match validateMemAccess policy records mem allocId addr accessTy mayAlias
          false alignCap with
  | .error k => .error k
  | .ok (_, alloc, off, sz) =>
    match decodeValBytes policy records (cppListSlice alloc.bytes off sz)
            accessTy with
    | some v =>
      if valLiveInMem policy records mem v accessTy then .ok v
      else .error .undefined
    | none   => .error .undefined

/-- Write a value of type `accessTy` to `(allocId, addr)`. -/
noncomputable def writeMemory (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) (allocId : Option Nat)
    (addr : Nat) (accessTy : CppTy) (mayAlias : Bool) (v : CppVal)
    (alignCap : Option Nat) : Except CppFaultKind CppMemory :=
  match validateMemAccess policy records mem allocId addr accessTy mayAlias
          true alignCap with
  | .error k => .error k
  | .ok (aid, alloc, off, _) =>
    match encodeValBytes policy records v accessTy with
    | none => .error .unsupported
    | some encoded =>
      match cppListWriteSlice alloc.bytes off encoded with
      | none => .error .undefined
      | some bytes' =>
        let alloc' := { alloc with bytes := bytes' }
        match replaceAlloc? aid alloc' mem.allocs with
        | some allocs' => .ok { mem with allocs := allocs' }
        | none         => .error .undefined

/-- Overwrite raw bytes at `(allocId, addr)` as a character-type access
(bit-field stores). -/
noncomputable def writeRawBytes (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) (allocId : Option Nat)
    (addr : Nat) (bs : List CppByte) : Except CppFaultKind CppMemory :=
  match validateMemAccess policy records mem allocId addr
          (.array (.int .w8 .unsigned true) bs.length) false true none with
  | .error k => .error k
  | .ok (aid, alloc, off, _) =>
    match cppListWriteSlice alloc.bytes off bs with
    | none => .error .undefined
    | some bytes' =>
      match replaceAlloc? aid { alloc with bytes := bytes' } mem.allocs with
      | some allocs' => .ok { mem with allocs := allocs' }
      | none         => .error .undefined

/-- Zero-initialize the `ty` object at `(allocId, addr)`: every byte, padding
included, becomes `0` (C++20 [dcl.init]p6). The same guards as
`validateMemAccess` apply, except that `ty` may have padding: this is not a
by-value copy. -/
noncomputable def writeZeroMemory (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) (allocId : Option Nat)
    (addr : Nat) (ty : CppTy) (alignCap : Option Nat) :
    Except CppFaultKind CppMemory :=
  if policy.strictAliasing || !CppTy.noRestrict ty then .error .unsupported
  else
  match cppTySize? policy records ty, cppTyAlign? policy records ty with
  | some sz, some tyAlign =>
    let align := match alignCap with
      | some c => if Nat.blt 0 c && Nat.blt c tyAlign then c else tyAlign
      | none   => tyAlign
    match allocId with
    | none => .error .undefined
    | some aid =>
      match findAlloc? aid mem.allocs with
      | none => .error .undefined
      | some alloc =>
        if !alloc.live || alloc.isConst || !Nat.beq (Nat.mod addr align) 0 ||
           Nat.blt addr alloc.baseAddr ||
           Nat.blt alloc.sizeBytes (addr - alloc.baseAddr + sz) then
          .error .undefined
        else
          match cppListWriteSlice alloc.bytes (addr - alloc.baseAddr)
                  (cppReplicate sz (.data (UInt8.ofNat 0))) with
          | none => .error .undefined
          | some bytes' =>
            match replaceAlloc? aid { alloc with bytes := bytes' }
                    mem.allocs with
            | some allocs' => .ok { mem with allocs := allocs' }
            | none         => .error .undefined
  | _, _ => .error .unsupported

/-- C++ zero-initialized value of scalar `ty`. -/
noncomputable def zeroValOf? (ty : CppTy) : Option CppVal :=
  match ty with
  | .void => none
  | .bool => some (.bool false)
  | .int w s _ => some (.int w s 0)
  | .ptr _ _ _ _ => some (.ptr none 0 none)
  | _ => none

/-- Interpret integer `CppVal` as mathematical `Int`. -/
noncomputable def cppIntToMathInt (w : CppIntWidth) (s : Signedness)
    (u : Nat) : Int :=
  match s with
  | .unsigned => Int.ofNat u
  | .signed =>
    let half := Nat.pow 2 (w.bitWidth - 1)
    if Nat.blt u half then Int.ofNat u
    else Int.negSucc (Nat.pow 2 w.bitWidth - u - 1)

/-- PNVI-ae-udi pointer addition (`base + offset * sizeof(elemTy)`), enforcing
live provenance and that the result stays within the pointer's subobject
range, or its allocation if it has none, or one past its end (C11 §6.5.6p8).
`NULL + 0` is `.unsupported`: C leaves it undefined, C++ defines it. -/
noncomputable def ptrAddOffset (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) (elemTy : CppTy)
    (base : CppVal) (offset : CppVal) : Except CppFaultKind CppVal :=
  match cppTySize? policy records elemTy with
  | none => .error .unsupported
  | some elemSize =>
    match base, offset with
    | .ptr (some aid) addr sr, .int ow os obits =>
      match findAlloc? aid mem.allocs with
      | none => .error .undefined
      | some alloc =>
        let lo := match sr with
          | some (l, _) => l
          | none => alloc.baseAddr
        let hi := match sr with
          | some (l, sz) => l + sz
          | none => alloc.baseAddr + alloc.sizeBytes
        if !alloc.live || Nat.blt addr lo || Nat.blt hi addr then
          .error .undefined
        else
          match cppIntToMathInt ow os obits with
          | Int.ofNat k =>
            let newAddr := addr + k * elemSize
            if Nat.ble newAddr hi then .ok (.ptr (some aid) newAddr sr)
            else .error .undefined
          | Int.negSucc k =>
            let delta := (k + 1) * elemSize
            if Nat.ble (lo + delta) addr then
              .ok (.ptr (some aid) (addr - delta) sr)
            else .error .undefined
    | .ptr none addr _, .int _ _ obits =>
      if Nat.beq addr 0 && Nat.beq obits 0 then .error .unsupported
      else .error .undefined
    | _, _ => .error .unsupported

end Trusted.CppSemantics

end
