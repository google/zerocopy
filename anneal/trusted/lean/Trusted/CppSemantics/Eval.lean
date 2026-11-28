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
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Trusted.CppAst
public import Trusted.CppSemantics.State
public import Trusted.CppSemantics.Memory

@[expose] public section

namespace Trusted.CppSemantics

open Trusted.CppAst

/-!
# Rung-0 C11 Expression and Place Evaluation (`Trusted.CppSemantics.Eval`)

Tactic-free Ring-0 evaluator for side-effect-free SSENF `CppExpr` and
`CppPlace` trees enforcing C11 `isoUB`/`wrapv` integer rules, division/shift
UB, PNVI-ae-udi pointer arithmetic and dereference bounds, and `.uninit`
detection.
-/

/-- `2^k` helper. -/
noncomputable def pow2 (k : Nat) : Nat := Nat.pow 2 k

/-- Return `true` iff mathematical integer `x` lies in `[-2^(W-1), 2^(W-1)-1]`.
-/
noncomputable def signedInRange (w : CppIntWidth) (x : Int) : Bool :=
  let half := pow2 (w.bitWidth - 1)
  match x with
  | Int.ofNat n   => Nat.blt n half
  | Int.negSucc n => Nat.blt n half

/-- Convert mathematical `Int` to canonical `W`-bit unsigned representation. -/
noncomputable def ofSignedIntWrap (w : CppIntWidth) (x : Int) : Nat :=
  let m := pow2 w.bitWidth
  match x with
  | Int.ofNat n   => Nat.mod n m
  | Int.negSucc n =>
    let r := Nat.mod (n + 1) m
    if Nat.beq r 0 then 0 else m - r

/-- Sign flag on `Int` (`true` iff strictly negative). -/
noncomputable def intIsNeg : Int → Bool
  | Int.ofNat _   => false
  | Int.negSucc _ => true

/-- Absolute value of `Int`. -/
noncomputable def intAbs : Int → Nat
  | Int.ofNat n   => n
  | Int.negSucc n => n + 1

/-- Construct an `Int` from sign flag and magnitude. -/
noncomputable def intFromSignMag (neg : Bool) (mag : Nat) : Int :=
  if neg then
    match mag with
    | 0     => Int.ofNat 0
    | k + 1 => Int.negSucc k
  else Int.ofNat mag

/-- Boolean equality on `Int`. -/
noncomputable def intBeq : Int → Int → Bool
  | Int.ofNat a,   Int.ofNat b   => Nat.beq a b
  | Int.negSucc a, Int.negSucc b => Nat.beq a b
  | _,             _             => false

/-- Strict less-than on `Int`. -/
noncomputable def intBlt : Int → Int → Bool
  | Int.ofNat a,   Int.ofNat b   => Nat.blt a b
  | Int.negSucc _, Int.ofNat _   => true
  | Int.ofNat _,   Int.negSucc _ => false
  | Int.negSucc a, Int.negSucc b => Nat.blt b a

/-- Check whether `x = INT_MIN` for signed width `w`. -/
noncomputable def isSignedMin (w : CppIntWidth) (x : Int) : Bool :=
  match x with
  | Int.negSucc n => Nat.beq (n + 1) (pow2 (w.bitWidth - 1))
  | Int.ofNat _   => false

/-- Apply `isoUB` vs. `wrapv` signed overflow policy to result `r`. -/
noncomputable def finishSignedArith (policy : CppLangPolicy) (w : CppIntWidth)
    (r : Int) : Except CppFaultKind CppVal :=
  match policy.signedOverflow with
  | .isoUB =>
    if signedInRange w r then .ok (.int w .signed (ofSignedIntWrap w r))
    else .error .undefined
  | .wrapv => .ok (.int w .signed (ofSignedIntWrap w r))

/-- Evaluate a unary operator `op` on value `v`. -/
noncomputable def evalUnOp (policy : CppLangPolicy) (mem : CppMemory)
    (op : CppUnOp) (v : CppVal) : Except CppFaultKind CppVal :=
  match op, v with
  | .neg, .int w .unsigned bits =>
    let m := pow2 w.bitWidth
    .ok (.int w .unsigned (if Nat.beq bits 0 then 0 else Nat.mod (m - bits) m))
  | .neg, .int w .signed bits =>
    finishSignedArith policy w (Int.neg (cppIntToMathInt w .signed bits))
  | .bitNot, .int w s bits =>
    let m := pow2 w.bitWidth
    .ok (.int w s (Nat.mod (Nat.xor bits (m - 1)) m))
  | .logNot, .bool b => .ok (.bool (!b))
  | .logNot, .int _ _ bits => .ok (.bool (Nat.beq bits 0))
  | .logNot, .ptr aid addr _ =>
    match aid with
    | none    => .ok (.bool (Nat.beq addr 0))
    | some id => if ptrLive mem id then .ok (.bool false) else .error .undefined
  | _, _ => .error .unsupported

/-- Evaluate an integer binary operator `op` on `(w, s, aBits, bBits)`. -/
noncomputable def evalIntBinOp (policy : CppLangPolicy) (op : CppBinOp)
    (w : CppIntWidth) (s : Signedness) (aBits bBits : Nat) :
    Except CppFaultKind CppVal :=
  let bw := w.bitWidth
  let m := pow2 bw
  match s with
  | .unsigned =>
    match op with
    | .add    => .ok (.int w .unsigned (Nat.mod (aBits + bBits) m))
    | .sub    =>
      .ok (.int w .unsigned (Nat.mod (aBits + m - Nat.mod bBits m) m))
    | .mul    => .ok (.int w .unsigned (Nat.mod (aBits * bBits) m))
    | .div    =>
      if Nat.beq bBits 0 then .error .undefined
      else .ok (.int w .unsigned (Nat.div aBits bBits))
    | .rem    =>
      if Nat.beq bBits 0 then .error .undefined
      else .ok (.int w .unsigned (Nat.mod aBits bBits))
    | .shl    =>
      if Nat.ble bw bBits then .error .undefined
      else .ok (.int w .unsigned (Nat.mod (Nat.shiftLeft aBits bBits) m))
    | .shr    =>
      if Nat.ble bw bBits then .error .undefined
      else .ok (.int w .unsigned (Nat.shiftRight aBits bBits))
    | .bitAnd => .ok (.int w .unsigned (Nat.mod (Nat.land aBits bBits) m))
    | .bitOr  => .ok (.int w .unsigned (Nat.mod (Nat.lor aBits bBits) m))
    | .bitXor => .ok (.int w .unsigned (Nat.mod (Nat.xor aBits bBits) m))
    | .eq     => .ok (.bool (Nat.beq aBits bBits))
    | .ne     => .ok (.bool (!Nat.beq aBits bBits))
    | .lt     => .ok (.bool (Nat.blt aBits bBits))
    | .le     => .ok (.bool (Nat.ble aBits bBits))
    | .gt     => .ok (.bool (Nat.blt bBits aBits))
    | .ge     => .ok (.bool (Nat.ble bBits aBits))
  | .signed =>
    let a := cppIntToMathInt w .signed aBits
    let b := cppIntToMathInt w .signed bBits
    match op with
    | .add => finishSignedArith policy w (Int.add a b)
    | .sub => finishSignedArith policy w (Int.sub a b)
    | .mul => finishSignedArith policy w (Int.mul a b)
    | .div =>
      if intBeq b (Int.ofNat 0) || (isSignedMin w a && intBeq b (Int.negSucc 0))
      then .error .undefined
      else
        let q := intFromSignMag (!(intIsNeg a == intIsNeg b))
                   (Nat.div (intAbs a) (intAbs b))
        .ok (.int w .signed (ofSignedIntWrap w q))
    | .rem =>
      if intBeq b (Int.ofNat 0) || (isSignedMin w a && intBeq b (Int.negSucc 0))
      then .error .undefined
      else
        let r := intFromSignMag (intIsNeg a) (Nat.mod (intAbs a) (intAbs b))
        .ok (.int w .signed (ofSignedIntWrap w r))
    | .shl =>
      match b with
      | Int.negSucc _ => .error .undefined
      | Int.ofNat sh =>
        if Nat.ble bw sh then .error .undefined
        else
          -- Shifting a negative value, or into or past the sign bit, is
          -- undefined in C11 §6.5.7p4 (`-fwrapv` covers only additive and
          -- multiplicative overflow) but defined in C++20 [expr.shift]p2.
          match a with
          | Int.negSucc _ => .error .unsupported
          | Int.ofNat an =>
            let shifted := Nat.shiftLeft an sh
            if Nat.blt shifted (pow2 (bw - 1)) then
              .ok (.int w .signed shifted)
            else .error .unsupported
    | .shr =>
      match b with
      | Int.negSucc _ => .error .undefined
      | Int.ofNat sh =>
        if Nat.ble bw sh then .error .undefined
        else
          match a with
          | Int.ofNat an => .ok (.int w .signed (Nat.shiftRight an sh))
          | Int.negSucc _ =>
            let fill := m - pow2 (bw - sh)
            .ok (.int w .signed
              (Nat.mod (Nat.lor (Nat.shiftRight aBits sh) fill) m))
    | .bitAnd => .ok (.int w .signed (Nat.mod (Nat.land aBits bBits) m))
    | .bitOr  => .ok (.int w .signed (Nat.mod (Nat.lor aBits bBits) m))
    | .bitXor => .ok (.int w .signed (Nat.mod (Nat.xor aBits bBits) m))
    | .eq     => .ok (.bool (intBeq a b))
    | .ne     => .ok (.bool (!intBeq a b))
    | .lt     => .ok (.bool (intBlt a b))
    | .le     => .ok (.bool (intBlt a b || intBeq a b))
    | .gt     => .ok (.bool (intBlt b a))
    | .ge     => .ok (.bool (intBlt b a || intBeq b a))

/-- `true` iff `addr` is one past the end of allocation `aid`. -/
noncomputable def ptrAtEnd (mem : CppMemory) (aid addr : Nat) : Bool :=
  match findAlloc? aid mem.allocs with
  | some a => Nat.beq addr (a.baseAddr + a.sizeBytes)
  | none   => false

/-- `true` iff `addr` is one past the end of subobject range `sr`. -/
noncomputable def atRangeEnd (sr : Option (Nat × Nat)) (addr : Nat) : Bool :=
  match sr with
  | some (lo, sz) => Nat.beq addr (lo + sz)
  | none          => false

/-- Pointer equality under C11 §6.5.9p6 and C++20 [expr.eq]p3. Comparing a
pointer to a dead or missing allocation is `.undefined` (its value is
indeterminate). A one-past-the-end pointer may equal the start of an adjacent
object, which C makes `true` and C++ leaves unspecified, so equal addresses
in distinct allocations or subobjects with one at its end are `.unsupported`;
so is comparing a provenance-carrying pointer with a non-null integer-derived
one. -/
noncomputable def ptrEqResult (mem : CppMemory) (aid1 : Option Nat)
    (addr1 : Nat) (sr1 : Option (Nat × Nat)) (aid2 : Option Nat) (addr2 : Nat)
    (sr2 : Option (Nat × Nat)) : Except CppFaultKind Bool :=
  match aid1, aid2 with
  | none, none => .ok (Nat.beq addr1 addr2)
  | some id1, some id2 =>
    if !ptrLive mem id1 || !ptrLive mem id2 then .error .undefined
    else if Nat.beq id1 id2 then
      if !Nat.beq addr1 addr2 then .ok false
      else if !optRangeBeq sr1 sr2 &&
              (atRangeEnd sr1 addr1 || atRangeEnd sr2 addr2) then
        .error .unsupported
      else .ok true
    else if ptrAtEnd mem id1 addr1 || ptrAtEnd mem id2 addr2 then
      .error .unsupported
    else .ok false
  | some id1, none =>
    if !ptrLive mem id1 then .error .undefined
    else if Nat.beq addr2 0 then .ok false
    else .error .unsupported
  | none, some id2 =>
    if !ptrLive mem id2 then .error .undefined
    else if Nat.beq addr1 0 then .ok false
    else .error .unsupported

/-- Evaluate pointer comparison operators under C11 §6.5.8 / §6.5.9.
Relational comparison of pointers into distinct live objects or subobjects is
undefined in C11 §6.5.8p5 but unspecified in C++20 [expr.rel]p4, and of two
null pointers undefined in C but defined in C++, so both are `.unsupported`.
-/
noncomputable def evalPtrBinOp (mem : CppMemory) (op : CppBinOp)
    (aid1 : Option Nat) (addr1 : Nat) (sr1 : Option (Nat × Nat))
    (aid2 : Option Nat) (addr2 : Nat) (sr2 : Option (Nat × Nat)) :
    Except CppFaultKind CppVal :=
  match op with
  | .eq =>
    match ptrEqResult mem aid1 addr1 sr1 aid2 addr2 sr2 with
    | .ok b    => .ok (.bool b)
    | .error k => .error k
  | .ne =>
    match ptrEqResult mem aid1 addr1 sr1 aid2 addr2 sr2 with
    | .ok b    => .ok (.bool (!b))
    | .error k => .error k
  | .lt | .le | .gt | .ge =>
    match aid1, aid2 with
    | some id1, some id2 =>
      if !ptrLive mem id1 || !ptrLive mem id2 then .error .undefined
      else if !Nat.beq id1 id2 || !optRangeBeq sr1 sr2 then .error .unsupported
      else
        match op with
        | .lt => .ok (.bool (Nat.blt addr1 addr2))
        | .le => .ok (.bool (Nat.ble addr1 addr2))
        | .gt => .ok (.bool (Nat.blt addr2 addr1))
        | .ge => .ok (.bool (Nat.ble addr2 addr1))
        | _   => .error .unsupported
    | none, none =>
      if Nat.beq addr1 0 && Nat.beq addr2 0 then .error .unsupported
      else .error .undefined
    | _, _ => .error .undefined
  | _ => .error .unsupported

/-- Evaluate a binary operator `op` on `(lv, rv)`. -/
noncomputable def evalBinOp (policy : CppLangPolicy) (mem : CppMemory)
    (op : CppBinOp) (lv rv : CppVal) : Except CppFaultKind CppVal :=
  match lv, rv with
  | .int w1 s1 a, .int w2 s2 b =>
    if CppIntWidth.beq w1 w2 && Signedness.beq s1 s2 then
      evalIntBinOp policy op w1 s1 a b
    else
      match op with
      | .shl | .shr =>
        match cppIntToMathInt w2 s2 b with
        | Int.negSucc _ => .error .undefined
        | Int.ofNat rn =>
          if Nat.ble w1.bitWidth rn then .error .undefined
          else evalIntBinOp policy op w1 s1 a rn
      | _ => .error .unsupported
  | .ptr aid1 addr1 sr1, .ptr aid2 addr2 sr2 =>
    evalPtrBinOp mem op aid1 addr1 sr1 aid2 addr2 sr2
  | .bool a, .bool b =>
    match op with
    | .eq => .ok (.bool (a == b))
    | .ne => .ok (.bool (a != b))
    | _   => .error .unsupported
  | _, _ => .error .unsupported

/-- Mark allocation `aid` read-only. -/
noncomputable def setAllocConst (mem : CppMemory) (aid : Nat) :
    Except CppFaultKind CppMemory :=
  match findAlloc? aid mem.allocs with
  | none => .error .undefined
  | some a =>
    match replaceAlloc? aid { a with isConst := true } mem.allocs with
    | some allocs' => .ok { mem with allocs := allocs' }
    | none         => .error .undefined

/-- Force local `lid` into stack memory, returning `(allocId, frame', mem')`.
-/
noncomputable def forceLocalToMemory (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (lid : LocalId) :
    Except CppFaultKind (Nat × CppFrame × CppMemory) :=
  match cppGetElem? body.locals lid, cppGetElem? frame.locals lid with
  | some decl, some slot =>
    match slot with
    | .dead => .error .undefined
    | .stackAddr aid => .ok (aid, frame, mem)
    | .uninit | .val _ =>
      match cppTySize? prog.policy prog.records decl.ty,
            cppTyAlign? prog.policy prog.records decl.ty with
      | some sz, some al =>
        let (aid, mem1) := allocStack mem sz al false (some decl.ty)
        let memRes : Except CppFaultKind CppMemory :=
          if !Nat.blt mem1.nextAddr ptrAddrBound then .error .unsupported
          else
          match slot with
          | .val v =>
            match findAlloc? aid mem1.allocs with
            | some alloc =>
              -- A `const` local becomes read-only storage once its value is
              -- written.
              match writeMemory prog.policy prog.records mem1 (some aid)
                      alloc.baseAddr decl.ty false v none with
              | .ok mem2 =>
                if decl.isConst then setAllocConst mem2 aid else .ok mem2
              | .error k => .error k
            | none => .error .undefined
          -- An uninitialized `const` local can only be initialized whole
          -- (`zeroInit` or a direct store), never through memory.
          | _ => if decl.isConst then setAllocConst mem1 aid else .ok mem1
        match memRes, cppSetElem? frame.locals lid (.stackAddr aid) with
        | .ok mem2, some locs' =>
          .ok (aid, { frame with locals := locs',
                                 stackAllocs := aid :: frame.stackAllocs },
               mem2)
        | .error k, _ => .error k
        | _, none     => .error .unsupported
      | _, _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Read a scalar or immediate local `lid` from `frame`/`mem`. An immediate
value must have a padding-free type, and reading a pointer to a dead object,
held directly or in an aggregate, is `.undefined`. -/
noncomputable def readLocalScalar (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (lid : LocalId) :
    Except CppFaultKind CppVal :=
  match cppGetElem? body.locals lid, cppGetElem? frame.locals lid with
  | some decl, some slot =>
    match slot with
    | .dead | .uninit => .error .undefined
    | .val v =>
      if !tyHasNoPadding prog.policy prog.records true 16 decl.ty then
        .error .unsupported
      else if valLiveInMem prog.policy prog.records mem v decl.ty then .ok v
      else .error .undefined
    | .stackAddr aid =>
      match findAlloc? aid mem.allocs with
      | some alloc =>
        readMemory prog.policy prog.records mem (some aid) alloc.baseAddr
          decl.ty false none
      | none => .error .undefined
  | _, _ => .error .unsupported

/-- Resolved memory address `(allocId, addr, ty, mayAlias)`. `alignCap` is the
smallest `alignBytes` of the records whose members were projected to reach the
address, so a member of a packed record is accessed at the record's alignment
(as through the record lvalue) rather than its type's. `subRange` is the
subobject (member or array) the address lies in, if narrower than the whole
allocation; a pointer formed from the address keeps it. -/
structure ResolvedAddr where
  allocId  : Option Nat
  addr     : Nat
  ty       : CppTy
  mayAlias : Bool
  alignCap : Option Nat := none
  subRange : Option (Nat × Nat) := none

/-- Lower an alignment cap to at most `a`. -/
noncomputable def alignCapMin (cap : Option Nat) (a : Nat) : Nat :=
  match cap with
  | some c => if Nat.blt c a then c else a
  | none   => a

/-- Check `*p` for `p = (aid, addr, sr)` of pointee type `pointee`, returning
the pointee's size. The pointee must lie entirely inside a live allocation
and inside `sr`, suitably aligned (C11 §6.5.3.2p4, C++20 [basic.life]p6), so
a null, dangling, misaligned, or one-past-the-end `p` is `.undefined`. When
`terminalAddrOf`, the dereference is the operand of `&` (`&*p`, `&p[i]`), which
C11 §6.5.3.2p3 evaluates without accessing `*p` but C++ does not, so a failure
on a live or null `p` is `.unsupported` instead. -/
noncomputable def derefCheck (prog : CppProgram) (mem : CppMemory)
    (terminalAddrOf : Bool) (aid : Option Nat) (addr : Nat)
    (sr : Option (Nat × Nat)) (pointee : CppTy) : Except CppFaultKind Nat :=
  match cppTySize? prog.policy prog.records pointee,
        cppTyAlign? prog.policy prog.records pointee with
  | some sz, some al =>
    if placeInBounds mem aid addr sz && subRangeContains sr addr sz &&
       Nat.beq (Nat.mod addr al) 0 then .ok sz
    else if terminalAddrOf then
      match aid with
      | some id => if ptrLive mem id then .error .unsupported
                   else .error .undefined
      | none    => .error .unsupported
    else .error .undefined
  | _, _ => .error .unsupported

/-- The subobject range of the object `*p` designates: unchanged for the
operand of `&`, the pointee itself when `p` carries a range, and none (the
whole allocation) otherwise. -/
noncomputable def derefRange (terminalAddrOf : Bool) (addr sz : Nat)
    (sr : Option (Nat × Nat)) : Option (Nat × Nat) :=
  if terminalAddrOf then sr
  else
    match sr with
    | some _ => some (addr, sz)
    | none   => none

/-- Step through remaining `CppProjElem`s from a resolved memory address.
`forAddrOf` marks the place as the operand of `&`. -/
noncomputable def resolveProjChain (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (forAddrOf : Bool)
    (cur : ResolvedAddr) :
    List CppProjElem → Except CppFaultKind ResolvedAddr
  | [] => .ok cur
  | proj :: rest =>
    match proj with
    | .deref =>
      match cur.ty with
      | .ptr pointee _ _ ma =>
        match readMemory prog.policy prog.records mem cur.allocId cur.addr
                cur.ty cur.mayAlias cur.alignCap with
        | .ok (.ptr aid' addr' sr') =>
          let term := forAddrOf && rest.isEmpty
          match derefCheck prog mem term aid' addr' sr' pointee with
          | .ok sz =>
            resolveProjChain prog body frame mem forAddrOf
              { allocId := aid', addr := addr', ty := pointee, mayAlias := ma,
                subRange := derefRange term addr' sz sr' }
              rest
          | .error k => .error k
        | .error k => .error k
        | .ok _    => .error .unsupported
      | _ => .error .unsupported
    | .field recId fIdx fTy =>
      match findRecord? prog.records recId with
      | some rec =>
        match cppGetElem? rec.fields fIdx,
              cppTySize? prog.policy prog.records fTy with
        | some fld, some fsz =>
          match fld.bitWidth with
          | none =>
            if !CppTy.beq cur.ty (.record recId) || !CppTy.beq fld.ty fTy ||
               !Nat.beq (Nat.mod fld.offsetBits 8) 0 then
              .error .unsupported
            else
              let a := cur.addr + Nat.div fld.offsetBits 8
              if !placeInBounds mem cur.allocId a fsz ||
                 !subRangeContains cur.subRange a fsz then .error .undefined
              else
                resolveProjChain prog body frame mem forAddrOf
                  { cur with addr := a, ty := fTy,
                             alignCap :=
                               some (alignCapMin cur.alignCap rec.alignBytes),
                             subRange := some (a, fsz) }
                  rest
          | some _ => .error .unsupported
        | _, _ => .error .unsupported
      | none => .error .unsupported
    | .index elemTy idxLocal =>
      match readLocalScalar prog body frame mem idxLocal with
      | .error k => .error k
      | .ok idxVal =>
        let term := forAddrOf && rest.isEmpty
        match cur.ty with
        | .ptr ptee _ _ ma =>
          -- `p[i]` is `*(p + i)` (C11 §6.5.2.1p2).
          if !CppTy.beq ptee elemTy then .error .unsupported
          else
            match readMemory prog.policy prog.records mem cur.allocId cur.addr
                    cur.ty cur.mayAlias cur.alignCap with
            | .error k => .error k
            | .ok bp =>
              match ptrAddOffset prog.policy prog.records mem elemTy bp
                      idxVal with
              | .ok (.ptr aid' addr' sr') =>
                match derefCheck prog mem term aid' addr' sr' elemTy with
                | .ok esz =>
                  resolveProjChain prog body frame mem forAddrOf
                    { allocId := aid', addr := addr', ty := elemTy,
                      mayAlias := ma,
                      subRange := derefRange term addr' esz sr' }
                    rest
                | .error k => .error k
              | .error k => .error k
              | .ok _    => .error .unsupported
        | .array arrElem arrLen =>
          -- Indexing an array subobject in place: the index must be in
          -- bounds (`&a[len]` is the C-only one-past-the-end exception), and
          -- the element keeps the array as its range.
          if !CppTy.beq arrElem elemTy then .error .unsupported
          else
            match cppTySize? prog.policy prog.records elemTy, idxVal with
            | some esz, .int iw is ibits =>
              match cppIntToMathInt iw is ibits with
              | Int.ofNat k =>
                if Nat.blt k arrLen then
                  resolveProjChain prog body frame mem forAddrOf
                    { cur with addr := cur.addr + k * esz, ty := elemTy,
                               subRange := some (cur.addr, arrLen * esz) }
                    rest
                else if term && Nat.beq k arrLen then .error .unsupported
                else .error .undefined
              | Int.negSucc _ => .error .undefined
            | _, _ => .error .unsupported
        | _ => .error .unsupported
    | .bitfield _ _ _ _ _ => .error .unsupported

/-- Resolve a `CppPlace` to a `ResolvedAddr` (forcing base to memory only when
needed). `forAddrOf` marks the place as the operand of `&`. -/
noncomputable def resolvePlaceAddr (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (forAddrOf : Bool) (place : CppPlace) :
    Except CppFaultKind (ResolvedAddr × CppFrame × CppMemory) :=
  let forceAndResolve (projs : List CppProjElem) :=
    match forceLocalToMemory prog body frame mem place.base with
    | .error k => .error k
    | .ok (aid, f', m') =>
      match cppGetElem? body.locals place.base, findAlloc? aid m'.allocs with
      | some decl, some alloc =>
        match resolveProjChain prog body f' m' forAddrOf
                { allocId := some aid, addr := alloc.baseAddr, ty := decl.ty,
                  mayAlias := false } projs with
        | .ok r    => .ok (r, f', m')
        | .error k => .error k
      | _, _ => .error .undefined
  match place.projs with
  | [] => forceAndResolve []
  | .deref :: rest =>
    match cppGetElem? body.locals place.base with
    | some decl =>
      match decl.ty with
      | .ptr pointee _ _ ma =>
        match readLocalScalar prog body frame mem place.base with
        | .ok (.ptr aid addr sr) =>
          let term := forAddrOf && rest.isEmpty
          match derefCheck prog mem term aid addr sr pointee with
          | .ok sz =>
            match resolveProjChain prog body frame mem forAddrOf
                    { allocId := aid, addr := addr, ty := pointee,
                      mayAlias := ma, subRange := derefRange term addr sz sr }
                    rest with
            | .ok r    => .ok (r, frame, mem)
            | .error k => .error k
          | .error k => .error k
        | .error k => .error k
        | .ok _    => .error .unsupported
      | _ => .error .unsupported
    | none => .error .unsupported
  | .index elemTy idxLocal :: rest =>
    match cppGetElem? body.locals place.base with
    | some decl =>
      match decl.ty with
      | .ptr ptee _ _ ma =>
        if !CppTy.beq ptee elemTy then .error .unsupported
        else
          match readLocalScalar prog body frame mem place.base,
                readLocalScalar prog body frame mem idxLocal with
          | .ok basePtr, .ok idxVal =>
            match ptrAddOffset prog.policy prog.records mem elemTy basePtr
                    idxVal with
            | .ok (.ptr aid addr sr) =>
              let term := forAddrOf && rest.isEmpty
              match derefCheck prog mem term aid addr sr elemTy with
              | .ok esz =>
                match resolveProjChain prog body frame mem forAddrOf
                        { allocId := aid, addr := addr, ty := elemTy,
                          mayAlias := ma,
                          subRange := derefRange term addr esz sr } rest with
                | .ok r    => .ok (r, frame, mem)
                | .error k => .error k
              | .error k => .error k
            | .error k => .error k
            | .ok _    => .error .unsupported
          | .error k, _ => .error k
          | _, .error k => .error k
      | _ => forceAndResolve (.index elemTy idxLocal :: rest)
    | none => .error .unsupported
  | .field fRec fIdx fTy :: rest =>
    forceAndResolve (.field fRec fIdx fTy :: rest)
  | .bitfield r i o w s :: rest =>
    forceAndResolve (.bitfield r i o w s :: rest)

/-- Split a projection chain ending in `.bitfield` into the record prefix and
`(recordId, fieldIdx, offsetBits, bitWidth, isSigned)`. -/
noncomputable def splitBitfield :
    List CppProjElem →
      Option (List CppProjElem × String × Nat × Nat × Nat × Bool)
  | [] => none
  | [.bitfield rid idx o w s] => some ([], rid, idx, o, w, s)
  | p :: rest =>
    match splitBitfield rest with
    | some (pre, bf) => some (p :: pre, bf)
    | none           => none

/-- Check that a `.bitfield rid idx o w sgn` projection read or written at
type `ty` matches the record it projects from: `r` has type `.record rid`, and
field `idx` of `rid` is a named bit-field of type `ty`, an integer type with
signedness `sgn` at least `w > 0` bits wide, at bit offset `o` of width `w`
inside the record. -/
noncomputable def bitfieldOk (prog : CppProgram) (r : ResolvedAddr)
    (rid : String) (idx o w : Nat) (sgn : Bool) (ty : CppTy) : Bool :=
  CppTy.beq r.ty (.record rid) && Nat.blt 0 w &&
    match findRecord? prog.records rid with
    | none => false
    | some rec =>
      Nat.blt 0 rec.alignBytes && Nat.ble (o + w) (rec.sizeBytes * 8) &&
        match cppGetElem? rec.fields idx with
        | none => false
        | some fld =>
          !(fld.name == "") && Nat.beq fld.offsetBits o &&
            optNatBeq fld.bitWidth (some w) && CppTy.beq fld.ty ty &&
            match fld.ty with
            | .int fw s _ =>
              Nat.ble w fw.bitWidth &&
                Signedness.beq s (if sgn then .signed else .unsigned)
            | _ => false

/-- Check that the record holding a bit-field lies entirely inside a live
allocation and its subobject range, aligned for the record (C11 §6.5.3.2p4):
a bit-field access accesses its record's storage unit. -/
noncomputable def bitfieldPlaced (prog : CppProgram) (mem : CppMemory)
    (r : ResolvedAddr) (rid : String) : Bool :=
  match findRecord? prog.records rid with
  | none => false
  | some rec =>
    placeInBounds mem r.allocId r.addr rec.sizeBytes &&
      subRangeContains r.subRange r.addr rec.sizeBytes &&
      Nat.beq (Nat.mod r.addr (alignCapMin r.alignCap rec.alignBytes)) 0

/-- Character-array type of `n` bytes (the storage covering a bit-field). -/
noncomputable def charArrTy (n : Nat) : CppTy :=
  .array (.int .w8 .unsigned true) n

/-- First byte and byte count covering bits `[o, o + w)`. -/
noncomputable def bitSpan (o w : Nat) : Nat × Nat :=
  (Nat.div o 8, Nat.div (o + w + 7) 8 - Nat.div o 8)

/-- Read bit-field bits `[o, o + w)` of the record at `r` as `ty`
(little-endian bit order, sign-extended iff `sgn`); any uninitialized or
pointer byte in the covering storage is `.undefined`. -/
noncomputable def readBitfield (prog : CppProgram) (mem : CppMemory)
    (r : ResolvedAddr) (o w : Nat) (sgn : Bool) (ty : CppTy) :
    Except CppFaultKind CppVal :=
  match ty, bitSpan o w with
  | .int tw ts _, (b0, n) =>
    match readMemory prog.policy prog.records mem r.allocId (r.addr + b0)
            (charArrTy n) false none with
    | .ok (.aggregate bs) =>
      match decodeIntBytes bs with
      | none => .error .undefined
      | some u =>
        let field := Nat.mod (Nat.shiftRight u (Nat.mod o 8)) (pow2 w)
        let x : Int :=
          if sgn && Nat.ble (pow2 (w - 1)) field then
            Int.subNatNat field (pow2 w)
          else Int.ofNat field
        .ok (.int tw ts (ofSignedIntWrap tw x))
    | .ok _    => .error .unsupported
    | .error k => .error k
  | _, _ => .error .unsupported

/-- Store `v` (truncated to `w` bits) into bit-field bits `[o, o + w)` of the
record at `r` by read-modify-write of the covering bytes. Partially
overwriting an uninitialized byte is `.unsupported` (fail closed). -/
noncomputable def writeBitfield (prog : CppProgram) (mem : CppMemory)
    (r : ResolvedAddr) (o w : Nat) (v : CppVal) :
    Except CppFaultKind CppMemory :=
  match v, bitSpan o w with
  | .int _ _ bits, (b0, n) =>
    let sh := Nat.mod o 8
    match readMemory prog.policy prog.records mem r.allocId (r.addr + b0)
            (charArrTy n) false none with
    | .ok (.aggregate bs) =>
      let old : Option Nat := match decodeIntBytes bs with
        | some u => some u
        | none   => if Nat.beq sh 0 && Nat.beq w (n * 8) then some 0 else none
      match old with
      | none => .error .unsupported
      | some u =>
        let m := pow2 w
        let cleared := u - Nat.shiftLeft (Nat.mod (Nat.shiftRight u sh) m) sh
        writeRawBytes prog.policy prog.records mem r.allocId (r.addr + b0)
          (encodeIntBytes n (cleared + Nat.shiftLeft (Nat.mod bits m) sh))
    | .ok _    => .error .unsupported
    | .error k => .error k
  | _, _ => .error .unsupported

/-- Read a value of type `ty` from `place`. -/
noncomputable def readPlaceVal (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (place : CppPlace) (ty : CppTy) :
    Except CppFaultKind (CppVal × CppFrame × CppMemory) :=
  match splitBitfield place.projs with
  | some (pre, rid, idx, o, w, sgn) =>
    match resolvePlaceAddr prog body frame mem false
            { place with projs := pre } with
    | .error k => .error k
    | .ok (r, f', m') =>
      if !bitfieldOk prog r rid idx o w sgn ty then .error .unsupported
      else if !bitfieldPlaced prog m' r rid then .error .undefined
      else
        match readBitfield prog m' r o w sgn ty with
        | .ok v    => .ok (v, f', m')
        | .error k => .error k
  | none =>
  match place.projs with
  | [] =>
    match cppGetElem? body.locals place.base with
    | none => .error .unsupported
    | some decl =>
      if !CppTy.beq decl.ty ty then .error .unsupported
      else
        match readLocalScalar prog body frame mem place.base with
        | .ok v    => .ok (v, frame, mem)
        | .error k => .error k
  | _ :: _ =>
    match resolvePlaceAddr prog body frame mem false place with
    | .error k => .error k
    | .ok (r, f', m') =>
      match readMemory prog.policy prog.records m' r.allocId r.addr ty
              r.mayAlias r.alignCap with
      | .ok v    => .ok (v, f', m')
      | .error k => .error k

/-- Write a value `v` of type `ty` into `place`. An immediate local must have
a padding-free type (a padded value is never copied by value), and a `const`
local may only be initialized, never overwritten. -/
noncomputable def writePlaceVal (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (place : CppPlace) (ty : CppTy)
    (v : CppVal) : Except CppFaultKind (CppFrame × CppMemory) :=
  match splitBitfield place.projs with
  | some (pre, rid, idx, o, w, sgn) =>
    match resolvePlaceAddr prog body frame mem false
            { place with projs := pre } with
    | .error k => .error k
    | .ok (r, f', m') =>
      if !bitfieldOk prog r rid idx o w sgn ty ||
         !checkCppVal prog.policy prog.records v ty then .error .unsupported
      else if !bitfieldPlaced prog m' r rid then .error .undefined
      else
        match writeBitfield prog m' r o w v with
        | .ok m''  => .ok (f', m'')
        | .error k => .error k
  | none =>
  match place.projs with
  | [] =>
    match cppGetElem? body.locals place.base with
    | none => .error .unsupported
    | some decl =>
      if !CppTy.beq decl.ty ty then .error .unsupported
      else
        match cppGetElem? frame.locals place.base with
        | none => .error .unsupported
        | some .dead => .error .undefined
        | some (.stackAddr aid) =>
          match findAlloc? aid mem.allocs with
          | some alloc =>
            match writeMemory prog.policy prog.records mem (some aid)
                    alloc.baseAddr ty false v none with
            | .ok m'   => .ok (frame, m')
            | .error k => .error k
          | none => .error .undefined
        | some .uninit =>
          if !tyHasNoPadding prog.policy prog.records true 16 decl.ty then
            .error .unsupported
          else
            match cppSetElem? frame.locals place.base (.val v) with
            | some locs' => .ok ({ frame with locals := locs' }, mem)
            | none       => .error .unsupported
        | some (.val _) =>
          if !tyHasNoPadding prog.policy prog.records true 16 decl.ty then
            .error .unsupported
          else if decl.isConst then .error .undefined
          else
            match cppSetElem? frame.locals place.base (.val v) with
            | some locs' => .ok ({ frame with locals := locs' }, mem)
            | none       => .error .unsupported
  | _ :: _ =>
    match resolvePlaceAddr prog body frame mem false place with
    | .error k => .error k
    | .ok (r, f', m') =>
      match writeMemory prog.policy prog.records m' r.allocId r.addr ty
              r.mayAlias v r.alignCap with
      | .ok m''  => .ok (f', m'')
      | .error k => .error k

/-- The pointee of a non-`restrict` pointer type, if `ty` is one. -/
noncomputable def ptrTyPointee? : CppTy → Option CppTy
  | .ptr p _ r _ => if !r && CppTy.noRestrict p then some p else none
  | _ => none

/-- Check a unary result `res` against the expression's declared type `ty`:
`!` yields `bool`, and `-`/`~` yield an integer of `ty`'s width and sign. -/
noncomputable def unResTyOk (op : CppUnOp) (ty : CppTy) (res : CppVal) : Bool :=
  match op, ty, res with
  | .logNot, .bool, .bool _ => true
  | .neg, .int tw ts _, .int w s _ =>
    CppIntWidth.beq w tw && Signedness.beq s ts
  | .bitNot, .int tw ts _, .int w s _ =>
    CppIntWidth.beq w tw && Signedness.beq s ts
  | _, _, _ => false

/-- Check a binary result `res` against the expression's declared type
`resTy`: comparisons yield `bool`, and arithmetic, shift, and bitwise
operators yield an integer of `resTy`'s width and sign. -/
noncomputable def binResTyOk (op : CppBinOp) (resTy : CppTy) (res : CppVal) :
    Bool :=
  match op with
  | .eq | .ne | .lt | .le | .gt | .ge =>
    match resTy, res with
    | .bool, .bool _ => true
    | _, _ => false
  | _ =>
    match resTy, res with
    | .int tw ts _, .int w s _ => CppIntWidth.beq w tw && Signedness.beq s ts
    | _, _ => false

/-- Check that `ptrTy` is a non-`restrict` pointer to `elemTy`. -/
noncomputable def ptrAddTyOk (elemTy ptrTy : CppTy) : Bool :=
  match ptrTyPointee? ptrTy with
  | some p => CppTy.beq p elemTy
  | none   => false

/-- Evaluate a pure SSENF `CppExpr` structurally. -/
noncomputable def evalExpr (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) :
    CppExpr → Except CppFaultKind (CppVal × CppFrame × CppMemory)
  | .constInt w s _ v =>
    match s with
    | .unsigned => .ok (.int w .unsigned (ofSignedIntWrap w v), frame, mem)
    | .signed =>
      match finishSignedArith prog.policy w v with
      | .ok res  => .ok (res, frame, mem)
      | .error k => .error k
  | .constBool b => .ok (.bool b, frame, mem)
  | .nullPtr ty =>
    match ptrTyPointee? ty with
    | some _ => .ok (.ptr none 0 none, frame, mem)
    | none   => .error .unsupported
  | .readPlace place ty => readPlaceVal prog body frame mem place ty
  | .addrOf place ptrTy =>
    match resolvePlaceAddr prog body frame mem true place with
    | .ok (r, f', m') =>
      match ptrTyPointee? ptrTy with
      | some ptee =>
        if CppTy.beq ptee r.ty then
          .ok (.ptr r.allocId r.addr r.subRange, f', m')
        else .error .unsupported
      | none => .error .unsupported
    | .error k => .error k
  | .unary op ty arg =>
    match evalExpr prog body frame mem arg with
    | .error k => .error k
    | .ok (v, f1, m1) =>
      match evalUnOp prog.policy m1 op v with
      | .ok res  =>
        if unResTyOk op ty res then .ok (res, f1, m1) else .error .unsupported
      | .error k => .error k
  | .binary op resTy lhs rhs =>
    match evalExpr prog body frame mem lhs with
    | .error k => .error k
    | .ok (lv, f1, m1) =>
      match evalExpr prog body f1 m1 rhs with
      | .error k => .error k
      | .ok (rv, f2, m2) =>
        match evalBinOp prog.policy m2 op lv rv with
        | .ok res  =>
          if binResTyOk op resTy res then .ok (res, f2, m2)
          else .error .unsupported
        | .error k => .error k
  | .intCast fromW fromS toW toS _ arg =>
    match evalExpr prog body frame mem arg with
    | .error k => .error k
    | .ok (.int w s bits, f1, m1) =>
      if CppIntWidth.beq w fromW && Signedness.beq s fromS then
        let x := cppIntToMathInt fromW fromS bits
        .ok (.int toW toS (ofSignedIntWrap toW x), f1, m1)
      else .error .unsupported
    | .ok (.void, _) | .ok (.bool _, _) | .ok (.ptr _ _ _, _)
    | .ok (.aggregate _, _) => .error .unsupported
  | .intToBool arg =>
    match evalExpr prog body frame mem arg with
    | .error k => .error k
    | .ok (.int _ _ bits, f1, m1) => .ok (.bool (!Nat.beq bits 0), f1, m1)
    | .ok (.bool b, f1, m1)       => .ok (.bool b, f1, m1)
    | .ok (.ptr none addr _, f1, m1) => .ok (.bool (!Nat.beq addr 0), f1, m1)
    | .ok (.ptr (some aid) _ _, f1, m1) =>
      if ptrLive m1 aid then .ok (.bool true, f1, m1) else .error .undefined
    | .ok _ => .error .unsupported
  | .boolToInt w s arg =>
    match evalExpr prog body frame mem arg with
    | .error k => .error k
    | .ok (.bool b, f1, m1) => .ok (.int w s (if b then 1 else 0), f1, m1)
    | .ok _ => .error .unsupported
  | .ptrAdd elemTy ptrTy base offset =>
    match evalExpr prog body frame mem base with
    | .error k => .error k
    | .ok (bv, f1, m1) =>
      match evalExpr prog body f1 m1 offset with
      | .error k => .error k
      | .ok (ov, f2, m2) =>
        match ptrAddOffset prog.policy prog.records m2 elemTy bv ov with
        | .ok res  =>
          if ptrAddTyOk elemTy ptrTy then .ok (res, f2, m2)
          else .error .unsupported
        | .error k => .error k
  | .ptrCast toPtrTy arg =>
    match evalExpr prog body frame mem arg with
    | .error k => .error k
    | .ok (.ptr aid addr sr, f1, m1) =>
      match ptrTyPointee? toPtrTy with
      | some _ => .ok (.ptr aid addr sr, f1, m1)
      | none   => .error .unsupported
    | .ok _ => .error .unsupported
  | .bitCast fromTy toTy arg =>
    match evalExpr prog body frame mem arg with
    | .error k => .error k
    | .ok (v, f1, m1) =>
      -- C++20 [bit.cast]p2: padding bits of `fromTy` (including `bool`'s)
      -- yield indeterminate result bits, and a `bool` result must hold a valid
      -- value, so both types must be padding-free with no `bool`. Every source
      -- byte must be initialized data: pointer provenance and indeterminate
      -- bytes are not modeled through `bit_cast`.
      if !tyHasNoPadding prog.policy prog.records false 16 fromTy ||
         !tyHasNoPadding prog.policy prog.records false 16 toTy then
        .error .unsupported
      else
        match cppTySize? prog.policy prog.records fromTy,
              cppTySize? prog.policy prog.records toTy,
              encodeValBytes prog.policy prog.records v fromTy with
        | some s1, some s2, some bs =>
          if !Nat.beq s1 s2 || !bytesAllData bs then .error .unsupported
          else
            match decodeValBytes prog.policy prog.records bs toTy with
            | some r => .ok (r, f1, m1)
            | none   => .error .unsupported
        | _, _, _ => .error .unsupported

/-- Evaluate a list of call arguments left-to-right. -/
noncomputable def evalExprList (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) :
    List CppExpr → Except CppFaultKind (List CppVal × CppFrame × CppMemory)
  | [] => .ok ([], frame, mem)
  | e :: es =>
    match evalExpr prog body frame mem e with
    | .error k => .error k
    | .ok (v, f1, m1) =>
      match evalExprList prog body f1 m1 es with
      | .error k        => .error k
      | .ok (vs, f2, m2) => .ok (v :: vs, f2, m2)

end Trusted.CppSemantics

end
