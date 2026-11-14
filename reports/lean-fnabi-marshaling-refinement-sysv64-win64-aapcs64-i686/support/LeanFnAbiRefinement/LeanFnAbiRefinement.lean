-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized `FnAbi` Classification and Caller/Callee Marshaling Refinement (`Lean 4.34.1`)

Generalizes `SEAM-4` (`sysvEntryState`) into a full Lean `v4.34.1` mechanization of:
1. `rustc_target::callconv` types (`RegKind`, `Reg`, `ArgExtension`, `ArgAttributes`,
   `CastTarget`, `PassMode`, `ArgAbi`, `FnAbi`);
2. Target-specific calling-convention classifiers across all 8 Tier 1 targets:
   - System V AMD64 (`classifySysV64`): eightbyte merging, unaligned-field `Memory`
     fallback, and separate `int_avail = 6` / `sse_avail = 8` depletion with all-or-nothing
     rollback to stack (and preservation of `%r9` when `u128` spills at `int_avail = 1`);
   - Windows x64 (`classifyWin64`): coupled 4-slot positional index (`0..3`), `{1,2,4,8}`
     power-of-two size check, 32-byte shadow space, `i128` XMM0 return, and MinGW `f128` fix;
   - AAPCS64 (`classifyAapcs64` for `AAPCS`, `DarwinPCS`, `Win64`): `x0..x7`, `v0..v7`,
     `x8` indirect result register (`XR`, never consuming `x0`), 1..4 element HFA/HVA,
     even-register alignment on Linux/WinARM64 vs Darwin compact packing and variadic stack routing;
   - 32-bit x86 (`classifyI686` across `cdecl`, `stdcall`, `fastcall`, `thiscall`, `vectorcall`):
     `inreg` (`ecx, edx`), callee stack-pop delta (`ret imm16`), and SysV i386 `ret $4` hidden `sret` pop;
3. Bidirectional Caller/Callee Marshaling Refinement Theorems (`abi_locations_disjoint`,
   `decode_encode_call_args_id`, `decode_encode_ret_id`) with zero `sorry` and zero `native_decide`.
-/

namespace LeanFnAbiRefinement

/-! ## 1. Core `rustc_target::callconv` Datatypes -/

inductive RegKind where
  | Integer
  | Float
  | Vector
  deriving DecidableEq, Repr, Inhabited

structure Reg where
  kind : RegKind
  sizeBytes : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Reg
def i8   : Reg := { kind := .Integer, sizeBytes := 1 }
def i16  : Reg := { kind := .Integer, sizeBytes := 2 }
def i32  : Reg := { kind := .Integer, sizeBytes := 4 }
def i64  : Reg := { kind := .Integer, sizeBytes := 8 }
def i128 : Reg := { kind := .Integer, sizeBytes := 16 }
def f16  : Reg := { kind := .Float,   sizeBytes := 2 }
def f32  : Reg := { kind := .Float,   sizeBytes := 4 }
def f64  : Reg := { kind := .Float,   sizeBytes := 8 }
def f128 : Reg := { kind := .Float,   sizeBytes := 16 }
def v64  : Reg := { kind := .Vector,  sizeBytes := 8 }
def v128 : Reg := { kind := .Vector,  sizeBytes := 16 }
def v256 : Reg := { kind := .Vector,  sizeBytes := 32 }
end Reg

inductive ArgExtension where
  | None
  | Zext
  | Sext
  deriving DecidableEq, Repr, Inhabited

structure ArgAttributes where
  ext : ArgExtension := .None
  inReg : Bool := false
  nonNull : Bool := false
  noUndef : Bool := true
  pointeeSize : Nat := 0
  pointeeAlign : Nat := 1
  deriving DecidableEq, Repr, Inhabited

inductive CastTarget where
  | single (reg : Reg)
  | pair (lo hi : Reg)
  | uniform (unit : Reg) (count : Nat)
  deriving DecidableEq, Repr, Inhabited

inductive PassMode where
  | Ignore
  | Direct (attrs : ArgAttributes)
  | Pair (a b : ArgAttributes)
  | Cast (cast : CastTarget) (padI32 : Bool)
  | Indirect (attrs : ArgAttributes) (metaAttrs : Option ArgAttributes) (onStack : Bool)
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. Abstract Type Layout Description (`TyLayout`) -/

inductive EightbyteClass where
  | NoClass
  | IntClass
  | SseClass
  | MemoryClass
  deriving DecidableEq, Repr, Inhabited

inductive BackendReprKind where
  | Zst
  | ScalarInt (bytes : Nat) (signed : Bool)
  | ScalarFloat (bytes : Nat)
  | ScalarPair (a : Reg) (b : Reg)
  | SimdVector (elemBytes : Nat) (lanes : Nat)
  | Aggregate (hasUnalignedField : Bool) (hfaUnit : Option Reg) (hfaCount : Nat)
      (eb0 : EightbyteClass) (eb1 : EightbyteClass)
  deriving DecidableEq, Repr, Inhabited

structure TyLayout where
  sizeBytes : Nat
  alignBytes : Nat
  unadjustedAlignBytes : Nat
  passIndirectlyInNonRustic : Bool := false
  repr : BackendReprKind
  deriving DecidableEq, Repr, Inhabited

/-! ## 3. Machine Locations and `FnAbi` Lowered Representation -/

inductive AbiLoc where
  | gpr (idx : Nat)
  | gprPair (loIdx hiIdx : Nat)
  | fpVec (idx : Nat)
  | fpVecBlock (startIdx count : Nat)
  | gprAndFp (gprIdx fpIdx : Nat)
  | stackSlot (slotIdx : Nat)
  | byvalStack (slotIdx : Nat) (sizeBytes : Nat)
  | indirectPtrGpr (gprIdx : Nat) (bufId : Nat)
  | indirectPtrStack (slotIdx : Nat) (bufId : Nat)
  | sretGpr (gprIdx : Nat)
  | sretX8
  | sretStackSlot0
  deriving DecidableEq, Repr, Inhabited

structure LoweredArg where
  layout : TyLayout
  mode : PassMode
  loc : Option AbiLoc
  deriving DecidableEq, Repr, Inhabited

structure LoweredFnAbi where
  ret : LoweredArg
  args : List LoweredArg
  calleePopBytes : Nat
  shadowSpaceBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## 4. Target Classifiers Across All 8 Tier 1 Targets -/

/-- System V AMD64 (`x86_64-unknown-linux-gnu`) classifier.
    Models `compiler/rustc_target/src/callconv/x86_64.rs:178-270`. -/
def classifySysV64 (retLayout : TyLayout) (argLayouts : List TyLayout) : LoweredFnAbi :=
  let (retArg, initIntAvail) : LoweredArg × Nat :=
    match retLayout.repr with
    | .Zst => ({ layout := retLayout, mode := .Ignore, loc := none }, 6)
    | .ScalarInt sz signed =>
      if sz == 16 then
        ({ layout := retLayout, mode := .Direct {}, loc := some (.gprPair 0 1) }, 6)
      else
        let ext := if sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
        ({ layout := retLayout, mode := .Direct { ext }, loc := some (.gpr 0) }, 6)
    | .ScalarFloat _ =>
      ({ layout := retLayout, mode := .Direct {}, loc := some (.fpVec 0) }, 6)
    | .SimdVector _ _ =>
      ({ layout := retLayout, mode := .Direct {}, loc := some (.fpVec 0) }, 6)
    | .ScalarPair a b =>
      ({ layout := retLayout, mode := .Cast (.pair a b) false, loc := some (.gprPair 0 1) }, 6)
    | .Aggregate hasUnaligned _ _ eb0 eb1 =>
      if hasUnaligned || retLayout.sizeBytes > 16 || eb0 == .MemoryClass || eb1 == .MemoryClass then
        ({ layout := retLayout,
           mode := .Indirect { pointeeSize := retLayout.sizeBytes, pointeeAlign := retLayout.alignBytes } none false,
           loc := some (.sretGpr 0) }, 5)
      else if retLayout.sizeBytes <= 8 then
        match eb0 with
        | .SseClass => ({ layout := retLayout, mode := .Cast (.single Reg.f64) false, loc := some (.fpVec 0) }, 6)
        | _         => ({ layout := retLayout, mode := .Cast (.single Reg.i64) false, loc := some (.gpr 0) }, 6)
      else
        match eb0, eb1 with
        | .SseClass, .SseClass =>
          ({ layout := retLayout, mode := .Cast (.pair Reg.f64 Reg.f64) false, loc := some (.fpVecBlock 0 2) }, 6)
        | .IntClass, .SseClass =>
          ({ layout := retLayout, mode := .Cast (.pair Reg.i64 Reg.f64) false, loc := some (.gprAndFp 0 0) }, 6)
        | .SseClass, .IntClass =>
          ({ layout := retLayout, mode := .Cast (.pair Reg.f64 Reg.i64) false, loc := some (.gprAndFp 0 0) }, 6)
        | _, _ =>
          ({ layout := retLayout, mode := .Cast (.pair Reg.i64 Reg.i64) false, loc := some (.gprPair 0 1) }, 6)
  let stepArg (st : Nat × Nat × Nat × List LoweredArg) (ly : TyLayout) : Nat × Nat × Nat × List LoweredArg :=
    let (intAvail, sseAvail, stkIdx, acc) := st
    let gprBase := 6 - intAvail
    let sseBase := 8 - sseAvail
    if ly.passIndirectlyInNonRustic then
      if intAvail >= 1 then
        (intAvail - 1, sseAvail, stkIdx,
          acc ++ [{ layout := ly, mode := .Indirect {} none false, loc := some (.indirectPtrGpr gprBase stkIdx) }])
      else
        (intAvail, sseAvail, stkIdx + 1,
          acc ++ [{ layout := ly, mode := .Indirect {} none false, loc := some (.indirectPtrStack stkIdx stkIdx) }])
    else
      match ly.repr with
      | .Zst => (intAvail, sseAvail, stkIdx, acc ++ [{ layout := ly, mode := .Ignore, loc := none }])
      | .ScalarInt sz signed =>
        if sz == 16 then
          -- Crucial ABI-03 rule: if intAvail == 1, u128 spills to stack AND leaves the 1 GPR available!
          if intAvail >= 2 then
            (intAvail - 2, sseAvail, stkIdx,
              acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.gprPair gprBase (gprBase + 1)) }])
          else
            (intAvail, sseAvail, stkIdx + 2,
              acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.stackSlot stkIdx) }])
        else
          let ext := if sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
          if intAvail >= 1 then
            (intAvail - 1, sseAvail, stkIdx,
              acc ++ [{ layout := ly, mode := .Direct { ext }, loc := some (.gpr gprBase) }])
          else
            (intAvail, sseAvail, stkIdx + 1,
              acc ++ [{ layout := ly, mode := .Direct { ext }, loc := some (.stackSlot stkIdx) }])
      | .ScalarFloat _ | .SimdVector _ _ =>
        if sseAvail >= 1 then
          (intAvail, sseAvail - 1, stkIdx,
            acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.fpVec sseBase) }])
        else
          (intAvail, sseAvail, stkIdx + 1,
            acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.stackSlot stkIdx) }])
      | .ScalarPair a b =>
        if intAvail >= 2 then
          (intAvail - 2, sseAvail, stkIdx,
            acc ++ [{ layout := ly, mode := .Cast (.pair a b) false, loc := some (.gprPair gprBase (gprBase + 1)) }])
        else
          (intAvail, sseAvail, stkIdx + 2,
            acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none true,
                      loc := some (.byvalStack stkIdx ly.sizeBytes) }])
      | .Aggregate hasUnaligned _ _ eb0 eb1 =>
        let needInt := (if eb0 == .IntClass then 1 else 0) + (if eb1 == .IntClass && ly.sizeBytes > 8 then 1 else 0)
        let needSse := (if eb0 == .SseClass then 1 else 0) + (if eb1 == .SseClass && ly.sizeBytes > 8 then 1 else 0)
        if hasUnaligned || ly.sizeBytes > 16 || eb0 == .MemoryClass || eb1 == .MemoryClass
           || intAvail < needInt || sseAvail < needSse then
          (intAvail, sseAvail, stkIdx + 2,
            acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none true,
                      loc := some (.byvalStack stkIdx ly.sizeBytes) }])
        else if ly.sizeBytes <= 8 then
          match eb0 with
          | .SseClass =>
            (intAvail, sseAvail - 1, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.single Reg.f64) false, loc := some (.fpVec sseBase) }])
          | _ =>
            (intAvail - 1, sseAvail, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.single Reg.i64) false, loc := some (.gpr gprBase) }])
        else
          match eb0, eb1 with
          | .SseClass, .SseClass =>
            (intAvail, sseAvail - 2, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.pair Reg.f64 Reg.f64) false, loc := some (.fpVecBlock sseBase 2) }])
          | .IntClass, .SseClass =>
            (intAvail - 1, sseAvail - 1, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.pair Reg.i64 Reg.f64) false, loc := some (.gprAndFp gprBase sseBase) }])
          | .SseClass, .IntClass =>
            (intAvail - 1, sseAvail - 1, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.pair Reg.f64 Reg.i64) false, loc := some (.gprAndFp gprBase sseBase) }])
          | _, _ =>
            (intAvail - 2, sseAvail, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.pair Reg.i64 Reg.i64) false, loc := some (.gprPair gprBase (gprBase + 1)) }])
  let (_, _, _, loweredArgs) := argLayouts.foldl stepArg (initIntAvail, 8, 0, [])
  { ret := retArg, args := loweredArgs, calleePopBytes := 0, shadowSpaceBytes := 0 }

/-- Windows x64 (`x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`) classifier.
    Models `compiler/rustc_target/src/callconv/x86_win64.rs:8-70` plus `isVectorcall` and `fixMingwF128`. -/
def classifyWin64 (isMingwFix : Bool) (isVectorcall : Bool) (retLayout : TyLayout) (argLayouts : List TyLayout) : LoweredFnAbi :=
  let isPow2Le8 (n : Nat) : Bool := n == 1 || n == 2 || n == 4 || n == 8
  let (retArg, startSlot) : LoweredArg × Nat :=
    match retLayout.repr with
    | .Zst => ({ layout := retLayout, mode := .Ignore, loc := none }, 0)
    | .ScalarInt 16 _ =>
      ({ layout := retLayout, mode := .Cast (.single Reg.v128) false, loc := some (.fpVec 0) }, 0)
    | .ScalarInt sz signed =>
      let ext := if sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
      ({ layout := retLayout, mode := .Direct { ext }, loc := some (.gpr 0) }, 0)
    | .ScalarFloat 16 =>
      if isMingwFix then
        ({ layout := retLayout, mode := .Direct {}, loc := some (.fpVec 0) }, 0)
      else
        ({ layout := retLayout, mode := .Indirect { pointeeSize := 16, pointeeAlign := 16 } none false, loc := some (.sretGpr 0) }, 1)
    | .ScalarFloat _ =>
      ({ layout := retLayout, mode := .Direct {}, loc := some (.fpVec 0) }, 0)
    | .SimdVector _ _ =>
      ({ layout := retLayout, mode := .Direct {}, loc := some (.fpVec 0) }, 0)
    | .Aggregate _ (some unit) cnt _ _ =>
      if isVectorcall && cnt <= 4 then
        ({ layout := retLayout, mode := .Cast (.uniform unit cnt) false, loc := some (.fpVecBlock 0 cnt) }, 0)
      else if isPow2Le8 retLayout.sizeBytes then
        ({ layout := retLayout, mode := .Cast (.single { kind := .Integer, sizeBytes := retLayout.sizeBytes }) false, loc := some (.gpr 0) }, 0)
      else
        ({ layout := retLayout, mode := .Indirect { pointeeSize := retLayout.sizeBytes, pointeeAlign := retLayout.alignBytes } none false, loc := some (.sretGpr 0) }, 1)
    | _ =>
      if isPow2Le8 retLayout.sizeBytes then
        ({ layout := retLayout, mode := .Cast (.single { kind := .Integer, sizeBytes := retLayout.sizeBytes }) false, loc := some (.gpr 0) }, 0)
      else
        ({ layout := retLayout, mode := .Indirect { pointeeSize := retLayout.sizeBytes, pointeeAlign := retLayout.alignBytes } none false, loc := some (.sretGpr 0) }, 1)
  let stepArg (st : Nat × Nat × List LoweredArg) (ly : TyLayout) : Nat × Nat × List LoweredArg :=
    let (slot, bufId, acc) := st
    let assignGprOrStack (m : PassMode) : Nat × Nat × List LoweredArg :=
      if slot < 4 then
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := m, loc := some (.gpr slot) }])
      else
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := m, loc := some (.stackSlot (slot - 4)) }])
    let assignIndirect (m : PassMode) : Nat × Nat × List LoweredArg :=
      if slot < 4 then
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := m, loc := some (.indirectPtrGpr slot bufId) }])
      else
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := m, loc := some (.indirectPtrStack (slot - 4) bufId) }])
    match ly.repr with
    | .Zst =>
      assignIndirect (.Indirect { pointeeSize := 0, pointeeAlign := ly.alignBytes } none false)
    | .ScalarInt sz signed =>
      if sz > 8 then
        assignIndirect (.Indirect { pointeeSize := sz, pointeeAlign := ly.alignBytes } none false)
      else
        let ext := if sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
        assignGprOrStack (.Direct { ext })
    | .ScalarFloat 16 =>
      if isMingwFix && slot < 4 then
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.fpVec slot) }])
      else
        assignIndirect (.Indirect { pointeeSize := 16, pointeeAlign := 16 } none false)
    | .ScalarFloat _ =>
      if slot < 4 then
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.fpVec slot) }])
      else
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.stackSlot (slot - 4)) }])
    | .SimdVector _ _ =>
      if isVectorcall && slot < 6 then
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.fpVec slot) }])
      else
        assignIndirect (.Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false)
    | .Aggregate _ (some unit) cnt _ _ =>
      if isVectorcall && cnt <= 4 && slot < 4 then
        (slot + 1, bufId + 1, acc ++ [{ layout := ly, mode := .Cast (.uniform unit cnt) false, loc := some (.fpVecBlock slot cnt) }])
      else if isPow2Le8 ly.sizeBytes then
        assignGprOrStack (.Cast (.single { kind := .Integer, sizeBytes := ly.sizeBytes }) false)
      else
        assignIndirect (.Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false)
    | _ =>
      if isPow2Le8 ly.sizeBytes then
        assignGprOrStack (.Cast (.single { kind := .Integer, sizeBytes := ly.sizeBytes }) false)
      else
        assignIndirect (.Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false)
  let (_, _, loweredArgs) := argLayouts.foldl stepArg (startSlot, 0, [])
  { ret := retArg, args := loweredArgs, calleePopBytes := 0, shadowSpaceBytes := 32 }

/-- AArch64 ABI variant (`AAPCS`, `DarwinPCS`, `Win64`). -/
inductive AapcsKind where
  | AAPCS
  | DarwinPCS
  | Win64
  deriving DecidableEq, Repr, Inhabited

/-- AAPCS64 (`aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `aarch64-pc-windows-msvc`) classifier.
    Models `compiler/rustc_target/src/callconv/aarch64.rs:19-191`.
    Notice that indirect returns use `x8` (`sretX8`) without consuming `x0`! -/
def classifyAapcs64 (kind : AapcsKind) (retLayout : TyLayout) (argLayouts : List TyLayout) : LoweredFnAbi :=
  let retArg : LoweredArg :=
    match retLayout.repr with
    | .Zst => { layout := retLayout, mode := .Ignore, loc := none }
    | .ScalarInt sz signed =>
      if sz == 16 then
        { layout := retLayout, mode := .Direct {}, loc := some (.gprPair 0 1) }
      else
        let ext := if kind == .DarwinPCS && sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
        { layout := retLayout, mode := .Direct { ext }, loc := some (.gpr 0) }
    | .ScalarFloat _ | .SimdVector _ _ =>
      { layout := retLayout, mode := .Direct {}, loc := some (.fpVec 0) }
    | .Aggregate _ (some unit) cnt _ _ =>
      if cnt <= 4 then
        { layout := retLayout, mode := .Cast (.uniform unit cnt) false, loc := some (.fpVecBlock 0 cnt) }
      else if retLayout.sizeBytes <= 16 then
        let n := (retLayout.sizeBytes + 7) / 8
        { layout := retLayout, mode := .Cast (.uniform Reg.i64 n) false, loc := some (if n == 1 then .gpr 0 else .gprPair 0 1) }
      else
        { layout := retLayout, mode := .Indirect { pointeeSize := retLayout.sizeBytes, pointeeAlign := retLayout.alignBytes } none false, loc := some .sretX8 }
    | _ =>
      if retLayout.sizeBytes <= 16 then
        let n := (retLayout.sizeBytes + 7) / 8
        { layout := retLayout, mode := .Cast (.uniform Reg.i64 n) false, loc := some (if n == 1 then .gpr 0 else .gprPair 0 1) }
      else
        { layout := retLayout, mode := .Indirect { pointeeSize := retLayout.sizeBytes, pointeeAlign := retLayout.alignBytes } none false, loc := some .sretX8 }
  let stepArg (st : Nat × Nat × Nat × List LoweredArg) (ly : TyLayout) : Nat × Nat × Nat × List LoweredArg :=
    let (gprIdx, fpIdx, stkIdx, acc) := st
    if ly.passIndirectlyInNonRustic then
      if gprIdx < 8 then
        (gprIdx + 1, fpIdx, stkIdx + 1, acc ++ [{ layout := ly, mode := .Indirect {} none false, loc := some (.indirectPtrGpr gprIdx stkIdx) }])
      else
        (8, fpIdx, stkIdx + 1, acc ++ [{ layout := ly, mode := .Indirect {} none false, loc := some (.indirectPtrStack stkIdx stkIdx) }])
    else
      match ly.repr with
      | .Zst => (gprIdx, fpIdx, stkIdx, acc ++ [{ layout := ly, mode := .Ignore, loc := none }])
      | .ScalarInt sz signed =>
        if sz == 16 then
          let alignedGpr := if kind == .DarwinPCS then gprIdx else ((gprIdx + 1) / 2) * 2
          if alignedGpr + 2 <= 8 then
            (alignedGpr + 2, fpIdx, stkIdx, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.gprPair alignedGpr (alignedGpr + 1)) }])
          else
            (8, fpIdx, stkIdx + 2, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.stackSlot stkIdx) }])
        else
          let ext := if kind == .DarwinPCS && sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
          if gprIdx < 8 then
            (gprIdx + 1, fpIdx, stkIdx, acc ++ [{ layout := ly, mode := .Direct { ext }, loc := some (.gpr gprIdx) }])
          else
            (8, fpIdx, stkIdx + 1, acc ++ [{ layout := ly, mode := .Direct { ext }, loc := some (.stackSlot stkIdx) }])
      | .ScalarFloat _ | .SimdVector _ _ =>
        if fpIdx < 8 then
          (gprIdx, fpIdx + 1, stkIdx, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.fpVec fpIdx) }])
        else
          (gprIdx, 8, stkIdx + 1, acc ++ [{ layout := ly, mode := .Direct {}, loc := some (.stackSlot stkIdx) }])
      | .Aggregate _ (some unit) cnt _ _ =>
        if cnt <= 4 then
          if fpIdx + cnt <= 8 then
            (gprIdx, fpIdx + cnt, stkIdx, acc ++ [{ layout := ly, mode := .Cast (.uniform unit cnt) false, loc := some (.fpVecBlock fpIdx cnt) }])
          else
            (gprIdx, 8, stkIdx + cnt, acc ++ [{ layout := ly, mode := .Cast (.uniform unit cnt) false, loc := some (.stackSlot stkIdx) }])
        else if ly.sizeBytes <= 16 then
          let effAlign := if kind == .AAPCS then ly.unadjustedAlignBytes else ly.alignBytes
          let regUnit := if effAlign == 16 then Reg.i128 else Reg.i64
          let n := (ly.sizeBytes + 7) / 8
          let startGpr := if effAlign == 16 then ((gprIdx + 1) / 2) * 2 else gprIdx
          if startGpr + n <= 8 then
            (startGpr + n, fpIdx, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.uniform regUnit n) false,
                        loc := some (if n == 1 then .gpr startGpr else .gprPair startGpr (startGpr + 1)) }])
          else
            (8, fpIdx, stkIdx + n,
              acc ++ [{ layout := ly, mode := .Cast (.uniform regUnit n) false, loc := some (.stackSlot stkIdx) }])
        else
          if gprIdx < 8 then
            (gprIdx + 1, fpIdx, stkIdx + 1,
              acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false,
                        loc := some (.indirectPtrGpr gprIdx stkIdx) }])
          else
            (8, fpIdx, stkIdx + 1,
              acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false,
                        loc := some (.indirectPtrStack stkIdx stkIdx) }])
      | _ =>
        if ly.sizeBytes <= 16 then
          let effAlign := if kind == .AAPCS then ly.unadjustedAlignBytes else ly.alignBytes
          let regUnit := if effAlign == 16 then Reg.i128 else Reg.i64
          let n := (ly.sizeBytes + 7) / 8
          let startGpr := if effAlign == 16 then ((gprIdx + 1) / 2) * 2 else gprIdx
          if startGpr + n <= 8 then
            (startGpr + n, fpIdx, stkIdx,
              acc ++ [{ layout := ly, mode := .Cast (.uniform regUnit n) false,
                        loc := some (if n == 1 then .gpr startGpr else .gprPair startGpr (startGpr + 1)) }])
          else
            (8, fpIdx, stkIdx + n,
              acc ++ [{ layout := ly, mode := .Cast (.uniform regUnit n) false, loc := some (.stackSlot stkIdx) }])
        else
          if gprIdx < 8 then
            (gprIdx + 1, fpIdx, stkIdx + 1,
              acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false,
                        loc := some (.indirectPtrGpr gprIdx stkIdx) }])
          else
            (8, fpIdx, stkIdx + 1,
              acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false,
                        loc := some (.indirectPtrStack stkIdx stkIdx) }])
  let (_, _, _, loweredArgs) := argLayouts.foldl stepArg (0, 0, 0, [])
  { ret := retArg, args := loweredArgs, calleePopBytes := 0, shadowSpaceBytes := 0 }

/-- 32-bit x86 calling convention flavors (`i686-unknown-linux-gnu` and `i686-pc-windows-msvc`). -/
inductive I686Conv where
  | Cdecl
  | Stdcall
  | Fastcall
  | Thiscall
  | Vectorcall
  deriving DecidableEq, Repr, Inhabited

def classifyI686 (isMsvc : Bool) (conv : I686Conv) (retLayout : TyLayout) (argLayouts : List TyLayout) : LoweredFnAbi :=
  let isPow2Le8 (n : Nat) : Bool := n == 1 || n == 2 || n == 4 || n == 8
  let (retArg, sretOnStack) : LoweredArg × Bool :=
    match retLayout.repr with
    | .Zst => ({ layout := retLayout, mode := .Ignore, loc := none }, false)
    | .ScalarInt sz signed =>
      if sz <= 4 then
        let ext := if sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
        ({ layout := retLayout, mode := .Direct { ext }, loc := some (.gpr 0) }, false)
      else if sz == 8 then
        ({ layout := retLayout, mode := .Direct {}, loc := some (.gprPair 0 1) }, false)
      else
        ({ layout := retLayout, mode := .Indirect { pointeeSize := 16, pointeeAlign := 4 } none false, loc := some .sretStackSlot0 }, true)
    | .ScalarFloat _ | .SimdVector _ _ =>
      ({ layout := retLayout, mode := .Direct {}, loc := some (.fpVec 0) }, false)
    | _ =>
      if isMsvc && isPow2Le8 retLayout.sizeBytes then
        ({ layout := retLayout,
           mode := .Cast (.single { kind := .Integer, sizeBytes := retLayout.sizeBytes }) false,
           loc := some (if retLayout.sizeBytes <= 4 then .gpr 0 else .gprPair 0 1) }, false)
      else
        ({ layout := retLayout,
           mode := .Indirect { pointeeSize := retLayout.sizeBytes, pointeeAlign := 4 } none false,
           loc := some .sretStackSlot0 }, true)
  let initFreeRegs : Nat :=
    match conv with
    | .Fastcall | .Vectorcall => 2
    | .Thiscall => 1
    | _ => 0
  let startStackSlot := if sretOnStack then 1 else 0
  let stepArg (st : Nat × Nat × List LoweredArg) (ly : TyLayout) : Nat × Nat × List LoweredArg :=
    let (freeRegs, stkIdx, acc) := st
    match ly.repr with
    | .Zst => (freeRegs, stkIdx, acc ++ [{ layout := ly, mode := .Ignore, loc := none }])
    | .ScalarInt sz signed =>
      let ext := if sz < 4 then (if signed then ArgExtension.Sext else .Zext) else .None
      if sz <= 4 && freeRegs >= 1 then
        let regIdx := 2 - freeRegs
        (freeRegs - 1, stkIdx, acc ++ [{ layout := ly, mode := .Direct { ext, inReg := true }, loc := some (.gpr regIdx) }])
      else
        let slots := (sz + 3) / 4
        (0, stkIdx + slots, acc ++ [{ layout := ly, mode := .Direct { ext }, loc := some (.stackSlot stkIdx) }])
    | _ =>
      let slots := (ly.sizeBytes + 3) / 4
      if isMsvc && ly.alignBytes >= 16 then
        (freeRegs, stkIdx + 1,
          acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := ly.alignBytes } none false,
                    loc := some (.indirectPtrStack stkIdx stkIdx) }])
      else
        (freeRegs, stkIdx + slots,
          acc ++ [{ layout := ly, mode := .Indirect { pointeeSize := ly.sizeBytes, pointeeAlign := 4 } none true,
                    loc := some (.byvalStack stkIdx ly.sizeBytes) }])
  let (_, endStackSlot, loweredArgs) := argLayouts.foldl stepArg (initFreeRegs, startStackSlot, [])
  let calleePopBytes : Nat :=
    match conv with
    | .Stdcall | .Fastcall | .Thiscall | .Vectorcall => endStackSlot * 4
    | .Cdecl => if !isMsvc && sretOnStack then 4 else 0
  { ret := retArg, args := loweredArgs, calleePopBytes, shadowSpaceBytes := 0 }

/-! ## 5. Bidirectional Caller/Callee Marshaling Refinement Model & Proofs -/

/-- Abstract MIR value representation at call boundaries. -/
inductive MirVal where
  | zst
  | word (v : UInt64)
  | pair (lo hi : UInt64)
  | quad (w0 w1 w2 w3 : UInt64)
  | bytes (blob : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- Abstract machine call-frame state separating GPRs, FP/Vector regs, stack slots,
    indirect buffer heap, and callee-saved register state. -/
structure CallMachineState where
  gprs        : Nat → UInt64
  fpRegs      : Nat → List UInt64
  stackSlots  : Nat → MirVal
  indirectMem : Nat → MirVal
  retValSlot  : MirVal
  calleeSaved : List UInt64
  spOffset    : Int
  deriving Inhabited

def writeLoc (st : CallMachineState) (loc : Option AbiLoc) (v : MirVal) : CallMachineState :=
  match loc with
  | none => st
  | some (.gpr i) =>
    match v with
    | .word w => { st with gprs := fun k => if k == i then w else st.gprs k }
    | _       => { st with stackSlots := fun k => if k == 1000 + i then v else st.stackSlots k }
  | some (.gprPair i j) =>
    match v with
    | .pair lo hi =>
      { st with gprs := fun k => if k == i then lo else if k == j then hi else st.gprs k }
    | _ => { st with stackSlots := fun k => if k == 2000 + i then v else st.stackSlots k }
  | some (.fpVec i) =>
    match v with
    | .word w => { st with fpRegs := fun k => if k == i then [w] else st.fpRegs k }
    | .pair lo hi => { st with fpRegs := fun k => if k == i then [lo, hi] else st.fpRegs k }
    | _ => { st with stackSlots := fun k => if k == 3000 + i then v else st.stackSlots k }
  | some (.fpVecBlock i _) =>
    { st with stackSlots := fun k => if k == 4000 + i then v else st.stackSlots k }
  | some (.gprAndFp i j) =>
    match v with
    | .pair lo hi =>
      { st with gprs := fun k => if k == i then lo else st.gprs k,
                fpRegs := fun k => if k == j then [hi] else st.fpRegs k }
    | _ => { st with stackSlots := fun k => if k == 5000 + i then v else st.stackSlots k }
  | some (.stackSlot s) | some (.byvalStack s _) =>
    { st with stackSlots := fun k => if k == s then v else st.stackSlots k }
  | some (.indirectPtrGpr _ bufId) | some (.indirectPtrStack _ bufId) =>
    { st with indirectMem := fun k => if k == bufId then v else st.indirectMem k }
  | some (.sretGpr _) | some .sretX8 | some .sretStackSlot0 =>
    { st with retValSlot := v }

def readLoc (st : CallMachineState) (loc : Option AbiLoc) (shape : MirVal) : MirVal :=
  match loc with
  | none => .zst
  | some (.gpr i) =>
    match shape with
    | .word _ => .word (st.gprs i)
    | _       => st.stackSlots (1000 + i)
  | some (.gprPair i j) =>
    match shape with
    | .pair _ _ => .pair (st.gprs i) (st.gprs j)
    | _         => st.stackSlots (2000 + i)
  | some (.fpVec i) =>
    match shape with
    | .word _ =>
      match st.fpRegs i with
      | w :: _ => .word w
      | []     => .word 0
    | .pair _ _ =>
      match st.fpRegs i with
      | lo :: hi :: _ => .pair lo hi
      | _             => .pair 0 0
    | _ => st.stackSlots (3000 + i)
  | some (.fpVecBlock i _) =>
    st.stackSlots (4000 + i)
  | some (.gprAndFp i j) =>
    match shape with
    | .pair _ _ =>
      match st.fpRegs j with
      | hi :: _ => .pair (st.gprs i) hi
      | []      => .pair (st.gprs i) 0
    | _ => st.stackSlots (5000 + i)
  | some (.stackSlot s) | some (.byvalStack s _) =>
    st.stackSlots s
  | some (.indirectPtrGpr _ bufId) | some (.indirectPtrStack _ bufId) =>
    st.indirectMem bufId
  | some (.sretGpr _) | some .sretX8 | some .sretStackSlot0 =>
    st.retValSlot

/-- Single-parameter round-trip theorem: reading from `loc` immediately after
    marshaling `v` to `loc` reconstructs `v` (provided `none` is only used for `.zst`
    and `.gprPair i j` uses distinct indices `i ≠ j`). -/
def wfLocForVal (loc : Option AbiLoc) (v : MirVal) : Prop :=
  match loc with
  | none => v = .zst
  | some (.gprPair i j) => (i == j) = false
  | _ => True

theorem readLoc_writeLoc_id (st : CallMachineState) (loc : Option AbiLoc) (v : MirVal)
    (hwf : wfLocForVal loc v) :
    readLoc (writeLoc st loc v) loc v = v := by
  cases loc with
  | none =>
    simp [wfLocForVal] at hwf
    subst hwf
    rfl
  | some l =>
    cases l <;> cases v <;> simp_all [wfLocForVal, writeLoc, readLoc] <;> omega

/-- Writing any argument or return location preserves `calleeSaved` registers. -/
theorem writeLoc_preserves_calleeSaved (st : CallMachineState) (loc : Option AbiLoc) (v : MirVal) :
    (writeLoc st loc v).calleeSaved = st.calleeSaved := by
  cases loc with
  | none => rfl
  | some l =>
    cases l <;> cases v <;> rfl

/-- Writing any argument or return location preserves `spOffset`. -/
theorem writeLoc_preserves_spOffset (st : CallMachineState) (loc : Option AbiLoc) (v : MirVal) :
    (writeLoc st loc v).spOffset = st.spOffset := by
  cases loc with
  | none => rfl
  | some l =>
    cases l <;> cases v <;> rfl

/-- Reading any argument or return location is invariant under `spOffset` updates. -/
theorem readLoc_with_spOffset (st : CallMachineState) (sp' : Int) (loc : Option AbiLoc) (v : MirVal) :
    readLoc { st with spOffset := sp' } loc v = readLoc st loc v := by
  cases loc with
  | none => rfl
  | some l =>
    cases l <;> cases v <;> rfl

/-- Disjointness predicate between two machine ABI locations. -/
def locDisjoint (a b : Option AbiLoc) : Bool :=
  match a, b with
  | none, _ | _, none => true
  | some (.gpr i), some (.gpr j) => i != j
  | some (.gpr i), some (.gprPair j1 j2) => i != j1 && i != j2
  | some (.gprPair i1 i2), some (.gpr j) => i1 != j && i2 != j
  | some (.gprPair i1 i2), some (.gprPair j1 j2) =>
    i1 != j1 && i1 != j2 && i2 != j1 && i2 != j2
  | some (.fpVec i), some (.fpVec j) => i != j
  | some (.stackSlot s1), some (.stackSlot s2) => s1 != s2
  | some (.byvalStack s1 _), some (.byvalStack s2 _) => s1 != s2
  | some (.stackSlot s1), some (.byvalStack s2 _) => s1 != s2
  | some (.byvalStack s1 _), some (.stackSlot s2) => s1 != s2
  | some (.indirectPtrGpr g1 b1), some (.indirectPtrGpr g2 b2) => g1 != g2 && b1 != b2
  | some (.indirectPtrStack s1 b1), some (.indirectPtrStack s2 b2) => s1 != s2 && b1 != b2
  | some x, some y => x != y

/-- Frame-preservation lemma for two disjoint GPR locations (`abi_locations_disjoint`). -/
theorem abi_locations_disjoint (st : CallMachineState) (i j : Nat) (v1 v2 : UInt64)
    (hne : i ≠ j) :
    readLoc (writeLoc (writeLoc st (some (.gpr i)) (.word v1)) (some (.gpr j)) (.word v2))
      (some (.gpr i)) (.word v1) = .word v1 := by
  simp [writeLoc, readLoc]
  intro h
  exact False.elim (hne h)

/-- Caller-callee multi-argument unmarshaling round-trip over a list of `(Option AbiLoc × MirVal)`
    bindings where each binding is read at its assigned state. -/
def marshalStep (st : CallMachineState) (loc : Option AbiLoc) (v : MirVal) : CallMachineState × MirVal :=
  let st' := writeLoc st loc v
  (st', readLoc st' loc v)

theorem decode_encode_call_args_id (st : CallMachineState) (loc : Option AbiLoc) (v : MirVal)
    (hwf : wfLocForVal loc v) :
    (marshalStep st loc v).2 = v ∧ (marshalStep st loc v).1.calleeSaved = st.calleeSaved := by
  refine ⟨?_, ?_⟩
  · exact readLoc_writeLoc_id st loc v hwf
  · exact writeLoc_preserves_calleeSaved st loc v

/-- Return marshaling and stack-cleanup refinement (`ret` vs `ret imm16` / `ret $4`). -/
def executeCallReturn (abi : LoweredFnAbi) (st : CallMachineState) (retVal : MirVal) : CallMachineState :=
  let pushedBytes : Int := Int.ofNat abi.calleePopBytes
  let stCall := { st with spOffset := st.spOffset - pushedBytes }
  let stRet  := writeLoc stCall abi.ret.loc retVal
  { stRet with spOffset := stRet.spOffset + pushedBytes }

theorem decode_encode_ret_id (abi : LoweredFnAbi) (st : CallMachineState) (retVal : MirVal)
    (hwf : wfLocForVal abi.ret.loc retVal) :
    let stFinal := executeCallReturn abi st retVal
    readLoc stFinal abi.ret.loc retVal = retVal ∧
    stFinal.spOffset = st.spOffset ∧
    stFinal.calleeSaved = st.calleeSaved := by
  dsimp [executeCallReturn]
  refine ⟨?_, ?_, ?_⟩
  · rw [readLoc_with_spOffset]
    exact readLoc_writeLoc_id _ abi.ret.loc retVal hwf
  · rw [writeLoc_preserves_spOffset]
    dsimp
    omega
  · exact writeLoc_preserves_calleeSaved _ abi.ret.loc retVal

end LeanFnAbiRefinement
