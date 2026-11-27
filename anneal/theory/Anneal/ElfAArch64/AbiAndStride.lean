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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Anneal.ElfAArch64.Decode

public section
namespace Anneal.ElfAArch64

/-!
# AAPCS64 Width-Safety, Leaf/Loop ABI-SFI, and SIMD Stride/Bounds Gates
(`Anneal.ElfAArch64.AbiAndStride`)

Pure Pass-1 (`0` `._unsafe_rec`, `0` `partial`, `0` `noncomputable`, axioms
`⊆ {propext}`) verification gates and soundness theorems over decoded
`Anneal.ElfAArch64` streams and SIMD dispatch preconditions:

1. **AAPCS64 Upper-32-Bit Width-Safety (`checkAapcs64WidthSafety`,
   `checkCfgWidthInvs_sound`):**
   - Under AAPCS64, 32-bit scalar parameters (`i32`/`u32`) enter in `w0..w7`
     with unspecified upper bits `[63:32]` (`RegWidthState.lo32Only`), while
     64-bit pointers/integers enter with all 64 bits defined (`.full64`).
   - Wildcard-free `insnGprReads` and `insnGprWrites` track exact bit-width
     reads (including `SBFM`/`UBFM` `imms < 32` for `sxtw`/`uxtw` vs.
     `imms >= 32` for 64-bit `lsl`/`lsr`/`asr`, `addSubExt` `ExtendKind`,
     `MOVK` partial-write read, and `TBZ`/`TBNZ` bit index).
   - CFG-aware inductive invariant checking (`checkCfgWidthInvs`) handles
     both straight-line functions and intra-function loops (`B`, `B.cond`,
     `CBZ`/`CBNZ`, `TBZ`/`TBNZ`), proving upper-32-bit GPR read
     noninterference along arbitrary-length CFG traces **relative to the
     per-step `WidthSoundStep` hypothesis** (`checkCfgWidthInvs_sound`;
     `NZCV` flags and memory contents are outside `WidthSoundStep`'s scope).
2. **Two-Tier AAPCS64 Leaf/Loop Register-Discipline & Non-Negative Store
   Gates (`checkAArch64LeafAbiFixedBases`,
   `checkAArch64LeafAbiMonotoneBases`):**
   - Syntactic register-discipline and non-negative store-offset checks
     certifying zero writes to callee-saved GPRs (`x19..x30`) and platform
     register `x18`, zero writes to callee-saved SIMD registers `v8..v15`
     (including multi-register `LD1` wraparound via `simdRegRange`), zero
     `SP` writes or stack memory touches, zero traps/syscalls/calls/indirect
     branches, in-bounds 4-byte-aligned intra-function branch targets, final
     `RET x30`, non-negative store displacements, and either fixed-base or
     syntactically monotone immediate store-base advances (upper buffer bounds
     and 64-bit pointer wraparound freedom must be established by the caller
     and are not proven by these register-discipline predicates).
3. **SIMD Stride, Alignment & Vector-Chunk Bounds Gates (`VecTailStrideGuard`,
   `PlaneCopyGuard`, `neonPostIndexLoop_inBounds`):**
   - Proves chunk-aligned row-padding safety (`w1 = alignUp w chunk <= stride`)
     and constructively refutes the inverted guard (`stride <= w1`) with a
     14-byte overrun witness (`w = 2, chunk = 16, stride = 2`).
   - Proves all preconditions of aligned multi-vector 2D plane copies
     (positive width/height, signed-overflow-free alignment, aligned base
     addresses, row linesizes, and chunk strides for per-chunk alignment,
     and chunk-within-stride containment), paired with fail-closed
     regressions in `Canaries`.
-/

/-! ## 1. AAPCS64 Parameter-Width Lattice & Operational Noninterference -/

/-- AAPCS64 parameter width at function entry. -/
inductive AbiParamWidth where
  | narrow32 -- `i32` / `u32` passed in `wN`; upper `[63:32]` unspecified
  | full64   -- pointer / `usize` / `i64` / `u64` passed in `xN`

/-- Function-entry AAPCS64 GPR signature: maps argument register to width. -/
structure Aapcs64Sig where
  params : List (Gpr × AbiParamWidth)

/-- Per-register defined-width abstract state. -/
inductive RegWidthState where
  | undef    -- uninitialized / clobbered: neither `[31:0]` nor `[63:32]` known
  | lo32Only -- low `[31:0]` defined; upper `[63:32]` unspecified / demonic
  | full64   -- all 64 bits `[63:0]` defined

/-- Information-order check `a ≤ b` (`undef ≤ lo32Only ≤ full64`): `a` makes
no stronger definedness promise than `b`. -/
@[expose] def RegWidthState.le (a b : RegWidthState) : Bool :=
  match a, b with
  | .undef,    _         => true
  | .lo32Only, .lo32Only => true
  | .lo32Only, .full64   => true
  | .full64,   .full64   => true
  | _,         _         => false

/-- Lattice meet (greatest lower bound) at CFG join points. -/
@[expose] def RegWidthState.meet (a b : RegWidthState) : RegWidthState :=
  match a, b with
  | .full64,   .full64   => .full64
  | .full64,   .lo32Only => .lo32Only
  | .lo32Only, .full64   => .lo32Only
  | .lo32Only, .lo32Only => .lo32Only
  | _,         _         => .undef

/-- True iff `st` satisfies a register read requirement (`need64 = true`
requires `.full64`; `need64 = false` requires `.lo32Only` or `.full64`). -/
@[expose] def RegWidthState.satisfies (st : RegWidthState) (need64 : Bool) :
    Bool :=
  match st, need64 with
  | .full64,   _     => true
  | .lo32Only, false => true
  | _,         _     => false

/-- Abstract width map over all 31 GPRs (`x0..x30`). -/
abbrev WidthEnv := Gpr → RegWidthState

/-- Materialized 8-register bank for flat O(1) CFG fixpoint storage (avoids
closure nesting across relaxation passes). -/
structure WidthBank8 where
  r0 : RegWidthState
  r1 : RegWidthState
  r2 : RegWidthState
  r3 : RegWidthState
  r4 : RegWidthState
  r5 : RegWidthState
  r6 : RegWidthState
  r7 : RegWidthState

/-- Materialized 31-register width table (`4` banks of `8`, slot 31 unused). -/
structure WidthTable where
  b0 : WidthBank8
  b1 : WidthBank8
  b2 : WidthBank8
  b3 : WidthBank8

@[expose] def WidthBank8.toFun (b : WidthBank8) (k : Nat) : RegWidthState :=
  match k with
  | 0 => b.r0 | 1 => b.r1 | 2 => b.r2 | 3 => b.r3
  | 4 => b.r4 | 5 => b.r5 | 6 => b.r6 | _ => b.r7

/-- Convert a materialized `WidthTable` back to a `WidthEnv` function. -/
@[expose] def WidthTable.toEnv (t : WidthTable) : WidthEnv :=
  fun r =>
    let n := r.toNat
    if Nat.blt n 8 then t.b0.toFun n
    else if Nat.blt n 16 then t.b1.toFun (n - 8)
    else if Nat.blt n 24 then t.b2.toFun (n - 16)
    else t.b3.toFun (n - 24)

/-- Pointwise meet on an 8-register bank. -/
@[expose] def WidthBank8.meet (a b : WidthBank8) : WidthBank8 :=
  ⟨a.r0.meet b.r0, a.r1.meet b.r1, a.r2.meet b.r2, a.r3.meet b.r3,
   a.r4.meet b.r4, a.r5.meet b.r5, a.r6.meet b.r6, a.r7.meet b.r7⟩

/-- Set slot `k ∈ 0..7` in a `WidthBank8` to `st`. -/
@[expose] def WidthBank8.set (b : WidthBank8) (k : Nat)
    (st : RegWidthState) : WidthBank8 :=
  match k with
  | 0 => { b with r0 := st } | 1 => { b with r1 := st }
  | 2 => { b with r2 := st } | 3 => { b with r3 := st }
  | 4 => { b with r4 := st } | 5 => { b with r5 := st }
  | 6 => { b with r6 := st } | _ => { b with r7 := st }

/-- Top `WidthTable` (all GPRs `.full64`). -/
@[expose] def widthTableTop : WidthTable :=
  let b : WidthBank8 :=
    ⟨.full64, .full64, .full64, .full64,
     .full64, .full64, .full64, .full64⟩
  ⟨b, b, b, b⟩

/-- Pointwise meet of two `WidthTable`s (strict data, zero closure nesting). -/
@[expose] def WidthTable.meet (a b : WidthTable) : WidthTable :=
  ⟨a.b0.meet b.b0, a.b1.meet b.b1, a.b2.meet b.b2, a.b3.meet b.b3⟩

/-- Set register `r` in a `WidthTable` to `st`. -/
@[expose] def WidthTable.set (t : WidthTable) (r : Gpr)
    (st : RegWidthState) : WidthTable :=
  let n := r.toNat
  if Nat.blt n 8 then { t with b0 := t.b0.set n st }
  else if Nat.blt n 16 then { t with b1 := t.b1.set (n - 8) st }
  else if Nat.blt n 24 then { t with b2 := t.b2.set (n - 16) st }
  else { t with b3 := t.b3.set (n - 24) st }

/-- Set a list of registers in a `WidthTable` to `st`. -/
@[expose] def WidthTable.setList (t : WidthTable) (rs : List Gpr)
    (st : RegWidthState) : WidthTable :=
  List.foldr (fun r acc => acc.set r st) t rs

/-- Materialize any `WidthEnv` into a flat `WidthTable`. -/
@[expose] def widthTableOfEnv (env : WidthEnv) : WidthTable :=
  { b0 := ⟨env .x0,  env .x1,  env .x2,  env .x3,
           env .x4,  env .x5,  env .x6,  env .x7⟩
    b1 := ⟨env .x8,  env .x9,  env .x10, env .x11,
           env .x12, env .x13, env .x14, env .x15⟩
    b2 := ⟨env .x16, env .x17, env .x18, env .x19,
           env .x20, env .x21, env .x22, env .x23⟩
    b3 := ⟨env .x24, env .x25, env .x26, env .x27,
           env .x28, env .x29, env .x30, .undef⟩ }

/-- Materialize any `WidthEnv` into a flat `WidthTable`-backed `WidthEnv`. -/
@[expose] def materializeWidthEnv (env : WidthEnv) : WidthEnv :=
  (widthTableOfEnv env).toEnv

/-- Enumerated list of all 31 architectural GPRs (`x0..x30`). -/
@[expose] def allGprs : List Gpr :=
  [ .x0,  .x1,  .x2,  .x3,  .x4,  .x5,  .x6,  .x7,
    .x8,  .x9,  .x10, .x11, .x12, .x13, .x14, .x15,
    .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23,
    .x24, .x25, .x26, .x27, .x28, .x29, .x30 ]

/-- Top environment (all GPRs `.full64`, used to initialize fixpoint for
non-entry PCs). -/
@[expose] def widthEnvTop : WidthEnv := fun _ => .full64

/-- Initial AAPCS64 entry width environment:
- declared parameters take `.full64` or `.lo32Only` per `sig`,
- callee-saved GPRs (`x19..x30`, incl. return address `x30`) start `.full64`,
- undeclared scratch registers (`x0..x18`) start `.undef`. -/
@[expose] def initWidthEnv (sig : Aapcs64Sig) : WidthEnv :=
  fun r =>
    match listFind? (fun p => p.1.beq r) sig.params with
    | some (_, .full64)   => .full64
    | some (_, .narrow32) => .lo32Only
    | none => if r.isCalleeSaved then .full64 else .undef

/-- Pointwise order `e1 ≤ e2` across all 31 GPRs. -/
@[expose] def widthEnvLe (e1 e2 : WidthEnv) : Bool :=
  listAll (fun r => RegWidthState.le (e1 r) (e2 r)) allGprs

/-- Pointwise meet of two width environments (materialized to avoid closure
nesting across CFG relaxation rounds). -/
@[expose] def widthEnvMeet (e1 e2 : WidthEnv) : WidthEnv :=
  materializeWidthEnv (fun r => RegWidthState.meet (e1 r) (e2 r))

/-- Set a single register in `env` to `st`. -/
@[expose] def widthEnvSet (env : WidthEnv) (r : Gpr) (st : RegWidthState) :
    WidthEnv :=
  fun q => if q.beq r then st else env q

/-- Set a list of registers in `env` to `st`. -/
@[expose] def widthEnvSetList (env : WidthEnv) (rs : List Gpr)
    (st : RegWidthState) : WidthEnv :=
  List.foldr (fun r acc => widthEnvSet acc r st) env rs

/-! ## 2. Wildcard-Free GPR/SIMD Read-Write & CFG Successor Extraction -/

@[expose] def regOrZrRead (rz : RegOrZr) (need64 : Bool) :
    List (Gpr × Bool) :=
  match rz with
  | .gpr r => [(r, need64)]
  | .zr    => []

@[expose] def regOrSpRead (rs : RegOrSp) (need64 : Bool) :
    List (Gpr × Bool) :=
  match rs with
  | .gpr r => [(r, need64)]
  | .sp    => []

@[expose] def regOrZrWrite (rz : RegOrZr) : List Gpr :=
  match rz with
  | .gpr r => [r]
  | .zr    => []

@[expose] def regOrSpWrite (rs : RegOrSp) (isZr : Bool) : List Gpr :=
  if isZr then []
  else
    match rs with
    | .gpr r => [r]
    | .sp    => []

/-- Wildcard-free GPR read list `(reg, need64)` for every `DecodedInsn`.
`need64 = true` iff the instruction reads any bit at position `>= 32`. -/
@[expose] def insnGprReads (i : DecodedInsn) : List (Gpr × Bool) :=
  match i with
  | .addSubImm w _ _ _ _ rn _ _ =>
    regOrSpRead rn w.is64
  | .logicImm w _ _ _ rn _ _ _ =>
    regOrZrRead rn w.is64
  | .moveWide w op rd _ _ =>
    match op with
    | .movk => regOrZrRead rd w.is64
    | .movn | .movz => []
  | .bitfield w op rd rn _ imms =>
    let rnNeed64 := w.is64 && Nat.ble 32 imms
    match op with
    | .bfm => regOrZrRead rn rnNeed64 ++ regOrZrRead rd w.is64
    | .sbfm | .ubfm => regOrZrRead rn rnNeed64
  | .pcRelAddr _ _ _ _ => []
  | .addSubShift w _ _ _ _ _ rn rm =>
    regOrZrRead rn w.is64 ++ regOrZrRead rm w.is64
  | .addSubExt w _ _ ext _ _ _ rn rm =>
    regOrSpRead rn w.is64 ++
    regOrZrRead rm (w.is64 && ext.readsUpper32)
  | .logicShift w _ _ _ _ rn rm =>
    regOrZrRead rn w.is64 ++ regOrZrRead rm w.is64
  | .condSel w _ _ _ rn rm =>
    regOrZrRead rn w.is64 ++ regOrZrRead rm w.is64
  | .maddSub w _ _ rn rm ra =>
    regOrZrRead rn w.is64 ++ regOrZrRead rm w.is64 ++
    regOrZrRead ra w.is64
  | .div w _ _ rn rm =>
    regOrZrRead rn w.is64 ++ regOrZrRead rm w.is64
  | .branch _ _ => []
  | .branchCond _ _ => []
  | .cbz w _ rt _ => regOrZrRead rt w.is64
  | .tbz _ bitIdx rt _ => regOrZrRead rt (Nat.ble 32 bitIdx)
  | .ret rn => regOrZrRead rn true
  | .branchReg _ rn => regOrZrRead rn true
  | .nop => []
  | .bti _ => []
  | .msrDit _ => []
  | .sysImm _ _ => []
  | .trapOrSys => []
  | .gpLoadStore isLoad _ _ destW rt rn _ _ =>
    regOrSpRead rn true ++
    (if isLoad then [] else regOrZrRead rt destW.is64)
  | .gpLoadStorePair isLoad w rt rt2 rn _ =>
    regOrSpRead rn true ++
    (if isLoad then []
     else regOrZrRead rt w.is64 ++ regOrZrRead rt2 w.is64)
  | .simdLoadStore _ _ _ rn _ _ =>
    regOrSpRead rn true
  | .simdLoadStorePair _ _ _ _ rn _ =>
    regOrSpRead rn true
  | .simdLdSt1 _ _ _ _ _ rn post =>
    regOrSpRead rn true ++
    (match post with
     | .reg rm => [(rm, true)]
     | .none | .imm _ => [])
  | .simdShiftImm _ _ _ _ _ _ => []
  | .simdThreeSame _ _ _ _ _ _ => []
  | .simdCmeqZero _ _ _ _ => []
  | .simdPerm _ _ _ _ _ _ => []

/-- Wildcard-free list of GPRs written by `i` (including writeback base
registers and `x30` on `BL`/`BLR`). -/
@[expose] def insnGprWrites (i : DecodedInsn) : List Gpr :=
  match i with
  | .addSubImm _ _ _ rd rdIsZr _ _ _ => regOrSpWrite rd rdIsZr
  | .logicImm _ _ rd rdIsZr _ _ _ _ => regOrSpWrite rd rdIsZr
  | .moveWide _ _ rd _ _ => regOrZrWrite rd
  | .bitfield _ _ rd _ _ _ => regOrZrWrite rd
  | .pcRelAddr _ rd _ _ => regOrZrWrite rd
  | .addSubShift _ _ _ _ _ rd _ _ => regOrZrWrite rd
  | .addSubExt _ _ _ _ _ rd rdIsZr _ _ => regOrSpWrite rd rdIsZr
  | .logicShift _ _ _ _ rd _ _ => regOrZrWrite rd
  | .condSel _ _ _ rd _ _ => regOrZrWrite rd
  | .maddSub _ _ rd _ _ _ => regOrZrWrite rd
  | .div _ _ rd _ _ => regOrZrWrite rd
  | .branch isLink _ => if isLink then [.x30] else []
  | .branchCond _ _ => []
  | .cbz _ _ _ _ => []
  | .tbz _ _ _ _ => []
  | .ret _ => []
  | .branchReg isLink _ => if isLink then [.x30] else []
  | .nop => []
  | .bti _ => []
  | .msrDit _ => []
  | .sysImm _ _ => []
  | .trapOrSys => []
  | .gpLoadStore isLoad _ _ _ rt rn mode _ =>
    let wb :=
      match mode with
      | .unsignedOff _ => []
      | .postIndex _ | .preIndex _ => regOrSpWrite rn false
    (if isLoad then regOrZrWrite rt else []) ++ wb
  | .gpLoadStorePair isLoad _ rt rt2 rn mode =>
    let wb :=
      match mode with
      | .signedOff _ => []
      | .postIndex _ | .preIndex _ => regOrSpWrite rn false
    (if isLoad then regOrZrWrite rt ++ regOrZrWrite rt2 else []) ++ wb
  | .simdLoadStore _ _ _ rn mode _ =>
    match mode with
    | .unsignedOff _ => []
    | .postIndex _ | .preIndex _ => regOrSpWrite rn false
  | .simdLoadStorePair _ _ _ _ rn mode =>
    match mode with
    | .signedOff _ => []
    | .postIndex _ | .preIndex _ => regOrSpWrite rn false
  | .simdLdSt1 _ _ _ _ _ rn post =>
    match post with
    | .none => []
    | .imm _ | .reg _ => regOrSpWrite rn false
  | .simdShiftImm _ _ _ _ _ _ => []
  | .simdThreeSame _ _ _ _ _ _ => []
  | .simdCmeqZero _ _ _ _ => []
  | .simdPerm _ _ _ _ _ _ => []

/-- Wildcard-free list of SIMD vector registers (`v0..v31`) written by `i`. -/
@[expose] def insnVRegWrites (i : DecodedInsn) : List VReg :=
  match i with
  | .simdLoadStore isLoad _ vt _ _ _ => if isLoad then [vt] else []
  | .simdLoadStorePair isLoad _ vt vt2 _ _ =>
    if isLoad then [vt, vt2] else []
  | .simdLdSt1 isLoad _ numRegs _ vt _ _ =>
    if isLoad then simdRegRange vt numRegs else []
  | .simdShiftImm _ _ _ _ vd _ => [vd]
  | .simdThreeSame _ _ _ vd _ _ => [vd]
  | .simdCmeqZero _ _ vd _ => [vd]
  | .simdPerm _ _ _ vd _ _ => [vd]
  | .addSubImm _ _ _ _ _ _ _ _ | .logicImm _ _ _ _ _ _ _ _
  | .moveWide _ _ _ _ _ | .bitfield _ _ _ _ _ _ | .pcRelAddr _ _ _ _
  | .addSubShift _ _ _ _ _ _ _ _ | .addSubExt _ _ _ _ _ _ _ _ _
  | .logicShift _ _ _ _ _ _ _ | .condSel _ _ _ _ _ _
  | .maddSub _ _ _ _ _ _ | .div _ _ _ _ _ | .branch _ _ | .branchCond _ _
  | .cbz _ _ _ _ | .tbz _ _ _ _ | .ret _ | .branchReg _ _
  | .nop | .bti _ | .msrDit _ | .sysImm _ _ | .trapOrSys
  | .gpLoadStore _ _ _ _ _ _ _ _ | .gpLoadStorePair _ _ _ _ _ _ => []

/-- True iff `i` writes `SP` or uses `SP` as a memory base register. -/
@[expose] def insnTouchesSp (i : DecodedInsn) : Bool :=
  match i with
  | .addSubImm _ _ _ rd rdIsZr rn _ _ =>
    (!rdIsZr && rd.isSp) || rn.isSp
  | .logicImm _ _ rd rdIsZr _ _ _ _ =>
    !rdIsZr && rd.isSp
  | .addSubExt _ _ _ _ _ rd rdIsZr rn _ =>
    (!rdIsZr && rd.isSp) || rn.isSp
  | .gpLoadStore _ _ _ _ _ rn _ _ => rn.isSp
  | .gpLoadStorePair _ _ _ _ rn _ => rn.isSp
  | .simdLoadStore _ _ _ rn _ _ => rn.isSp
  | .simdLoadStorePair _ _ _ _ rn _ => rn.isSp
  | .simdLdSt1 _ _ _ _ _ rn _ => rn.isSp
  | .moveWide _ _ _ _ _ | .bitfield _ _ _ _ _ _ | .pcRelAddr _ _ _ _
  | .addSubShift _ _ _ _ _ _ _ _ | .logicShift _ _ _ _ _ _ _
  | .condSel _ _ _ _ _ _ | .maddSub _ _ _ _ _ _ | .div _ _ _ _ _
  | .branch _ _ | .branchCond _ _ | .cbz _ _ _ _ | .tbz _ _ _ _
  | .ret _ | .branchReg _ _ | .nop | .bti _ | .msrDit _ | .sysImm _ _
  | .trapOrSys
  | .simdShiftImm _ _ _ _ _ _ | .simdThreeSame _ _ _ _ _ _
  | .simdCmeqZero _ _ _ _ | .simdPerm _ _ _ _ _ _ => false

/-- Resolve an intra-function branch target PC from `pc` and signed byte
offset `offBytes`. Returns `none` if unaligned (`offBytes % 4 != 0`) or out
of range `[0, numInsns)`. -/
@[expose] def branchTargetPc? (pc numInsns : Nat) (offBytes : Int) :
    Option Nat :=
  let curBytes := Int.ofNat (pc * 4)
  let tgtBytes := Int.add curBytes offBytes
  match tgtBytes with
  | Int.negSucc _ => none
  | Int.ofNat b =>
    if !Nat.beq (Nat.mod b 4) 0 then none
    else
      let tgtPc := Nat.div b 4
      if Nat.blt tgtPc numInsns then some tgtPc else none

/-- Compute exact intra-function CFG successor PCs for instruction `i` at
index `pc` in a function of length `numInsns`. Returns `none` on any
out-of-bounds branch, fallthrough past end of function, call, indirect
branch (including non-`x30` `RET`), or trap/syscall. -/
@[expose] def insnSuccPcs? (pc numInsns : Nat) (i : DecodedInsn) :
    Option (List Nat) :=
  let nextPc? : Option Nat :=
    if Nat.blt (pc + 1) numInsns then some (pc + 1) else none
  match i with
  | .ret (.gpr .x30) => some []
  | .ret _ => none
  | .branch false off =>
    match branchTargetPc? pc numInsns off with
    | some t => some [t]
    | none => none
  | .branchCond _ off | .cbz _ _ _ off | .tbz _ _ _ off =>
    match branchTargetPc? pc numInsns off, nextPc? with
    | some t, some n => some [t, n]
    | _, _ => none
  | .branch true _ | .branchReg _ _ | .sysImm _ _ | .trapOrSys => none
  | .addSubImm _ _ _ _ _ _ _ _ | .logicImm _ _ _ _ _ _ _ _
  | .moveWide _ _ _ _ _ | .bitfield _ _ _ _ _ _ | .pcRelAddr _ _ _ _
  | .addSubShift _ _ _ _ _ _ _ _ | .addSubExt _ _ _ _ _ _ _ _ _
  | .logicShift _ _ _ _ _ _ _ | .condSel _ _ _ _ _ _
  | .maddSub _ _ _ _ _ _ | .div _ _ _ _ _ | .nop | .bti _ | .msrDit _
  | .gpLoadStore _ _ _ _ _ _ _ _ | .gpLoadStorePair _ _ _ _ _ _
  | .simdLoadStore _ _ _ _ _ _ | .simdLoadStorePair _ _ _ _ _ _
  | .simdLdSt1 _ _ _ _ _ _ _ | .simdShiftImm _ _ _ _ _ _
  | .simdThreeSame _ _ _ _ _ _ | .simdCmeqZero _ _ _ _
  | .simdPerm _ _ _ _ _ _ =>
    match nextPc? with
    | some n => some [n]
    | none => none

/-- Post-state abstract width environment after executing `i` in `env`
(assuming all reads of `i` were satisfied). Because every architectural
32-bit `W` write zero-extends `[63:32] := 0` and every valid 64-bit `X` write
consumes only defined inputs, every written GPR becomes `.full64`. -/
@[expose] def postWidthEnv (i : DecodedInsn) (env : WidthEnv) : WidthEnv :=
  widthEnvSetList env (insnGprWrites i) .full64

/-! ## 3. CFG Width-Safety Checker & Soundness Theorem -/

/-- Check whether every GPR read of instruction `i` is satisfied by `env`. -/
@[expose] def insnReadsWidthOk (env : WidthEnv) (i : DecodedInsn) : Bool :=
  listAll (fun p => RegWidthState.satisfies (env p.1) p.2) (insnGprReads i)

/-- Verify a candidate per-PC invariant table `invs` over `insns` starting
from AAPCS64 signature `sig`:
1. `invs.length == insns.length` and `0 < insns.length`;
2. `invs[0] ≤ initWidthEnv sig`;
3. At every `pc < insns.length`:
   - `insns[pc]` does not write `x30` (so `RET x30` cannot redirect control
     to an unanalyzed intra-function PC),
   - `insnReadsWidthOk invs[pc] insns[pc] = true`, and
   - every CFG successor `s ∈ insnSuccPcs? pc insns.length insns[pc]`
     satisfies `invs[s] ≤ postWidthEnv insns[pc] invs[pc]`. -/
@[expose] def checkCfgWidthInvs (sig : Aapcs64Sig) (insns : List DecodedInsn)
    (invs : List WidthEnv) : Bool :=
  let n := insns.length
  if Nat.beq n 0 || !Nat.beq invs.length n then false
  else
    match listGet? invs 0 with
    | none => false
    | some env0 =>
      if !widthEnvLe env0 (initWidthEnv sig) then false
      else
        let checkPc : Nat → Bool := fun pc =>
          match listGet? insns pc, listGet? invs pc with
          | some insn, some env =>
            if listAny (fun g => g.beq .x30) (insnGprWrites insn) then false
            else if !insnReadsWidthOk env insn then false
            else
              match insnSuccPcs? pc n insn with
              | none => false
              | some succs =>
                let post := postWidthEnv insn env
                listAll (fun s =>
                  match listGet? invs s with
                  | none => false
                  | some envS => widthEnvLe envS post) succs
          | _, _ => false
        @Nat.rec (fun _ => Nat → Bool)
          (fun _ => true)
          (fun _ ih pc => checkPc pc && ih (pc + 1))
          n 0

/-- Update element `idx` of a list via `@Nat.rec`. -/
@[expose] def listSet {α : Type} (xs : List α) (idx : Nat) (v : α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun ys =>
      match ys with
      | [] => []
      | _ :: rest => v :: rest)
    (fun _ ih ys =>
      match ys with
      | [] => []
      | y :: rest => y :: ih rest)
    idx xs

/-- Build a list of length `n` with `init0` at index `0` and `restVal` at all
indices `1..n-1`. -/
@[expose] def mkInitTableList {α : Type} (n : Nat) (init0 restVal : α) :
    List α :=
  match n with
  | 0 => []
  | k + 1 =>
    init0 ::
      @Nat.rec (fun _ => List α) [] (fun _ ih => restVal :: ih) k

/-- One Gauss-Seidel relaxation pass over materialized `WidthTable`s. -/
@[expose] def relaxWidthTablePass (insns : List DecodedInsn)
    (tbls : List WidthTable) : List WidthTable :=
  let n := insns.length
  @Nat.rec (fun _ => Nat → List WidthTable → List WidthTable)
    (fun _ cur => cur)
    (fun _ ih pc cur =>
      let cur' :=
        match listGet? insns pc, listGet? cur pc with
        | some insn, some t =>
          match insnSuccPcs? pc n insn with
          | none => cur
          | some succs =>
            let post := t.setList (insnGprWrites insn) .full64
            List.foldr
              (fun s tbl =>
                match listGet? tbl s with
                | none => tbl
                | some oldS => listSet tbl s (oldS.meet post))
              cur succs
        | _, _ => cur
      ih (pc + 1) cur')
    n 0 tbls

/-- Infer a candidate greatest-fixpoint CFG width invariant table using flat
`WidthTable` storage (zero closure nesting across relaxation rounds). Runs up
to 4 Gauss-Seidel forward passes (sufficient for straight-line code and common
single/2-deep loops); this affects only completeness, never soundness, and
callers with deeper nested loops may pass an explicit invariant table directly
to `checkCfgWidthInvs`. -/
@[expose] def inferCfgWidthInvs (sig : Aapcs64Sig)
    (insns : List DecodedInsn) : List WidthEnv :=
  let n := insns.length
  let initTbl :=
    mkInitTableList n (widthTableOfEnv (initWidthEnv sig)) widthTableTop
  let rounds := if Nat.blt n 4 then n + 2 else 4
  let finalTbls :=
    @Nat.rec (fun _ => List WidthTable → List WidthTable)
      (fun tbl => tbl)
      (fun _ ih tbl => ih (relaxWidthTablePass insns tbl))
      rounds initTbl
  finalTbls.map WidthTable.toEnv

/-- Automatic CFG-aware AAPCS64 upper-32-bit width-safety gate. -/
@[expose] def checkAapcs64WidthSafety (sig : Aapcs64Sig)
    (insns : List DecodedInsn) : Bool :=
  checkCfgWidthInvs sig insns (inferCfgWidthInvs sig insns)

/-! ### Operational Noninterference Semantics & Proof (`0` `Classical.choice`)
-/

/-- Architectural 64-bit general-purpose register file. -/
abbrev RegFile64 := Gpr → Nat

@[expose] def pow2_32 : Nat := 4294967296
@[expose] def pow2_64 : Nat := 18446744073709551616

/-- Two concrete register files agree on all bits promised defined by `env`:
- `.full64`: exact equality modulo `2^64` (all 64 bits agree);
- `.lo32Only`: equality modulo `2^32` (low 32 bits agree; upper `[63:32]`
  may hold arbitrary attacker-controlled garbage!);
- `.undef`: unconstrained. -/
@[expose] def WidthEnvAgree (env : WidthEnv) (rf1 rf2 : RegFile64) : Prop :=
  ∀ r : Gpr,
    match env r with
    | .full64   => Nat.mod (rf1 r) pow2_64 = Nat.mod (rf2 r) pow2_64
    | .lo32Only => Nat.mod (rf1 r) pow2_32 = Nat.mod (rf2 r) pow2_32
    | .undef    => True

/-- Two concrete register files agree on every GPR read performed by `insn`. -/
@[expose] def InsnReadsAgree (insn : DecodedInsn) (rf1 rf2 : RegFile64) :
    Prop :=
  ∀ p, List.Mem p (insnGprReads insn) →
    if p.2 then Nat.mod (rf1 p.1) pow2_64 = Nat.mod (rf2 p.1) pow2_64
    else Nat.mod (rf1 p.1) pow2_32 = Nat.mod (rf2 p.1) pow2_32

/-- Sound abstract step assumption on concrete execution: if all GPR reads of
`insn` agree between `rf1` and `rf2`, then after executing `insn` every
written register agrees on all 64 bits and every unwritten register is
preserved. -/
@[expose] def WidthSoundStep (insn : DecodedInsn)
    (rf1 rf2 rf1' rf2' : RegFile64) : Prop :=
  InsnReadsAgree insn rf1 rf2 →
    (∀ r : Gpr, List.Mem r (insnGprWrites insn) →
      Nat.mod (rf1' r) pow2_64 = Nat.mod (rf2' r) pow2_64) ∧
    (∀ r : Gpr, ¬(List.Mem r (insnGprWrites insn)) →
      rf1' r = rf1 r ∧ rf2' r = rf2 r)

/-- Self-contained `Nat.add_mod_right` over `Init.Data.Nat.Div.Basic`. -/
theorem nat_add_mul_mod_left (a b c : Nat) (hc : 0 < c) :
    Nat.mod (a + b * c) c = Nat.mod a c := by
  induction b with
  | zero =>
    rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
    have hStep : a + (k + 1) * c = (a + k * c) + c := by
      rw [Nat.succ_mul, Nat.add_assoc]
    rw [hStep]
    have hMod : Nat.mod (a + k * c + c) c =
        if 0 < c ∧ c ≤ a + k * c + c then Nat.mod (a + k * c + c - c) c
        else a + k * c + c :=
      Nat.mod_eq_ite (a + k * c + c) c
    rw [hMod]
    have hLe : c ≤ a + k * c + c := Nat.le_add_left c (a + k * c)
    simp only [hc, hLe, and_self, ite_true, Nat.add_sub_cancel]
    exact ih

/-- Helper: `if false = true then a else b` reduces definitionally to `b`. -/
theorem ite_false_eq_true_abi {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

/-- Helper: `(a % (m * m)) % m = a % m` for `0 < m`. -/
theorem nat_mod_sq_mod (a m : Nat) (hm : 0 < m) :
    Nat.mod (Nat.mod a (m * m)) m = Nat.mod a m := by
  have hDM := Nat.div_add_mod a (m * m)
  have hRewrite : a = Nat.mod a (m * m) + (m * Nat.div a (m * m)) * m := by
    rw [Nat.add_comm]
    have hMul : m * m * Nat.div a (m * m) = m * Nat.div a (m * m) * m := by
      rw [Nat.mul_assoc m m (Nat.div a (m * m)),
          Nat.mul_comm m (m * Nat.div a (m * m))]
    rw [← hMul]
    exact hDM.symm
  have hMod := nat_add_mul_mod_left (Nat.mod a (m * m))
    (m * Nat.div a (m * m)) m hm
  rw [← hRewrite] at hMod
  exact hMod.symm

/-- Helper: `2^32` divides `2^64`, so agreement mod `2^64` implies agreement
mod `2^32`. -/
theorem mod_pow2_64_implies_mod_pow2_32 {a b : Nat}
    (h : Nat.mod a pow2_64 = Nat.mod b pow2_64) :
    Nat.mod a pow2_32 = Nat.mod b pow2_32 := by
  have hPos : 0 < pow2_32 := Nat.zero_lt_succ 4294967295
  have hDiv : pow2_64 = pow2_32 * pow2_32 := rfl
  have ha := nat_mod_sq_mod a pow2_32 hPos
  have hb := nat_mod_sq_mod b pow2_32 hPos
  rw [hDiv] at h
  exact Eq.trans ha.symm (Eq.trans (congrArg (fun x => Nat.mod x pow2_32) h) hb)

/-- Reflection lemmas for `Gpr.beq`. -/
theorem gpr_beq_refl (r : Gpr) : r.beq r = true := by
  cases r <;> rfl

theorem gprOfNat_toNat (r : Gpr) : gprOfNat? r.toNat = some r := by
  cases r <;> rfl

theorem gpr_eq_of_beq {a b : Gpr} (h : a.beq b = true) : a = b := by
  have hNat : a.toNat = b.toNat := Nat.eq_of_beq_eq_true h
  have hOpt : some a = some b := by
    rw [← gprOfNat_toNat a, ← gprOfNat_toNat b, hNat]
  exact Option.some.inj hOpt

/-- Every `Gpr` belongs to `allGprs`. -/
theorem mem_allGprs (r : Gpr) : List.Mem r allGprs := by
  cases r <;>
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)

/-- `listAll p xs = true` implies `p x = true` for every `x` in `xs`. -/
theorem listAll_eq_true_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α), listAll p xs = true → ∀ x, List.Mem x xs → p x = true := by
  intro xs
  induction xs with
  | nil => intro _ _ hm; cases hm
  | cons hd tl ih =>
    intro h x hx
    change (p hd && listAll p tl) = true at h
    revert h
    cases hhd : p hd with
    | false => intro h; exact Bool.noConfusion h
    | true =>
      intro h
      cases hx with
      | head => exact hhd
      | tail _ hmem => exact ih h x hmem

/-- Helper: `listGet? xs idx = some v` implies `idx < xs.length`. -/
theorem listGet_some_lt {α : Type} :
    ∀ (idx : Nat) (xs : List α) (v : α),
      listGet? xs idx = some v → idx < xs.length := by
  intro idx
  induction idx with
  | zero =>
    intro xs v h
    cases xs with
    | nil => change none = some v at h; cases h
    | cons _ _ => exact Nat.zero_lt_succ _
  | succ k ih =>
    intro xs v h
    cases xs with
    | nil => change none = some v at h; cases h
    | cons _ tl =>
      have hk := ih tl v h
      exact Nat.succ_lt_succ hk

/-- Monotonicity of `WidthEnvAgree` under `widthEnvLe`. -/
theorem widthEnvAgree_mono {e1 e2 : WidthEnv} {rf1 rf2 : RegFile64}
    (hle : widthEnvLe e1 e2 = true) (hAg : WidthEnvAgree e2 rf1 rf2) :
    WidthEnvAgree e1 rf1 rf2 := by
  intro r
  have hr := listAll_eq_true_iff (fun g => RegWidthState.le (e1 g) (e2 g))
    allGprs hle r (mem_allGprs r)
  have h2 := hAg r
  cases h1 : e1 r <;> cases h2r : e2 r
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · rw [h1, h2r] at hr; exact Bool.noConfusion hr
  · rw [h2r] at h2; exact h2
  · rw [h2r] at h2; exact mod_pow2_64_implies_mod_pow2_32 h2
  · rw [h1, h2r] at hr; exact Bool.noConfusion hr
  · rw [h1, h2r] at hr; exact Bool.noConfusion hr
  · rw [h2r] at h2; exact h2

/-- If `env` agrees on `rf1, rf2` and `insnReadsWidthOk env insn = true`, then
every GPR read performed by `insn` agrees on all read bits. -/
theorem insnReadsWidthOk_sound {env : WidthEnv} {insn : DecodedInsn}
    {rf1 rf2 : RegFile64}
    (hOk : insnReadsWidthOk env insn = true)
    (hAg : WidthEnvAgree env rf1 rf2) :
    InsnReadsAgree insn rf1 rf2 := by
  intro p hp
  unfold insnReadsWidthOk at hOk
  have hSat := listAll_eq_true_iff
    (fun q => RegWidthState.satisfies (env q.1) q.2)
    (insnGprReads insn) hOk p hp
  have hReg := hAg p.1
  cases hp2 : p.2 with
  | true =>
    cases hEnv : env p.1 with
    | undef => rw [hEnv, hp2] at hSat; exact Bool.noConfusion hSat
    | lo32Only => rw [hEnv, hp2] at hSat; exact Bool.noConfusion hSat
    | full64 =>
      rw [hEnv] at hReg
      exact hReg
  | false =>
    cases hEnv : env p.1 with
    | undef => rw [hEnv, hp2] at hSat; exact Bool.noConfusion hSat
    | lo32Only =>
      rw [hEnv] at hReg
      exact hReg
    | full64 =>
      rw [hEnv] at hReg
      exact mod_pow2_64_implies_mod_pow2_32 hReg

/-- Helper: `widthEnvSetList` sets every `r` in `rs` to `st` and preserves
every `r` not in `rs`. -/
theorem widthEnvSetList_mem (env : WidthEnv) (rs : List Gpr)
    (st : RegWidthState) :
    (∀ r, List.Mem r rs → widthEnvSetList env rs st r = st) ∧
    (∀ r, ¬(List.Mem r rs) → widthEnvSetList env rs st r = env r) := by
  induction rs with
  | nil =>
    exact ⟨(fun _ h => by cases h), (fun _ _ => rfl)⟩
  | cons hd tl ih =>
    refine ⟨?_, ?_⟩
    · intro r hr
      change widthEnvSet (widthEnvSetList env tl st) hd st r = st
      unfold widthEnvSet
      cases hr with
      | head =>
        rw [gpr_beq_refl hd]
        rfl
      | tail _ hmem =>
        cases heq : r.beq hd with
        | true => rfl
        | false => exact ih.1 r hmem
    · intro r hnot
      change widthEnvSet (widthEnvSetList env tl st) hd st r = env r
      unfold widthEnvSet
      cases heq : r.beq hd with
      | true =>
        have hrEq : r = hd := gpr_eq_of_beq heq
        subst hrEq
        exact False.elim (hnot (List.Mem.head tl))
      | false =>
        have hNotTl : ¬(List.Mem r tl) := fun hm => hnot (List.Mem.tail hd hm)
        exact ih.2 r hNotTl

/-- Single-step preservation of `WidthEnvAgree` across `postWidthEnv`. -/
theorem postWidthEnv_preserves_agree {env : WidthEnv} {insn : DecodedInsn}
    {rf1 rf2 rf1' rf2' : RegFile64}
    (hOk : insnReadsWidthOk env insn = true)
    (hAg : WidthEnvAgree env rf1 rf2)
    (hStep : WidthSoundStep insn rf1 rf2 rf1' rf2') :
    WidthEnvAgree (postWidthEnv insn env) rf1' rf2' := by
  have hReads := insnReadsWidthOk_sound hOk hAg
  have hPost := hStep hReads
  intro r
  unfold postWidthEnv
  cases hMem : listAny (fun w => w.beq r) (insnGprWrites insn) with
  | true =>
    have hIn : List.Mem r (insnGprWrites insn) := by
      have aux : ∀ (ws : List Gpr),
          listAny (fun w => w.beq r) ws = true → List.Mem r ws := by
        intro ws
        induction ws with
        | nil => intro hf; exact Bool.noConfusion hf
        | cons hd tl ih =>
          intro h1
          change (hd.beq r || listAny (fun w => w.beq r) tl) = true at h1
          revert h1
          cases heq : hd.beq r with
          | true =>
            intro h1; have hrEq : hd = r := gpr_eq_of_beq heq
            subst hrEq
            exact List.Mem.head tl
          | false =>
            intro h1
            exact List.Mem.tail hd (ih h1)
      exact aux (insnGprWrites insn) hMem
    have hSet := (widthEnvSetList_mem env (insnGprWrites insn) .full64).1 r hIn
    rw [hSet]
    exact hPost.1 r hIn
  | false =>
    have hNotIn : ¬(List.Mem r (insnGprWrites insn)) := by
      intro hin
      have aux : ∀ (ws : List Gpr),
          List.Mem r ws → listAny (fun w => w.beq r) ws = true := by
        intro ws h
        induction h with
        | head =>
          change (r.beq r || listAny (fun (w : Gpr) => w.beq r) _) = true
          rw [gpr_beq_refl r]
          rfl
        | tail hd _ ih =>
          change (hd.beq r || listAny (fun (w : Gpr) => w.beq r) _) = true
          rw [ih]
          cases hd.beq r <;> rfl
      have ht := aux (insnGprWrites insn) hin
      rw [ht] at hMem
      exact Bool.noConfusion hMem
    have hKeep := (widthEnvSetList_mem env (insnGprWrites insn) .full64).2 r
      hNotIn
    rw [hKeep]
    have hEqs := hPost.2 r hNotIn
    rw [hEqs.1, hEqs.2]
    exact hAg r

/-- Helper: extract per-PC check from the `@Nat.rec` loop in
`checkCfgWidthInvs`. -/
theorem natRec_checkLoop_mem (checkPc : Nat → Bool) :
    ∀ (cnt start pc : Nat),
      @Nat.rec (fun _ => Nat → Bool)
        (fun _ => true)
        (fun _ ih p => checkPc p && ih (p + 1))
        cnt start = true →
      start ≤ pc → pc < start + cnt →
      checkPc pc = true := by
  intro cnt
  induction cnt with
  | zero =>
    intro start pc _ hle hlt
    exact False.elim (Nat.not_lt_of_ge hle hlt)
  | succ k ih =>
    intro start pc h hle hlt
    change (checkPc start &&
      @Nat.rec (fun _ => Nat → Bool)
        (fun _ => true)
        (fun _ ih p => checkPc p && ih (p + 1))
        k (start + 1)) = true at h
    revert h
    cases hc : checkPc start with
    | false => intro h; exact Bool.noConfusion h
    | true =>
      intro h
      cases Nat.eq_or_lt_of_le hle with
      | inl heq => subst heq; exact hc
      | inr hgt =>
        have hle' : start + 1 ≤ pc := hgt
        have hlt' : pc < (start + 1) + k := by
          rw [Nat.add_right_comm start 1 k]
          exact hlt
        exact ih (start + 1) pc h hle' hlt'

/-- Concrete CFG execution trace witness over `insns` starting from any pair
of AAPCS64-equivalent entry register files under `sig`. -/
inductive CfgWidthTrace (sig : Aapcs64Sig) (insns : List DecodedInsn) :
    Nat → RegFile64 → RegFile64 → Prop where
  | entry (rf1 rf2 : RegFile64) :
      WidthEnvAgree (initWidthEnv sig) rf1 rf2 →
      CfgWidthTrace sig insns 0 rf1 rf2
  | step {pc succPc : Nat} {insn : DecodedInsn} {succs : List Nat}
      {rf1 rf2 rf1' rf2' : RegFile64} :
      CfgWidthTrace sig insns pc rf1 rf2 →
      listGet? insns pc = some insn →
      insnSuccPcs? pc insns.length insn = some succs →
      List.Mem succPc succs →
      WidthSoundStep insn rf1 rf2 rf1' rf2' →
      CfgWidthTrace sig insns succPc rf1' rf2'

/-- **AAPCS64 Upper-32-Bit Noninterference Soundness Theorem (relative to
`WidthSoundStep`):**
If `checkCfgWidthInvs sig insns invs = true`, then along EVERY reachable CFG
trace whose steps satisfy `WidthSoundStep`, starting from any two
AAPCS64-equivalent entry register files (whose `.narrow32` parameters may
carry arbitrary attacker-controlled garbage in bits `[63:32]`):
1. `invs[pc]` holds (`WidthEnvAgree`), AND
2. the instruction at `pc` reads ONLY architecturally defined GPR bits
   (`InsnReadsAgree`).
Note: `NZCV` flags and memory state are outside `WidthSoundStep` and are
discharged by a separate operational semantics layer. -/
theorem checkCfgWidthInvs_sound (sig : Aapcs64Sig) (insns : List DecodedInsn)
    (invs : List WidthEnv)
    (hCheck : checkCfgWidthInvs sig insns invs = true) :
    ∀ {pc : Nat} {rf1 rf2 : RegFile64},
      CfgWidthTrace sig insns pc rf1 rf2 →
      ∃ env insn,
        listGet? invs pc = some env ∧
        listGet? insns pc = some insn ∧
        WidthEnvAgree env rf1 rf2 ∧
        InsnReadsAgree insn rf1 rf2 := by
  unfold checkCfgWidthInvs at hCheck
  dsimp only at hCheck
  revert hCheck
  cases hLenZero : Nat.beq insns.length 0 with
  | true =>
    intro hCheck
    simp only [Bool.true_or, ite_true] at hCheck
    exact Bool.noConfusion hCheck
  | false =>
    intro hCheck
    revert hCheck
    cases hLenEq : Nat.beq invs.length insns.length with
    | false =>
      intro hCheck
      simp only [Bool.not_false, Bool.false_or, ite_true] at hCheck
      exact Bool.noConfusion hCheck
    | true =>
      intro hCheck
      simp only [Bool.not_true, Bool.false_or, ite_false_eq_true_abi] at hCheck
      have hLenPos : 0 < insns.length := by
        revert hLenZero
        cases hN : insns.length with
        | zero => intro hLenZero; exact Bool.noConfusion hLenZero
        | succ m => intro hLenZero; exact Nat.zero_lt_succ m
      have hLenSame : invs.length = insns.length := Nat.eq_of_beq_eq_true hLenEq
      revert hCheck
      cases hEnv0 : listGet? invs 0 with
      | none =>
        intro hCheck
        dsimp only at hCheck
        exact Bool.noConfusion hCheck
      | some env0 =>
        intro hCheck
        dsimp only at hCheck
        revert hCheck
        cases hLe0 : widthEnvLe env0 (initWidthEnv sig) with
        | false =>
          intro hCheck
          simp only [Bool.not_false, ite_true] at hCheck
          exact Bool.noConfusion hCheck
        | true =>
          intro hCheck
          simp only [Bool.not_true, ite_false_eq_true_abi] at hCheck
          have hLoop : ∀ pc, pc < insns.length →
              (match listGet? insns pc, listGet? invs pc with
               | some insn, some env =>
                 if listAny (fun g => g.beq .x30) (insnGprWrites insn) then
                   false
                 else if !insnReadsWidthOk env insn then false
                 else
                   match insnSuccPcs? pc insns.length insn with
                   | none => false
                   | some succs =>
                     let post := postWidthEnv insn env
                     listAll (fun s =>
                       match listGet? invs s with
                       | none => false
                       | some envS => widthEnvLe envS post) succs
               | _, _ => false) = true := by
            intro pc hlt
            exact natRec_checkLoop_mem _ insns.length 0 pc hCheck
              (Nat.zero_le pc) (by rw [Nat.zero_add]; exact hlt)
          have hPcProps : ∀ pc, pc < insns.length →
              ∃ insn env succs,
                listGet? insns pc = some insn ∧
                listGet? invs pc = some env ∧
                insnReadsWidthOk env insn = true ∧
                insnSuccPcs? pc insns.length insn = some succs ∧
                (∀ s, List.Mem s succs → ∃ envS,
                  listGet? invs s = some envS ∧
                  widthEnvLe envS (postWidthEnv insn env) = true) := by
            intro pc hlt
            have hp := hLoop pc hlt
            revert hp
            cases hi : listGet? insns pc with
            | none => intro hp; dsimp only at hp; exact Bool.noConfusion hp
            | some insn =>
              intro hp
              revert hp
              cases hv : listGet? invs pc with
              | none =>
                intro hp; dsimp only at hp; exact Bool.noConfusion hp
              | some env =>
                intro hp
                dsimp only at hp
                cases hx30 :
                    listAny (fun g => g.beq .x30) (insnGprWrites insn) with
                | true =>
                  rw [hx30] at hp
                  simp only [ite_true] at hp
                  exact Bool.noConfusion hp
                | false =>
                  rw [hx30] at hp
                  simp only [ite_false_eq_true_abi] at hp
                  revert hp
                  cases hr : insnReadsWidthOk env insn with
                  | false =>
                    intro hp
                    simp only [Bool.not_false, ite_true] at hp
                    exact Bool.noConfusion hp
                  | true =>
                    intro hp
                    simp only [Bool.not_true, ite_false_eq_true_abi] at hp
                    revert hp
                    cases hs : insnSuccPcs? pc insns.length insn with
                    | none =>
                      intro hp; dsimp only at hp
                      exact Bool.noConfusion hp
                    | some succs =>
                      intro hp
                      dsimp only at hp
                      refine ⟨insn, env, succs, rfl, rfl, hr, hs, ?_⟩
                      intro s hsm
                      have hall := listAll_eq_true_iff _ succs hp s hsm
                      revert hall
                      cases hvs : listGet? invs s with
                      | none =>
                        intro hall
                        dsimp only at hall
                        exact Bool.noConfusion hall
                      | some envS =>
                        intro hall
                        dsimp only at hall
                        exact ⟨envS, rfl, hall⟩
          intro pc rf1 rf2 hTr
          induction hTr with
          | entry rf1 rf2 hEntry =>
            cases hPcProps 0 hLenPos with
            | intro insn0 h1 =>
              cases h1 with
              | intro env0' h2 =>
                cases h2 with
                | intro _ h3 =>
                  have hi0 := h3.1
                  have hv0 := h3.2.1
                  have hr0 := h3.2.2.1
                  have hEnvEq : env0 = env0' :=
                    Option.some.inj (Eq.trans hEnv0.symm hv0)
                  subst hEnvEq
                  have hAg0 : WidthEnvAgree env0 rf1 rf2 :=
                    widthEnvAgree_mono hLe0 hEntry
                  exact ⟨env0, insn0, hv0, hi0, hAg0,
                         insnReadsWidthOk_sound hr0 hAg0⟩
          | step hPrev hGetI hSucc hMemS hStep ih =>
            cases ih with
            | intro envP h1 =>
              cases h1 with
              | intro insnP h2 =>
                have hvP := h2.1
                have hiP := h2.2.1
                have hAgP := h2.2.2.1
                have hInsnEq : insnP = _ :=
                  Option.some.inj (Eq.trans hiP.symm hGetI)
                subst hInsnEq
                have hPcLt := listGet_some_lt _ insns _ hiP
                cases hPcProps _ hPcLt with
                | intro insnP' h3 =>
                  cases h3 with
                  | intro envP' h4 =>
                    cases h4 with
                    | intro succs' h5 =>
                      have hiP' := h5.1
                      have hvP' := h5.2.1
                      have hrP' := h5.2.2.1
                      have hSucc' := h5.2.2.2.1
                      have hEdges := h5.2.2.2.2
                      have hIEq2 : insnP = insnP' :=
                        Option.some.inj (Eq.trans hiP.symm hiP')
                      subst hIEq2
                      have hVEq2 : envP = envP' :=
                        Option.some.inj (Eq.trans hvP.symm hvP')
                      subst hVEq2
                      have hSEq : _ = succs' :=
                        Option.some.inj (Eq.trans hSucc.symm hSucc')
                      subst hSEq
                      cases hEdges _ hMemS with
                      | intro envS h6 =>
                        have hvS := h6.1
                        have hLeS := h6.2
                        have hPostAg :
                            WidthEnvAgree (postWidthEnv insnP envP) _ _ :=
                          postWidthEnv_preserves_agree hrP' hAgP hStep
                        have hSuccAg : WidthEnvAgree envS _ _ :=
                          widthEnvAgree_mono hLeS hPostAg
                        have hltInvs := listGet_some_lt _ invs _ hvS
                        rw [hLenSame] at hltInvs
                        cases hPcProps _ hltInvs with
                        | intro insnS h7 =>
                          cases h7 with
                          | intro envS' h8 =>
                            cases h8 with
                            | intro _ h9 =>
                              have hiS := h9.1
                              have hvS' := h9.2.1
                              have hrS' := h9.2.2.1
                              have hVSEq : envS = envS' :=
                                Option.some.inj (Eq.trans hvS.symm hvS')
                              subst hVSEq
                              exact ⟨envS, insnS, hvS, hiS, hSuccAg,
                                     insnReadsWidthOk_sound hrS' hSuccAg⟩

/-- Corollary: `checkAapcs64WidthSafety sig insns = true` guarantees
upper-32-bit noninterference along every reachable CFG trace. -/
theorem checkAapcs64WidthSafety_sound (sig : Aapcs64Sig)
    (insns : List DecodedInsn)
    (h : checkAapcs64WidthSafety sig insns = true) :
    ∀ {pc : Nat} {rf1 rf2 : RegFile64},
      CfgWidthTrace sig insns pc rf1 rf2 →
      ∃ env insn,
        listGet? (inferCfgWidthInvs sig insns) pc = some env ∧
        listGet? insns pc = some insn ∧
        WidthEnvAgree env rf1 rf2 ∧
        InsnReadsAgree insn rf1 rf2 :=
  checkCfgWidthInvs_sound sig insns (inferCfgWidthInvs sig insns) h

/-! ## 4. Two-Tier AAPCS64 Leaf/Loop ABI & SFI Confinement Gate -/

/-- Return the store base register if `i` performs a memory store, else `none`.
-/
@[expose] def insnStoreBase? (i : DecodedInsn) : Option RegOrSp :=
  match i with
  | .gpLoadStore false _ _ _ _ rn _ _ => some rn
  | .gpLoadStorePair false _ _ _ rn _ => some rn
  | .simdLoadStore false _ _ rn _ _ => some rn
  | .simdLoadStorePair false _ _ _ rn _ => some rn
  | .simdLdSt1 false _ _ _ _ rn _ => some rn
  | _ => none

/-- True iff `i` performs a store with writeback / post-index update. -/
@[expose] def insnStoreHasWriteback (i : DecodedInsn) : Bool :=
  match i with
  | .gpLoadStore false _ _ _ _ _ (.unsignedOff _) _ => false
  | .gpLoadStore false _ _ _ _ _ _ _ => true
  | .gpLoadStorePair false _ _ _ _ (.signedOff _) => false
  | .gpLoadStorePair false _ _ _ _ _ => true
  | .simdLoadStore false _ _ _ (.unsignedOff _) _ => false
  | .simdLoadStore false _ _ _ _ _ => true
  | .simdLoadStorePair false _ _ _ _ (.signedOff _) => false
  | .simdLoadStorePair false _ _ _ _ _ => true
  | .simdLdSt1 false _ _ _ _ _ .none => false
  | .simdLdSt1 false _ _ _ _ _ _ => true
  | _ => false

/-- True iff `i` is a monotone non-negative immediate update of `r` (either
immediate post-index load/store on `r` with `imm >= 0` and no aliasing GP load
`rt == r`, or `add xR, xR, #imm`). -/
@[expose] def insnMonotoneAdvanceOf (r : Gpr) (i : DecodedInsn) : Bool :=
  match i with
  | .simdLdSt1 _ _ _ _ _ (.gpr base) (.imm _) => base.beq r
  | .gpLoadStore isLoad _ _ _ rt (.gpr base) (.postIndex (Int.ofNat _)) _ =>
    base.beq r && (!isLoad || !rt.beq (.gpr base))
  | .simdLoadStore _ _ _ (.gpr base) (.postIndex (Int.ofNat _)) _ =>
    base.beq r
  | .addSubImm .x64 false _ (.gpr rd) false (.gpr rn) _ none =>
    rd.beq r && rn.beq r
  | _ => false

/-- True iff `i` is forbidden in a leaf/loop SFI kernel (`BL`, `BR`, `BLR`,
`SVC`/`HVC`/`SMC`/`BRK`/`HLT`, or non-`x30` `RET`). -/
@[expose] def insnIsForbiddenLeafControl (i : DecodedInsn) : Bool :=
  match i with
  | .branch true _ => true
  | .branchReg _ _ => true
  | .sysImm _ _ => true
  | .trapOrSys => true
  | .ret rn => !rn.beq (.gpr .x30)
  | _ => false

/-- True iff `r` is in `rs`. -/
@[expose] def gprInList (rs : List Gpr) (r : Gpr) : Bool :=
  listAny (fun x => x.beq r) rs

/-- True iff `i` preserves all AAPCS64 callee-saved GPRs (`x19..x30`),
platform register `x18`, callee-saved SIMD registers (`v8..v15`), and `SP`,
and executes no forbidden control/trap instruction. -/
@[expose] def insnLeafAbiBaseOk (i : DecodedInsn) : Bool :=
  !insnIsForbiddenLeafControl i &&
  !insnTouchesSp i &&
  !listAny (fun r => r.isCalleeSaved || r.isPlatformReg) (insnGprWrites i) &&
  !listAny VReg.isCalleeSavedLo64 (insnVRegWrites i)

/-- True iff every instruction at `pc < insns.length` has valid in-bounds
4-byte-aligned CFG successors via `insnSuccPcs?` and does not write `x30`
(preventing indirect intra-function `RET x30` redirection). -/
@[expose] def allIntraFuncBranchesValid (insns : List DecodedInsn) : Bool :=
  let n := insns.length
  @Nat.rec (fun _ => Nat → Bool)
    (fun _ => true)
    (fun _ ih pc =>
      let ok :=
        match listGet? insns pc with
        | none => false
        | some i =>
          (insnSuccPcs? pc n i).isSome &&
          !listAny (fun g => g.beq .x30) (insnGprWrites i)
      ok && ih (pc + 1))
    n 0

/-- True iff any store displacement in `i` is non-negative (`>= 0`), rejecting
negative signed pair/pre/post-index store offsets that could underflow below a
buffer base. -/
@[expose] def insnStoreDispNonNeg (i : DecodedInsn) : Bool :=
  match i with
  | .gpLoadStore false _ _ _ _ _ (.postIndex (Int.negSucc _)) _ => false
  | .gpLoadStore false _ _ _ _ _ (.preIndex (Int.negSucc _)) _ => false
  | .gpLoadStorePair false _ _ _ _ (.signedOff (Int.negSucc _)) => false
  | .gpLoadStorePair false _ _ _ _ (.postIndex (Int.negSucc _)) => false
  | .gpLoadStorePair false _ _ _ _ (.preIndex (Int.negSucc _)) => false
  | .simdLoadStore false _ _ _ (.postIndex (Int.negSucc _)) _ => false
  | .simdLoadStore false _ _ _ (.preIndex (Int.negSucc _)) _ => false
  | .simdLoadStorePair false _ _ _ _ (.signedOff (Int.negSucc _)) => false
  | .simdLoadStorePair false _ _ _ _ (.postIndex (Int.negSucc _)) => false
  | .simdLoadStorePair false _ _ _ _ (.preIndex (Int.negSucc _)) => false
  | _ => true

/-- Tier 1 (Fixed Entry Bases — syntactic register discipline & non-negative
store offsets): every instruction satisfies `insnLeafAbiBaseOk`, all
intra-function branches stay in bounds, the final instruction is `RET x30`,
every store targets an unmodified `allowedStoreBases` register with
non-negative displacement and no writeback, and no instruction modifies any
register in `allowedStoreBases`. Upper buffer bounds on positive displacements
must be established by the caller (not proven here). -/
@[expose] def checkAArch64LeafAbiFixedBases (allowedStoreBases : List Gpr)
    (insns : List DecodedInsn) : Bool :=
  match listGetLast? insns with
  | some (.ret (.gpr .x30)) =>
    allIntraFuncBranchesValid insns &&
    listAll (fun i =>
      insnLeafAbiBaseOk i &&
      !listAny (gprInList allowedStoreBases) (insnGprWrites i) &&
      match insnStoreBase? i with
      | none => true
      | some .sp => false
      | some (.gpr b) =>
        gprInList allowedStoreBases b && !insnStoreHasWriteback i &&
        insnStoreDispNonNeg i)
      insns
  | _ => false

/-- Tier 2 (Monotone Post-Index / Strided Bases — syntactic register
discipline & non-negative store offsets): every instruction satisfies
`insnLeafAbiBaseOk`, all intra-function branches stay in bounds, the final
instruction is `RET x30`, every store targets a base in `allowedStoreBases`
with non-negative displacement, and any write to a register `b` in
`allowedStoreBases` is syntactically a non-negative immediate advance
(`insnMonotoneAdvanceOf b i`). Upper buffer bounds and 64-bit pointer
wraparound freedom must be established by the caller (not proven here). -/
@[expose] def checkAArch64LeafAbiMonotoneBases (allowedStoreBases : List Gpr)
    (insns : List DecodedInsn) : Bool :=
  match listGetLast? insns with
  | some (.ret (.gpr .x30)) =>
    allIntraFuncBranchesValid insns &&
    listAll (fun i =>
      insnLeafAbiBaseOk i &&
      listAll (fun w =>
        if gprInList allowedStoreBases w then insnMonotoneAdvanceOf w i
        else true) (insnGprWrites i) &&
      match insnStoreBase? i with
      | none => true
      | some .sp => false
      | some (.gpr b) =>
        gprInList allowedStoreBases b && insnStoreDispNonNeg i)
      insns
  | _ => false

/-- Certificate structure for Tier 1 fixed-base AAPCS64 leaf register
discipline and non-negative store offsets. -/
structure AArch64LeafAbiFixedBasesCert (allowedStoreBases : List Gpr)
    (insns : List DecodedInsn) : Prop where
  endsWithRetX30 : listGetLast? insns = some (.ret (.gpr .x30))
  branchesInBounds : allIntraFuncBranchesValid insns = true
  allInsnSafe : ∀ i, List.Mem i insns →
    insnLeafAbiBaseOk i = true ∧
    (∀ w, List.Mem w (insnGprWrites i) →
      gprInList allowedStoreBases w = false) ∧
    (∀ b, insnStoreBase? i = some b →
      ∃ r, b = .gpr r ∧ gprInList allowedStoreBases r = true ∧
           insnStoreHasWriteback i = false ∧
           insnStoreDispNonNeg i = true)

/-- Certificate structure for Tier 2 monotone-base AAPCS64 leaf/loop register
discipline and non-negative store offsets. -/
structure AArch64LeafAbiMonotoneBasesCert (allowedStoreBases : List Gpr)
    (insns : List DecodedInsn) : Prop where
  endsWithRetX30 : listGetLast? insns = some (.ret (.gpr .x30))
  branchesInBounds : allIntraFuncBranchesValid insns = true
  allInsnSafe : ∀ i, List.Mem i insns →
    insnLeafAbiBaseOk i = true ∧
    (∀ w, List.Mem w (insnGprWrites i) →
      gprInList allowedStoreBases w = true →
      insnMonotoneAdvanceOf w i = true) ∧
    (∀ b, insnStoreBase? i = some b →
      ∃ r, b = .gpr r ∧ gprInList allowedStoreBases r = true ∧
           insnStoreDispNonNeg i = true)

/-- Helper: `!listAny p xs = true` implies `p x = false` for all `x` in `xs`.
-/
theorem not_listAny_eq_true_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (!listAny p xs) = true →
      ∀ x, List.Mem x xs → p x = false := by
  intro xs
  induction xs with
  | nil => intro _ _ hm; cases hm
  | cons hd tl ih =>
    intro h x hx
    change (!(p hd || listAny p tl)) = true at h
    revert h
    cases hhd : p hd with
    | true => intro h; exact Bool.noConfusion h
    | false =>
      intro h
      cases hx with
      | head => exact hhd
      | tail _ hmem => exact ih h x hmem

/-- Soundness of Tier 1 fixed-base AAPCS64 leaf ABI/SFI checker. -/
theorem checkAArch64LeafAbiFixedBases_sound (allowedStoreBases : List Gpr)
    (insns : List DecodedInsn)
    (h : checkAArch64LeafAbiFixedBases allowedStoreBases insns = true) :
    AArch64LeafAbiFixedBasesCert allowedStoreBases insns := by
  unfold checkAArch64LeafAbiFixedBases at h
  revert h
  cases hLast : listGetLast? insns with
  | none => intro h; exact Bool.noConfusion h
  | some lastI =>
    intro h
    cases lastI with
    | ret rn =>
      cases rn with
      | zr => exact Bool.noConfusion h
      | gpr r =>
        cases r with
        | x30 =>
          revert h
          cases hBr : allIntraFuncBranchesValid insns with
          | false => intro h; exact Bool.noConfusion h
          | true =>
            intro h
            simp only [Bool.true_and] at h
            refine ⟨hLast, hBr, ?_⟩
            intro i hi
            have hall := listAll_eq_true_iff _ insns h i hi
            revert hall
            cases hBase : insnLeafAbiBaseOk i with
            | false =>
              intro hall
              simp only [Bool.false_and] at hall
              exact Bool.noConfusion hall
            | true =>
              intro hall
              simp only [Bool.true_and] at hall
              revert hall
              cases hNoWr : (!listAny (gprInList allowedStoreBases)
                  (insnGprWrites i)) with
              | false =>
                intro hall
                simp only [Bool.false_and] at hall
                exact Bool.noConfusion hall
              | true =>
                intro hall
                simp only [Bool.true_and] at hall
                refine ⟨rfl,
                  not_listAny_eq_true_iff _ _ hNoWr, ?_⟩
                intro b hb
                rw [hb] at hall
                cases b with
                | sp => exact Bool.noConfusion hall
                | gpr rg =>
                  dsimp only at hall
                  revert hall
                  cases hIn : gprInList allowedStoreBases rg with
                  | false =>
                    intro hall
                    simp only [Bool.false_and] at hall
                    exact Bool.noConfusion hall
                  | true =>
                    intro hall
                    simp only [Bool.true_and] at hall
                    revert hall
                    cases hWb : insnStoreHasWriteback i with
                    | true =>
                      intro hall
                      simp only [Bool.not_true, Bool.false_and] at hall
                      exact Bool.noConfusion hall
                    | false =>
                      intro hall
                      simp only [Bool.not_false, Bool.true_and] at hall
                      exact ⟨rg, rfl, hIn, rfl, hall⟩
        | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12
        | x13 | x14 | x15 | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
        | x24 | x25 | x26 | x27 | x28 | x29 => exact Bool.noConfusion h
    | addSubImm _ _ _ _ _ _ _ _ | logicImm _ _ _ _ _ _ _ _
    | moveWide _ _ _ _ _ | bitfield _ _ _ _ _ _ | pcRelAddr _ _ _ _
    | addSubShift _ _ _ _ _ _ _ _ | addSubExt _ _ _ _ _ _ _ _ _
    | logicShift _ _ _ _ _ _ _ | condSel _ _ _ _ _ _
    | maddSub _ _ _ _ _ _ | div _ _ _ _ _ | branch _ _ | branchCond _ _
    | cbz _ _ _ _ | tbz _ _ _ _ | branchReg _ _
    | nop | bti _ | msrDit _ | sysImm _ _ | trapOrSys
    | gpLoadStore _ _ _ _ _ _ _ _
    | gpLoadStorePair _ _ _ _ _ _ | simdLoadStore _ _ _ _ _ _
    | simdLoadStorePair _ _ _ _ _ _ | simdLdSt1 _ _ _ _ _ _ _
    | simdShiftImm _ _ _ _ _ _ | simdThreeSame _ _ _ _ _ _
    | simdCmeqZero _ _ _ _ | simdPerm _ _ _ _ _ _ =>
      exact Bool.noConfusion h

/-- Soundness of Tier 2 monotone-base AAPCS64 leaf/loop ABI/SFI checker. -/
theorem checkAArch64LeafAbiMonotoneBases_sound (allowedStoreBases : List Gpr)
    (insns : List DecodedInsn)
    (h : checkAArch64LeafAbiMonotoneBases allowedStoreBases insns = true) :
    AArch64LeafAbiMonotoneBasesCert allowedStoreBases insns := by
  unfold checkAArch64LeafAbiMonotoneBases at h
  revert h
  cases hLast : listGetLast? insns with
  | none => intro h; exact Bool.noConfusion h
  | some lastI =>
    intro h
    cases lastI with
    | ret rn =>
      cases rn with
      | zr => exact Bool.noConfusion h
      | gpr r =>
        cases r with
        | x30 =>
          revert h
          cases hBr : allIntraFuncBranchesValid insns with
          | false => intro h; exact Bool.noConfusion h
          | true =>
            intro h
            simp only [Bool.true_and] at h
            refine ⟨hLast, hBr, ?_⟩
            intro i hi
            have hall := listAll_eq_true_iff _ insns h i hi
            revert hall
            cases hBase : insnLeafAbiBaseOk i with
            | false =>
              intro hall
              simp only [Bool.false_and] at hall
              exact Bool.noConfusion hall
            | true =>
              intro hall
              simp only [Bool.true_and] at hall
              revert hall
              cases hMono : listAll (fun w =>
                  if gprInList allowedStoreBases w then
                    insnMonotoneAdvanceOf w i
                  else true) (insnGprWrites i) with
              | false =>
                intro hall
                simp only [Bool.false_and] at hall
                exact Bool.noConfusion hall
              | true =>
                intro hall
                simp only [Bool.true_and] at hall
                refine ⟨rfl, ?_, ?_⟩
                · intro w hw hIn
                  have hmw := listAll_eq_true_iff _ (insnGprWrites i)
                    hMono w hw
                  rw [hIn] at hmw
                  simp only [ite_true] at hmw
                  exact hmw
                · intro b hb
                  rw [hb] at hall
                  cases b with
                  | sp => exact Bool.noConfusion hall
                  | gpr rg =>
                    dsimp only at hall
                    revert hall
                    cases hIn : gprInList allowedStoreBases rg with
                    | false =>
                      intro hall
                      simp only [Bool.false_and] at hall
                      exact Bool.noConfusion hall
                    | true =>
                      intro hall
                      simp only [Bool.true_and] at hall
                      exact ⟨rg, rfl, hIn, hall⟩
        | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12
        | x13 | x14 | x15 | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
        | x24 | x25 | x26 | x27 | x28 | x29 => exact Bool.noConfusion h
    | addSubImm _ _ _ _ _ _ _ _ | logicImm _ _ _ _ _ _ _ _
    | moveWide _ _ _ _ _ | bitfield _ _ _ _ _ _ | pcRelAddr _ _ _ _
    | addSubShift _ _ _ _ _ _ _ _ | addSubExt _ _ _ _ _ _ _ _ _
    | logicShift _ _ _ _ _ _ _ | condSel _ _ _ _ _ _
    | maddSub _ _ _ _ _ _ | div _ _ _ _ _ | branch _ _ | branchCond _ _
    | cbz _ _ _ _ | tbz _ _ _ _ | branchReg _ _
    | nop | bti _ | msrDit _ | sysImm _ _ | trapOrSys
    | gpLoadStore _ _ _ _ _ _ _ _
    | gpLoadStorePair _ _ _ _ _ _ | simdLoadStore _ _ _ _ _ _
    | simdLoadStorePair _ _ _ _ _ _ | simdLdSt1 _ _ _ _ _ _ _
    | simdShiftImm _ _ _ _ _ _ | simdThreeSame _ _ _ _ _ _
    | simdCmeqZero _ _ _ _ | simdPerm _ _ _ _ _ _ =>
      exact Bool.noConfusion h

/-! ## 5. SIMD Stride, Alignment & Vector-Chunk Bounds Gates -/

/-- Round `w` up to the next multiple of `chunk` (`FFALIGN(w, chunk)` in
unsigned `Nat` arithmetic). -/
@[expose] def alignUp (w chunk : Nat) : Nat :=
  if Nat.beq chunk 0 then w
  else Nat.div (w + (chunk - 1)) chunk * chunk

/-- Self-contained `(q * c) % c = 0` for `0 < c`. -/
theorem nat_mul_mod_left_pos (q c : Nat) (hc : 0 < c) :
    Nat.mod (q * c) c = 0 := by
  have h := nat_add_mul_mod_left 0 q c hc
  rw [Nat.zero_add] at h
  rw [h]
  exact Nat.zero_mod c

/-- `alignUp w chunk` is always a multiple of `chunk` when `chunk > 0`. -/
theorem alignUp_mod_eq_zero (w chunk : Nat) (hc : 0 < chunk) :
    Nat.mod (alignUp w chunk) chunk = 0 := by
  unfold alignUp
  have hNe : Nat.beq chunk 0 = false := by
    cases chunk with
    | zero => exact False.elim (Nat.lt_irrefl 0 hc)
    | succ _ => rfl
  rw [hNe]
  exact nat_mul_mod_left_pos _ chunk hc

/-- Self-contained `a < b → a ≤ b - 1`. -/
theorem nat_le_sub_one_of_lt {a b : Nat} (h : a < b) : a ≤ b - 1 := by
  cases b with
  | zero => exact False.elim (Nat.not_lt_zero a h)
  | succ m => exact Nat.le_of_succ_le_succ h

/-- Self-contained `a * c < b * c → a < b`. -/
theorem nat_lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) :
    a < b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge =>
    have hMul := Nat.mul_le_mul_right c hge
    exact False.elim (Nat.not_lt_of_ge hMul h)

/-- `w ≤ alignUp w chunk` for every `chunk > 0`. -/
theorem le_alignUp (w chunk : Nat) (hc : 0 < chunk) :
    w ≤ alignUp w chunk := by
  unfold alignUp
  have hNe : Nat.beq chunk 0 = false := by
    cases chunk with
    | zero => exact False.elim (Nat.lt_irrefl 0 hc)
    | succ _ => rfl
  rw [hNe]
  have hDM := Nat.div_add_mod (w + (chunk - 1)) chunk
  have hModLt := Nat.mod_lt (w + (chunk - 1)) hc
  have hModLe : Nat.mod (w + (chunk - 1)) chunk ≤ chunk - 1 :=
    nat_le_sub_one_of_lt hModLt
  have hSumLe : w + (chunk - 1) ≤
      Nat.div (w + (chunk - 1)) chunk * chunk + (chunk - 1) := by
    have hEq : w + (chunk - 1) =
        Nat.div (w + (chunk - 1)) chunk * chunk +
        Nat.mod (w + (chunk - 1)) chunk := by
      rw [Nat.mul_comm]
      exact hDM.symm
    exact Nat.le_trans (Nat.le_of_eq hEq) (Nat.add_le_add_left hModLe _)
  exact Nat.le_of_add_le_add_right hSumLe

/-- `alignUp w chunk < w + chunk` for every `chunk > 0`. -/
theorem alignUp_lt_add (w chunk : Nat) (hc : 0 < chunk) :
    alignUp w chunk < w + chunk := by
  unfold alignUp
  have hNe : Nat.beq chunk 0 = false := by
    cases chunk with
    | zero => exact False.elim (Nat.lt_irrefl 0 hc)
    | succ _ => rfl
  rw [hNe]
  have hDM := Nat.div_add_mod (w + (chunk - 1)) chunk
  have hLe1 : Nat.div (w + (chunk - 1)) chunk * chunk ≤ w + (chunk - 1) := by
    rw [Nat.mul_comm]
    exact Nat.le_trans
      (Nat.le_add_right _ (Nat.mod (w + (chunk - 1)) chunk))
      (Nat.le_of_eq hDM)
  have hSubLt : chunk - 1 < chunk := by
    cases chunk with
    | zero => exact False.elim (Nat.lt_irrefl 0 hc)
    | succ m => exact Nat.lt_succ_self m
  exact Nat.lt_of_le_of_lt hLe1 (Nat.add_lt_add_left hSubLt w)

/-- **SIMD Tail-Padding Stride Guard (`VecTailStrideGuard`):**
Validates that rounding width `w` up to a multiple of `chunkBytes` (e.g.
16-byte NEON vector chunks) fits inside both `dstStride` and `srcStride`
without overflowing signed `maxSigned` (e.g. 32-bit signed or pointer-diff
limit). -/
@[expose] def checkVecTailStrideGuard
    (w chunkBytes dstStride srcStride maxSigned : Nat) : Bool :=
  Nat.blt 0 chunkBytes &&
  Nat.ble (w + (chunkBytes - 1)) maxSigned &&
  let w1 := alignUp w chunkBytes
  Nat.ble w1 dstStride &&
  Nat.ble w1 srcStride

/-- **Soundness of `checkVecTailStrideGuard`:**
When `checkVecTailStrideGuard w chunkBytes dstStride srcStride maxSigned`
holds, every chunk index `k` with `k * chunkBytes < w` satisfies:
1. `(k + 1) * chunkBytes ≤ alignUp w chunkBytes ≤ dstStride` (zero row overrun
   on destination),
2. `(k + 1) * chunkBytes ≤ srcStride` (zero row overrun on source),
3. For every row `r < height`, byte range
   `[r * dstStride + k * chunkBytes, r * dstStride + (k + 1) * chunkBytes)`
   lies strictly inside `[r * dstStride, (r + 1) * dstStride)` and inside
   `[0, height * dstStride)` (zero cross-row overlap or buffer overrun). -/
theorem checkVecTailStrideGuard_sound
    (w chunkBytes dstStride srcStride maxSigned height : Nat)
    (h : checkVecTailStrideGuard w chunkBytes dstStride srcStride maxSigned =
         true) :
    0 < chunkBytes ∧
    alignUp w chunkBytes ≤ dstStride ∧
    alignUp w chunkBytes ≤ srcStride ∧
    (∀ k, k * chunkBytes < w →
      (k + 1) * chunkBytes ≤ dstStride ∧
      (k + 1) * chunkBytes ≤ srcStride ∧
      (∀ r, r < height →
        r * dstStride + (k + 1) * chunkBytes ≤ (r + 1) * dstStride ∧
        r * dstStride + (k + 1) * chunkBytes ≤ height * dstStride)) := by
  unfold checkVecTailStrideGuard at h
  dsimp only at h
  revert h
  cases hc : Nat.blt 0 chunkBytes with
  | false => intro h; exact Bool.noConfusion h
  | true =>
    intro h
    simp only [Bool.true_and] at h
    revert h
    cases hMax : Nat.ble (w + (chunkBytes - 1)) maxSigned with
    | false => intro h; exact Bool.noConfusion h
    | true =>
      intro h
      simp only [Bool.true_and] at h
      revert h
      cases hDst : Nat.ble (alignUp w chunkBytes) dstStride with
      | false => intro h; exact Bool.noConfusion h
      | true =>
        intro h
        simp only [Bool.true_and] at h
        have hcPos : 0 < chunkBytes := Nat.le_of_ble_eq_true hc
        have hDstLe : alignUp w chunkBytes ≤ dstStride :=
          Nat.le_of_ble_eq_true hDst
        have hSrcLe : alignUp w chunkBytes ≤ srcStride :=
          Nat.le_of_ble_eq_true h
        refine ⟨hcPos, hDstLe, hSrcLe, ?_⟩
        intro k hkLt
        have hWLe := le_alignUp w chunkBytes hcPos
        have hKLtA : k * chunkBytes < alignUp w chunkBytes :=
          Nat.lt_of_lt_of_le hkLt hWLe
        have hEqQ : alignUp w chunkBytes =
            Nat.div (w + (chunkBytes - 1)) chunkBytes * chunkBytes := by
          unfold alignUp
          have hNe : Nat.beq chunkBytes 0 = false := by
            cases chunkBytes with
            | zero => exact False.elim (Nat.lt_irrefl 0 hcPos)
            | succ _ => rfl
          rw [hNe]
          rfl
        rw [hEqQ] at hKLtA
        have hkLtQ : k < Nat.div (w + (chunkBytes - 1)) chunkBytes :=
          nat_lt_of_mul_lt_mul_right hKLtA
        have hSuccLeA : (k + 1) * chunkBytes ≤ alignUp w chunkBytes := by
          rw [hEqQ]
          exact Nat.mul_le_mul_right chunkBytes hkLtQ
        have hSuccDst : (k + 1) * chunkBytes ≤ dstStride :=
          Nat.le_trans hSuccLeA hDstLe
        have hSuccSrc : (k + 1) * chunkBytes ≤ srcStride :=
          Nat.le_trans hSuccLeA hSrcLe
        refine ⟨hSuccDst, hSuccSrc, ?_⟩
        intro r hrLt
        have hRow : r * dstStride + (k + 1) * chunkBytes ≤
            (r + 1) * dstStride := by
          rw [Nat.succ_mul r dstStride]
          exact Nat.add_le_add_left hSuccDst (r * dstStride)
        have hTot : (r + 1) * dstStride ≤ height * dstStride :=
          Nat.mul_le_mul_right dstStride hrLt
        exact ⟨hRow, Nat.le_trans hRow hTot⟩

/-- **Refutation of Inverted Stride Guard (`stride ≤ alignUp w 16`):**
For `w = 2`, `chunkBytes = 16`, `stride = 2`: the inverted check
`stride ≤ alignUp w 16` succeeds (`2 ≤ 16`), yet the first 16-byte SIMD chunk
write overruns the 2-byte row stride by `14` bytes (`16 - 2 = 14`), while
`checkVecTailStrideGuard` rejects it fail-closed. -/
theorem invertedStrideGuard_overruns_14_bytes :
    Nat.ble 2 (alignUp 2 16) = true ∧
    alignUp 2 16 - 2 = 14 ∧
    checkVecTailStrideGuard 2 16 2 2 2147483647 = false :=
  ⟨rfl, rfl, rfl⟩

/-- **Aligned Multi-Vector 2D Plane-Copy Dispatch Guard (`PlaneCopyGuard`):**
Validates all preconditions before dispatching an aligned multi-vector 2D
plane copy (`chunkBytes` e.g. 64, `alignBytes` e.g. 16, signed `maxSigned`
e.g. `2^63 - 1`):
1. `0 < bytewidth` (signed positive width; prevents `0`/negative loop wrap),
2. `0 < height` (signed positive height; prevents row-counter underflow),
3. `bytewidth + (chunkBytes - 1) <= maxSigned` (prevents signed `alignUp`
   overflow to negative),
4. `chunkBytes % alignBytes == 0`, `srcAddr % alignBytes == 0`,
   `dstAddr % alignBytes == 0`, `srcLinesize % alignBytes == 0`, and
   `dstLinesize % alignBytes == 0` (guarantees aligned per-row and per-chunk
   vector accesses `addr + r * linesize + k * chunkBytes` for every row `r`
   and chunk `k`, preventing alignment faults),
5. `alignUp bytewidth chunkBytes <= dstLinesize` and `<= srcLinesize` (ensures
   every chunk write fits inside row stride without overrunning rows). -/
@[expose] def checkPlaneCopyDispatchGuard
    (srcAddr dstAddr dstLinesize srcLinesize bytewidth height : Int)
    (chunkBytes alignBytes maxSigned : Nat) : Bool :=
  if !Nat.blt 0 chunkBytes || !Nat.blt 0 alignBytes ||
     !Nat.beq (Nat.mod chunkBytes alignBytes) 0 then false
  else
    match srcAddr, dstAddr, dstLinesize, srcLinesize, bytewidth, height with
    | Int.ofNat sa, Int.ofNat da, Int.ofNat dl, Int.ofNat sl,
      Int.ofNat bw, Int.ofNat h =>
      Nat.blt 0 bw &&
      Nat.blt 0 h &&
      Nat.ble (bw + (chunkBytes - 1)) maxSigned &&
      Nat.beq (Nat.mod sa alignBytes) 0 &&
      Nat.beq (Nat.mod da alignBytes) 0 &&
      Nat.beq (Nat.mod dl alignBytes) 0 &&
      Nat.beq (Nat.mod sl alignBytes) 0 &&
      Nat.ble (alignUp bw chunkBytes) dl &&
      Nat.ble (alignUp bw chunkBytes) sl
    | _, _, _, _, _, _ => false

/-- Helper: if `addr % a = 0` and `stride % a = 0` (`a > 0`), then every row
address `(addr + r * stride) % a = 0`. -/
theorem row_addr_aligned (addr stride a r : Nat) (ha : 0 < a)
    (hAddr : Nat.mod addr a = 0) (hStride : Nat.mod stride a = 0) :
    Nat.mod (addr + r * stride) a = 0 := by
  have hS : stride = Nat.div stride a * a := by
    have hDM : a * Nat.div stride a + Nat.mod stride a = stride :=
      Nat.div_add_mod stride a
    rw [hStride, Nat.add_zero, Nat.mul_comm] at hDM
    exact hDM.symm
  have hMul : (r * Nat.div stride a) * a = r * stride := by
    rw [Nat.mul_assoc, ← hS]
  rw [← hMul, nat_add_mul_mod_left addr (r * Nat.div stride a) a ha]
  exact hAddr

/-- Helper: if `addr % a = 0`, `stride % a = 0`, and `chunk % a = 0` (`a > 0`),
then every chunk address `(addr + r * stride + k * chunk) % a = 0`. -/
theorem chunk_addr_aligned (addr stride chunk a r k : Nat) (ha : 0 < a)
    (hAddr : Nat.mod addr a = 0) (hStride : Nat.mod stride a = 0)
    (hChunk : Nat.mod chunk a = 0) :
    Nat.mod (addr + r * stride + k * chunk) a = 0 :=
  row_addr_aligned (addr + r * stride) chunk a k ha
    (row_addr_aligned addr stride a r ha hAddr hStride) hChunk

/-- **Soundness of `checkPlaneCopyDispatchGuard`:**
Every accepted dispatch guarantees positive `bytewidth` and `height`, signed-
overflow-free `alignUp bytewidth chunkBytes`, aligned `chunkBytes`,
`srcAddr`/`dstAddr`, and row linesizes (`dl`/`sl`, yielding aligned per-row
and per-chunk addresses for every `r` and `k`), and chunk-within-stride
containment on both source and destination planes. -/
theorem checkPlaneCopyDispatchGuard_sound
    (sa da dl sl bw h chunkBytes alignBytes maxSigned : Nat)
    (hOk : checkPlaneCopyDispatchGuard
      (Int.ofNat sa) (Int.ofNat da) (Int.ofNat dl) (Int.ofNat sl)
      (Int.ofNat bw) (Int.ofNat h) chunkBytes alignBytes maxSigned = true) :
    0 < chunkBytes ∧
    0 < alignBytes ∧
    Nat.mod chunkBytes alignBytes = 0 ∧
    0 < bw ∧
    0 < h ∧
    bw + (chunkBytes - 1) ≤ maxSigned ∧
    Nat.mod sa alignBytes = 0 ∧
    Nat.mod da alignBytes = 0 ∧
    Nat.mod dl alignBytes = 0 ∧
    Nat.mod sl alignBytes = 0 ∧
    (∀ r k, Nat.mod (sa + r * sl + k * chunkBytes) alignBytes = 0 ∧
            Nat.mod (da + r * dl + k * chunkBytes) alignBytes = 0) ∧
    alignUp bw chunkBytes ≤ dl ∧
    alignUp bw chunkBytes ≤ sl := by
  unfold checkPlaneCopyDispatchGuard at hOk
  dsimp only at hOk
  revert hOk
  cases hc : Nat.blt 0 chunkBytes with
  | false =>
    intro hOk
    simp only [Bool.not_false, Bool.true_or, ite_true] at hOk
    exact Bool.noConfusion hOk
  | true =>
    intro hOk
    revert hOk
    cases ha : Nat.blt 0 alignBytes with
    | false =>
      intro hOk
      simp only [Bool.not_false, Bool.or_true, Bool.true_or, ite_true] at hOk
      exact Bool.noConfusion hOk
    | true =>
      intro hOk
      revert hOk
      cases hca : Nat.beq (Nat.mod chunkBytes alignBytes) 0 with
      | false =>
        intro hOk
        simp only [Bool.not_false, Bool.or_true, ite_true] at hOk
        exact Bool.noConfusion hOk
      | true =>
        intro hOk
        simp only [Bool.not_true, Bool.or_self, ite_false_eq_true_abi] at hOk
        revert hOk
        cases hbw : Nat.blt 0 bw with
        | false => intro hOk; exact Bool.noConfusion hOk
        | true =>
          intro hOk
          simp only [Bool.true_and] at hOk
          revert hOk
          cases hh : Nat.blt 0 h with
          | false => intro hOk; exact Bool.noConfusion hOk
          | true =>
            intro hOk
            simp only [Bool.true_and] at hOk
            revert hOk
            cases hmax : Nat.ble (bw + (chunkBytes - 1)) maxSigned with
            | false => intro hOk; exact Bool.noConfusion hOk
            | true =>
              intro hOk
              simp only [Bool.true_and] at hOk
              revert hOk
              cases hsa : Nat.beq (Nat.mod sa alignBytes) 0 with
              | false => intro hOk; exact Bool.noConfusion hOk
              | true =>
                intro hOk
                simp only [Bool.true_and] at hOk
                revert hOk
                cases hda : Nat.beq (Nat.mod da alignBytes) 0 with
                | false => intro hOk; exact Bool.noConfusion hOk
                | true =>
                  intro hOk
                  simp only [Bool.true_and] at hOk
                  revert hOk
                  cases hdla : Nat.beq (Nat.mod dl alignBytes) 0 with
                  | false => intro hOk; exact Bool.noConfusion hOk
                  | true =>
                    intro hOk
                    simp only [Bool.true_and] at hOk
                    revert hOk
                    cases hsla : Nat.beq (Nat.mod sl alignBytes) 0 with
                    | false => intro hOk; exact Bool.noConfusion hOk
                    | true =>
                      intro hOk
                      simp only [Bool.true_and] at hOk
                      revert hOk
                      cases hdl : Nat.ble (alignUp bw chunkBytes) dl with
                      | false => intro hOk; exact Bool.noConfusion hOk
                      | true =>
                        intro hOk
                        simp only [Bool.true_and] at hOk
                        have haPos : 0 < alignBytes := Nat.le_of_ble_eq_true ha
                        have hChunkEq : Nat.mod chunkBytes alignBytes = 0 :=
                          Nat.eq_of_beq_eq_true hca
                        have hSaEq : Nat.mod sa alignBytes = 0 :=
                          Nat.eq_of_beq_eq_true hsa
                        have hDaEq : Nat.mod da alignBytes = 0 :=
                          Nat.eq_of_beq_eq_true hda
                        have hDlEq : Nat.mod dl alignBytes = 0 :=
                          Nat.eq_of_beq_eq_true hdla
                        have hSlEq : Nat.mod sl alignBytes = 0 :=
                          Nat.eq_of_beq_eq_true hsla
                        exact ⟨Nat.le_of_ble_eq_true hc, haPos, hChunkEq,
                          Nat.le_of_ble_eq_true hbw, Nat.le_of_ble_eq_true hh,
                          Nat.le_of_ble_eq_true hmax, hSaEq, hDaEq, hDlEq,
                          hSlEq,
                          (fun r k =>
                            ⟨chunk_addr_aligned sa sl chunkBytes alignBytes r k
                               haPos hSaEq hSlEq hChunkEq,
                             chunk_addr_aligned da dl chunkBytes alignBytes r k
                               haPos hDaEq hDlEq hChunkEq⟩),
                          Nat.le_of_ble_eq_true hdl,
                          Nat.le_of_ble_eq_true hOk⟩

/-- **NEON Post-Index Loop Footprint Bound (`neonPostIndexLoop_inBounds`):**
Starting at `base`, `n` iterations of a post-index `step`-byte vector access
(such as `ld1 {v0.4s}, [x1], #16` or `st1 {v4.8h}, [x0], #16`) access only
offsets in `[base, base + n * step)`, and when `n * step ≤ bufLen` every
access stays inside `[base, base + bufLen)`. -/
theorem neonPostIndexLoop_inBounds (base step n bufLen : Nat)
    (hFit : n * step ≤ bufLen) :
    ∀ iter, iter < n →
      base + iter * step + step ≤ base + bufLen := by
  intro iter hlt
  have hStep : (iter + 1) * step ≤ n * step :=
    Nat.mul_le_mul_right step hlt
  have hExpand : iter * step + step = (iter + 1) * step :=
    (Nat.succ_mul iter step).symm
  rw [Nat.add_assoc, hExpand]
  exact Nat.add_le_add_left (Nat.le_trans hStep hFit) base

end Anneal.ElfAArch64
