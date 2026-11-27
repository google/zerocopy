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

public section
namespace Anneal.ElfAArch64

/-!
# Total Fixed-Width AArch64 (A64) & NEON Instruction Stream Decoder
(`Anneal.ElfAArch64.Decode`)

Pure Pass-1 (`0` `._unsafe_rec`, `0` `partial`, `0` `noncomputable`, axioms
`⊆ {propext}`) little-endian 32-bit AArch64 instruction decoder over
`List UInt8` and `List AArch64Reloc`:

1. **Explicit `X31` disambiguation (`RegOrZr`, `RegOrSp`):** Separates
   general-purpose register `x0..x30` from `XZR`/`WZR` and `SP`/`WSP` at
   the AST level so instructions that address `SP` vs. `ZR` can never be
   conflated.
2. **Exact ARMv8-A A64 encoding validation (`decodeWord`):**
   - Data processing immediate: `ADD`/`ADDS`/`SUB`/`SUBS` (rejecting
     reserved `sh >= 2`), logical bitmask immediate (`AND`/`ORR`/`EOR`/`ANDS`
     with full `DecodeBitMasks` legality check rejecting `sf=0, N=1` and
     all-ones `s == levels`), `MOVN`/`MOVZ`/`MOVK` (rejecting `opc=1` and
     32-bit `hw >= 2`), `SBFM`/`BFM`/`UBFM` (enforcing `N == sf`, `opc != 3`,
     and 32-bit `immr/imms < 32`), and `ADR`/`ADRP` (requiring explicit
     relocations in relocatable object mode).
   - Data processing register: shifted `ADD`/`SUB`/logical (`shift != 3`,
     32-bit `imm6 < 32`), extended-register `ADD`/`SUB` (`imm3 <= 4` with
     explicit `ExtendKind`), `CSEL`/`CSINC`/`CSINV`/`CSNEG`,
     `MADD`/`MSUB`, and `UDIV`/`SDIV` (`.div`).
   - Branches & system: `B`, `BL`, `B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`,
     `RET`, `BR`, `BLR`, `NOP`, `BTI`, `MSR DIT, #{0,1}` (`.msrDit`),
     `SVC`/`HVC`/`SMC` as `.sysImm` (carrying `LL` and `imm16`), and
     `BRK`/`HLT` as `.trapOrSys`.
   - Loads & stores: GP unsigned-offset and pre/post-index `LDR`/`STR`
     (enforcing writeback `Rn != Rt`), GP `LDP`/`STP` (enforcing `Rt != Rt2`
     on load and writeback `Rn != Rt ∧ Rn != Rt2`), SIMD/FP `LDR`/`STR` and
     `LDP`/`STP`, and Advanced SIMD multi-structure `LD1`/`ST1` (no-offset,
     immediate post-index, and register post-index, enforcing valid `opcode`
     for 1–4 registers including `.1D` arrangements).
   - Advanced SIMD (NEON) compute: shift-by-immediate, three-same,
     two-register misc (`cmeq #0`), and permute (`uzp1`/`uzp2`/`zip1`/
     `zip2`/`trn1`/`trn2`).
3. **4-byte alignment & 1-to-1 relocation coverage (`decodeStream`,
   `localDecodeCoverageOk`):** Rejects trailing partial words (`len % 4 != 0`)
   and unconsumed or duplicated relocations fail-closed.
-/

/-! ## 1. Total List & Bitfield Helpers (`0` `._unsafe_rec`) -/

/-- Structural `List.take` via `@Nat.rec`. -/
@[expose] def listTake {α : Type} (n : Nat) (xs : List α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun _ => [])
    (fun _ ih ys =>
      match ys with
      | [] => []
      | y :: rest => y :: ih rest)
    n xs

/-- Structural `List.drop` via `@Nat.rec`. -/
@[expose] def listDrop {α : Type} (n : Nat) (xs : List α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun ys => ys)
    (fun _ ih ys =>
      match ys with
      | [] => []
      | _ :: rest => ih rest)
    n xs

/-- Structural `List` indexing via `@Nat.rec`. -/
@[expose] def listGet? {α : Type} (xs : List α) (n : Nat) : Option α :=
  @Nat.rec (fun _ => List α → Option α)
    (fun ys =>
      match ys with
      | [] => none
      | y :: _ => some y)
    (fun _ ih ys =>
      match ys with
      | [] => none
      | _ :: rest => ih rest)
    n xs

/-- Structural `List.find?` via `List.foldr`. -/
@[expose] def listFind? {α : Type} (p : α → Bool) (xs : List α) : Option α :=
  List.foldr (fun x acc => if p x then some x else acc) none xs

/-- Structural `List.all` via `List.foldr`. -/
@[expose] def listAll {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  List.foldr (fun x acc => p x && acc) true xs

/-- Structural `List.any` via `List.foldr`. -/
@[expose] def listAny {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  List.foldr (fun x acc => p x || acc) false xs

/-- Structural `List.getLast?` via `List.foldl`. -/
@[expose] def listGetLast? {α : Type} (xs : List α) : Option α :=
  List.foldl (fun _ x => some x) none xs

/-- Structural `List.countP` via `List.foldl`. -/
@[expose] def listCountP {α : Type} (p : α → Bool) (xs : List α) : Nat :=
  List.foldl (fun acc x => if p x then acc + 1 else acc) 0 xs

/-- Membership test on `List Nat`. -/
@[expose] def natListContains (xs : List Nat) (v : Nat) : Bool :=
  listAny (fun x => Nat.beq x v) xs

/-- True iff all elements of `xs : List Nat` are pairwise distinct. -/
@[expose] def natListAllDistinct (xs : List Nat) : Bool :=
  let st := List.foldr
    (fun x acc =>
      let seen := acc.1
      let ok := acc.2
      (x :: seen, ok && !natListContains seen x))
    ([], true) xs
  st.2

/-- True iff `a` and `b` denote the same finite set of distinct `Nat`s. -/
@[expose] def natListSameSet (a b : List Nat) : Bool :=
  natListAllDistinct a &&
  natListAllDistinct b &&
  Nat.beq a.length b.length &&
  listAll (fun x => natListContains b x) a

/-- Unsigned `Nat` power of two `2^k` (flat O(1) table for `k <= 32`, `@Nat.rec`
for larger exponents so kernel & elaborator WHNF stays shallow). -/
@[expose] def pow2Nat (k : Nat) : Nat :=
  match k with
  | 0  => 1          | 1  => 2          | 2  => 4          | 3  => 8
  | 4  => 16         | 5  => 32         | 6  => 64         | 7  => 128
  | 8  => 256        | 9  => 512        | 10 => 1024       | 11 => 2048
  | 12 => 4096       | 13 => 8192       | 14 => 16384      | 15 => 32768
  | 16 => 65536      | 17 => 131072     | 18 => 262144     | 19 => 524288
  | 20 => 1048576    | 21 => 2097152    | 22 => 4194304    | 23 => 8388608
  | 24 => 16777216   | 25 => 33554432   | 26 => 67108864   | 27 => 134217728
  | 28 => 268435456  | 29 => 536870912  | 30 => 1073741824 | 31 => 2147483648
  | 32 => 4294967296
  | n  => @Nat.rec (fun _ => Nat) 1 (fun _ ih => ih * 2) n

/-- Extract `width` bits starting at bit position `lo` from `w : Nat`. -/
@[expose] def bits (w lo width : Nat) : Nat :=
  Nat.mod (Nat.div w (pow2Nat lo)) (pow2Nat width)

/-- Extract single bit `pos` from `w : Nat` as `Bool`. -/
@[expose] def bitAt (w pos : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.div w (pow2Nat pos)) 2) 1

/-- Sign-extend an `n`-bit unsigned integer `u < 2^n` to `Int`. -/
@[expose] def sextBits (n u : Nat) : Int :=
  match n with
  | 0 => Int.ofNat 0
  | k + 1 =>
    let half := pow2Nat k
    let full := half * 2
    let masked := Nat.mod u full
    if Nat.blt masked half then Int.ofNat masked
    else Int.sub (Int.ofNat masked) (Int.ofNat full)

/-- Little-endian 16-bit unsigned integer from two bytes. -/
@[expose] def le16Nat (b0 b1 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat

/-- Little-endian 32-bit unsigned integer from four bytes. -/
@[expose] def le32Nat (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))

/-- Little-endian 64-bit unsigned integer from eight bytes. -/
@[expose] def le64Nat (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : Nat :=
  le32Nat b0 b1 b2 b3 + 4294967296 * le32Nat b4 b5 b6 b7

/-- Sign-extend a 64-bit unsigned `Nat` into `Int`. -/
@[expose] def sext64 (u : Nat) : Int :=
  if Nat.blt u 9223372036854775808 then Int.ofNat u
  else Int.sub (Int.ofNat u) (Int.ofNat 18446744073709551616)

/-! ## 2. AArch64 Registers, Conditions, Widths, and Relocations -/

/-- General-purpose register width: 32-bit `W` (writes zero-extend `[63:32]`)
or 64-bit `X` (reads and writes all 64 bits). -/
inductive RegWidth where
  | w32
  | x64

@[expose] def RegWidth.is64 : RegWidth → Bool
  | .w32 => false
  | .x64 => true

/-- General-purpose register `x0..x30` (explicitly excluding encoding `31`,
which is disambiguated via `RegOrZr` and `RegOrSp`). -/
inductive Gpr where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30

/-- Convert `Gpr` to its architectural 5-bit register number `0..30`. -/
@[expose] def Gpr.toNat : Gpr → Nat
  | .x0  => 0  | .x1  => 1  | .x2  => 2  | .x3  => 3
  | .x4  => 4  | .x5  => 5  | .x6  => 6  | .x7  => 7
  | .x8  => 8  | .x9  => 9  | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19
  | .x20 => 20 | .x21 => 21 | .x22 => 22 | .x23 => 23
  | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27
  | .x28 => 28 | .x29 => 29 | .x30 => 30

/-- Boolean equality on `Gpr`. -/
@[expose] def Gpr.beq (a b : Gpr) : Bool :=
  Nat.beq a.toNat b.toNat

/-- Decode a 5-bit register number `0..30` into `Option Gpr` (`31` -> `none`).
-/
@[expose] def gprOfNat? (n : Nat) : Option Gpr :=
  match n with
  | 0  => some .x0  | 1  => some .x1  | 2  => some .x2  | 3  => some .x3
  | 4  => some .x4  | 5  => some .x5  | 6  => some .x6  | 7  => some .x7
  | 8  => some .x8  | 9  => some .x9  | 10 => some .x10 | 11 => some .x11
  | 12 => some .x12 | 13 => some .x13 | 14 => some .x14 | 15 => some .x15
  | 16 => some .x16 | 17 => some .x17 | 18 => some .x18 | 19 => some .x19
  | 20 => some .x20 | 21 => some .x21 | 22 => some .x22 | 23 => some .x23
  | 24 => some .x24 | 25 => some .x25 | 26 => some .x26 | 27 => some .x27
  | 28 => some .x28 | 29 => some .x29 | 30 => some .x30
  | _  => none

/-- Operand register where encoding `31` means `XZR`/`WZR`. -/
inductive RegOrZr where
  | gpr (r : Gpr)
  | zr

@[expose] def RegOrZr.beq (a b : RegOrZr) : Bool :=
  match a, b with
  | .gpr x, .gpr y => x.beq y
  | .zr,    .zr    => true
  | _,      _      => false

/-- Operand register where encoding `31` means `SP`/`WSP`. -/
inductive RegOrSp where
  | gpr (r : Gpr)
  | sp

@[expose] def RegOrSp.isSp : RegOrSp → Bool
  | .sp    => true
  | .gpr _ => false

@[expose] def decodeRegOrZr (n : Nat) : RegOrZr :=
  match gprOfNat? n with
  | some r => .gpr r
  | none => .zr

@[expose] def decodeRegOrSp (n : Nat) : RegOrSp :=
  match gprOfNat? n with
  | some r => .gpr r
  | none => .sp

/-- True iff `r` is an AAPCS64 callee-saved GPR (`x19..x28`), frame pointer
(`x29`), or link register (`x30`). -/
@[expose] def Gpr.isCalleeSaved : Gpr → Bool
  | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25
  | .x26 | .x27 | .x28 | .x29 | .x30 => true
  | _ => false

/-- True iff `r` is the platform register `x18` (reserved on Darwin/Windows
and some hardened Linux platforms). -/
@[expose] def Gpr.isPlatformReg : Gpr → Bool
  | .x18 => true
  | _ => false

/-- 128-bit SIMD/FP vector register `v0..v31`. -/
inductive VReg where
  | v0  | v1  | v2  | v3  | v4  | v5  | v6  | v7
  | v8  | v9  | v10 | v11 | v12 | v13 | v14 | v15
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31

@[expose] def VReg.toNat : VReg → Nat
  | .v0  => 0  | .v1  => 1  | .v2  => 2  | .v3  => 3
  | .v4  => 4  | .v5  => 5  | .v6  => 6  | .v7  => 7
  | .v8  => 8  | .v9  => 9  | .v10 => 10 | .v11 => 11
  | .v12 => 12 | .v13 => 13 | .v14 => 14 | .v15 => 15
  | .v16 => 16 | .v17 => 17 | .v18 => 18 | .v19 => 19
  | .v20 => 20 | .v21 => 21 | .v22 => 22 | .v23 => 23
  | .v24 => 24 | .v25 => 25 | .v26 => 26 | .v27 => 27
  | .v28 => 28 | .v29 => 29 | .v30 => 30 | .v31 => 31

@[expose] def vregOfNatMod32 (n : Nat) : VReg :=
  match Nat.mod n 32 with
  | 0  => .v0  | 1  => .v1  | 2  => .v2  | 3  => .v3
  | 4  => .v4  | 5  => .v5  | 6  => .v6  | 7  => .v7
  | 8  => .v8  | 9  => .v9  | 10 => .v10 | 11 => .v11
  | 12 => .v12 | 13 => .v13 | 14 => .v14 | 15 => .v15
  | 16 => .v16 | 17 => .v17 | 18 => .v18 | 19 => .v19
  | 20 => .v20 | 21 => .v21 | 22 => .v22 | 23 => .v23
  | 24 => .v24 | 25 => .v25 | 26 => .v26 | 27 => .v27
  | 28 => .v28 | 29 => .v29 | 30 => .v30 | _  => .v31

/-- True iff `v` is one of `v8..v15`, whose low 64 bits (`d8..d15`) are
AAPCS64 callee-saved. -/
@[expose] def VReg.isCalleeSavedLo64 : VReg → Bool
  | .v8 | .v9 | .v10 | .v11 | .v12 | .v13 | .v14 | .v15 => true
  | _ => false

/-- All 16 AArch64 condition codes. -/
inductive Cond where
  | eq | ne | cs | cc | mi | pl | vs | vc
  | hi | ls | ge | lt | gt | le | al | nv

@[expose] def condOfNat (n : Nat) : Cond :=
  match Nat.mod n 16 with
  | 0  => .eq | 1  => .ne | 2  => .cs | 3  => .cc
  | 4  => .mi | 5  => .pl | 6  => .vs | 7  => .vc
  | 8  => .hi | 9  => .ls | 10 => .ge | 11 => .lt
  | 12 => .gt | 13 => .le | 14 => .al | _  => .nv

/-- Shift kind for shifted-register data processing. -/
inductive ShiftKind where
  | lsl
  | lsr
  | asr
  | ror

/-- Extend kind for extended-register `ADD`/`SUB` (`option` bits `[15:13]`). -/
inductive ExtendKind where
  | uxtb | uxth | uxtw | uxtx
  | sxtb | sxth | sxtw | sxtx

@[expose] def extendKindOfNat (n : Nat) : ExtendKind :=
  match Nat.mod n 8 with
  | 0 => .uxtb | 1 => .uxth | 2 => .uxtw | 3 => .uxtx
  | 4 => .sxtb | 5 => .sxth | 6 => .sxtw | _ => .sxtx

/-- True iff an `ExtendKind` reads bit `>= 32` of `Rm` when `sf = x64`. -/
@[expose] def ExtendKind.readsUpper32 : ExtendKind → Bool
  | .uxtx | .sxtx => true
  | _ => false

/-- Relocation kinds admitted for AArch64 `.rodata` addressing. -/
inductive AArch64RelocKind where
  | adrPrelPgHi21    -- R_AARCH64_ADR_PREL_PG_HI21 (275)
  | adrPrelLo21      -- R_AARCH64_ADR_PREL_LO21 (274)
  | addAbsLo12Nc     -- R_AARCH64_ADD_ABS_LO12_NC (277)
  | ldst64AbsLo12Nc  -- R_AARCH64_LDST64_ABS_LO12_NC (286)
  | ldst128AbsLo12Nc -- R_AARCH64_LDST128_ABS_LO12_NC (299)

@[expose] def AArch64RelocKind.beq (a b : AArch64RelocKind) : Bool :=
  match a, b with
  | .adrPrelPgHi21,    .adrPrelPgHi21    => true
  | .adrPrelLo21,      .adrPrelLo21      => true
  | .addAbsLo12Nc,     .addAbsLo12Nc     => true
  | .ldst64AbsLo12Nc,  .ldst64AbsLo12Nc  => true
  | .ldst128AbsLo12Nc, .ldst128AbsLo12Nc => true
  | _,                 _                 => false

/-- Relocatable AArch64 instruction relocation record anchored at a 4-byte
aligned byte offset within the decoded function. -/
structure AArch64Reloc where
  offset : Nat
  kind   : AArch64RelocKind
  secIdx : Nat
  target : Int

/-- Decoder configuration controlling relocatable-object strictness. -/
structure DecodeConfig where
  requireRelocForPcRel : Bool := true

/-! ## 3. Decoded AArch64 Instruction AST -/

/-- Logical immediate / register operation kind. -/
inductive LogicOp where
  | and_ | orr | eor | ands
  | bic  | orn | eon | bics

/-- Bitfield move variant (`SBFM`, `BFM`, `UBFM`). -/
inductive BitfieldOp where
  | sbfm | bfm | ubfm

/-- Move wide variant (`MOVN`, `MOVZ`, `MOVK`). -/
inductive MoveWideOp where
  | movn | movz | movk

/-- Conditional select variant (`CSEL`, `CSINC`, `CSINV`, `CSNEG`). -/
inductive CondSelOp where
  | csel | csinc | csinv | csneg

/-- Addressing mode for GP/SIMD single-register load/store. -/
inductive AddrMode where
  | unsignedOff (immBytes : Nat)
  | postIndex   (immBytes : Int)
  | preIndex    (immBytes : Int)

/-- Addressing mode for `LDP`/`STP`. -/
inductive PairAddrMode where
  | signedOff (immBytes : Int)
  | postIndex (immBytes : Int)
  | preIndex  (immBytes : Int)

/-- Post-index update mode for Advanced SIMD `LD1`/`ST1`. -/
inductive SimdPostIdx where
  | none
  | imm (bytes : Nat)
  | reg (rm : Gpr)

/-- Advanced SIMD shift-by-immediate operation subset. -/
inductive SimdShiftOp where
  | fcvtzs
  | sqrshrn
  | sqshrun
  | sri
  | shl
  | sshr
  | ushr
  | srshr

/-- Advanced SIMD three-same operation subset. -/
inductive SimdThreeSameOp where
  | uqadd | uqsub | umin | umax
  | add   | sub   | and_ | bic | orr | eor

/-- Advanced SIMD permute operation subset. -/
inductive SimdPermOp where
  | uzp1 | uzp2 | trn1 | trn2 | zip1 | zip2

/-- Decoded AArch64 (A64) instruction AST. -/
inductive DecodedInsn where
  | addSubImm (w : RegWidth) (isSub : Bool) (setFlags : Bool)
      (rd : RegOrSp) (rdIsZr : Bool) (rn : RegOrSp) (imm : Nat)
      (reloc? : Option AArch64Reloc)
  | logicImm (w : RegWidth) (op : LogicOp)
      (rd : RegOrSp) (rdIsZr : Bool) (rn : RegOrZr)
      (nBit : Bool) (immr : Nat) (imms : Nat)
  | moveWide (w : RegWidth) (op : MoveWideOp)
      (rd : RegOrZr) (imm16 : Nat) (hw : Nat)
  | bitfield (w : RegWidth) (op : BitfieldOp)
      (rd : RegOrZr) (rn : RegOrZr) (immr : Nat) (imms : Nat)
  | pcRelAddr (isAdrp : Bool) (rd : RegOrZr) (imm : Int)
      (reloc? : Option AArch64Reloc)
  | addSubShift (w : RegWidth) (isSub : Bool) (setFlags : Bool)
      (shift : ShiftKind) (imm6 : Nat)
      (rd : RegOrZr) (rn : RegOrZr) (rm : RegOrZr)
  | addSubExt (w : RegWidth) (isSub : Bool) (setFlags : Bool)
      (ext : ExtendKind) (imm3 : Nat)
      (rd : RegOrSp) (rdIsZr : Bool) (rn : RegOrSp) (rm : RegOrZr)
  | logicShift (w : RegWidth) (op : LogicOp) (shift : ShiftKind) (imm6 : Nat)
      (rd : RegOrZr) (rn : RegOrZr) (rm : RegOrZr)
  | condSel (w : RegWidth) (op : CondSelOp) (cond : Cond)
      (rd : RegOrZr) (rn : RegOrZr) (rm : RegOrZr)
  | maddSub (w : RegWidth) (isSub : Bool)
      (rd : RegOrZr) (rn : RegOrZr) (rm : RegOrZr) (ra : RegOrZr)
  | div (w : RegWidth) (isSigned : Bool)
      (rd : RegOrZr) (rn : RegOrZr) (rm : RegOrZr)
  | branch (isLink : Bool) (offBytes : Int)
  | branchCond (cond : Cond) (offBytes : Int)
  | cbz (w : RegWidth) (isNonZero : Bool) (rt : RegOrZr) (offBytes : Int)
  | tbz (isNonZero : Bool) (bitIdx : Nat) (rt : RegOrZr) (offBytes : Int)
  | ret (rn : RegOrZr)
  | branchReg (isLink : Bool) (rn : RegOrZr)
  | nop
  | bti (targetMask : Nat)
  | msrDit (enable : Bool)
  | sysImm (ll : Nat) (imm16 : Nat)
  | trapOrSys
  | gpLoadStore (isLoad : Bool) (accessBytes : Nat) (signExt : Bool)
      (destW : RegWidth) (rt : RegOrZr) (rn : RegOrSp) (mode : AddrMode)
      (reloc? : Option AArch64Reloc)
  | gpLoadStorePair (isLoad : Bool) (w : RegWidth) (rt : RegOrZr)
      (rt2 : RegOrZr) (rn : RegOrSp) (mode : PairAddrMode)
  | simdLoadStore (isLoad : Bool) (accessBytes : Nat) (vt : VReg)
      (rn : RegOrSp) (mode : AddrMode) (reloc? : Option AArch64Reloc)
  | simdLoadStorePair (isLoad : Bool) (elemBytes : Nat) (vt : VReg)
      (vt2 : VReg) (rn : RegOrSp) (mode : PairAddrMode)
  | simdLdSt1 (isLoad : Bool) (isQ : Bool) (numRegs : Nat) (elemSize : Nat)
      (vt : VReg) (rn : RegOrSp) (post : SimdPostIdx)
  | simdShiftImm (op : SimdShiftOp) (isQ : Bool) (immh : Nat) (immb : Nat)
      (vd : VReg) (vn : VReg)
  | simdThreeSame (op : SimdThreeSameOp) (isQ : Bool) (size : Nat)
      (vd : VReg) (vn : VReg) (vm : VReg)
  | simdCmeqZero (isQ : Bool) (size : Nat) (vd : VReg) (vn : VReg)
  | simdPerm (op : SimdPermOp) (isQ : Bool) (size : Nat)
      (vd : VReg) (vn : VReg) (vm : VReg)

/-- Exact list of vector registers accessed by `LD1`/`ST1` (wrapping modulo 32
per ARMv8-A `LD1`/`ST1` multi-structure semantics). -/
@[expose] def simdRegRange (start : VReg) (count : Nat) : List VReg :=
  let base := start.toNat
  match count with
  | 1 => [vregOfNatMod32 base]
  | 2 => [vregOfNatMod32 base, vregOfNatMod32 (base + 1)]
  | 3 => [vregOfNatMod32 base, vregOfNatMod32 (base + 1),
          vregOfNatMod32 (base + 2)]
  | 4 => [vregOfNatMod32 base, vregOfNatMod32 (base + 1),
          vregOfNatMod32 (base + 2), vregOfNatMod32 (base + 3)]
  | _ => []

/-- Total byte width transferred by an `LD1`/`ST1` instruction. -/
@[expose] def simdLdSt1Bytes (isQ : Bool) (numRegs : Nat) : Nat :=
  numRegs * (if isQ then 16 else 8)

/-! ## 4. Exact ARMv8-A Bitfield Decoding Helpers -/

/-- Highest set bit index (`0..6`) for a non-zero 7-bit integer `v`, or `none`
when `v = 0`. -/
@[expose] def highestBit7? (v : Nat) : Option Nat :=
  if Nat.ble 64 v then some 6
  else if Nat.ble 32 v then some 5
  else if Nat.ble 16 v then some 4
  else if Nat.ble 8 v then some 3
  else if Nat.ble 4 v then some 2
  else if Nat.ble 2 v then some 1
  else if Nat.ble 1 v then some 0
  else none

/-- Exact ARMv8-A `DecodeBitMasks` validity predicate for logical immediate
encodings (`sf`, `N`, `imms`). Rejects `sf=0 ∧ N=1`, `len < 1`, and
all-ones `s == levels`. -/
@[expose] def validLogicalImm (is64 : Bool) (nBit : Bool) (imms : Nat) : Bool :=
  if !is64 && nBit then false
  else
    let notImms := 63 - Nat.mod imms 64
    let comb := (if nBit then 64 else 0) + notImms
    match highestBit7? comb with
    | none => false
    | some len =>
      if Nat.blt len 1 then false
      else
        let levels := pow2Nat len - 1
        let s := Nat.mod imms (pow2Nat len)
        !Nat.beq s levels

/-- Look up an exact relocation anchored at byte offset `off` matching `kind`.
Returns `none` if zero or multiple conflicting relocations exist. -/
@[expose] def findRelocAt? (relocs : List AArch64Reloc) (off : Nat)
    (kind : AArch64RelocKind) : Option AArch64Reloc :=
  let hits := relocs.filter (fun r => Nat.beq r.offset off)
  match hits with
  | [r] => if r.kind.beq kind then some r else none
  | _ => none

/-- Look up any relocation at byte offset `off` (used to reject unexpected
relocations on instructions that do not consume one). -/
@[expose] def hasAnyRelocAt (relocs : List AArch64Reloc) (off : Nat) : Bool :=
  listAny (fun r => Nat.beq r.offset off) relocs

/-! ## 5. Single 32-Bit AArch64 Instruction Word Decoder -/

/-- Decode Data Processing — Immediate instructions (`[28:26] = 100`). -/
@[expose] def decodeDpImm (cfg : DecodeConfig) (relocs : List AArch64Reloc)
    (off word : Nat) : Option DecodedInsn :=
  let op0 := bits word 23 3
  let sf := bitAt word 31
  let w := if sf then RegWidth.x64 else RegWidth.w32
  let rdN := bits word 0 5
  let rnN := bits word 5 5
  -- PC-relative ADR / ADRP (`[28:24] = 10000`, so `op0 ∈ {0, 1}`)
  if Nat.beq (bits word 24 5) 0x10 then
    let isAdrp := sf
    let immlo := bits word 29 2
    let immhi := bits word 5 19
    let raw21 := 4 * immhi + immlo
    let s21 := sextBits 21 raw21
    let effImm := if isAdrp then Int.mul (Int.ofNat 4096) s21 else s21
    let needKind :=
      if isAdrp then AArch64RelocKind.adrPrelPgHi21
      else AArch64RelocKind.adrPrelLo21
    match findRelocAt? relocs off needKind with
    | some r =>
      some (.pcRelAddr isAdrp (decodeRegOrZr rdN) effImm (some r))
    | none =>
      if cfg.requireRelocForPcRel || hasAnyRelocAt relocs off then none
      else some (.pcRelAddr isAdrp (decodeRegOrZr rdN) effImm none)
  -- ADD / ADDS / SUB / SUBS (immediate): `[28:23] = 100010` (`op0 = 2`)
  else if Nat.beq op0 2 then
    let isSub := bitAt word 30
    let setFlags := bitAt word 29
    let sh := bitAt word 22
    let imm12 := bits word 10 12
    let effImm := if sh then 4096 * imm12 else imm12
    let rdSp := decodeRegOrSp rdN
    let rdIsZr := setFlags && Nat.beq rdN 31
    let rnSp := decodeRegOrSp rnN
    let reloc? :=
      if sf && !isSub && !setFlags && !sh then
        findRelocAt? relocs off .addAbsLo12Nc
      else none
    if hasAnyRelocAt relocs off && reloc?.isNone then none
    else
      some (.addSubImm w isSub setFlags rdSp rdIsZr rnSp effImm reloc?)
  -- Logical immediate: `[28:23] = 100100` (`op0 = 4`)
  else if Nat.beq op0 4 then
    if hasAnyRelocAt relocs off then none
    else
      let opc := bits word 29 2
      let nBit := bitAt word 22
      let immr := bits word 16 6
      let imms := bits word 10 6
      if !validLogicalImm sf nBit imms then none
      else
        let lop :=
          match opc with
          | 0 => LogicOp.and_
          | 1 => LogicOp.orr
          | 2 => LogicOp.eor
          | _ => LogicOp.ands
        let rdIsZr := Nat.beq opc 3 && Nat.beq rdN 31
        some (.logicImm w lop (decodeRegOrSp rdN) rdIsZr
          (decodeRegOrZr rnN) nBit immr imms)
  -- Move wide immediate (`MOVN`/`MOVZ`/`MOVK`): `[28:23] = 100101` (`op0 = 5`)
  else if Nat.beq op0 5 then
    if hasAnyRelocAt relocs off then none
    else
      let opc := bits word 29 2
      let hw := bits word 21 2
      let imm16 := bits word 5 16
      if !sf && Nat.ble 2 hw then none
      else
        match opc with
        | 0 => some (.moveWide w .movn (decodeRegOrZr rdN) imm16 hw)
        | 2 => some (.moveWide w .movz (decodeRegOrZr rdN) imm16 hw)
        | 3 => some (.moveWide w .movk (decodeRegOrZr rdN) imm16 hw)
        | _ => none
  -- Bitfield (`SBFM`, `BFM`, `UBFM`): `[28:23] = 100110` (`op0 = 6`)
  else if Nat.beq op0 6 then
    if hasAnyRelocAt relocs off then none
    else
      let opc := bits word 29 2
      let nBit := bitAt word 22
      let immr := bits word 16 6
      let imms := bits word 10 6
      if nBit != sf then none
      else if !sf && (Nat.ble 32 immr || Nat.ble 32 imms) then none
      else
        match opc with
        | 0 => some (.bitfield w .sbfm (decodeRegOrZr rdN)
                (decodeRegOrZr rnN) immr imms)
        | 1 => some (.bitfield w .bfm (decodeRegOrZr rdN)
                (decodeRegOrZr rnN) immr imms)
        | 2 => some (.bitfield w .ubfm (decodeRegOrZr rdN)
                (decodeRegOrZr rnN) immr imms)
        | _ => none
  else none

/-- Decode Branches, Exception Generation, and System instructions
(`[28:26] = 101`). -/
@[expose] def decodeBranchSys (relocs : List AArch64Reloc) (off word : Nat) :
    Option DecodedInsn :=
  if hasAnyRelocAt relocs off then none
  else
    let op0 := bits word 29 3
    -- Unconditional branch immediate: `B` (`op0=0`) / `BL` (`op0=4`)
    if (Nat.beq op0 0 || Nat.beq op0 4) && Nat.beq (bits word 26 3) 5 then
      let isLink := bitAt word 31
      let s26 := sextBits 26 (bits word 0 26)
      some (.branch isLink (Int.mul s26 (Int.ofNat 4)))
    -- Compare and branch immediate (`CBZ`/`CBNZ`): `[30:25] = 011010`
    else if Nat.beq (bits word 25 6) 0x1A then
      let w := if bitAt word 31 then RegWidth.x64 else RegWidth.w32
      let isNz := bitAt word 24
      let s19 := sextBits 19 (bits word 5 19)
      let rt := decodeRegOrZr (bits word 0 5)
      some (.cbz w isNz rt (Int.mul s19 (Int.ofNat 4)))
    -- Test and branch immediate (`TBZ`/`TBNZ`): `[30:25] = 011011`
    else if Nat.beq (bits word 25 6) 0x1B then
      let b5 := if bitAt word 31 then 32 else 0
      let isNz := bitAt word 24
      let b40 := bits word 19 5
      let s14 := sextBits 14 (bits word 5 14)
      let rt := decodeRegOrZr (bits word 0 5)
      some (.tbz isNz (b5 + b40) rt (Int.mul s14 (Int.ofNat 4)))
    -- Conditional branch immediate (`B.cond`): `[31:24] = 01010100`, `[4] = 0`
    else if Nat.beq (bits word 24 8) 0x54 && !bitAt word 4 then
      let s19 := sextBits 19 (bits word 5 19)
      let cond := condOfNat (bits word 0 4)
      some (.branchCond cond (Int.mul s19 (Int.ofNat 4)))
    -- Exception generation (`SVC`/`HVC`/`SMC` -> `sysImm`; `BRK`/`HLT` ->
    -- `trapOrSys`): `[31:24] = 0xD4`, `op2[4:2] = 000`
    else if Nat.beq (bits word 24 8) 0xD4 && Nat.beq (bits word 2 3) 0 then
      let opc := bits word 21 3
      let ll := bits word 0 2
      if Nat.beq opc 0 && Nat.blt 0 ll then
        some (.sysImm ll (bits word 5 16))
      else if (Nat.beq opc 1 && Nat.beq ll 0) ||
              (Nat.beq opc 2 && Nat.beq ll 0) then
        some .trapOrSys
      else none
    -- System HINTs & PSTATE.DIT: `NOP` (`0xD503201F`), `BTI`, `MSR DIT, #{0,1}`
    else if Nat.beq word 0xD503201F then
      some .nop
    else if Nat.beq word 0xD503415F then
      some (.msrDit true)
    else if Nat.beq word 0xD503405F then
      some (.msrDit false)
    else if Nat.beq (bits word 12 20) 0xD5032 &&
            Nat.beq (bits word 8 4) 4 &&
            Nat.beq (bits word 0 5) 0x1F &&
            !bitAt word 5 then
      some (.bti (bits word 6 2))
    -- Unconditional branch register (`BR`, `BLR`, `RET`): `[31:25] = 1101011`
    else if Nat.beq (bits word 25 7) 0x6B &&
            Nat.beq (bits word 16 5) 0x1F &&
            Nat.beq (bits word 10 6) 0 &&
            Nat.beq (bits word 0 5) 0 then
      let opc := bits word 21 4
      let rn := decodeRegOrZr (bits word 5 5)
      match opc with
      | 0 => some (.branchReg false rn)
      | 1 => some (.branchReg true rn)
      | 2 => some (.ret rn)
      | _ => none
    else none

/-- Decode Data Processing — Register instructions (`[27:25] = 101`). -/
@[expose] def decodeDpReg (relocs : List AArch64Reloc) (off word : Nat) :
    Option DecodedInsn :=
  if hasAnyRelocAt relocs off then none
  else
    let sf := bitAt word 31
    let w := if sf then RegWidth.x64 else RegWidth.w32
    let rdN := bits word 0 5
    let rnN := bits word 5 5
    let rmN := bits word 16 5
    -- Logical (shifted register): `[28:24] = 01010`
    if Nat.beq (bits word 24 5) 0x0A then
      let opc := bits word 29 2
      let nBit := bitAt word 21
      let shN := bits word 22 2
      let imm6 := bits word 10 6
      if !sf && Nat.ble 32 imm6 then none
      else
        let sh :=
          match shN with
          | 0 => ShiftKind.lsl
          | 1 => ShiftKind.lsr
          | 2 => ShiftKind.asr
          | _ => ShiftKind.ror
        let lop :=
          match opc, nBit with
          | 0, false => LogicOp.and_
          | 0, true  => LogicOp.bic
          | 1, false => LogicOp.orr
          | 1, true  => LogicOp.orn
          | 2, false => LogicOp.eor
          | 2, true  => LogicOp.eon
          | _, false => LogicOp.ands
          | _, true  => LogicOp.bics
        some (.logicShift w lop sh imm6 (decodeRegOrZr rdN)
          (decodeRegOrZr rnN) (decodeRegOrZr rmN))
    -- ADD/SUB (shifted register): `[28:24] = 01011`, `[21] = 0`
    else if Nat.beq (bits word 24 5) 0x0B && !bitAt word 21 then
      let isSub := bitAt word 30
      let setFlags := bitAt word 29
      let shN := bits word 22 2
      let imm6 := bits word 10 6
      if Nat.beq shN 3 then none
      else if !sf && Nat.ble 32 imm6 then none
      else
        let sh :=
          match shN with
          | 0 => ShiftKind.lsl
          | 1 => ShiftKind.lsr
          | _ => ShiftKind.asr
        some (.addSubShift w isSub setFlags sh imm6
          (decodeRegOrZr rdN) (decodeRegOrZr rnN) (decodeRegOrZr rmN))
    -- ADD/SUB (extended register): `[28:21] = 01011001`
    else if Nat.beq (bits word 21 8) 0x59 then
      let isSub := bitAt word 30
      let setFlags := bitAt word 29
      let ext := extendKindOfNat (bits word 13 3)
      let imm3 := bits word 10 3
      if Nat.blt 4 imm3 then none
      else
        let rdIsZr := setFlags && Nat.beq rdN 31
        some (.addSubExt w isSub setFlags ext imm3
          (decodeRegOrSp rdN) rdIsZr (decodeRegOrSp rnN) (decodeRegOrZr rmN))
    -- Conditional select (`CSEL`, `CSINC`, `CSINV`, `CSNEG`):
    -- `[29:21] = 011010100`, `[11] = 0`
    else if Nat.beq (bits word 21 9) 0x0D4 && !bitAt word 11 then
      let op := bitAt word 30
      let o2 := bitAt word 10
      let cond := condOfNat (bits word 12 4)
      let csOp :=
        match op, o2 with
        | false, false => CondSelOp.csel
        | false, true  => CondSelOp.csinc
        | true,  false => CondSelOp.csinv
        | true,  true  => CondSelOp.csneg
      some (.condSel w csOp cond (decodeRegOrZr rdN)
        (decodeRegOrZr rnN) (decodeRegOrZr rmN))
    -- Data processing 2-source (`UDIV`, `SDIV`): `[30:21] = 0011010110`,
    -- `[15:11] = 00001`, `[10] = isSigned`
    else if Nat.beq (bits word 21 10) 0x0D6 &&
            Nat.beq (bits word 11 5) 1 then
      let isSigned := bitAt word 10
      some (.div w isSigned (decodeRegOrZr rdN) (decodeRegOrZr rnN)
        (decodeRegOrZr rmN))
    -- Data processing 3-source (`MADD`, `MSUB`): `[30:21] = 0011011000`
    else if Nat.beq (bits word 21 10) 0x0D8 then
      let isSub := bitAt word 15
      let raN := bits word 10 5
      some (.maddSub w isSub (decodeRegOrZr rdN) (decodeRegOrZr rnN)
        (decodeRegOrZr rmN) (decodeRegOrZr raN))
    else none

/-- Decode GP & SIMD/FP Loads and Stores plus Advanced SIMD `LD1`/`ST1`. -/
@[expose] def decodeLoadStore (relocs : List AArch64Reloc) (off word : Nat) :
    Option DecodedInsn :=
  let rtN := bits word 0 5
  let rnN := bits word 5 5
  let rnSp := decodeRegOrSp rnN
  -- 1. Advanced SIMD LD1/ST1 multiple structures (no offset):
  -- `[31] = 0, [29:23] = 0011000, [21:16] = 000000`
  if !bitAt word 31 && Nat.beq (bits word 23 7) 0x18 &&
     Nat.beq (bits word 16 6) 0 then
    if hasAnyRelocAt relocs off then none
    else
      let isQ := bitAt word 30
      let isLoad := bitAt word 22
      let opcode := bits word 12 4
      let size := bits word 10 2
      let numRegs? :=
        match opcode with
        | 0x7 => some 1
        | 0xA => some 2
        | 0x6 => some 3
        | 0x2 => some 4
        | _ => none
      match numRegs? with
      | none => none
      | some nr =>
        some (.simdLdSt1 isLoad isQ nr size (vregOfNatMod32 rtN) rnSp .none)
  -- 2. Advanced SIMD LD1/ST1 multiple structures (post-index):
  -- `[31] = 0, [29:23] = 0011001, [21] = 0`
  else if !bitAt word 31 && Nat.beq (bits word 23 7) 0x19 &&
          !bitAt word 21 then
    if hasAnyRelocAt relocs off then none
    else
      let isQ := bitAt word 30
      let isLoad := bitAt word 22
      let rmN := bits word 16 5
      let opcode := bits word 12 4
      let size := bits word 10 2
      let numRegs? :=
        match opcode with
        | 0x7 => some 1
        | 0xA => some 2
        | 0x6 => some 3
        | 0x2 => some 4
        | _ => none
      match numRegs? with
      | none => none
      | some nr =>
        let post :=
          match gprOfNat? rmN with
          | none => SimdPostIdx.imm (simdLdSt1Bytes isQ nr)
          | some rm => SimdPostIdx.reg rm
        some (.simdLdSt1 isLoad isQ nr size (vregOfNatMod32 rtN) rnSp post)
  -- 3. Load/Store Register Pair (`LDP`/`STP` GP & SIMD/FP):
  -- `[29:27] = 101`, `[25:23] ∈ {001 post, 010 signed, 011 pre}`
  else if Nat.beq (bits word 27 3) 5 &&
          (Nat.beq (bits word 23 3) 1 || Nat.beq (bits word 23 3) 2 ||
           Nat.beq (bits word 23 3) 3) then
    if hasAnyRelocAt relocs off then none
    else
      let opc := bits word 30 2
      let isSimd := bitAt word 26
      let modeN := bits word 23 3
      let isLoad := bitAt word 22
      let s7 := sextBits 7 (bits word 15 7)
      let rt2N := bits word 10 5
      if !isSimd then
        if Nat.beq opc 1 || Nat.beq opc 3 then none
        else
          let is64 := Nat.beq opc 2
          let scale : Nat := if is64 then 8 else 4
          let immBytes := Int.mul s7 (Int.ofNat scale)
          let mode :=
            if Nat.beq modeN 1 then PairAddrMode.postIndex immBytes
            else if Nat.beq modeN 2 then PairAddrMode.signedOff immBytes
            else PairAddrMode.preIndex immBytes
          let isWb := Nat.beq modeN 1 || Nat.beq modeN 3
          if isLoad && Nat.beq rtN rt2N then none
          else if isWb && !Nat.beq rnN 31 &&
                  (Nat.beq rnN rtN || Nat.beq rnN rt2N) then none
          else
            let w := if is64 then RegWidth.x64 else RegWidth.w32
            some (.gpLoadStorePair isLoad w (decodeRegOrZr rtN)
              (decodeRegOrZr rt2N) rnSp mode)
      else
        if Nat.beq opc 3 then none
        else if isLoad && Nat.beq rtN rt2N then none
        else
          let elemBytes : Nat :=
            if Nat.beq opc 0 then 4 else if Nat.beq opc 1 then 8 else 16
          let immBytes := Int.mul s7 (Int.ofNat elemBytes)
          let mode :=
            if Nat.beq modeN 1 then PairAddrMode.postIndex immBytes
            else if Nat.beq modeN 2 then PairAddrMode.signedOff immBytes
            else PairAddrMode.preIndex immBytes
          some (.simdLoadStorePair isLoad elemBytes (vregOfNatMod32 rtN)
            (vregOfNatMod32 rt2N) rnSp mode)
  -- 4. Single-register Load/Store unsigned offset:
  -- `[29:27] = 111, [25:24] = 01`
  else if Nat.beq (bits word 27 3) 7 && Nat.beq (bits word 24 2) 1 then
    let size := bits word 30 2
    let isSimd := bitAt word 26
    let opc := bits word 22 2
    let imm12 := bits word 10 12
    if !isSimd then
      let scale := pow2Nat size
      let immBytes := imm12 * scale
      let decoded? : Option (Bool × Bool × RegWidth) :=
        match size, opc with
        | 0, 0 => some (false, false, .w32)
        | 0, 1 => some (true,  false, .w32)
        | 0, 2 => some (true,  true,  .x64)
        | 0, 3 => some (true,  true,  .w32)
        | 1, 0 => some (false, false, .w32)
        | 1, 1 => some (true,  false, .w32)
        | 1, 2 => some (true,  true,  .x64)
        | 1, 3 => some (true,  true,  .w32)
        | 2, 0 => some (false, false, .w32)
        | 2, 1 => some (true,  false, .w32)
        | 2, 2 => some (true,  true,  .x64)
        | 3, 0 => some (false, false, .x64)
        | 3, 1 => some (true,  false, .x64)
        | _, _ => none
      match decoded? with
      | none => none
      | some (isLoad, signExt, dw) =>
        let reloc? :=
          if isLoad && Nat.beq scale 8 then
            findRelocAt? relocs off .ldst64AbsLo12Nc
          else none
        if hasAnyRelocAt relocs off && reloc?.isNone then none
        else
          some (.gpLoadStore isLoad scale signExt dw (decodeRegOrZr rtN)
            rnSp (.unsignedOff immBytes) reloc?)
    else
      let scale? : Option (Bool × Nat) :=
        match size, opc with
        | 0, 0 => some (false, 1)
        | 0, 1 => some (true,  1)
        | 0, 2 => some (false, 16)
        | 0, 3 => some (true,  16)
        | 1, 0 => some (false, 2)
        | 1, 1 => some (true,  2)
        | 2, 0 => some (false, 4)
        | 2, 1 => some (true,  4)
        | 3, 0 => some (false, 8)
        | 3, 1 => some (true,  8)
        | _, _ => none
      match scale? with
      | none => none
      | some (isLoad, scale) =>
        let immBytes := imm12 * scale
        let reloc? :=
          if isLoad && Nat.beq scale 16 then
            findRelocAt? relocs off .ldst128AbsLo12Nc
          else if isLoad && Nat.beq scale 8 then
            findRelocAt? relocs off .ldst64AbsLo12Nc
          else none
        if hasAnyRelocAt relocs off && reloc?.isNone then none
        else
          some (.simdLoadStore isLoad scale (vregOfNatMod32 rtN) rnSp
            (.unsignedOff immBytes) reloc?)
  -- 5. Single-register Load/Store immediate pre/post-index:
  -- `[29:27] = 111, [25:24] = 00, [21] = 0, [11:10] ∈ {01 post, 11 pre}`
  else if Nat.beq (bits word 27 3) 7 && Nat.beq (bits word 24 2) 0 &&
          !bitAt word 21 &&
          (Nat.beq (bits word 10 2) 1 || Nat.beq (bits word 10 2) 3) then
    if hasAnyRelocAt relocs off then none
    else
      let size := bits word 30 2
      let isSimd := bitAt word 26
      let opc := bits word 22 2
      let s9 := sextBits 9 (bits word 12 9)
      let isPre := Nat.beq (bits word 10 2) 3
      let mode := if isPre then AddrMode.preIndex s9 else AddrMode.postIndex s9
      if !isSimd then
        if !Nat.beq rnN 31 && Nat.beq rnN rtN then none
        else
          let scale := pow2Nat size
          let decoded? : Option (Bool × Bool × RegWidth) :=
            match size, opc with
            | 0, 0 => some (false, false, .w32)
            | 0, 1 => some (true,  false, .w32)
            | 0, 2 => some (true,  true,  .x64)
            | 0, 3 => some (true,  true,  .w32)
            | 1, 0 => some (false, false, .w32)
            | 1, 1 => some (true,  false, .w32)
            | 1, 2 => some (true,  true,  .x64)
            | 1, 3 => some (true,  true,  .w32)
            | 2, 0 => some (false, false, .w32)
            | 2, 1 => some (true,  false, .w32)
            | 2, 2 => some (true,  true,  .x64)
            | 3, 0 => some (false, false, .x64)
            | 3, 1 => some (true,  false, .x64)
            | _, _ => none
          match decoded? with
          | none => none
          | some (isLoad, signExt, dw) =>
            some (.gpLoadStore isLoad scale signExt dw (decodeRegOrZr rtN)
              rnSp mode none)
      else
        let scale? : Option (Bool × Nat) :=
          match size, opc with
          | 0, 0 => some (false, 1)
          | 0, 1 => some (true,  1)
          | 0, 2 => some (false, 16)
          | 0, 3 => some (true,  16)
          | 1, 0 => some (false, 2)
          | 1, 1 => some (true,  2)
          | 2, 0 => some (false, 4)
          | 2, 1 => some (true,  4)
          | 3, 0 => some (false, 8)
          | 3, 1 => some (true,  8)
          | _, _ => none
        match scale? with
        | none => none
        | some (isLoad, scale) =>
          some (.simdLoadStore isLoad scale (vregOfNatMod32 rtN) rnSp mode none)
  else none

/-- Decode Advanced SIMD (NEON) compute instructions (`[28:25] = 0111`). -/
@[expose] def decodeSimdCompute (relocs : List AArch64Reloc) (off word : Nat) :
    Option DecodedInsn :=
  if hasAnyRelocAt relocs off || bitAt word 31 then none
  else
    let isQ := bitAt word 30
    let uBit := bitAt word 29
    let vd := vregOfNatMod32 (bits word 0 5)
    let vn := vregOfNatMod32 (bits word 5 5)
    let vm := vregOfNatMod32 (bits word 16 5)
    -- 1. Advanced SIMD shift by immediate: `[28:23] = 011110`, `immh != 0`,
    -- `[10] = 1`
    if Nat.beq (bits word 23 6) 0x1E && bitAt word 10 then
      let immh := bits word 19 4
      let immb := bits word 16 3
      let opcode := bits word 11 5
      if Nat.beq immh 0 then none
      else
        let sop? : Option SimdShiftOp :=
          match uBit, opcode with
          | false, 0x1F =>
            if Nat.ble 4 immh && !(!isQ && Nat.ble 8 immh) then some .fcvtzs
            else none
          | false, 0x13 =>
            if Nat.blt immh 8 then some .sqrshrn else none
          | true, 0x10 =>
            if Nat.blt immh 8 then some .sqshrun else none
          | true, 0x08 =>
            if !isQ && Nat.ble 8 immh then none else some .sri
          | false, 0x0A =>
            if !isQ && Nat.ble 8 immh then none else some .shl
          | false, 0x00 =>
            if !isQ && Nat.ble 8 immh then none else some .sshr
          | true, 0x00 =>
            if !isQ && Nat.ble 8 immh then none else some .ushr
          | false, 0x04 =>
            if !isQ && Nat.ble 8 immh then none else some .srshr
          | _, _ => none
        match sop? with
        | none => none
        | some sop => some (.simdShiftImm sop isQ immh immb vd vn)
    -- 2. Advanced SIMD three same: `[28:24] = 01110`, `[21] = 1`, `[10] = 1`
    else if Nat.beq (bits word 24 5) 0x0E && bitAt word 21 &&
            bitAt word 10 then
      let size := bits word 22 2
      let opcode := bits word 11 5
      let op? : Option SimdThreeSameOp :=
        match uBit, size, opcode with
        | true,  _, 0x01 =>
          if !isQ && Nat.beq size 3 then none else some .uqadd
        | true,  _, 0x05 =>
          if !isQ && Nat.beq size 3 then none else some .uqsub
        | true,  _, 0x0D =>
          if Nat.beq size 3 then none else some .umin
        | true,  _, 0x0C =>
          if Nat.beq size 3 then none else some .umax
        | false, _, 0x10 =>
          if !isQ && Nat.beq size 3 then none else some .add
        | true,  _, 0x10 =>
          if !isQ && Nat.beq size 3 then none else some .sub
        | false, 0, 0x03 => some .and_
        | false, 1, 0x03 => some .bic
        | false, 2, 0x03 => some .orr
        | true,  0, 0x03 => some .eor
        | _,     _, _    => none
      match op? with
      | none => none
      | some op => some (.simdThreeSame op isQ size vd vn vm)
    -- 3. Advanced SIMD two-reg misc (`CMEQ #0`):
    -- `[28:24]=01110`, `[21:17]=10000`, `[11:10]=10`, `U=0`, `op=01001`
    else if Nat.beq (bits word 24 5) 0x0E && !uBit &&
            Nat.beq (bits word 17 5) 0x10 &&
            Nat.beq (bits word 10 2) 2 &&
            Nat.beq (bits word 12 5) 0x09 then
      let size := bits word 22 2
      if !isQ && Nat.beq size 3 then none
      else some (.simdCmeqZero isQ size vd vn)
    -- 4. Advanced SIMD permute (`UZP1/2`, `TRN1/2`, `ZIP1/2`):
    -- `[29:24] = 001110`, `[21] = 0`, `[15] = 0`, `[11:10] = 10`
    else if !uBit && Nat.beq (bits word 24 5) 0x0E &&
            !bitAt word 21 && !bitAt word 15 &&
            Nat.beq (bits word 10 2) 2 then
      let size := bits word 22 2
      let op3 := bits word 12 3
      if !isQ && Nat.beq size 3 then none
      else
        let pop? : Option SimdPermOp :=
          match op3 with
          | 1 => some .uzp1
          | 2 => some .trn1
          | 3 => some .zip1
          | 5 => some .uzp2
          | 6 => some .trn2
          | 7 => some .zip2
          | _ => none
        match pop? with
        | none => none
        | some pop => some (.simdPerm pop isQ size vd vn vm)
    else none

/-- Decode a single 32-bit AArch64 instruction word at byte offset `off`.
Fail-closed (`none`) on any unallocated, reserved, or unmodeled encoding. -/
@[expose] def decodeWord (cfg : DecodeConfig) (relocs : List AArch64Reloc)
    (off word : Nat) : Option DecodedInsn :=
  let op0 := bits word 25 4
  if Nat.beq (Nat.div op0 2) 4 then
    decodeDpImm cfg relocs off word
  else if Nat.beq (Nat.div op0 2) 5 then
    decodeBranchSys relocs off word
  else if bitAt word 27 && !bitAt word 25 then
    decodeLoadStore relocs off word
  else if bitAt word 27 && !bitAt word 26 && bitAt word 25 then
    decodeDpReg relocs off word
  else if bitAt word 27 && bitAt word 26 && bitAt word 25 then
    decodeSimdCompute relocs off word
  else none

/-! ## 6. Stream Decoder & 1-to-1 Relocation Coverage -/

/-- Relocation offset consumed by a decoded instruction, if any. -/
@[expose] def insnRelocOffset? (i : DecodedInsn) : Option Nat :=
  match i with
  | .addSubImm _ _ _ _ _ _ _ (some r) => some r.offset
  | .pcRelAddr _ _ _ (some r) => some r.offset
  | .gpLoadStore _ _ _ _ _ _ _ (some r) => some r.offset
  | .simdLoadStore _ _ _ _ _ (some r) => some r.offset
  | _ => none

/-- Bounded `@Nat.rec` stream decoder parameterized by a single-word step
function `step off word`. Rejects any trailing bytes (`len % 4 != 0`). -/
@[expose] def decodeStreamWith (step : Nat → Nat → Option DecodedInsn)
    (fuel off : Nat) (bs : List UInt8) :
    Option (List (Nat × DecodedInsn)) :=
  @Nat.rec (fun _ => Nat → List UInt8 → Option (List (Nat × DecodedInsn)))
    (fun _ rem =>
      match rem with
      | [] => some []
      | _ :: _ => none)
    (fun _ ih curOff rem =>
      match rem with
      | [] => some []
      | b0 :: b1 :: b2 :: b3 :: rest =>
        match step curOff (le32Nat b0 b1 b2 b3) with
        | none => none
        | some insn =>
          match ih (curOff + 4) rest with
          | none => none
          | some tail => some ((curOff, insn) :: tail)
      | _ => none)
    fuel off bs

/-- Total AArch64 byte-stream decoder producing `(byteOffset, DecodedInsn)`
pairs. Enforces exact 4-byte word alignment across the entire slice. -/
@[expose] def decodeStream (cfg : DecodeConfig) (relocs : List AArch64Reloc)
    (bs : List UInt8) : Option (List (Nat × DecodedInsn)) :=
  decodeStreamWith (decodeWord cfg relocs) (Nat.div bs.length 4 + 1) 0 bs

/-- Collect the offsets of all relocations consumed by a decoded stream. -/
@[expose] def consumedRelocOffsets (tr : List (Nat × DecodedInsn)) :
    List Nat :=
  List.foldr
    (fun e acc =>
      match insnRelocOffset? e.2 with
      | none => acc
      | some o => o :: acc)
    [] tr

/-- Local stream decode coverage check: every byte in `bs` is decoded as a
4-byte-aligned instruction AND the set of relocation offsets consumed by
decoded instructions matches `relocs` 1-to-1 (no unconsumed or duplicate
relocations). -/
@[expose] def localDecodeCoverageOk (cfg : DecodeConfig)
    (relocs : List AArch64Reloc) (bs : List UInt8) : Bool :=
  match decodeStream cfg relocs bs with
  | none => false
  | some tr =>
    let provided := relocs.map (fun r => r.offset)
    let consumed := consumedRelocOffsets tr
    natListSameSet provided consumed

/-! ## 7. Structural Decoder Theorems (`⊆ {propext}` axioms) -/

/-- `decodeWord` is a pure deterministic function of its inputs. -/
theorem decodeWord_deterministic (cfg : DecodeConfig)
    (relocs : List AArch64Reloc) (off word : Nat) (i1 i2 : DecodedInsn)
    (h1 : decodeWord cfg relocs off word = some i1)
    (h2 : decodeWord cfg relocs off word = some i2) : i1 = i2 := by
  have h : some i1 = some i2 := Eq.trans h1.symm h2
  exact Option.some.inj h

/-- Helper: `(a + 4) % 4 = a % 4` using only `Init.Data.Nat.Div.Basic`. -/
theorem nat_add_mod_four (a : Nat) : Nat.mod (a + 4) 4 = Nat.mod a 4 := by
  have hMod : Nat.mod (a + 4) 4 =
      if 0 < 4 ∧ 4 ≤ a + 4 then Nat.mod (a + 4 - 4) 4 else a + 4 :=
    Nat.mod_eq_ite (a + 4) 4
  rw [hMod]
  have hPos : 0 < 4 := Nat.zero_lt_succ 3
  have hLe : 4 ≤ a + 4 := Nat.le_add_left 4 a
  simp only [hPos, hLe, and_self, ite_true, Nat.add_sub_cancel]

/-- Every instruction decoded by `decodeStreamWith` has byte length 4 and
monotonically increasing offset `off + 4 * idx`. -/
theorem decodeStreamWith_len_and_offsets
    (step : Nat → Nat → Option DecodedInsn) :
    ∀ (fuel off : Nat) (bs : List UInt8) (tr : List (Nat × DecodedInsn)),
      decodeStreamWith step fuel off bs = some tr →
      bs.length = tr.length * 4 ∧
      (∀ e, List.Mem e tr → Nat.mod e.1 4 = Nat.mod off 4) := by
  intro fuel
  induction fuel with
  | zero =>
    intro off bs tr h
    cases bs with
    | nil =>
      change some [] = some tr at h
      have ht : [] = tr := Option.some.inj h
      subst ht
      exact ⟨rfl, fun _ hm => by cases hm⟩
    | cons _ _ =>
      change none = some tr at h
      cases h
  | succ k ih =>
    intro off bs tr h
    cases bs with
    | nil =>
      change some [] = some tr at h
      have ht : [] = tr := Option.some.inj h
      subst ht
      exact ⟨rfl, fun _ hm => by cases hm⟩
    | cons b0 r1 =>
      cases r1 with
      | nil => change none = some tr at h; cases h
      | cons b1 r2 =>
        cases r2 with
        | nil => change none = some tr at h; cases h
        | cons b2 r3 =>
          cases r3 with
          | nil => change none = some tr at h; cases h
          | cons b3 rest =>
            change
              (match step off (le32Nat b0 b1 b2 b3) with
               | none => none
               | some insn =>
                 match decodeStreamWith step k (off + 4) rest with
                 | none => none
                 | some tail => some ((off, insn) :: tail)) = some tr at h
            cases hd : step off (le32Nat b0 b1 b2 b3) with
            | none =>
              rw [hd] at h
              change none = some tr at h
              cases h
            | some insn =>
              rw [hd] at h
              cases ht : decodeStreamWith step k (off + 4) rest with
              | none =>
                rw [ht] at h
                change none = some tr at h
                cases h
              | some tail =>
                rw [ht] at h
                change some ((off, insn) :: tail) = some tr at h
                have hEq : (off, insn) :: tail = tr := Option.some.inj h
                subst hEq
                have hRec := ih (off + 4) rest tail ht
                refine ⟨?_, ?_⟩
                · simp only [List.length_cons, Nat.succ_mul]
                  exact congrArg (· + 4) hRec.1
                · intro e he
                  cases he with
                  | head => rfl
                  | tail _ hmem =>
                    have hMod := hRec.2 e hmem
                    exact Eq.trans hMod (nat_add_mod_four off)

/-- Any byte stream accepted by `decodeStream` has length `4 * tr.length` and
every instruction starts at a 4-byte aligned offset (`off % 4 = 0`). -/
theorem decodeStream_aligned (cfg : DecodeConfig) (relocs : List AArch64Reloc)
    (bs : List UInt8) (tr : List (Nat × DecodedInsn))
    (h : decodeStream cfg relocs bs = some tr) :
    bs.length = tr.length * 4 ∧ (∀ e, List.Mem e tr → Nat.mod e.1 4 = 0) :=
  decodeStreamWith_len_and_offsets (decodeWord cfg relocs)
    (Nat.div bs.length 4 + 1) 0 bs tr h

end Anneal.ElfAArch64
