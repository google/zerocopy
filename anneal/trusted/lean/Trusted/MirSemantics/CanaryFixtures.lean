-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Boundary

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Pass 1 Non-Vacuity Canary Fixtures (`Trusted.MirSemantics.CanaryFixtures`)

Trusted concrete programs, queries, and helper propositions referenced by the
locked Pass 1 `*Claim` definitions in `Trusted.MirSemantics` and Pass 2 canaries
in `Trusted.Correspondence`.
-/

/-- Standard positive canary proposition: `(p, q)` is well-formed and returns
`expectedRet` with empty `callerMem`. -/
noncomputable def PositiveCanaryClaim (p : Program) (q : Query)
    (expectedRet : Val) : Prop :=
  WellFormed p q ∧ Behavior p q (.returned ⟨expectedRet, ⟨[]⟩⟩)

/-- Standard negative fault canary proposition: `(p, q)` reaches
`.fault expectedFault`, does not reach `.fault otherFault`, and is not
`WellFormed`. -/
noncomputable def NegativeCanaryClaim (p : Program) (q : Query)
    (expectedFault otherFault : FaultKind) : Prop :=
  ReachesResult p q (.fault expectedFault) ∧
  ¬ ReachesResult p q (.fault otherFault) ∧
  ¬ WellFormed p q

/-- `u32` type descriptor (`IntWidth.i32`, unsigned). -/
noncomputable def u32Ty : MirTy := .int .i32 false

/-- `u8` type descriptor (`IntWidth.i8`, unsigned). -/
noncomputable def u8Ty : MirTy := .int .i8 false

/-- `i8` type descriptor (`IntWidth.i8`, signed). -/
noncomputable def i8Ty : MirTy := .int .i8 true

/-- Construct a scalar `Val` of width `w` and signedness `s` from raw bit
pattern `bits : Nat`. -/
noncomputable def scalarNatVal (w : IntWidth) (s : Bool) (bits : Nat) : Val :=
  .scalar ⟨w, s, BitVec.ofNat 128 bits⟩

/-- Construct a `u32` scalar `Val` from `n : Nat`. -/
noncomputable def u32Val (n : Nat) : Val := scalarNatVal .i32 false n

/-- Construct an `i8` scalar `Val` from its raw 8-bit unsigned
representation. -/
noncomputable def i8Val (bits : Nat) : Val := scalarNatVal .i8 true bits

/-- Construct a `u8` scalar `Val` from `n : Nat`. -/
noncomputable def u8Val (n : Nat) : Val := scalarNatVal .i8 false n

/-- Single-block binary-operator test program:
`fn binop(a: lhsTy, b: rhsTy) -> retTy { _0 = op(copy _1, copy _2); return }` -/
noncomputable def mkBinOpProg (op : BinOp) (retTy lhsTy rhsTy : MirTy) :
    Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [retTy, lhsTy, rhsTy]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp op (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Single-block unary-operator test program:
`fn unop(a: ty) -> ty { _0 = op(copy _1); return }` -/
noncomputable def mkUnOpProg (op : UnOp) (ty : MirTy) : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [ty, ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.unaryOp op (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Canary `D1` (`ok` pole):
`fn add(a: u32, b: u32) -> u32 { _0 = a + b; return }` -/
noncomputable def progAddU32 : Program :=
  mkBinOpProg .add u32Ty u32Ty u32Ty

/-- Input query `(30u32, 12u32)` for `progAddU32`. -/
noncomputable def queryAdd30_12 : Query :=
  { args := [u32Val 30, u32Val 12] }

/-- Canary `D2` (`ok` pole):
`fn empty() { return }` (`_0 : ()` live-initialized as a 0-byte ZST). -/
noncomputable def progEmptyUnitFn : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := []
      terminator := .return_
    }]
  }]

/-- Empty input query `()` for 0-argument test programs. -/
noncomputable def queryEmpty : Query := { args := [] }

/-- Multi-block control-flow and statement canary program exercising
`StatementKind.nop`, `StatementKind.storageLive`, `StatementKind.storageDead`
(followed by re-allocation via `storageLive` and assignment),
`TerminatorKind.goto`, and `TerminatorKind.switchInt` across both a matched
branch arm (`10u32 -> bb2 -> 100u32`) and the `otherwise` fallback arm
(`_ -> bb3 -> 200u32`). -/
noncomputable def progStmtsAndCf : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    basicBlocks := [
      -- bb0: nop, StorageLive(_2), StorageDead(_2), StorageLive(_2),
      -- _2 = copy _1, Goto(bb1)
      {
        statements := [
          .nop,
          .storageLive 2,
          .storageDead 2,
          .storageLive 2,
          .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))
        ]
        terminator := .goto 1
      },
      -- bb1: SwitchInt(move _2) [10 -> bb2, otherwise -> bb3]
      {
        statements := []
        terminator := .switchInt (.move ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 10, 2)]
          otherwise := 3
        }
      },
      -- bb2 (matched branch): _0 = const 100u32; StorageDead(_2); Return
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 100)⟩)),
          .storageDead 2
        ]
        terminator := .return_
      },
      -- bb3 (otherwise branch): _0 = const 200u32; StorageDead(_2); Return
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 200)⟩)),
          .storageDead 2
        ]
        terminator := .return_
      }
    ]
  }]

/-- Helper proposition for a single integer width `w`:
1. Unsigned `MAX + 1` wraps modulo $2^{\text{bitWidth}}$ to `0`.
2. Signed `INT_MAX + 1` wraps to `INT_MIN` (`2^(bitWidth - 1)`). -/
noncomputable def IntWidthBoundaryCanary (w : IntWidth) : Prop :=
  let uTy : MirTy := .int w false
  let sTy : MirTy := .int w true
  let uMax : Nat := Nat.pow 2 w.bitWidth - 1
  let sMax : Nat := Nat.pow 2 (w.bitWidth - 1) - 1
  let sMinBits : Nat := Nat.pow 2 (w.bitWidth - 1)
  PositiveCanaryClaim (mkBinOpProg .add uTy uTy uTy)
    { args := [scalarNatVal w false uMax, scalarNatVal w false 1] }
    (scalarNatVal w false 0) ∧
  PositiveCanaryClaim (mkBinOpProg .add sTy sTy sTy)
    { args := [scalarNatVal w true sMax, scalarNatVal w true 1] }
    (scalarNatVal w true sMinBits)

/-- Canary `D3` (`undefined` pole):
`fn div_zero(a: u32) -> u32 { _0 = a / 0; return }` -/
noncomputable def progDivByZero : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Input query `(10u32)` for `progDivByZero`. -/
noncomputable def queryDivByZero : Query := { args := [u32Val 10] }

/-- Canary `D4` (`undefined` pole):
signed `(-128i8) % (-1i8)` remainder overflow UB. -/
noncomputable def progSignedRemOverflowI8 : Program :=
  mkBinOpProg .rem i8Ty i8Ty i8Ty

/-- Input query `(-128i8, -1i8)` for `progSignedRemOverflowI8`. -/
noncomputable def querySignedRemOverflowI8 : Query :=
  { args := [i8Val 128, i8Val 255] }

/-- Canary `D5` (`unsupported` pole):
unmodeled statement `.unsupported` steps to `.fault .unsupported`. -/
noncomputable def progUnsupported : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := [.unsupported]
      terminator := .return_
    }]
  }]

/-- Unchecked-overflow canary program (`undefined` pole):
`fn add_unchecked(a: u32, b: u32) -> u32 { _0 = AddUnchecked(a, b); return }` -/
noncomputable def progAddUncheckedU32 : Program :=
  mkBinOpProg .addUnchecked u32Ty u32Ty u32Ty

/-- Input query `(u32::MAX, 1u32)`, whose mathematical sum overflows `u32`. -/
noncomputable def queryU32MaxPlusOne : Query :=
  { args := [u32Val 4294967295, u32Val 1] }

/-- Program reading a local after `StatementKind.storageDead`:
`StorageLive(_1); _1 = const 7u32; StorageDead(_1); _0 = copy _1; return`. -/
noncomputable def progStorageDeadReadUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .storageDead 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Memory-lifecycle program (`CanaryMemoryLifecycleAnnealClaim`):
`fn f(_1: u32) -> u32 { StorageLive(_2); _2 = copy _1; _0 = copy _2;
StorageDead(_2); return }`. -/
noncomputable def progMemLifecycle : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩)),
        .storageDead 2
      ]
      terminator := .return_
    }]
  }]

/-- Input query `(0x01020304u32)` for `progMemLifecycle`, whose four bytes are
distinct so the canary pins their order in memory. -/
noncomputable def queryMemLifecycle : Query :=
  { args := [u32Val 16909060] }

/-- Uninitialized-read program (`CanaryMemoryLifecycleAnnealClaim`):
`fn f() -> u32 { StorageLive(_1); _0 = copy _1; return }`. -/
noncomputable def progMemUninitRead : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Program executing `StatementKind.storageDead 0` on the return place `_0`. -/
noncomputable def progStorageDeadReturnPlaceUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := [.storageDead 0]
      terminator := .return_
    }]
  }]

/-- Program executing `TerminatorKind.unreachable`. -/
noncomputable def progUnreachableUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := []
      terminator := .unreachable
    }]
  }]

/-- Explicit-repr fieldless enum `#[repr(u8)] enum ReprU8 { A = 10, B = 20 }`
with non-index discriminants and `u8` discriminant/tag width. -/
noncomputable def canaryReprU8EnumTy : EnumTy := {
  id := 1
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [10, 20]
}

/-- Signed-tag fieldless enum `enum SignedTag { Neg = -1, Pos = 1 }` with 1-byte
signed `i8` in-memory tag (`0xff = 255` for `-1`) and 64-bit signed `isize`
discriminant (`2^64 - 1`). -/
noncomputable def canarySignedTagEnumTy : EnumTy := {
  id := 2
  discrWidth := .isize
  discrSigned := true
  tagRepr := .scalar .i8 true
  discriminants := [Nat.pow 2 64 - 1, 1]
}

/-- Positive canary program decoding `const ReprU8::B` (`.scalar 20`, variant 1)
and reading `Rvalue.discriminant` into a `u8` return place `_0`. -/
noncomputable def progEnumExplicitReprU8 : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .enum canaryReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant
          ⟨.enum canaryReprU8EnumTy, .scalar (BitVec.ofNat 128 20)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- Positive canary program decoding `const SignedTag::Neg` (1-byte signed tag
`0xff = 255`, sign-extended to `-1isize = 2^64 - 1`) and reading
`Rvalue.discriminant` into an `isize` return place `_0`. -/
noncomputable def progEnumSignedTagIsize : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.int .isize true, .enum canarySignedTagEnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant
          ⟨.enum canarySignedTagEnumTy, .scalar (BitVec.ofNat 128 255)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- Single-variant inhabited ZST fieldless enum `enum Single { Only = 42 }`
(`Variants::Single { index: 0 }`, `Size::ZERO`). -/
noncomputable def canarySingleZstEnumTy : EnumTy := {
  id := 3
  discrWidth := .isize
  discrSigned := true
  tagRepr := .zeroSized
  discriminants := [42]
}

/-- Positive canary `fn() -> Single { return }` returning an inhabited ZST
1-variant enum without an explicit assignment to `_0`. -/
noncomputable def progZstSingleEnumImplicitRet : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.enum canarySingleZstEnumTy]
    basicBlocks := [{
      statements := []
      terminator := .return_
    }]
  }]

/-- Positive canary exercising `StorageLive`, `Operand.move` (non-deinitializing
on ZST), `ConstLit.zeroSized`, and `Rvalue.discriminant` on `Single`. -/
noncomputable def progZstSingleEnumMoveAndDiscr : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [
      .int .isize true,
      .enum canarySingleZstEnumTy,
      .enum canarySingleZstEnumTy,
      .enum canarySingleZstEnumTy
    ]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .storageLive 2,
        .storageLive 3,
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.use (.constant
          ⟨.enum canarySingleZstEnumTy, .zeroSized⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 3,
        .storageDead 2,
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- Negative UB canary: `ConstLit.scalar 1` on `ReprU8 { A = 10, B = 20 }` is an
invalid enum tag (not variant index 1!) and faults with `.undefined`. -/
noncomputable def progEnumInvalidTagConstUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .enum canaryReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩ (.use (.constant
          ⟨.enum canaryReprU8EnumTy, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)
      ]
      terminator := .return_
    }]
  }]

/-- Negative UB canary: reading `Rvalue.discriminant` from an uninitialized
scalar-tagged enum local faults with `.undefined`. -/
noncomputable def progEnumUninitDiscrUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u8Ty, .enum canaryReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)
      ]
      terminator := .return_
    }]
  }]

/-- Indirect-operations program (`CanaryMemoryLifecycleAnnealClaim`):
`fn f(_1: u32) -> u32 { _0 = move _1; StorageLive(_1); return }`. With `_1`
and `_0` moved into memory, it moves out of an `.indirect` local, writes an
`.indirect` local, re-runs `StorageLive` on an `.indirect` local, and returns
from an `.indirect` `_0`. -/
noncomputable def progMemIndirectOps : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)),
        .storageLive 1
      ]
      terminator := .return_
    }]
  }]

/-- Ill-typed copy program (`CanaryMemoryLifecycleAnnealClaim`):
`fn f() -> u32 { StorageLive(_1); _0 = copy _1; return }` with `_1: bool`.
The `bool` source does not match the `u32` destination. -/
noncomputable def progMemIllTypedUse : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, .bool]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Non-primitive operand program (`CanaryMemoryLifecycleAnnealClaim`):
`fn f() -> bool { StorageLive(_1); _0 = Not(copy _1); return }` with
`_1: ReprU8`. An enum is not primitive-readable, so `Not` cannot read it. -/
noncomputable def progMemNonPrimitiveUnOp : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.bool, .enum canaryReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨0, []⟩ (.unaryOp .not (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Construct a `char` `Val` from its Unicode scalar value `n`. -/
noncomputable def charVal (n : Nat) : Val := .char (Char.ofNat n)

/-- The `(T, bool)` result type of `BinOp::{Add,Sub,Mul}WithOverflow` on the
integer type `ty`. -/
noncomputable def overflowPairTy (ty : MirTy) : MirTy := .tuple [ty, .bool]

/-- Single-block integer-cast test program:
`fn cast(a: srcTy) -> dstTy { _0 = copy _1 as dstTy (IntToInt); return }` -/
noncomputable def mkIntToIntCastProg (srcTy dstTy : MirTy) : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [dstTy, srcTy]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) dstTy)
      ]
      terminator := .return_
    }]
  }]

/-- Three-way comparison followed by a discriminant read:
`fn f(a: ty, b: ty) -> i8 { _3 = Cmp(copy _1, copy _2);
_0 = discriminant(_3); return }` -/
noncomputable def mkCmpDiscriminantProg (ty : MirTy) : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 2
    locals := [i8Ty, ty, ty, .ordering]
    basicBlocks := [{
      statements := [
        .assign ⟨3, []⟩ (.binaryOp .cmp (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨3, []⟩)
      ]
      terminator := .return_
    }]
  }]

/-- `char` switch program:
`fn f(c: char) -> u32 { switchInt(copy _1) -> [97 ('a'): bb1, otherwise: bb2] }`
where `bb1` returns `1u32` and `bb2` returns `2u32`. -/
noncomputable def progCharSwitch : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, .char]
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 97, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- Negative UB canary: the surrogate code point `0xD800` is not a Unicode
scalar value, so the constant `_0 = const 0xD800 as char` is an invalid `char`
and faults with `.undefined`. -/
noncomputable def progInvalidCharConstUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.char]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩
          (.use (.constant ⟨.char, .scalar (BitVec.ofNat 128 0xd800)⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Negative UB canary: a `char` switch whose case value `0xD800` is not a
Unicode scalar value faults with `.undefined` when the case is compared. -/
noncomputable def progInvalidCharSwitchCaseUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, .char]
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0xd800, 1)]
          otherwise := 1
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- Negative UB canary: casting an uninitialized `u8` local
(`fn f() -> u32 { StorageLive(_1); _0 = copy _1 as u32; return }`) faults with
`.undefined`. -/
noncomputable def progCastUninitSourceUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u8Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) u32Ty)
      ]
      terminator := .return_
    }]
  }]

/-- Safe 0-arg unit body for `CanaryCrateAndBodyVerifiedAnnealClaim`. -/
noncomputable def canarySafeUnitBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "canary::safe_unit"
}

/-- `unsafe fn(flag: bool) -> u32` body that returns `42` when `flag = true` and
executes `unreachable` when `flag = false`. -/
noncomputable def canaryUnsafeGuardedBody (isUnsafeFlag : Bool) : Body := {
  argumentCount := 1
  locals := [u32Ty, .bool]
  basicBlocks := [
    {
      statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) {
        branches := [(BitVec.ofNat 128 1, 1)]
        otherwise := 2
      }
    },
    {
      statements := [
        .assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
      ]
      terminator := .return_
    },
    {
      statements := []
      terminator := .unreachable
    }
  ]
  isUnsafe := isUnsafeFlag
  identity := "canary::unsafe_guarded"
}

/-- Safe `fn(x: !) -> ()` body exercising uninhabited `MirTy.never` parameter
verification while enforcing `BodyStaticAdmitted`. -/
noncomputable def canaryNeverParamBody (badStorage : Bool) : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{
    statements := if badStorage then [.storageLive 9] else []
    terminator := .unreachable
  }]
  isUnsafe := false
  identity := "canary::never_param"
}

/-- Valid 3-body crate combining a safe body (with `safety = False` ignored),
an `unsafe` body guarded by `safety`, and an uninhabited `!`-parameter body. -/
noncomputable def canaryValidCrate : Crate := {
  program := {
    scope := .crate
    pointerWidthBits := 64
    mirProfileVersion := 1
    bodies := [
      canarySafeUnitBody,
      canaryUnsafeGuardedBody true,
      canaryNeverParamBody false
    ]
  }
  specs := {
    safety := fun id args =>
      if stringBeq id "canary::unsafe_guarded" then
        args = [.bool true]
      else
        False
    property := fun p => Nat.beq p.bodies.length 3 = true
  }
}

end Trusted.MirSemantics

end
