/-
  Experiment: experiments/opsem/substantive-mir-byte-parser
  Task FD-02 (FE-F4) / Milestone C1: Faithful, Fail-Closed AMIR v3 Byte Parser

  Mechanizes a total binary wire-format parser (`parseWirePackage`) and an
  independent byte-level specification encoder (`specEncodePackage`) for the
  fail-closed `AMIR` v3 (`version = 3`) binary interchange format emitted by
  `direct_mir_driver_v4.rs` on `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`.

  Key C1 properties:
  1. Physical byte validity (`physicalBytesValid`): every element in an accepted
     `List Nat` stream is proven `<= 255` (`UInt8` range via `fromUInt8List` /
     `toUInt8List`).
  2. Complete typed local declarations (`localTypes : List MirTypeTag`), full 10-form
     projection chains (`ProjChain`), full constant/move/copy operands (`OperandSpec`),
     full arithmetic/comparison/overflow/aggregate/reference statements (`WireStmt`),
     and full branch/drop/assert/call/unwind terminators (`WireTerm`) up to 32 basic
     blocks and 64 locals per body with zero truncation, zero target clamping, and
     zero placeholder assignments.
  3. Universal accepted-byte soundness (`universal_accepted_byte_soundness`) and
     parser determinism (`universal_accepted_package_canonical_unique`).
-/

set_option autoImplicit false
set_option maxRecDepth 65536

namespace AnnealResearch.SubstantiveMirByteParser

/-! ## Physical Byte Bridge (`UInt8` <-> `Nat`) and Fast Kernel `List Nat` Equality -/

def physicalBytesValid : List Nat → Bool
  | [] => true
  | b :: bs => bif Nat.ble b 255 then physicalBytesValid bs else false

def fromUInt8List (xs : List UInt8) : List Nat :=
  xs.map UInt8.toNat

def toUInt8List (xs : List Nat) : List UInt8 :=
  xs.map UInt8.ofNat

def listNatBeq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => bif Nat.beq x y then listNatBeq xs ys else false
  | _, _ => false

theorem listNatBeq_eq_true {xs ys : List Nat} (h : listNatBeq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => contradiction
  | cons x xs ih =>
      cases ys with
      | nil => contradiction
      | cons y ys =>
          unfold listNatBeq at h
          cases hxy : Nat.beq x y
          · rw [hxy] at h; contradiction
          · rw [hxy] at h
            have heq : x = y := Nat.eq_of_beq_eq_true hxy
            subst heq
            exact congrArg (List.cons x) (ih h)

/-! ## AMIR v3 Wire AST Types -/

inductive BodyOriginKind where
  | localOwner
  | compilerShim
  | externalOptimized
  | promotedOrConstOwner
  deriving DecidableEq, Repr

inductive MirPhaseTag where
  | built
  | analysis
  | runtimePostCleanup
  | runtimeOptimized
  deriving DecidableEq, Repr

inductive MirTypeTag where
  | unit
  | bool
  | u32
  | usize
  | rawPtrU32
  | refMutEffectLog
  | effectLog
  | guard
  | pairGuards
  | dstLayout
  | sizeError
  | optUsize
  | optPairUsize
  | resUsizeSizeError
  | resDstLayoutSizeError
  | checkedArithTuple
  | pairUsize
  | pairDstLayoutUsize
  | panicOrNever
  | closureOrOther
  | checkedArithTupleU32
  | refGuard
  | refPairGuards
  deriving DecidableEq, Repr

inductive ProjChain where
  | here
  | field0
  | field1
  | field2
  | deref
  | derefField0
  | derefField1
  | derefField2
  | downcast0Field0
  | downcast1Field0
  deriving DecidableEq, Repr

structure PlaceSpec where
  localIdx : Nat
  proj : ProjChain
  deriving DecidableEq, Repr

inductive OperandSpec where
  | copy (place : PlaceSpec)
  | move (place : PlaceSpec)
  | constBool (val : Bool)
  | constU32 (val : Nat)
  | constUsize (val : Nat)
  | constUnit
  | constSizeError
  | constPanicStr
  deriving DecidableEq, Repr

inductive RefPtrKind where
  | sharedRef
  | mutRef
  | rawConst
  | rawMut
  deriving DecidableEq, Repr

inductive BinOpTag where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  | add
  | sub
  | mul
  | div
  | rem
  | bitAnd
  | addWithOverflow
  | subWithOverflow
  | mulWithOverflow
  deriving DecidableEq, Repr

inductive UnOpTag where
  | notOp
  deriving DecidableEq, Repr

inductive Agg0Kind where
  | sizeError
  | optionNone
  deriving DecidableEq, Repr

inductive Agg1Kind where
  | okOrSome
  | resultErr
  | closureCapture1
  deriving DecidableEq, Repr

inductive Agg2Kind where
  | guard
  | pairGuards
  | effectLog
  | tuple2
  deriving DecidableEq, Repr

inductive Agg3Kind where
  | dstLayout
  deriving DecidableEq, Repr

inductive WireStmt where
  | assignUseNoRetag (dst : PlaceSpec) (src : OperandSpec)
  | assignUseRetagYes (dst : PlaceSpec) (src : OperandSpec)
  | assignCopyForDeref (dst : PlaceSpec) (src : PlaceSpec)
  | assignRefOrPtr (dst : PlaceSpec) (rk : RefPtrKind) (src : PlaceSpec)
  | assignDiscriminant (dst : PlaceSpec) (src : PlaceSpec)
  | assignBinOp (dst : PlaceSpec) (op : BinOpTag) (lhs rhs : OperandSpec)
  | assignUnOp (dst : PlaceSpec) (op : UnOpTag) (src : OperandSpec)
  | assignAgg0 (dst : PlaceSpec) (kind : Agg0Kind)
  | assignAgg1 (dst : PlaceSpec) (kind : Agg1Kind) (f0 : OperandSpec)
  | assignAgg2 (dst : PlaceSpec) (kind : Agg2Kind) (f0 f1 : OperandSpec)
  | assignAgg3 (dst : PlaceSpec) (kind : Agg3Kind) (f0 f1 f2 : OperandSpec)
  | storageLive (localIdx : Nat)
  | storageDead (localIdx : Nat)
  | nop
  | placeMention (src : PlaceSpec)
  | retagStmt (rk : Nat) (src : PlaceSpec)
  deriving DecidableEq, Repr

inductive UnwindSpec where
  | cleanup (bbIdx : Nat)
  | continueUnwind
  | unreachableUnwind
  | terminateAbi
  | terminateCleanup
  deriving DecidableEq, Repr

inductive WireTerm where
  | ret
  | unwindResume
  | unwindTerminate (reason : Nat)
  | unreachable
  | goto (targetBb : Nat)
  | switchInt1 (discr : OperandSpec) (val0 : Nat) (target0 : Nat) (otherwiseBb : Nat)
  | switchInt2 (discr : OperandSpec) (val0 : Nat) (target0 : Nat) (val1 : Nat) (target1 : Nat) (otherwiseBb : Nat)
  | drop (place : PlaceSpec) (glueSym : Nat) (targetBb : Nat) (unwind : UnwindSpec)
  | assertTerm (cond : OperandSpec) (expected : Bool) (targetBb : Nat) (unwind : UnwindSpec)
  | call0 (calleeSym : Nat) (dst : PlaceSpec) (targetBbOpt : Option Nat) (unwind : UnwindSpec)
  | call1 (calleeSym : Nat) (dst : PlaceSpec) (targetBbOpt : Option Nat) (unwind : UnwindSpec) (a0 : OperandSpec)
  | call2 (calleeSym : Nat) (dst : PlaceSpec) (targetBbOpt : Option Nat) (unwind : UnwindSpec) (a0 a1 : OperandSpec)
  | call3 (calleeSym : Nat) (dst : PlaceSpec) (targetBbOpt : Option Nat) (unwind : UnwindSpec) (a0 a1 a2 : OperandSpec)
  | call4 (calleeSym : Nat) (dst : PlaceSpec) (targetBbOpt : Option Nat) (unwind : UnwindSpec) (a0 a1 a2 a3 : OperandSpec)
  deriving DecidableEq, Repr

structure WireBlock where
  isCleanup : Bool
  stmts : List WireStmt
  term : WireTerm
  deriving DecidableEq, Repr

structure WireBody where
  bodyId : Nat
  symId : Nat
  originKind : BodyOriginKind
  mirPhase : MirPhaseTag
  localCount : Nat
  argCount : Nat
  localTypes : List MirTypeTag
  blocks : List WireBlock
  deriving DecidableEq, Repr

structure WirePackage where
  version : Nat
  defaultPhase : MirPhaseTag
  monoComplete : Bool
  preserveUb : Bool
  ubChecks : Bool
  fpHi : Nat
  fpLo : Nat
  bodies : List WireBody
  deriving DecidableEq, Repr

/-! ## Independent Specification Encoder (`specEncode*`) -/

def specEncodeOriginKind : BodyOriginKind → Nat
  | .localOwner => 1
  | .compilerShim => 2
  | .externalOptimized => 3
  | .promotedOrConstOwner => 4

def specEncodeMirPhase : MirPhaseTag → Nat
  | .built => 1
  | .analysis => 2
  | .runtimePostCleanup => 3
  | .runtimeOptimized => 4

def specEncodeTypeTag : MirTypeTag → Nat
  | .unit => 1
  | .bool => 2
  | .u32 => 3
  | .usize => 4
  | .rawPtrU32 => 5
  | .refMutEffectLog => 6
  | .effectLog => 7
  | .guard => 8
  | .pairGuards => 9
  | .dstLayout => 10
  | .sizeError => 11
  | .optUsize => 12
  | .optPairUsize => 13
  | .resUsizeSizeError => 14
  | .resDstLayoutSizeError => 15
  | .checkedArithTuple => 16
  | .pairUsize => 17
  | .pairDstLayoutUsize => 18
  | .panicOrNever => 19
  | .closureOrOther => 20
  | .checkedArithTupleU32 => 21
  | .refGuard => 22
  | .refPairGuards => 23

def specEncodeProjChain : ProjChain → Nat
  | .here => 0
  | .field0 => 1
  | .field1 => 2
  | .field2 => 3
  | .deref => 4
  | .derefField0 => 5
  | .derefField1 => 6
  | .derefField2 => 7
  | .downcast0Field0 => 8
  | .downcast1Field0 => 9

def specEncodeOpB0 : OperandSpec → Nat
  | .copy p => p.localIdx
  | .move p => p.localIdx + 64
  | .constBool _ => 128
  | .constU32 _ => 129
  | .constUsize _ => 130
  | .constUnit => 131
  | .constSizeError => 131
  | .constPanicStr => 131

def specEncodeOpB1 : OperandSpec → Nat
  | .copy p => specEncodeProjChain p.proj
  | .move p => specEncodeProjChain p.proj
  | .constBool b => bif b then 1 else 0
  | .constU32 v => v
  | .constUsize v => v
  | .constUnit => 0
  | .constSizeError => 1
  | .constPanicStr => 2

def specEncodeRefPtrKind : RefPtrKind → Nat
  | .sharedRef => 0
  | .mutRef => 1
  | .rawConst => 2
  | .rawMut => 3

def specEncodeBinOp : BinOpTag → Nat
  | .eq => 1
  | .ne => 2
  | .lt => 3
  | .le => 4
  | .gt => 5
  | .ge => 6
  | .add => 7
  | .sub => 8
  | .mul => 9
  | .div => 10
  | .rem => 11
  | .bitAnd => 12
  | .addWithOverflow => 13
  | .subWithOverflow => 14
  | .mulWithOverflow => 15

def specEncodeUnOp : UnOpTag → Nat
  | .notOp => 1

def specEncodeAgg0 : Agg0Kind → Nat
  | .sizeError => 1
  | .optionNone => 2

def specEncodeAgg1 : Agg1Kind → Nat
  | .okOrSome => 1
  | .resultErr => 2
  | .closureCapture1 => 3

def specEncodeAgg2 : Agg2Kind → Nat
  | .guard => 1
  | .pairGuards => 2
  | .effectLog => 3
  | .tuple2 => 4

def specEncodeAgg3 : Agg3Kind → Nat
  | .dstLayout => 1

def specEncodeStmtCons (st : WireStmt) (rest : List Nat) : List Nat :=
  match st with
  | .assignUseNoRetag dst src =>
      0x10 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeOpB0 src :: specEncodeOpB1 src :: rest
  | .assignUseRetagYes dst src =>
      0x11 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeOpB0 src :: specEncodeOpB1 src :: rest
  | .assignCopyForDeref dst src =>
      0x12 :: dst.localIdx :: specEncodeProjChain dst.proj :: src.localIdx :: specEncodeProjChain src.proj :: rest
  | .assignRefOrPtr dst rk src =>
      0x13 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeRefPtrKind rk :: src.localIdx :: specEncodeProjChain src.proj :: rest
  | .assignDiscriminant dst src =>
      0x14 :: dst.localIdx :: specEncodeProjChain dst.proj :: src.localIdx :: specEncodeProjChain src.proj :: rest
  | .assignBinOp dst op lhs rhs =>
      0x15 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeBinOp op :: specEncodeOpB0 lhs :: specEncodeOpB1 lhs :: specEncodeOpB0 rhs :: specEncodeOpB1 rhs :: rest
  | .assignUnOp dst op src =>
      0x16 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeUnOp op :: specEncodeOpB0 src :: specEncodeOpB1 src :: rest
  | .assignAgg0 dst k =>
      0x17 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeAgg0 k :: rest
  | .assignAgg1 dst k f0 =>
      0x18 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeAgg1 k :: specEncodeOpB0 f0 :: specEncodeOpB1 f0 :: rest
  | .assignAgg2 dst k f0 f1 =>
      0x19 :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeAgg2 k :: specEncodeOpB0 f0 :: specEncodeOpB1 f0 :: specEncodeOpB0 f1 :: specEncodeOpB1 f1 :: rest
  | .assignAgg3 dst k f0 f1 f2 =>
      0x1A :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeAgg3 k :: specEncodeOpB0 f0 :: specEncodeOpB1 f0 :: specEncodeOpB0 f1 :: specEncodeOpB1 f1 :: specEncodeOpB0 f2 :: specEncodeOpB1 f2 :: rest
  | .storageLive l => 0x20 :: l :: rest
  | .storageDead l => 0x21 :: l :: rest
  | .nop => 0x22 :: rest
  | .placeMention src => 0x30 :: src.localIdx :: specEncodeProjChain src.proj :: rest
  | .retagStmt rk src => 0x31 :: rk :: src.localIdx :: specEncodeProjChain src.proj :: rest

def specEncodeUnwind : UnwindSpec → Nat
  | .cleanup bb => bb
  | .continueUnwind => 252
  | .unreachableUnwind => 253
  | .terminateAbi => 254
  | .terminateCleanup => 255

def specEncodeTargetOpt : Option Nat → Nat
  | some b => b
  | none => 255

def specEncodeTermCons (tm : WireTerm) (rest : List Nat) : List Nat :=
  match tm with
  | .ret => 0x40 :: rest
  | .unwindResume => 0x41 :: rest
  | .unwindTerminate r => 0x42 :: r :: rest
  | .unreachable => 0x43 :: rest
  | .goto t => 0x44 :: t :: rest
  | .switchInt1 discr v0 t0 other =>
      0x45 :: specEncodeOpB0 discr :: specEncodeOpB1 discr :: v0 :: t0 :: other :: rest
  | .switchInt2 discr v0 t0 v1 t1 other =>
      0x46 :: specEncodeOpB0 discr :: specEncodeOpB1 discr :: v0 :: t0 :: v1 :: t1 :: other :: rest
  | .drop p g t uw =>
      0x47 :: p.localIdx :: specEncodeProjChain p.proj :: g :: t :: specEncodeUnwind uw :: rest
  | .assertTerm cond exp t uw =>
      0x48 :: specEncodeOpB0 cond :: specEncodeOpB1 cond :: (bif exp then 1 else 0) :: t :: specEncodeUnwind uw :: rest
  | .call0 c dst t uw =>
      0x49 :: c :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeTargetOpt t :: specEncodeUnwind uw :: rest
  | .call1 c dst t uw a0 =>
      0x4A :: c :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeTargetOpt t :: specEncodeUnwind uw :: specEncodeOpB0 a0 :: specEncodeOpB1 a0 :: rest
  | .call2 c dst t uw a0 a1 =>
      0x4B :: c :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeTargetOpt t :: specEncodeUnwind uw :: specEncodeOpB0 a0 :: specEncodeOpB1 a0 :: specEncodeOpB0 a1 :: specEncodeOpB1 a1 :: rest
  | .call3 c dst t uw a0 a1 a2 =>
      0x4C :: c :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeTargetOpt t :: specEncodeUnwind uw :: specEncodeOpB0 a0 :: specEncodeOpB1 a0 :: specEncodeOpB0 a1 :: specEncodeOpB1 a1 :: specEncodeOpB0 a2 :: specEncodeOpB1 a2 :: rest
  | .call4 c dst t uw a0 a1 a2 a3 =>
      0x4D :: c :: dst.localIdx :: specEncodeProjChain dst.proj :: specEncodeTargetOpt t :: specEncodeUnwind uw :: specEncodeOpB0 a0 :: specEncodeOpB1 a0 :: specEncodeOpB0 a1 :: specEncodeOpB1 a1 :: specEncodeOpB0 a2 :: specEncodeOpB1 a2 :: specEncodeOpB0 a3 :: specEncodeOpB1 a3 :: rest

def specEncodeStmtsCons : List WireStmt → List Nat → List Nat
  | [], rest => rest
  | s :: ss, rest => specEncodeStmtCons s (specEncodeStmtsCons ss rest)

def specEncodeBlockCons (b : WireBlock) (rest : List Nat) : List Nat :=
  let cleanByte := bif b.isCleanup then 1 else 0
  cleanByte :: b.stmts.length :: specEncodeStmtsCons b.stmts (specEncodeTermCons b.term rest)

def specEncodeBlocksCons : List WireBlock → List Nat → List Nat
  | [], rest => rest
  | b :: bs, rest => specEncodeBlockCons b (specEncodeBlocksCons bs rest)

def specEncodeTypeTagsCons : List MirTypeTag → List Nat → List Nat
  | [], rest => rest
  | t :: ts, rest => specEncodeTypeTag t :: specEncodeTypeTagsCons ts rest

def specEncodeBodyCons (body : WireBody) (rest : List Nat) : List Nat :=
  body.bodyId ::
  body.symId ::
  specEncodeOriginKind body.originKind ::
  specEncodeMirPhase body.mirPhase ::
  body.localCount ::
  body.argCount ::
  body.blocks.length ::
  specEncodeTypeTagsCons body.localTypes (specEncodeBlocksCons body.blocks rest)

def specEncodeBodiesCons : List WireBody → List Nat
  | [] => []
  | b :: bs => specEncodeBodyCons b (specEncodeBodiesCons bs)

def specEncodeFlags (monoComplete preserveUb ubChecks : Bool) : Nat :=
  bif monoComplete then
    bif preserveUb then
      bif ubChecks then 11 else 3
    else
      bif ubChecks then 9 else 1
  else
    0

def specEncodePackage (pkg : WirePackage) : List Nat :=
  0x41 :: 0x4D :: 0x49 :: 0x52 ::
  pkg.version ::
  specEncodeMirPhase pkg.defaultPhase ::
  specEncodeFlags pkg.monoComplete pkg.preserveUb pkg.ubChecks ::
  pkg.fpHi ::
  pkg.fpLo ::
  pkg.bodies.length ::
  specEncodeBodiesCons pkg.bodies

/-! ## Boundary 2: Structural & Dialect Well-Formedness Admission -/

def checkPlaceWellFormed (maxLocal : Nat) (p : PlaceSpec) : Bool :=
  Nat.ble p.localIdx maxLocal

def checkOperandWellFormed (maxLocal : Nat) : OperandSpec → Bool
  | .copy p => Nat.ble p.localIdx maxLocal
  | .move p => Nat.ble p.localIdx maxLocal
  | .constBool _ => true
  | .constU32 v => Nat.ble v 255
  | .constUsize v => Nat.ble v 255
  | .constUnit => true
  | .constSizeError => true
  | .constPanicStr => true

def checkStmtWellFormed (maxLocal : Nat) : WireStmt → Bool
  | .assignUseNoRetag dst src => Nat.ble dst.localIdx maxLocal && checkOperandWellFormed maxLocal src
  | .assignUseRetagYes dst src => Nat.ble dst.localIdx maxLocal && checkOperandWellFormed maxLocal src
  | .assignCopyForDeref dst src => Nat.ble dst.localIdx maxLocal && Nat.ble src.localIdx maxLocal
  | .assignRefOrPtr dst _ src => Nat.ble dst.localIdx maxLocal && Nat.ble src.localIdx maxLocal
  | .assignDiscriminant dst src => Nat.ble dst.localIdx maxLocal && Nat.ble src.localIdx maxLocal
  | .assignBinOp dst _ lhs rhs =>
      Nat.ble dst.localIdx maxLocal && checkOperandWellFormed maxLocal lhs && checkOperandWellFormed maxLocal rhs
  | .assignUnOp dst _ src => Nat.ble dst.localIdx maxLocal && checkOperandWellFormed maxLocal src
  | .assignAgg0 dst _ => Nat.ble dst.localIdx maxLocal
  | .assignAgg1 dst _ f0 => Nat.ble dst.localIdx maxLocal && checkOperandWellFormed maxLocal f0
  | .assignAgg2 dst _ f0 f1 =>
      Nat.ble dst.localIdx maxLocal && checkOperandWellFormed maxLocal f0 && checkOperandWellFormed maxLocal f1
  | .assignAgg3 dst _ f0 f1 f2 =>
      Nat.ble dst.localIdx maxLocal && checkOperandWellFormed maxLocal f0 &&
      checkOperandWellFormed maxLocal f1 && checkOperandWellFormed maxLocal f2
  | .storageLive l => Nat.ble l maxLocal
  | .storageDead l => Nat.ble l maxLocal
  | .nop => true
  | .placeMention src => Nat.ble src.localIdx maxLocal
  | .retagStmt rk src => Nat.ble rk 3 && Nat.ble src.localIdx maxLocal

def checkTargetBbWellFormed (maxBb : Nat) (t : Nat) : Bool :=
  Nat.ble t maxBb

def checkTargetOptWellFormed (maxBb : Nat) : Option Nat → Bool
  | some t => Nat.ble t maxBb
  | none => true

def checkUnwindWellFormed (maxBb : Nat) : UnwindSpec → Bool
  | .cleanup bb => Nat.ble bb maxBb
  | .continueUnwind => true
  | .unreachableUnwind => true
  | .terminateAbi => true
  | .terminateCleanup => true

def checkTermWellFormed (maxLocal maxBb : Nat) : WireTerm → Bool
  | .ret => true
  | .unwindResume => true
  | .unwindTerminate r => Nat.beq r 1 || Nat.beq r 2
  | .unreachable => true
  | .goto t => Nat.ble t maxBb
  | .switchInt1 discr v0 t0 other =>
      checkOperandWellFormed maxLocal discr && Nat.ble v0 255 &&
      Nat.ble t0 maxBb && Nat.ble other maxBb
  | .switchInt2 discr v0 t0 v1 t1 other =>
      checkOperandWellFormed maxLocal discr && Nat.ble v0 255 && Nat.ble v1 255 &&
      Nat.ble t0 maxBb && Nat.ble t1 maxBb && Nat.ble other maxBb
  | .drop p g t uw =>
      Nat.ble p.localIdx maxLocal && Nat.ble g 255 &&
      Nat.ble t maxBb && checkUnwindWellFormed maxBb uw
  | .assertTerm cond _ t uw =>
      checkOperandWellFormed maxLocal cond && Nat.ble t maxBb && checkUnwindWellFormed maxBb uw
  | .call0 c dst t uw =>
      Nat.ble 1 c && Nat.ble c 255 && Nat.ble dst.localIdx maxLocal &&
      checkTargetOptWellFormed maxBb t && checkUnwindWellFormed maxBb uw
  | .call1 c dst t uw a0 =>
      Nat.ble 1 c && Nat.ble c 255 && Nat.ble dst.localIdx maxLocal &&
      checkTargetOptWellFormed maxBb t && checkUnwindWellFormed maxBb uw &&
      checkOperandWellFormed maxLocal a0
  | .call2 c dst t uw a0 a1 =>
      Nat.ble 1 c && Nat.ble c 255 && Nat.ble dst.localIdx maxLocal &&
      checkTargetOptWellFormed maxBb t && checkUnwindWellFormed maxBb uw &&
      checkOperandWellFormed maxLocal a0 && checkOperandWellFormed maxLocal a1
  | .call3 c dst t uw a0 a1 a2 =>
      Nat.ble 1 c && Nat.ble c 255 && Nat.ble dst.localIdx maxLocal &&
      checkTargetOptWellFormed maxBb t && checkUnwindWellFormed maxBb uw &&
      checkOperandWellFormed maxLocal a0 && checkOperandWellFormed maxLocal a1 && checkOperandWellFormed maxLocal a2
  | .call4 c dst t uw a0 a1 a2 a3 =>
      Nat.ble 1 c && Nat.ble c 255 && Nat.ble dst.localIdx maxLocal &&
      checkTargetOptWellFormed maxBb t && checkUnwindWellFormed maxBb uw &&
      checkOperandWellFormed maxLocal a0 && checkOperandWellFormed maxLocal a1 &&
      checkOperandWellFormed maxLocal a2 && checkOperandWellFormed maxLocal a3

def checkStmtsWellFormed (maxLocal : Nat) : List WireStmt → Bool
  | [] => true
  | s :: ss => bif checkStmtWellFormed maxLocal s then checkStmtsWellFormed maxLocal ss else false

def checkBlockWellFormed (maxLocal maxBb : Nat) (blk : WireBlock) : Bool :=
  Nat.ble blk.stmts.length 64 &&
  checkStmtsWellFormed maxLocal blk.stmts &&
  checkTermWellFormed maxLocal maxBb blk.term

def checkBlocksWellFormed (maxLocal maxBb : Nat) : List WireBlock → Bool
  | [] => true
  | b :: bs => bif checkBlockWellFormed maxLocal maxBb b then checkBlocksWellFormed maxLocal maxBb bs else false

def checkBodyWellFormed (body : WireBody) : Bool :=
  let nBlk := body.blocks.length
  Nat.ble 1 body.bodyId && Nat.ble body.bodyId 255 &&
  Nat.ble 1 body.symId && Nat.ble body.symId 255 &&
  Nat.ble 1 body.localCount && Nat.ble body.localCount 64 &&
  Nat.beq body.localTypes.length body.localCount &&
  Nat.ble body.argCount (body.localCount - 1) &&
  Nat.ble 1 nBlk && Nat.ble nBlk 32 &&
  checkBlocksWellFormed (body.localCount - 1) (nBlk - 1) body.blocks

def checkBodiesWellFormed : List WireBody → Bool
  | [] => true
  | b :: bs => bif checkBodyWellFormed b then checkBodiesWellFormed bs else false

def checkPackageWellFormed (pkg : WirePackage) : Bool :=
  Nat.beq pkg.version 3 &&
  Nat.ble pkg.fpHi 255 &&
  Nat.ble pkg.fpLo 255 &&
  Nat.ble 1 pkg.bodies.length && Nat.ble pkg.bodies.length 64 &&
  checkBodiesWellFormed pkg.bodies

/-! ## Stage B2b: Unique Body Identities, Referenced-Callee/Drop-Glue Closure, and Phase Invariants -/

def isDeclaredIntrinsicSym (sym : Nat) : Bool :=
  Nat.beq sym 20 || Nat.beq sym 21 || Nat.beq sym 22 || Nat.beq sym 23 ||
  Nat.beq sym 25 || Nat.beq sym 26 || Nat.beq sym 27 || Nat.beq sym 28 ||
  Nat.beq sym 29 || Nat.beq sym 30 || Nat.beq sym 31 || Nat.beq sym 37 ||
  Nat.beq sym 38 || Nat.beq sym 39 || Nat.beq sym 40 || Nat.beq sym 41 ||
  Nat.beq sym 42

def bodiesContainSymId (sym : Nat) : List WireBody → Bool
  | [] => false
  | b :: bs => bif Nat.beq b.symId sym then true else bodiesContainSymId sym bs

def checkUniqueSymIds : List WireBody → Bool
  | [] => true
  | b :: bs => bif bodiesContainSymId b.symId bs then false else checkUniqueSymIds bs

def checkCalleeResolved (allBodies : List WireBody) (calleeSym : Nat) : Bool :=
  isDeclaredIntrinsicSym calleeSym || bodiesContainSymId calleeSym allBodies

def checkTermClosure (allBodies : List WireBody) : WireTerm → Bool
  | .ret => true
  | .unwindResume => true
  | .unwindTerminate _ => true
  | .unreachable => true
  | .goto _ => true
  | .switchInt1 _ _ _ _ => true
  | .switchInt2 _ _ _ _ _ _ => true
  | .drop _ glueSym _ _ => Nat.beq glueSym 0 || bodiesContainSymId glueSym allBodies
  | .assertTerm _ _ _ _ => true
  | .call0 c _ _ _ => checkCalleeResolved allBodies c
  | .call1 c _ _ _ _ => checkCalleeResolved allBodies c
  | .call2 c _ _ _ _ _ => checkCalleeResolved allBodies c
  | .call3 c _ _ _ _ _ _ => checkCalleeResolved allBodies c
  | .call4 c _ _ _ _ _ _ _ => checkCalleeResolved allBodies c

def checkBlocksClosure (allBodies : List WireBody) : List WireBlock → Bool
  | [] => true
  | blk :: blks =>
      bif checkTermClosure allBodies blk.term then checkBlocksClosure allBodies blks else false

def checkBodiesClosure (allBodies : List WireBody) : List WireBody → Bool
  | [] => true
  | b :: bs =>
      bif checkBlocksClosure allBodies b.blocks then checkBodiesClosure allBodies bs else false

def checkBodyPhaseConsistent (defaultPhase : MirPhaseTag) (b : WireBody) : Bool :=
  match b.originKind with
  | .localOwner => b.mirPhase == defaultPhase
  | .compilerShim => b.mirPhase == .runtimeOptimized || b.mirPhase == defaultPhase
  | .externalOptimized => b.mirPhase == .runtimeOptimized || b.mirPhase == defaultPhase
  | .promotedOrConstOwner => true

def checkBodiesPhaseConsistent (defaultPhase : MirPhaseTag) : List WireBody → Bool
  | [] => true
  | b :: bs =>
      bif checkBodyPhaseConsistent defaultPhase b then
        checkBodiesPhaseConsistent defaultPhase bs
      else false

def checkPackageAdmissionClosure (pkg : WirePackage) : Bool :=
  checkPackageWellFormed pkg &&
  checkUniqueSymIds pkg.bodies &&
  checkBodiesClosure pkg.bodies pkg.bodies &&
  checkBodiesPhaseConsistent pkg.defaultPhase pkg.bodies

/-! ## Boundary 1: Byte-Stream Framing and Syntax Decoder -/

inductive Layer1Error where
  | malformedSyntax
  | unsupportedFeature (opcode : Nat)
  deriving DecidableEq, Repr

inductive ParseOutcome (α : Type) where
  | accepted (val : α)
  | rejectedNonPhysicalByte
  | rejectedMalformedSyntax
  | rejectedTrailingBytes (trailingCount : Nat)
  | rejectedUnsupportedFeature (opcode : Nat)
  | rejectedIllFormedBody
  | rejectedNonCanonicalEncoding
  deriving DecidableEq, Repr

def decodeOriginKind (b : Nat) : Option BodyOriginKind :=
  bif Nat.beq b 1 then some .localOwner
  else bif Nat.beq b 2 then some .compilerShim
  else bif Nat.beq b 3 then some .externalOptimized
  else bif Nat.beq b 4 then some .promotedOrConstOwner
  else none

def decodeMirPhase (b : Nat) : Option MirPhaseTag :=
  bif Nat.beq b 1 then some .built
  else bif Nat.beq b 2 then some .analysis
  else bif Nat.beq b 3 then some .runtimePostCleanup
  else bif Nat.beq b 4 then some .runtimeOptimized
  else none

def decodeTypeTag (b : Nat) : Option MirTypeTag :=
  bif Nat.ble b 10 then
    bif Nat.ble b 5 then
      bif Nat.beq b 1 then some .unit
      else bif Nat.beq b 2 then some .bool
      else bif Nat.beq b 3 then some .u32
      else bif Nat.beq b 4 then some .usize
      else bif Nat.beq b 5 then some .rawPtrU32
      else none
    else
      bif Nat.beq b 6 then some .refMutEffectLog
      else bif Nat.beq b 7 then some .effectLog
      else bif Nat.beq b 8 then some .guard
      else bif Nat.beq b 9 then some .pairGuards
      else some .dstLayout
  else bif Nat.ble b 20 then
    bif Nat.ble b 15 then
      bif Nat.beq b 11 then some .sizeError
      else bif Nat.beq b 12 then some .optUsize
      else bif Nat.beq b 13 then some .optPairUsize
      else bif Nat.beq b 14 then some .resUsizeSizeError
      else some .resDstLayoutSizeError
    else
      bif Nat.beq b 16 then some .checkedArithTuple
      else bif Nat.beq b 17 then some .pairUsize
      else bif Nat.beq b 18 then some .pairDstLayoutUsize
      else bif Nat.beq b 19 then some .panicOrNever
      else some .closureOrOther
  else bif Nat.ble b 23 then
    bif Nat.beq b 21 then some .checkedArithTupleU32
    else bif Nat.beq b 22 then some .refGuard
    else some .refPairGuards
  else none

def decodeProjChain (b : Nat) : Option ProjChain :=
  bif Nat.ble b 4 then
    bif Nat.beq b 0 then some .here
    else bif Nat.beq b 1 then some .field0
    else bif Nat.beq b 2 then some .field1
    else bif Nat.beq b 3 then some .field2
    else some .deref
  else bif Nat.ble b 9 then
    bif Nat.beq b 5 then some .derefField0
    else bif Nat.beq b 6 then some .derefField1
    else bif Nat.beq b 7 then some .derefField2
    else bif Nat.beq b 8 then some .downcast0Field0
    else some .downcast1Field0
  else none

def decodePlace2 (b0 b1 : Nat) : Option PlaceSpec :=
  bif Nat.ble b0 63 then
    match decodeProjChain b1 with
    | some pr => some { localIdx := b0, proj := pr }
    | none => none
  else
    none

def decodeOperand2 (b0 b1 : Nat) : Option OperandSpec :=
  bif Nat.ble b0 63 then
    match decodeProjChain b1 with
    | some pr => some (.copy { localIdx := b0, proj := pr })
    | none => none
  else bif Nat.ble b0 127 then
    match decodeProjChain b1 with
    | some pr => some (.move { localIdx := b0 - 64, proj := pr })
    | none => none
  else bif Nat.beq b0 128 then
    bif Nat.beq b1 0 then some (.constBool false)
    else bif Nat.beq b1 1 then some (.constBool true)
    else none
  else bif Nat.beq b0 129 then
    bif Nat.ble b1 255 then some (.constU32 b1) else none
  else bif Nat.beq b0 130 then
    bif Nat.ble b1 255 then some (.constUsize b1) else none
  else bif Nat.beq b0 131 then
    bif Nat.beq b1 0 then some .constUnit
    else bif Nat.beq b1 1 then some .constSizeError
    else bif Nat.beq b1 2 then some .constPanicStr
    else none
  else
    none

def decodeRefPtrKind (b : Nat) : Option RefPtrKind :=
  bif Nat.beq b 0 then some .sharedRef
  else bif Nat.beq b 1 then some .mutRef
  else bif Nat.beq b 2 then some .rawConst
  else bif Nat.beq b 3 then some .rawMut
  else none

def decodeBinOp (b : Nat) : Option BinOpTag :=
  bif Nat.ble b 8 then
    bif Nat.ble b 4 then
      bif Nat.beq b 1 then some .eq
      else bif Nat.beq b 2 then some .ne
      else bif Nat.beq b 3 then some .lt
      else bif Nat.beq b 4 then some .le
      else none
    else
      bif Nat.beq b 5 then some .gt
      else bif Nat.beq b 6 then some .ge
      else bif Nat.beq b 7 then some .add
      else some .sub
  else bif Nat.ble b 15 then
    bif Nat.ble b 12 then
      bif Nat.beq b 9 then some .mul
      else bif Nat.beq b 10 then some .div
      else bif Nat.beq b 11 then some .rem
      else some .bitAnd
    else
      bif Nat.beq b 13 then some .addWithOverflow
      else bif Nat.beq b 14 then some .subWithOverflow
      else some .mulWithOverflow
  else none

def decodeUnOp (b : Nat) : Option UnOpTag :=
  bif Nat.beq b 1 then some .notOp else none

def decodeAgg0 (b : Nat) : Option Agg0Kind :=
  bif Nat.beq b 1 then some .sizeError
  else bif Nat.beq b 2 then some .optionNone
  else none

def decodeAgg1 (b : Nat) : Option Agg1Kind :=
  bif Nat.beq b 1 then some .okOrSome
  else bif Nat.beq b 2 then some .resultErr
  else bif Nat.beq b 3 then some .closureCapture1
  else none

def decodeAgg2 (b : Nat) : Option Agg2Kind :=
  bif Nat.beq b 1 then some .guard
  else bif Nat.beq b 2 then some .pairGuards
  else bif Nat.beq b 3 then some .effectLog
  else bif Nat.beq b 4 then some .tuple2
  else none

def decodeAgg3 (b : Nat) : Option Agg3Kind :=
  bif Nat.beq b 1 then some .dstLayout else none

def decodeUnwind (b : Nat) : Option UnwindSpec :=
  bif Nat.ble b 31 then some (.cleanup b)
  else bif Nat.beq b 252 then some .continueUnwind
  else bif Nat.beq b 253 then some .unreachableUnwind
  else bif Nat.beq b 254 then some .terminateAbi
  else bif Nat.beq b 255 then some .terminateCleanup
  else none

def decodeTargetOpt (b : Nat) : Option (Option Nat) :=
  bif Nat.ble b 31 then some (some b)
  else bif Nat.beq b 255 then some none
  else none

def parseOneStmt (input : List Nat) : Except Layer1Error (WireStmt × List Nat) :=
  match input with
  | [] => .error .malformedSyntax
  | op :: rest0 =>
      bif Nat.beq op 0x20 then
        match rest0 with
        | l :: rest => bif Nat.ble l 63 then .ok (.storageLive l, rest) else .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x21 then
        match rest0 with
        | l :: rest => bif Nat.ble l 63 then .ok (.storageDead l, rest) else .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x11 then
        match rest0 with
        | d0 :: d1 :: s0 :: s1 :: rest =>
            match decodePlace2 d0 d1, decodeOperand2 s0 s1 with
            | some dst, some src => .ok (.assignUseRetagYes dst src, rest)
            | _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x10 then
        match rest0 with
        | d0 :: d1 :: s0 :: s1 :: rest =>
            match decodePlace2 d0 d1, decodeOperand2 s0 s1 with
            | some dst, some src => .ok (.assignUseNoRetag dst src, rest)
            | _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x12 then
        match rest0 with
        | d0 :: d1 :: s0 :: s1 :: rest =>
            match decodePlace2 d0 d1, decodePlace2 s0 s1 with
            | some dst, some src => .ok (.assignCopyForDeref dst src, rest)
            | _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x13 then
        match rest0 with
        | d0 :: d1 :: rkB :: s0 :: s1 :: rest =>
            match decodePlace2 d0 d1, decodeRefPtrKind rkB, decodePlace2 s0 s1 with
            | some dst, some rk, some src => .ok (.assignRefOrPtr dst rk src, rest)
            | _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x14 then
        match rest0 with
        | d0 :: d1 :: s0 :: s1 :: rest =>
            match decodePlace2 d0 d1, decodePlace2 s0 s1 with
            | some dst, some src => .ok (.assignDiscriminant dst src, rest)
            | _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x15 then
        match rest0 with
        | d0 :: d1 :: opB :: l0 :: l1 :: r0 :: r1 :: rest =>
            match decodePlace2 d0 d1, decodeBinOp opB, decodeOperand2 l0 l1, decodeOperand2 r0 r1 with
            | some dst, some bop, some lhs, some rhs => .ok (.assignBinOp dst bop lhs rhs, rest)
            | _, _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x16 then
        match rest0 with
        | d0 :: d1 :: opB :: s0 :: s1 :: rest =>
            match decodePlace2 d0 d1, decodeUnOp opB, decodeOperand2 s0 s1 with
            | some dst, some uop, some src => .ok (.assignUnOp dst uop src, rest)
            | _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x17 then
        match rest0 with
        | d0 :: d1 :: kB :: rest =>
            match decodePlace2 d0 d1, decodeAgg0 kB with
            | some dst, some k => .ok (.assignAgg0 dst k, rest)
            | _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x18 then
        match rest0 with
        | d0 :: d1 :: kB :: a0 :: a1 :: rest =>
            match decodePlace2 d0 d1, decodeAgg1 kB, decodeOperand2 a0 a1 with
            | some dst, some k, some f0 => .ok (.assignAgg1 dst k f0, rest)
            | _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x19 then
        match rest0 with
        | d0 :: d1 :: kB :: a0 :: a1 :: b0 :: b1 :: rest =>
            match decodePlace2 d0 d1, decodeAgg2 kB, decodeOperand2 a0 a1, decodeOperand2 b0 b1 with
            | some dst, some k, some f0, some f1 => .ok (.assignAgg2 dst k f0 f1, rest)
            | _, _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x1A then
        match rest0 with
        | d0 :: d1 :: kB :: a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: rest =>
            match decodePlace2 d0 d1, decodeAgg3 kB, decodeOperand2 a0 a1, decodeOperand2 b0 b1, decodeOperand2 c0 c1 with
            | some dst, some k, some f0, some f1, some f2 => .ok (.assignAgg3 dst k f0 f1 f2, rest)
            | _, _, _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x22 then
        .ok (.nop, rest0)
      else bif Nat.beq op 0x30 then
        match rest0 with
        | s0 :: s1 :: rest =>
            match decodePlace2 s0 s1 with
            | some src => .ok (.placeMention src, rest)
            | none => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x31 then
        match rest0 with
        | rk :: s0 :: s1 :: rest =>
            bif Nat.ble rk 3 then
              match decodePlace2 s0 s1 with
              | some src => .ok (.retagStmt rk src, rest)
              | none => .error .malformedSyntax
            else .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0xF0 || Nat.beq op 0xF1 || Nat.beq op 0xF2 then
        .error (.unsupportedFeature op)
      else
        .error .malformedSyntax

def parseStmtsLoop : Nat → List Nat → Except Layer1Error (List WireStmt × List Nat)
  | 0, rest => .ok ([], rest)
  | n + 1, rest =>
      match parseOneStmt rest with
      | .error e => .error e
      | .ok (st, rest1) =>
          match parseStmtsLoop n rest1 with
          | .error e => .error e
          | .ok (sts, rest2) => .ok (st :: sts, rest2)

def parseOneTerm (input : List Nat) : Except Layer1Error (WireTerm × List Nat) :=
  match input with
  | [] => .error .malformedSyntax
  | op :: rest0 =>
      bif Nat.beq op 0x40 then .ok (.ret, rest0)
      else bif Nat.beq op 0x41 then .ok (.unwindResume, rest0)
      else bif Nat.beq op 0x42 then
        match rest0 with
        | r :: rest =>
            bif Nat.beq r 1 || Nat.beq r 2 then .ok (.unwindTerminate r, rest)
            else .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x43 then .ok (.unreachable, rest0)
      else bif Nat.beq op 0x44 then
        match rest0 with
        | t :: rest =>
            bif Nat.ble t 31 then .ok (.goto t, rest) else .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x45 then
        match rest0 with
        | d0 :: d1 :: v0 :: t0 :: other :: rest =>
            match decodeOperand2 d0 d1 with
            | some discr =>
                bif Nat.ble v0 255 && Nat.ble t0 31 && Nat.ble other 31 then
                  .ok (.switchInt1 discr v0 t0 other, rest)
                else .error .malformedSyntax
            | none => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x46 then
        match rest0 with
        | d0 :: d1 :: v0 :: t0 :: v1 :: t1 :: other :: rest =>
            match decodeOperand2 d0 d1 with
            | some discr =>
                bif Nat.ble v0 255 && Nat.ble t0 31 && Nat.ble v1 255 && Nat.ble t1 31 && Nat.ble other 31 then
                  .ok (.switchInt2 discr v0 t0 v1 t1 other, rest)
                else .error .malformedSyntax
            | none => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x47 then
        match rest0 with
        | p0 :: p1 :: g :: t :: uwB :: rest =>
            match decodePlace2 p0 p1, decodeUnwind uwB with
            | some pl, some uw =>
                bif Nat.ble g 255 && Nat.ble t 31 then
                  .ok (.drop pl g t uw, rest)
                else .error .malformedSyntax
            | _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x48 then
        match rest0 with
        | c0 :: c1 :: expB :: t :: uwB :: rest =>
            match decodeOperand2 c0 c1, decodeUnwind uwB with
            | some cond, some uw =>
                bif (Nat.beq expB 0 || Nat.beq expB 1) && Nat.ble t 31 then
                  .ok (.assertTerm cond (Nat.beq expB 1) t uw, rest)
                else .error .malformedSyntax
            | _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x49 then
        match rest0 with
        | c :: d0 :: d1 :: tB :: uwB :: rest =>
            match decodePlace2 d0 d1, decodeTargetOpt tB, decodeUnwind uwB with
            | some dst, some tOpt, some uw =>
                bif Nat.ble 1 c && Nat.ble c 255 then
                  .ok (.call0 c dst tOpt uw, rest)
                else .error .malformedSyntax
            | _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x4A then
        match rest0 with
        | c :: d0 :: d1 :: tB :: uwB :: a00 :: a01 :: rest =>
            match decodePlace2 d0 d1, decodeTargetOpt tB, decodeUnwind uwB, decodeOperand2 a00 a01 with
            | some dst, some tOpt, some uw, some a0 =>
                bif Nat.ble 1 c && Nat.ble c 255 then
                  .ok (.call1 c dst tOpt uw a0, rest)
                else .error .malformedSyntax
            | _, _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x4B then
        match rest0 with
        | c :: d0 :: d1 :: tB :: uwB :: a00 :: a01 :: a10 :: a11 :: rest =>
            match decodePlace2 d0 d1, decodeTargetOpt tB, decodeUnwind uwB, decodeOperand2 a00 a01, decodeOperand2 a10 a11 with
            | some dst, some tOpt, some uw, some a0, some a1 =>
                bif Nat.ble 1 c && Nat.ble c 255 then
                  .ok (.call2 c dst tOpt uw a0 a1, rest)
                else .error .malformedSyntax
            | _, _, _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x4C then
        match rest0 with
        | c :: d0 :: d1 :: tB :: uwB :: a00 :: a01 :: a10 :: a11 :: a20 :: a21 :: rest =>
            match decodePlace2 d0 d1, decodeTargetOpt tB, decodeUnwind uwB, decodeOperand2 a00 a01, decodeOperand2 a10 a11, decodeOperand2 a20 a21 with
            | some dst, some tOpt, some uw, some a0, some a1, some a2 =>
                bif Nat.ble 1 c && Nat.ble c 255 then
                  .ok (.call3 c dst tOpt uw a0 a1 a2, rest)
                else .error .malformedSyntax
            | _, _, _, _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0x4D then
        match rest0 with
        | c :: d0 :: d1 :: tB :: uwB :: a00 :: a01 :: a10 :: a11 :: a20 :: a21 :: a30 :: a31 :: rest =>
            match decodePlace2 d0 d1, decodeTargetOpt tB, decodeUnwind uwB, decodeOperand2 a00 a01, decodeOperand2 a10 a11, decodeOperand2 a20 a21, decodeOperand2 a30 a31 with
            | some dst, some tOpt, some uw, some a0, some a1, some a2, some a3 =>
                bif Nat.ble 1 c && Nat.ble c 255 then
                  .ok (.call4 c dst tOpt uw a0 a1 a2 a3, rest)
                else .error .malformedSyntax
            | _, _, _, _, _, _, _ => .error .malformedSyntax
        | _ => .error .malformedSyntax
      else bif Nat.beq op 0xE0 || Nat.beq op 0xE1 || Nat.beq op 0xE2 || Nat.beq op 0xE3 then
        .error (.unsupportedFeature op)
      else
        .error .malformedSyntax

def parseBlockBytes : List Nat → Except Layer1Error (WireBlock × List Nat)
  | cleanByte :: stmtCount :: rest =>
      bif Nat.ble 2 cleanByte || Nat.ble 65 stmtCount then .error .malformedSyntax
      else
        match parseStmtsLoop stmtCount rest with
        | .error e => .error e
        | .ok (stmts, restAfterStmts) =>
            match parseOneTerm restAfterStmts with
            | .error e => .error e
            | .ok (term, restNext) =>
                .ok ({ isCleanup := Nat.beq cleanByte 1, stmts := stmts, term := term }, restNext)
  | _ => .error .malformedSyntax

def parseBlocksLoop : Nat → List Nat → Except Layer1Error (List WireBlock × List Nat)
  | 0, rest => .ok ([], rest)
  | n + 1, rest =>
      match parseBlockBytes rest with
      | .error e => .error e
      | .ok (blk, rest1) =>
          match parseBlocksLoop n rest1 with
          | .error e => .error e
          | .ok (blks, rest2) => .ok (blk :: blks, rest2)

def parseTypeTagsLoop : Nat → List Nat → Except Layer1Error (List MirTypeTag × List Nat)
  | 0, rest => .ok ([], rest)
  | n + 1, b :: rest =>
      match decodeTypeTag b with
      | some t =>
          match parseTypeTagsLoop n rest with
          | .error e => .error e
          | .ok (ts, rest2) => .ok (t :: ts, rest2)
      | none => .error .malformedSyntax
  | _ + 1, [] => .error .malformedSyntax

def parseBodyBytes : List Nat → Except Layer1Error (WireBody × List Nat)
  | bodyId :: symId :: origByte :: phaseByte :: localCount :: argCount :: blockCount :: rest =>
      match decodeOriginKind origByte, decodeMirPhase phaseByte with
      | some orig, some ph =>
          match parseTypeTagsLoop localCount rest with
          | .error e => .error e
          | .ok (tys, restAfterTypes) =>
              match parseBlocksLoop blockCount restAfterTypes with
              | .error e => .error e
              | .ok (blks, restNext) =>
                  .ok ({ bodyId := bodyId
                        , symId := symId
                        , originKind := orig
                        , mirPhase := ph
                        , localCount := localCount
                        , argCount := argCount
                        , localTypes := tys
                        , blocks := blks }, restNext)
      | _, _ => .error .malformedSyntax
  | _ => .error .malformedSyntax

def parseBodiesLoop : Nat → List Nat → Except Layer1Error (List WireBody × List Nat)
  | 0, rest => .ok ([], rest)
  | n + 1, rest =>
      match parseBodyBytes rest with
      | .error e => .error e
      | .ok (b, rest1) =>
          match parseBodiesLoop n rest1 with
          | .error e => .error e
          | .ok (bs, rest2) => .ok (b :: bs, rest2)

def decodeFlagsByte (b : Nat) : Option (Bool × Bool × Bool) :=
  bif Nat.beq b 9 then some (true, false, true)
  else bif Nat.beq b 11 then some (true, true, true)
  else bif Nat.beq b 1 then some (true, false, false)
  else bif Nat.beq b 3 then some (true, true, false)
  else none

def parseRawPackageBytes : List Nat → Except Layer1Error (WirePackage × List Nat)
  | m0 :: m1 :: m2 :: m3 :: ver :: defPhaseByte :: flagsByte :: fpHi :: fpLo :: bodyCount :: rest =>
      bif Nat.beq m0 0x41 && Nat.beq m1 0x4D && Nat.beq m2 0x49 && Nat.beq m3 0x52 && Nat.beq ver 3 then
        match decodeMirPhase defPhaseByte, decodeFlagsByte flagsByte with
        | some defPhase, some (monoC, presUb, ubChk) =>
            match parseBodiesLoop bodyCount rest with
            | .error e => .error e
            | .ok (bodies, restNext) =>
                .ok ({ version := ver
                      , defaultPhase := defPhase
                      , monoComplete := monoC
                      , preserveUb := presUb
                      , ubChecks := ubChk
                      , fpHi := fpHi
                      , fpLo := fpLo
                      , bodies := bodies }, restNext)
        | _, _ => .error .malformedSyntax
      else .error .malformedSyntax
  | _ => .error .malformedSyntax

def unconsumedTrailingBytes (bytes : List Nat) : Nat :=
  match parseRawPackageBytes bytes with
  | .ok (_, rest) => rest.length
  | .error _ => 0

def parseWirePackage (bytes : List Nat) : ParseOutcome WirePackage :=
  if physicalBytesValid bytes = true then
    match parseRawPackageBytes bytes with
    | .error .malformedSyntax => .rejectedMalformedSyntax
    | .error (.unsupportedFeature op) => .rejectedUnsupportedFeature op
    | .ok (pkg, rest) =>
        match rest with
        | _ :: _ => .rejectedTrailingBytes rest.length
        | [] =>
            if checkPackageWellFormed pkg = true then
              if listNatBeq (specEncodePackage pkg) bytes = true then
                .accepted pkg
              else
                .rejectedNonCanonicalEncoding
            else
              .rejectedIllFormedBody
  else
    .rejectedNonPhysicalByte

/-! ## Universal Soundness and Parser Determinism Theorems -/

theorem universal_accepted_byte_soundness
    (bytes : List Nat) (pkg : WirePackage)
    (h : parseWirePackage bytes = .accepted pkg) :
    physicalBytesValid bytes = true ∧
    specEncodePackage pkg = bytes ∧
    checkPackageWellFormed pkg = true ∧
    unconsumedTrailingBytes bytes = 0 := by
  unfold parseWirePackage unconsumedTrailingBytes at *
  split at h
  · rename_i hphys
    cases hraw : parseRawPackageBytes bytes with
    | error e =>
        rw [hraw] at h
        cases e <;> contradiction
    | ok pair =>
        rcases pair with ⟨pkg0, rest⟩
        rw [hraw] at h
        cases rest with
        | cons _ _ => contradiction
        | nil =>
            dsimp at h
            split at h
            · rename_i hwf
              split at h
              · rename_i henc
                injection h with hpkg
                subst hpkg
                exact ⟨hphys, listNatBeq_eq_true henc, hwf, rfl⟩
              · contradiction
            · contradiction
  · contradiction

theorem universal_accepted_package_canonical_unique
    (bytes : List Nat) (pkg₁ pkg₂ : WirePackage)
    (h₁ : parseWirePackage bytes = .accepted pkg₁)
    (h₂ : parseWirePackage bytes = .accepted pkg₂) :
    pkg₁ = pkg₂ := by
  have h12 : ParseOutcome.accepted pkg₁ = ParseOutcome.accepted pkg₂ :=
    h₁.symm.trans h₂
  injection h12

/-! ## Real Compiler-Emitted `.amir` v3 Byte Vectors from `direct_mir_driver_v4.rs` -/

def realPlaceMentionPreserveUbBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 110, 3, 1, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 2, 9, 1, 3, 6, 2, 4, 3, 5, 2, 1, 1, 2, 0, 7, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 3, 10, 1, 3, 4, 1, 1, 3, 5, 1, 1, 0, 8, 32, 2, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 17, 2, 0, 131, 0, 33, 2, 17, 0, 0, 129, 0, 64]

def realPlaceMentionDefaultBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 9, 26, 248, 3, 1, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 6, 32, 3, 17, 3, 0, 1, 4, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 2, 9, 1, 3, 6, 2, 4, 3, 5, 2, 1, 1, 2, 0, 6, 32, 3, 17, 3, 0, 131, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 3, 10, 1, 3, 4, 1, 1, 3, 5, 1, 1, 0, 7, 32, 2, 32, 3, 17, 3, 0, 131, 0, 33, 3, 17, 2, 0, 131, 0, 33, 2, 17, 0, 0, 129, 0, 64]

def realCleanupSubjectPreserveUbBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 167, 56, 9, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 3, 1, 3, 10, 2, 5, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 252, 131, 2, 0, 0, 74, 27, 7, 0, 255, 252, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 252, 73, 0, 129, 100, 0, 1, 33, 9, 64, 4, 4, 1, 3, 22, 4, 17, 3, 2, 2, 6, 6, 9, 8, 6, 8, 6, 1, 2, 8, 1, 6, 1, 8, 3, 2, 6, 2, 2, 0, 20, 17, 21, 0, 128, 0, 17, 20, 0, 128, 0, 32, 5, 32, 6, 32, 7, 19, 7, 0, 1, 3, 4, 25, 6, 0, 1, 129, 1, 71, 0, 33, 7, 32, 8, 32, 9, 19, 9, 0, 1, 4, 4, 25, 8, 0, 1, 129, 2, 73, 0, 33, 9, 17, 20, 0, 128, 1, 25, 5, 0, 2, 70, 0, 72, 0, 33, 8, 33, 6, 32, 10, 32, 11, 17, 11, 0, 1, 0, 69, 75, 0, 0, 4, 1, 0, 8, 32, 12, 17, 20, 0, 128, 0, 17, 21, 0, 128, 1, 17, 12, 0, 69, 1, 32, 13, 32, 14, 16, 19, 0, 12, 2, 19, 14, 0, 1, 19, 4, 75, 1, 13, 0, 2, 13, 78, 0, 129, 10, 0, 6, 33, 14, 33, 13, 32, 15, 32, 16, 17, 21, 0, 128, 0, 17, 16, 0, 76, 0, 74, 24, 15, 0, 3, 13, 80, 0, 0, 5, 33, 16, 33, 15, 17, 10, 0, 131, 0, 17, 21, 0, 128, 0, 33, 12, 68, 5, 0, 1, 17, 10, 0, 131, 0, 68, 5, 0, 5, 33, 11, 33, 10, 32, 17, 32, 18, 17, 18, 0, 2, 0, 75, 3, 17, 0, 6, 16, 82, 0, 129, 5, 0, 3, 33, 18, 17, 0, 0, 17, 0, 33, 17, 69, 20, 0, 0, 10, 11, 1, 0, 65, 0, 2, 17, 20, 0, 128, 0, 33, 5, 64, 1, 0, 71, 5, 2, 7, 7, 255, 0, 0, 71, 5, 2, 7, 8, 7, 0, 0, 71, 5, 1, 7, 10, 9, 1, 0, 71, 12, 0, 7, 16, 255, 1, 0, 69, 21, 0, 0, 16, 12, 1, 0, 71, 5, 2, 7, 7, 255, 1, 0, 71, 5, 1, 7, 14, 255, 1, 0, 69, 20, 0, 0, 14, 15, 5, 5, 1, 3, 24, 3, 9, 3, 2, 6, 6, 9, 8, 6, 8, 6, 8, 1, 6, 6, 1, 8, 3, 2, 8, 6, 6, 6, 6, 6, 2, 0, 22, 17, 23, 0, 128, 0, 32, 4, 32, 5, 32, 6, 19, 6, 0, 1, 2, 4, 25, 5, 0, 1, 129, 1, 70, 0, 33, 6, 32, 7, 32, 8, 19, 8, 0, 1, 3, 4, 25, 7, 0, 1, 129, 2, 72, 0, 33, 8, 25, 4, 0, 2, 69, 0, 71, 0, 33, 7, 33, 5, 32, 9, 17, 23, 0, 128, 1, 17, 9, 0, 68, 1, 32, 10, 32, 11, 16, 21, 0, 9, 2, 19, 11, 0, 1, 21, 4, 75, 1, 10, 0, 1, 8, 75, 0, 129, 10, 0, 9, 33, 11, 33, 10, 32, 12, 16, 22, 0, 9, 2, 19, 12, 0, 3, 22, 4, 32, 13, 32, 14, 17, 23, 0, 128, 0, 17, 14, 0, 73, 0, 74, 25, 13, 0, 2, 8, 78, 0, 0, 5, 33, 14, 33, 13, 32, 15, 32, 16, 17, 16, 0, 1, 0, 75, 3, 15, 0, 3, 8, 80, 0, 129, 7, 0, 19, 33, 16, 32, 17, 32, 18, 32, 19, 32, 20, 19, 20, 0, 1, 12, 4, 19, 19, 0, 1, 20, 4, 19, 18, 0, 1, 19, 4, 25, 17, 0, 1, 129, 3, 82, 0, 33, 18, 17, 4, 1, 81, 0, 33, 17, 33, 20, 33, 19, 17, 0, 0, 15, 0, 33, 15, 33, 12, 17, 23, 0, 128, 0, 33, 9, 71, 4, 0, 8, 4, 6, 0, 1, 33, 4, 64, 1, 0, 71, 4, 2, 7, 6, 255, 1, 0, 65, 1, 0, 71, 9, 0, 7, 5, 255, 1, 0, 69, 23, 0, 0, 5, 7, 6, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 8, 2, 4, 2, 1, 5, 1, 23, 0, 0, 71, 1, 5, 7, 4, 3, 1, 0, 65, 0, 0, 64, 1, 0, 71, 1, 6, 7, 1, 255, 0, 0, 71, 1, 6, 7, 2, 252, 9, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

def realZerocopyLayoutHoldoutBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 227, 80, 10, 1, 15, 1, 3, 2, 1, 1, 10, 10, 0, 1, 17, 0, 0, 1, 4, 64, 2, 16, 1, 3, 11, 2, 7, 2, 10, 10, 2, 2, 2, 2, 4, 4, 4, 4, 0, 6, 32, 3, 32, 4, 17, 4, 0, 1, 7, 32, 5, 17, 5, 0, 2, 7, 21, 3, 0, 1, 68, 0, 69, 0, 69, 67, 0, 0, 4, 1, 0, 8, 33, 5, 33, 4, 32, 6, 32, 7, 17, 7, 0, 1, 5, 32, 8, 17, 8, 0, 2, 5, 21, 6, 0, 1, 71, 0, 72, 0, 69, 70, 0, 0, 3, 2, 0, 9, 33, 8, 33, 7, 32, 9, 17, 9, 0, 1, 6, 32, 10, 17, 10, 0, 2, 6, 21, 0, 0, 1, 73, 0, 74, 0, 33, 10, 33, 9, 68, 6, 0, 2, 33, 8, 33, 7, 68, 5, 0, 2, 33, 5, 33, 4, 68, 5, 0, 1, 17, 0, 0, 128, 0, 68, 6, 0, 2, 33, 6, 33, 3, 64, 3, 17, 1, 3, 2, 1, 1, 1, 10, 0, 1, 17, 0, 0, 131, 0, 64, 4, 18, 1, 3, 2, 1, 1, 11, 11, 0, 1, 17, 0, 0, 1, 4, 64, 5, 19, 1, 3, 3, 2, 1, 2, 11, 11, 0, 1, 17, 0, 0, 128, 1, 64, 6, 44, 1, 3, 2, 1, 1, 1, 11, 0, 1, 17, 0, 0, 131, 0, 64, 7, 11, 1, 3, 23, 2, 11, 14, 4, 4, 1, 2, 4, 19, 11, 4, 4, 4, 2, 2, 4, 4, 4, 4, 4, 16, 12, 4, 4, 11, 0, 5, 32, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 21, 4, 0, 1, 69, 0, 130, 0, 69, 68, 0, 0, 2, 1, 0, 7, 33, 5, 32, 7, 23, 7, 0, 1, 24, 0, 0, 2, 71, 0, 33, 7, 33, 4, 33, 3, 68, 10, 0, 10, 33, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 8, 32, 9, 17, 9, 0, 1, 0, 32, 10, 17, 10, 0, 2, 0, 21, 11, 0, 1, 10, 0, 130, 0, 72, 75, 0, 0, 3, 252, 0, 7, 21, 8, 0, 11, 73, 0, 74, 0, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 8, 0, 21, 12, 0, 1, 77, 0, 130, 0, 69, 76, 0, 0, 5, 4, 0, 5, 33, 13, 32, 14, 17, 14, 0, 1, 0, 24, 0, 0, 1, 78, 0, 33, 14, 68, 9, 0, 7, 33, 13, 32, 15, 32, 16, 17, 16, 0, 2, 0, 32, 17, 17, 17, 0, 8, 0, 21, 18, 0, 14, 16, 0, 17, 0, 72, 82, 2, 0, 6, 252, 0, 8, 17, 15, 0, 82, 1, 33, 17, 33, 16, 32, 19, 32, 20, 17, 20, 0, 1, 0, 32, 21, 17, 21, 0, 15, 0, 75, 23, 19, 0, 7, 252, 84, 0, 85, 0, 0, 4, 33, 21, 33, 20, 32, 22, 23, 22, 0, 1, 75, 28, 0, 0, 8, 252, 83, 0, 86, 0, 0, 3, 33, 22, 33, 19, 33, 15, 68, 9, 0, 2, 33, 12, 33, 8, 68, 10, 0, 0, 64, 8, 12, 1, 3, 40, 2, 23, 15, 10, 10, 1, 2, 19, 11, 4, 14, 14, 4, 4, 4, 14, 19, 14, 4, 4, 2, 4, 4, 4, 2, 14, 14, 12, 4, 4, 11, 4, 14, 19, 14, 4, 18, 10, 4, 4, 2, 4, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 3, 69, 68, 0, 0, 2, 1, 0, 6, 32, 6, 23, 6, 0, 1, 24, 0, 0, 2, 70, 0, 33, 6, 33, 4, 33, 3, 68, 22, 0, 10, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 7, 32, 8, 32, 9, 32, 10, 17, 10, 0, 1, 2, 32, 11, 17, 11, 0, 2, 1, 75, 11, 9, 0, 3, 252, 74, 0, 75, 0, 0, 2, 33, 11, 33, 10, 74, 29, 8, 0, 4, 252, 73, 0, 0, 3, 33, 9, 48, 8, 0, 20, 12, 0, 8, 0, 70, 76, 0, 0, 6, 1, 7, 5, 0, 0, 67, 0, 12, 32, 16, 17, 16, 0, 8, 8, 17, 7, 0, 16, 0, 33, 16, 33, 8, 32, 17, 32, 18, 32, 19, 17, 19, 0, 1, 1, 32, 20, 17, 20, 0, 2, 1, 21, 18, 0, 6, 83, 0, 84, 0, 69, 82, 0, 0, 10, 9, 0, 4, 32, 13, 17, 13, 0, 8, 9, 32, 15, 17, 15, 0, 13, 0, 74, 30, 0, 0, 8, 252, 79, 0, 0, 3, 33, 15, 33, 13, 33, 8, 68, 21, 0, 3, 33, 20, 33, 19, 17, 17, 0, 1, 1, 68, 11, 0, 3, 33, 20, 33, 19, 17, 17, 0, 2, 1, 68, 11, 0, 4, 33, 18, 32, 21, 32, 22, 17, 22, 0, 2, 3, 69, 86, 0, 0, 13, 12, 0, 1, 17, 21, 0, 7, 0, 68, 20, 0, 7, 32, 23, 32, 24, 32, 25, 32, 26, 17, 26, 0, 7, 0, 32, 27, 17, 27, 0, 2, 2, 75, 23, 25, 0, 14, 252, 90, 0, 91, 0, 0, 4, 33, 27, 33, 26, 32, 28, 23, 28, 0, 1, 75, 28, 24, 0, 15, 252, 89, 0, 92, 0, 0, 2, 33, 28, 33, 25, 74, 29, 23, 0, 16, 252, 88, 0, 0, 3, 33, 24, 48, 23, 0, 20, 29, 0, 23, 0, 70, 93, 0, 0, 17, 1, 18, 5, 0, 5, 32, 33, 17, 33, 0, 23, 8, 17, 21, 0, 33, 0, 33, 33, 33, 23, 68, 20, 0, 4, 32, 30, 17, 30, 0, 23, 9, 32, 32, 17, 32, 0, 30, 0, 74, 30, 0, 0, 19, 252, 96, 0, 0, 6, 33, 32, 33, 30, 33, 23, 33, 22, 33, 21, 33, 17, 68, 21, 0, 23, 33, 22, 32, 34, 32, 35, 32, 36, 17, 36, 0, 17, 0, 32, 37, 17, 37, 0, 21, 0, 32, 38, 17, 38, 0, 2, 3, 26, 35, 0, 1, 100, 0, 101, 0, 102, 0, 33, 38, 33, 37, 33, 36, 32, 39, 17, 39, 0, 7, 0, 25, 34, 0, 4, 99, 0, 103, 0, 33, 39, 33, 35, 24, 0, 0, 1, 98, 0, 33, 34, 33, 21, 33, 17, 33, 7, 68, 22, 0, 1, 33, 7, 68, 22, 0, 0, 64, 9, 13, 1, 3, 53, 4, 25, 13, 10, 4, 4, 4, 1, 2, 4, 2, 4, 4, 4, 2, 19, 2, 1, 2, 4, 4, 19, 17, 4, 4, 4, 16, 1, 2, 4, 4, 2, 4, 19, 4, 4, 4, 16, 4, 4, 4, 2, 4, 4, 4, 4, 4, 16, 16, 17, 4, 4, 4, 16, 4, 0, 5, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 1, 21, 6, 0, 1, 71, 0, 130, 0, 69, 70, 0, 0, 2, 1, 0, 1, 33, 7, 68, 5, 0, 8, 33, 7, 32, 8, 32, 9, 32, 10, 17, 10, 0, 2, 0, 32, 11, 17, 11, 0, 1, 1, 21, 12, 0, 1, 11, 0, 130, 0, 72, 76, 0, 0, 3, 252, 0, 4, 21, 9, 0, 11, 74, 0, 75, 0, 33, 11, 33, 10, 21, 8, 0, 2, 73, 0, 130, 0, 69, 72, 0, 0, 6, 4, 0, 1, 33, 9, 68, 5, 0, 4, 23, 0, 0, 2, 33, 8, 33, 6, 33, 5, 68, 24, 0, 7, 33, 9, 17, 5, 0, 131, 0, 33, 8, 33, 6, 33, 5, 32, 14, 17, 14, 0, 1, 3, 69, 78, 0, 0, 8, 7, 0, 7, 32, 25, 32, 26, 32, 27, 17, 27, 0, 3, 0, 32, 28, 17, 28, 0, 1, 2, 21, 26, 0, 3, 91, 0, 92, 0, 69, 90, 0, 0, 13, 12, 0, 7, 32, 15, 32, 16, 32, 17, 17, 17, 0, 3, 0, 32, 18, 17, 18, 0, 1, 2, 21, 16, 0, 3, 81, 0, 82, 0, 69, 80, 0, 0, 10, 9, 0, 5, 33, 18, 33, 17, 23, 0, 0, 2, 33, 16, 33, 15, 68, 23, 0, 12, 33, 18, 33, 17, 17, 15, 0, 131, 0, 33, 16, 33, 15, 32, 20, 32, 21, 32, 22, 17, 22, 0, 3, 0, 32, 23, 17, 23, 0, 1, 2, 21, 24, 0, 14, 22, 0, 23, 0, 72, 88, 2, 0, 11, 252, 0, 7, 17, 21, 0, 88, 1, 33, 23, 33, 22, 25, 20, 0, 4, 85, 0, 130, 1, 33, 21, 24, 0, 0, 1, 84, 0, 33, 20, 68, 22, 0, 2, 33, 28, 33, 27, 68, 16, 0, 6, 33, 28, 33, 27, 32, 29, 32, 30, 17, 30, 0, 4, 0, 21, 29, 0, 1, 94, 0, 130, 0, 69, 93, 0, 0, 15, 14, 0, 1, 33, 30, 68, 16, 0, 11, 33, 30, 17, 25, 0, 131, 0, 33, 29, 33, 26, 33, 25, 32, 32, 32, 33, 17, 33, 0, 3, 0, 32, 34, 17, 34, 0, 1, 2, 21, 35, 0, 14, 33, 0, 34, 0, 72, 99, 2, 0, 17, 252, 0, 4, 23, 0, 0, 2, 33, 29, 33, 26, 33, 25, 68, 23, 0, 9, 17, 32, 0, 99, 1, 33, 34, 33, 33, 32, 36, 32, 37, 17, 37, 0, 32, 0, 32, 38, 17, 38, 0, 4, 0, 21, 39, 0, 1, 38, 0, 130, 0, 72, 103, 0, 0, 18, 252, 0, 12, 21, 36, 0, 10, 101, 0, 102, 0, 33, 38, 33, 37, 32, 40, 32, 41, 17, 41, 0, 1, 2, 32, 42, 32, 43, 17, 43, 0, 36, 0, 32, 44, 17, 44, 0, 4, 0, 21, 45, 0, 15, 43, 0, 44, 0, 72, 109, 2, 0, 19, 252, 0, 4, 17, 42, 0, 109, 1, 33, 44, 33, 43, 21, 46, 0, 13, 41, 0, 42, 0, 72, 110, 2, 0, 20, 252, 0, 10, 17, 40, 0, 110, 1, 33, 42, 33, 41, 32, 47, 32, 48, 32, 49, 17, 49, 0, 3, 0, 32, 50, 17, 50, 0, 40, 0, 21, 51, 0, 14, 49, 0, 50, 0, 72, 115, 2, 0, 21, 252, 0, 13, 17, 48, 0, 115, 1, 33, 50, 33, 49, 32, 52, 17, 52, 0, 36, 0, 25, 47, 0, 4, 112, 0, 116, 0, 33, 52, 33, 48, 24, 0, 0, 1, 111, 0, 33, 47, 33, 40, 33, 36, 33, 32, 68, 22, 0, 1, 33, 14, 68, 24, 0, 1, 33, 14, 68, 24, 0, 0, 64, 10, 14, 1, 3, 31, 3, 14, 4, 4, 4, 4, 10, 4, 4, 1, 1, 2, 4, 4, 1, 2, 13, 13, 10, 4, 4, 4, 4, 1, 2, 4, 19, 4, 4, 4, 19, 1, 19, 0, 7, 32, 4, 26, 4, 0, 1, 130, 4, 130, 8, 128, 1, 32, 5, 17, 5, 0, 130, 8, 32, 6, 17, 6, 0, 130, 0, 32, 7, 68, 1, 0, 6, 32, 9, 32, 10, 17, 10, 0, 5, 0, 32, 11, 17, 11, 0, 2, 0, 21, 9, 0, 4, 74, 0, 75, 0, 69, 73, 0, 0, 12, 2, 0, 12, 33, 11, 33, 10, 32, 12, 32, 13, 32, 14, 32, 15, 32, 16, 17, 16, 0, 4, 0, 32, 17, 17, 17, 0, 1, 0, 32, 18, 17, 18, 0, 5, 0, 77, 13, 15, 0, 3, 252, 80, 0, 81, 0, 82, 0, 130, 4, 0, 4, 19, 14, 0, 0, 15, 0, 33, 18, 33, 17, 33, 16, 74, 31, 13, 0, 4, 252, 78, 0, 0, 0, 69, 77, 0, 0, 7, 5, 0, 5, 33, 15, 33, 14, 32, 19, 32, 20, 17, 20, 0, 6, 0, 75, 40, 19, 0, 6, 252, 84, 0, 130, 1, 0, 4, 33, 20, 17, 6, 0, 83, 0, 33, 19, 17, 12, 0, 131, 0, 68, 8, 0, 3, 33, 15, 33, 14, 17, 12, 0, 131, 0, 68, 8, 0, 7, 33, 13, 33, 12, 32, 21, 32, 22, 32, 23, 17, 23, 0, 3, 0, 21, 22, 0, 1, 87, 0, 130, 0, 69, 86, 0, 0, 10, 9, 0, 4, 33, 23, 17, 7, 0, 131, 0, 33, 22, 33, 21, 68, 13, 0, 9, 33, 23, 17, 21, 0, 131, 0, 33, 22, 33, 21, 32, 25, 32, 26, 17, 26, 0, 5, 0, 32, 27, 17, 27, 0, 3, 0, 75, 40, 25, 0, 11, 252, 90, 0, 91, 0, 0, 6, 33, 27, 33, 26, 17, 5, 0, 89, 0, 33, 25, 17, 8, 0, 131, 0, 33, 9, 68, 1, 0, 5, 33, 11, 33, 10, 32, 29, 17, 7, 0, 131, 0, 33, 29, 68, 13, 0, 6, 33, 9, 33, 7, 17, 0, 0, 6, 0, 33, 6, 33, 5, 33, 4, 64]

def realLoopPrefixProbePreserveUbBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 13, 126, 1, 1, 43, 1, 3, 22, 4, 9, 3, 5, 2, 4, 4, 1, 2, 4, 3, 1, 1, 2, 4, 4, 4, 4, 4, 3, 3, 19, 1, 19, 0, 3, 32, 5, 32, 6, 17, 6, 0, 2, 0, 69, 70, 0, 0, 2, 1, 0, 2, 48, 1, 4, 17, 5, 0, 131, 0, 68, 3, 0, 1, 17, 5, 0, 131, 0, 68, 3, 0, 7, 33, 6, 33, 5, 32, 7, 17, 7, 0, 130, 0, 32, 8, 17, 8, 0, 129, 0, 32, 9, 68, 4, 0, 6, 32, 11, 32, 12, 17, 12, 0, 7, 0, 32, 13, 17, 13, 0, 3, 0, 21, 11, 0, 2, 76, 0, 77, 0, 69, 75, 0, 0, 8, 5, 0, 7, 33, 13, 33, 12, 32, 14, 32, 15, 17, 15, 0, 7, 0, 32, 16, 17, 16, 0, 4, 0, 75, 40, 14, 0, 6, 252, 79, 0, 80, 0, 0, 7, 33, 16, 33, 15, 17, 7, 0, 78, 0, 33, 14, 32, 17, 32, 18, 17, 18, 0, 8, 0, 75, 20, 17, 0, 7, 252, 82, 0, 129, 1, 0, 5, 33, 18, 21, 8, 0, 12, 81, 0, 129, 3, 33, 17, 17, 10, 0, 131, 0, 33, 11, 68, 4, 0, 10, 33, 13, 33, 12, 32, 20, 17, 9, 0, 131, 0, 33, 20, 33, 11, 33, 9, 17, 0, 0, 8, 0, 33, 8, 33, 7, 64]

def realLoopPrefixProbeDefaultBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 9, 62, 212, 1, 1, 43, 1, 3, 22, 4, 9, 3, 5, 2, 4, 4, 1, 2, 4, 3, 1, 1, 2, 4, 4, 4, 4, 4, 3, 3, 19, 1, 19, 0, 3, 32, 5, 32, 6, 17, 6, 0, 2, 0, 69, 70, 0, 0, 2, 1, 0, 1, 17, 5, 0, 131, 0, 68, 3, 0, 1, 17, 5, 0, 131, 0, 68, 3, 0, 7, 33, 6, 33, 5, 32, 7, 17, 7, 0, 130, 0, 32, 8, 17, 8, 0, 129, 0, 32, 9, 68, 4, 0, 6, 32, 11, 32, 12, 17, 12, 0, 7, 0, 32, 13, 17, 13, 0, 3, 0, 21, 11, 0, 2, 76, 0, 77, 0, 69, 75, 0, 0, 8, 5, 0, 7, 33, 13, 33, 12, 32, 14, 32, 15, 17, 15, 0, 7, 0, 32, 16, 17, 16, 0, 4, 0, 75, 40, 14, 0, 6, 252, 79, 0, 80, 0, 0, 7, 33, 16, 33, 15, 17, 7, 0, 78, 0, 33, 14, 32, 17, 32, 18, 17, 18, 0, 8, 0, 75, 20, 17, 0, 7, 252, 82, 0, 129, 1, 0, 5, 33, 18, 21, 8, 0, 12, 81, 0, 129, 3, 33, 17, 17, 10, 0, 131, 0, 33, 11, 68, 4, 0, 10, 33, 13, 33, 12, 32, 20, 17, 9, 0, 131, 0, 33, 20, 33, 11, 33, 9, 17, 0, 0, 8, 0, 33, 8, 33, 7, 64]

def stmtsHavePlaceMention : List WireStmt → Bool
  | [] => false
  | .placeMention _ :: _ => true
  | _ :: ss => stmtsHavePlaceMention ss

def bodyHasPlaceMention : List WireBlock → Bool
  | [] => false
  | blk :: blks => bif stmtsHavePlaceMention blk.stmts then true else bodyHasPlaceMention blks

def isDerefProj : ProjChain → Bool
  | .deref => true
  | _ => false

def stmtIsDerefCopy : WireStmt → Bool
  | .assignUseNoRetag _ (.copy src) => isDerefProj src.proj
  | .assignUseRetagYes _ (.copy src) => isDerefProj src.proj
  | .assignUseNoRetag _ (.move src) => isDerefProj src.proj
  | .assignUseRetagYes _ (.move src) => isDerefProj src.proj
  | .assignCopyForDeref _ src => isDerefProj src.proj
  | _ => false

def stmtsHaveDerefCopy : List WireStmt → Bool
  | [] => false
  | st :: ss => bif stmtIsDerefCopy st then true else stmtsHaveDerefCopy ss

def bodyHasDerefCopyAssign : List WireBlock → Bool
  | [] => false
  | blk :: blks => bif stmtsHaveDerefCopy blk.stmts then true else bodyHasDerefCopyAssign blks

structure BodyAcceptSummary where
  symId : Nat
  originKind : BodyOriginKind
  mirPhase : MirPhaseTag
  blockCount : Nat
  localCount : Nat
  hasDerefCopy : Bool
  hasPlaceMention : Bool
  deriving DecidableEq, Repr

structure PackageAcceptSummary where
  bodyCount : Nat
  preserveUb : Bool
  bodies : List BodyAcceptSummary
  deriving DecidableEq, Repr

def summarizeBodies : List WireBody → List BodyAcceptSummary
  | [] => []
  | b :: bs =>
      { symId := b.symId
      , originKind := b.originKind
      , mirPhase := b.mirPhase
      , blockCount := b.blocks.length
      , localCount := b.localCount
      , hasDerefCopy := bodyHasDerefCopyAssign b.blocks
      , hasPlaceMention := bodyHasPlaceMention b.blocks } :: summarizeBodies bs

def acceptedPackageSummary (bytes : List Nat) : Option PackageAcceptSummary :=
  match parseWirePackage bytes with
  | .accepted pkg =>
      some { bodyCount := pkg.bodies.length
            , preserveUb := pkg.preserveUb
            , bodies := summarizeBodies pkg.bodies }
  | _ => none

def parseAdmittedPackageBytes (bytes : List Nat) : Option WirePackage :=
  match parseWirePackage bytes with
  | .accepted pkg =>
      bif checkPackageAdmissionClosure pkg then some pkg else none
  | _ => none

def parseAdmittedRawPackageBytes (bytes : List Nat) : Option WirePackage :=
  match parseRawPackageBytes bytes with
  | .ok (pkg, []) =>
      bif checkPackageAdmissionClosure pkg then some pkg else none
  | _ => none

def isAdmittedPackageBytes (bytes : List Nat) : Bool :=
  match parseWirePackage bytes with
  | .accepted pkg => checkPackageAdmissionClosure pkg
  | _ => false

theorem real_place_mention_preserve_ub_bytes_accepted_and_preserves_mentions :
    acceptedPackageSummary realPlaceMentionPreserveUbBytes =
      some { bodyCount := 3
            , preserveUb := true
            , bodies :=
              [ { symId := 6, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 4, localCount := 6, hasDerefCopy := true, hasPlaceMention := true }
              , { symId := 9, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 4, localCount := 6, hasDerefCopy := false, hasPlaceMention := true }
              , { symId := 10, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 1, localCount := 4, hasDerefCopy := false, hasPlaceMention := true }
              ] } ∧
    isAdmittedPackageBytes realPlaceMentionPreserveUbBytes = true := by
  decide

theorem real_place_mention_default_bytes_accepted_and_drops_wildcard_mentions :
    acceptedPackageSummary realPlaceMentionDefaultBytes =
      some { bodyCount := 3
            , preserveUb := false
            , bodies :=
              [ { symId := 6, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 4, localCount := 6, hasDerefCopy := true, hasPlaceMention := false }
              , { symId := 9, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 4, localCount := 6, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 10, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 1, localCount := 4, hasDerefCopy := false, hasPlaceMention := false }
              ] } ∧
    isAdmittedPackageBytes realPlaceMentionDefaultBytes = true := by
  decide

theorem real_cleanup_subject_preserve_ub_bytes_accepted_without_block_truncation :
    acceptedPackageSummary realCleanupSubjectPreserveUbBytes =
      some { bodyCount := 9
            , preserveUb := true
            , bodies :=
              [ { symId := 1, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 4, localCount := 9, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 2, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 2, localCount := 6, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 3, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 5, localCount := 10, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 4, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 17, localCount := 22, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 5, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 9, localCount := 24, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 6, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 4, localCount := 6, hasDerefCopy := true, hasPlaceMention := true }
              , { symId := 7, originKind := .compilerShim, mirPhase := .runtimeOptimized, blockCount := 2, localCount := 4, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 8, originKind := .compilerShim, mirPhase := .runtimeOptimized, blockCount := 5, localCount := 2, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 24, originKind := .externalOptimized, mirPhase := .runtimeOptimized, blockCount := 2, localCount := 2, hasDerefCopy := false, hasPlaceMention := false }
              ] } ∧
    isAdmittedPackageBytes realCleanupSubjectPreserveUbBytes = true := by
  decide

theorem real_zerocopy_layout_holdout_bytes_accepted_without_block_truncation :
    acceptedPackageSummary realZerocopyLayoutHoldoutBytes =
      some { bodyCount := 10
            , preserveUb := true
            , bodies :=
              [ { symId := 15, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 1, localCount := 2, hasDerefCopy := true, hasPlaceMention := false }
              , { symId := 16, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 7, localCount := 11, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 17, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 1, localCount := 2, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 18, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 1, localCount := 2, hasDerefCopy := true, hasPlaceMention := false }
              , { symId := 19, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 1, localCount := 3, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 44, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 1, localCount := 2, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 11, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 11, localCount := 23, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 12, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 23, localCount := 40, hasDerefCopy := false, hasPlaceMention := true }
              , { symId := 13, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 25, localCount := 53, hasDerefCopy := false, hasPlaceMention := false }
              , { symId := 14, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 14, localCount := 31, hasDerefCopy := false, hasPlaceMention := false }
              ] } ∧
    isAdmittedPackageBytes realZerocopyLayoutHoldoutBytes = true := by
  decide

theorem real_loop_prefix_probe_preserve_ub_bytes_accepted_and_admitted :
    acceptedPackageSummary realLoopPrefixProbePreserveUbBytes =
      some { bodyCount := 1
            , preserveUb := true
            , bodies :=
              [ { symId := 43, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 9, localCount := 22, hasDerefCopy := false, hasPlaceMention := true }
              ] } ∧
    isAdmittedPackageBytes realLoopPrefixProbePreserveUbBytes = true := by
  decide

#print axioms universal_accepted_byte_soundness
#print axioms universal_accepted_package_canonical_unique
#print axioms real_place_mention_preserve_ub_bytes_accepted_and_preserves_mentions
#print axioms real_place_mention_default_bytes_accepted_and_drops_wildcard_mentions
#print axioms real_cleanup_subject_preserve_ub_bytes_accepted_without_block_truncation
#print axioms real_zerocopy_layout_holdout_bytes_accepted_without_block_truncation
#print axioms real_loop_prefix_probe_preserve_ub_bytes_accepted_and_admitted

end AnnealResearch.SubstantiveMirByteParser
