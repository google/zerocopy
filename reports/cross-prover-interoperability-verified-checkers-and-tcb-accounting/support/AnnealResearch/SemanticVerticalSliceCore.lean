/-
  Experiment: experiments/opsem/semantic-vertical-slice
  Task FD-03 (FE-I1 & FE-I4) / Milestones C2 & C3 (Updated under #62 R2, R3, R4):
  Decoded-AST Operational Interpreter, Disjoint Cleanup Storage & Chronological Observer,
  Finite-Width `u32`/`usize` Machine Primitives, `Arguments::from_str` vs `panic_fmt`
  Separation, Unconditional All-Prefix Loop Theorem, and Matched-Scope Charon Comparison

  Key C2 & C3 properties (#62 R2–R4):
  1. Executes the decoded `WirePackage` (`WireBody`, `WireBlock`, `WireStmt`, `WireTerm`)
     from `SubstantiveMirByteParser` directly over a concrete call stack, per-frame local store
     (`List (Nat × RtVal)`), per-local declared `MirTypeTag` table (`List MirTypeTag`),
     disjoint `EffectLog` heap allocations (`slot 0` for `log1`, `slot 1` for `log2`), and
     a ghost chronological event observer (`obsEvents : List Nat`).
     Never dispatches on package-level header flags (`preserveUb`, `monoComplete`) or
     hardcoded outcomes.
  2. R2 (Disjoint Cleanup Storage & Chronological Observer):
     - Passes `log1 = .heapPtr 0` and `log2 = .heapPtr 1` as distinct heap allocations,
       preserving their disjoint residual states `(stepCount, traceAcc)` across references,
       moves, `core::mem::drop::<Guard>` (`sym = 24`), `core::mem::forget::<Guard>` (`sym = 25`),
       partial field reinitialization, and drop glue (`sym = 7, 8`).
     - Records global chronological events (`obsEvents : List Nat`) directly from the executed
       `EffectLog::record` (`sym = 1`) call and its actual tag argument without altering Rust
       program storage or reconstructing tags via accumulator subtraction.
  3. R3 (Finite-Width `u32`/`usize` Machine Primitives & `Arguments::from_str` vs `panic_fmt`):
     - Enforces 32-bit `u32` (`mod 2^32`) and 64-bit `usize` (`mod 2^64`) wrapping, checked,
       and overflow-reporting (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow`)
       semantics using the destination local's `MirTypeTag` and width-specific intrinsic
       callees (`20, 21, 42` for `u32` vs `40, 41, 23` for `usize`).
     - Proves all 10 C0 `zerocopy_layout_holdout.rs` vectors including the 64-bit checked-add
       overflow boundary `align_to(usize::MAX - 1, 4) = Err(SizeError)` (`none`) and the
       `u32` wrapping boundary on `EffectLog::record` (`step_count = u32::MAX -> 0`,
       `trace_acc = 0x10000000 * 16 + 7 -> 7`).
     - Separates `core::fmt::Arguments::from_str` (`sym = 26`, normal return constructing
       `.opaqueFmtArgs`) from `core::panicking::panic_fmt` (`sym = 27`, initiating `.unwinding`).
  4. R4 (Unconditional All-Prefix Loop Theorem on Unmodified Captured Source):
     - Captures `unbounded_period4_probe` (`sym = 43` in `realLoopPrefixProbePreserveUbBytes`)
       from unmodified `place_mention_probe.rs` and proves an unconditional all-prefix theorem
       (`unbounded_period4_all_prefixes_running_and_enabled : ∀ n : Nat, ...`) over all
       reachable interpreter states (entry prefix `0..6`, loop-header cuts `7 + 4 * k` at `bb4`,
       and intermediate loop-body blocks `bb5, bb6, bb7`) with zero unproved hypotheses,
       paired with the finite bad-prefix UB witness (`probe_ptr = true, ptrValid = false`)
       and terminating witness (`step = 4 -> some 2`).
-/

import AnnealResearch.SubstantiveMirByteParser

set_option autoImplicit false
set_option maxRecDepth 65536

namespace AnnealResearch.SemanticVerticalSlice

open AnnealResearch.SubstantiveMirByteParser

/-! ## Bridge Lemma: `parseWirePackage = .accepted pkg` Implies `parseRawPackageBytes = .ok (pkg, [])` -/

theorem accepted_bytes_raw_parse_sound
    (bytes : List Nat) (pkg : WirePackage)
    (h : parseWirePackage bytes = .accepted pkg) :
    parseRawPackageBytes bytes = .ok (pkg, []) ∧
    physicalBytesValid bytes = true ∧
    specEncodePackage pkg = bytes ∧
    checkPackageWellFormed pkg = true := by
  unfold parseWirePackage at h
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
                exact ⟨rfl, hphys, listNatBeq_eq_true henc, hwf⟩
              · contradiction
            · contradiction
  · contradiction

/-! ## Boundary 3: Subject & Compilation-Context Binding -/

structure SubjectBindingContract where
  expectedVersion : Nat
  expectedPhase : MirPhaseTag
  requireMonoComplete : Bool
  requirePreserveUb : Bool
  requireUbChecks : Bool
  expectedFpHi : Nat
  expectedFpLo : Nat
  requiredSymIds : List Nat
  deriving DecidableEq, Repr

def bodyListHasSym (sym : Nat) : List WireBody → Bool
  | [] => false
  | b :: bs => bif Nat.beq b.symId sym then true else bodyListHasSym sym bs

def bodyListHasAllSyms (bodies : List WireBody) : List Nat → Bool
  | [] => true
  | s :: ss => bif bodyListHasSym s bodies then bodyListHasAllSyms bodies ss else false

def checkSubjectBinding (contract : SubjectBindingContract) (pkg : WirePackage) : Bool :=
  Nat.beq pkg.version contract.expectedVersion &&
  decide (pkg.defaultPhase = contract.expectedPhase) &&
  (bif contract.requireMonoComplete then pkg.monoComplete else true) &&
  (bif contract.requirePreserveUb then pkg.preserveUb else true) &&
  (bif contract.requireUbChecks then pkg.ubChecks else true) &&
  Nat.beq pkg.fpHi contract.expectedFpHi &&
  Nat.beq pkg.fpLo contract.expectedFpLo &&
  bodyListHasAllSyms pkg.bodies contract.requiredSymIds

def cleanupSubjectBindingContract : SubjectBindingContract :=
  { expectedVersion := 3
  , expectedPhase := .runtimePostCleanup
  , requireMonoComplete := true
  , requirePreserveUb := true
  , requireUbChecks := true
  , expectedFpHi := 167
  , expectedFpLo := 56
  , requiredSymIds := [1, 2, 3, 4, 5, 6, 7, 8, 24] }

def placeMentionPreserveUbBindingContract : SubjectBindingContract :=
  { expectedVersion := 3
  , expectedPhase := .runtimePostCleanup
  , requireMonoComplete := true
  , requirePreserveUb := true
  , requireUbChecks := true
  , expectedFpHi := 62
  , expectedFpLo := 110
  , requiredSymIds := [6, 9, 10] }

def zerocopyHoldoutBindingContract : SubjectBindingContract :=
  { expectedVersion := 3
  , expectedPhase := .runtimePostCleanup
  , requireMonoComplete := true
  , requirePreserveUb := true
  , requireUbChecks := true
  , expectedFpHi := 227
  , expectedFpLo := 80
  , requiredSymIds := [15, 16, 17, 18, 19, 44, 11, 12, 13, 14] }

def loopPrefixProbePreserveUbBindingContract : SubjectBindingContract :=
  { expectedVersion := 3
  , expectedPhase := .runtimePostCleanup
  , requireMonoComplete := true
  , requirePreserveUb := true
  , requireUbChecks := true
  , expectedFpHi := 13
  , expectedFpLo := 126
  , requiredSymIds := [43] }

/-! ## Boundary 4: Decoded-AST Operational Semantics (`R2` & `R3`) -/

def u32Mod : Nat := 4294967296
def u32Max : Nat := 4294967295
def usizeMod : Nat := 18446744073709551616
def usizeMax : Nat := 18446744073709551615

inductive RtVal where
  | scalar (v : Nat)
  | agg0 (kind : Nat)
  | agg1 (kind : Nat) (f0 : RtVal)
  | agg2 (kind : Nat) (f0 f1 : RtVal)
  | agg3 (kind : Nat) (f0 f1 f2 : RtVal)
  | heapPtr (slot : Nat)
  | extPtr (valid : Bool)
  | refVal (inner : RtVal)
  | opaqueFmtArgs (tag : Nat)
  deriving DecidableEq, Repr

/--
  Pure Rust `EffectLog` allocation slot (`step_count: u32`, `trace_acc: u32`).
  Global chronological events are tracked separately in `ExecState.obsEvents` without
  modifying Rust program storage or reconstructing tags by subtraction.
-/
structure HeapLogSlot where
  stepCount : Nat
  traceAcc : Nat
  deriving DecidableEq, Repr

structure PendingReturn where
  retDst : PlaceSpec
  targetBbOpt : Option Nat
  unwind : UnwindSpec
  isDropGlue : Bool
  deriving DecidableEq, Repr

structure ExecFrame where
  symId : Nat
  localTypes : List MirTypeTag
  bodyBlocks : List WireBlock
  bbIdx : Nat
  remStmts : List WireStmt
  curTerm : WireTerm
  locals : List (Nat × RtVal)
  pending : Option PendingReturn
  deriving DecidableEq, Repr

inductive ExecStatus where
  | running
  | returned (retVal : RtVal)
  | unwinding
  | unwoundTop
  | terminatedAbort (reason : Nat)
  | ub
  | missingBody (symId : Nat)
  | stuck
  deriving DecidableEq, Repr

structure ExecState where
  status : ExecStatus
  stack : List ExecFrame
  heap : List HeapLogSlot
  obsEvents : List Nat
  deriving DecidableEq, Repr

def findBodyBySym (bodies : List WireBody) (sym : Nat) : Option WireBody :=
  match bodies with
  | [] => none
  | b :: bs => bif Nat.beq b.symId sym then some b else findBodyBySym bs sym

def getBlockAt : List WireBlock → Nat → Option WireBlock
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: bs, n + 1 => getBlockAt bs n

def getLocalTypeAt : List MirTypeTag → Nat → MirTypeTag
  | [], _ => .u32
  | t :: _, 0 => t
  | _ :: ts, n + 1 => getLocalTypeAt ts n

def modulusForType : MirTypeTag → Option Nat
  | .u32 => some u32Mod
  | .checkedArithTupleU32 => some u32Mod
  | .usize => some usizeMod
  | .checkedArithTuple => some usizeMod
  | .bool => some 2
  | _ => none

def getLocal (locals : List (Nat × RtVal)) (k : Nat) : Option RtVal :=
  match locals with
  | [] => none
  | (k', v) :: rest => bif Nat.beq k k' then some v else getLocal rest k

def setLocal (locals : List (Nat × RtVal)) (k : Nat) (v : RtVal) : List (Nat × RtVal) :=
  match locals with
  | [] => [(k, v)]
  | (k', v') :: rest =>
      bif Nat.beq k k' then (k, v) :: rest
      else bif Nat.blt k k' then (k, v) :: (k', v') :: rest
      else (k', v') :: setLocal rest k v

def eraseLocal (locals : List (Nat × RtVal)) (k : Nat) : List (Nat × RtVal) :=
  match locals with
  | [] => []
  | (k', v') :: rest =>
      bif Nat.beq k k' then rest
      else (k', v') :: eraseLocal rest k

def getHeapSlot : List HeapLogSlot → Nat → Option HeapLogSlot
  | [], _ => none
  | h :: _, 0 => some h
  | _ :: hs, n + 1 => getHeapSlot hs n

def setHeapSlot : List HeapLogSlot → Nat → HeapLogSlot → List HeapLogSlot
  | [], _, _ => []
  | _ :: hs, 0, nh => nh :: hs
  | h :: hs, n + 1, nh => h :: setHeapSlot hs n nh

def unwrapRef : RtVal → RtVal
  | .refVal inner => inner
  | v => v

def getFieldVal (v : RtVal) (idx : Nat) : Option RtVal :=
  match unwrapRef v with
  | .agg1 _ f0 => bif Nat.beq idx 0 then some f0 else none
  | .agg2 _ f0 f1 =>
      bif Nat.beq idx 0 then some f0
      else bif Nat.beq idx 1 then some f1
      else none
  | .agg3 _ f0 f1 f2 =>
      bif Nat.beq idx 0 then some f0
      else bif Nat.beq idx 1 then some f1
      else bif Nat.beq idx 2 then some f2
      else none
  | _ => none

def setFieldVal (v : RtVal) (idx : Nat) (nv : RtVal) : Option RtVal :=
  match v with
  | .agg1 k _ => bif Nat.beq idx 0 then some (.agg1 k nv) else none
  | .agg2 k f0 f1 =>
      bif Nat.beq idx 0 then some (.agg2 k nv f1)
      else bif Nat.beq idx 1 then some (.agg2 k f0 nv)
      else none
  | .agg3 k f0 f1 f2 =>
      bif Nat.beq idx 0 then some (.agg3 k nv f1 f2)
      else bif Nat.beq idx 1 then some (.agg3 k f0 nv f2)
      else bif Nat.beq idx 2 then some (.agg3 k f0 f1 nv)
      else none
  | .refVal inner =>
      match setFieldVal inner idx nv with
      | some ninner => some (.refVal ninner)
      | none => none
  | _ => none

inductive ReadResult where
  | val (v : RtVal)
  | ub
  | stuck
  deriving DecidableEq, Repr

def readPlace (locals : List (Nat × RtVal)) (heap : List HeapLogSlot) (p : PlaceSpec) : ReadResult :=
  match getLocal locals p.localIdx with
  | none => .stuck
  | some base =>
      match p.proj with
      | .here => .val base
      | .field0 =>
          match getFieldVal base 0 with
          | some v => .val v
          | none => .stuck
      | .field1 =>
          match getFieldVal base 1 with
          | some v => .val v
          | none => .stuck
      | .field2 =>
          match getFieldVal base 2 with
          | some v => .val v
          | none => .stuck
      | .downcast0Field0 =>
          match getFieldVal base 0 with
          | some v => .val v
          | none => .stuck
      | .downcast1Field0 =>
          match getFieldVal base 0 with
          | some v => .val v
          | none => .stuck
      | .deref =>
          match base with
          | .extPtr true => .val (.scalar 0)
          | .extPtr false => .ub
          | .heapPtr slot =>
              match getHeapSlot heap slot with
              | some h => .val (.agg2 3 (.scalar h.stepCount) (.scalar h.traceAcc))
              | none => .stuck
          | .refVal inner => .val inner
          | _ => .stuck
      | .derefField0 =>
          match base with
          | .heapPtr slot =>
              match getHeapSlot heap slot with
              | some h => .val (.scalar h.stepCount)
              | none => .stuck
          | _ =>
              match getFieldVal (unwrapRef base) 0 with
              | some v => .val v
              | none => .stuck
      | .derefField1 =>
          match base with
          | .heapPtr slot =>
              match getHeapSlot heap slot with
              | some h => .val (.scalar h.traceAcc)
              | none => .stuck
          | _ =>
              match getFieldVal (unwrapRef base) 1 with
              | some v => .val v
              | none => .stuck
      | .derefField2 =>
          match getFieldVal (unwrapRef base) 2 with
          | some v => .val v
          | none => .stuck

def makeRef (locals : List (Nat × RtVal)) (heap : List HeapLogSlot) (p : PlaceSpec) : ReadResult :=
  match getLocal locals p.localIdx with
  | none => .stuck
  | some base =>
      match p.proj with
      | .deref =>
          match base with
          | .heapPtr slot => .val (.heapPtr slot)
          | .extPtr b => .val (.extPtr b)
          | .refVal inner => .val (.refVal inner)
          | _ => .stuck
      | _ =>
          match readPlace locals heap p with
          | .val (.heapPtr slot) => .val (.heapPtr slot)
          | .val (.extPtr b) => .val (.extPtr b)
          | .val v => .val (.refVal v)
          | .ub => .ub
          | .stuck => .stuck

def writePlace
    (locals : List (Nat × RtVal))
    (heap : List HeapLogSlot)
    (p : PlaceSpec)
    (nv : RtVal) : Option (List (Nat × RtVal) × List HeapLogSlot) :=
  match p.proj with
  | .here => some (setLocal locals p.localIdx nv, heap)
  | .field0 =>
      match getLocal locals p.localIdx with
      | some base =>
          match setFieldVal base 0 nv with
          | some nb => some (setLocal locals p.localIdx nb, heap)
          | none => none
      | none => none
  | .field1 =>
      match getLocal locals p.localIdx with
      | some base =>
          match setFieldVal base 1 nv with
          | some nb => some (setLocal locals p.localIdx nb, heap)
          | none => none
      | none => none
  | .field2 =>
      match getLocal locals p.localIdx with
      | some base =>
          match setFieldVal base 2 nv with
          | some nb => some (setLocal locals p.localIdx nb, heap)
          | none => none
      | none => none
  | .derefField0 =>
      match getLocal locals p.localIdx, nv with
      | some (.heapPtr slot), .scalar sc =>
          match getHeapSlot heap slot with
          | some h =>
              let nh : HeapLogSlot := { stepCount := sc, traceAcc := h.traceAcc }
              some (locals, setHeapSlot heap slot nh)
          | none => none
      | _, _ => none
  | .derefField1 =>
      match getLocal locals p.localIdx, nv with
      | some (.heapPtr slot), .scalar ta =>
          match getHeapSlot heap slot with
          | some h =>
              let nh : HeapLogSlot := { stepCount := h.stepCount, traceAcc := ta }
              some (locals, setHeapSlot heap slot nh)
          | none => none
      | _, _ => none
  | _ => none

def evalOperand (locals : List (Nat × RtVal)) (heap : List HeapLogSlot) : OperandSpec → ReadResult
  | .copy p => readPlace locals heap p
  | .move p => readPlace locals heap p
  | .constBool b => .val (.scalar (bif b then 1 else 0))
  | .constU32 v => .val (.scalar v)
  | .constUsize v => .val (.scalar v)
  | .constUnit => .val (.agg0 1)
  | .constSizeError => .val (.agg0 1)
  | .constPanicStr => .val (.scalar 999)

def evalBinOp (dstTy : MirTypeTag) (op : BinOpTag) (lv rv : RtVal) : Option RtVal :=
  match lv, rv with
  | .scalar a, .scalar b =>
      match op with
      | .eq => some (.scalar (bif Nat.beq a b then 1 else 0))
      | .ne => some (.scalar (bif Nat.beq a b then 0 else 1))
      | .lt => some (.scalar (bif Nat.blt a b then 1 else 0))
      | .le => some (.scalar (bif Nat.ble a b then 1 else 0))
      | .gt => some (.scalar (bif Nat.blt b a then 1 else 0))
      | .ge => some (.scalar (bif Nat.ble b a then 1 else 0))
      | .div => bif Nat.beq b 0 then none else some (.scalar (a / b))
      | .rem => bif Nat.beq b 0 then none else some (.scalar (a % b))
      | .bitAnd => some (.scalar (Nat.land a b))
      | .add =>
          match modulusForType dstTy with
          | some m =>
              let s := a + b
              bif Nat.blt s m then some (.scalar s) else none
          | none => none
      | .sub =>
          match modulusForType dstTy with
          | some _ =>
              bif Nat.ble b a then some (.scalar (a - b)) else none
          | none => none
      | .mul =>
          match modulusForType dstTy with
          | some m =>
              let p := a * b
              bif Nat.blt p m then some (.scalar p) else none
          | none => none
      | .addWithOverflow =>
          match modulusForType dstTy with
          | some m =>
              let s := a + b
              let ovf := bif Nat.blt s m then 0 else 1
              some (.agg2 4 (.scalar (s % m)) (.scalar ovf))
          | none => none
      | .subWithOverflow =>
          match modulusForType dstTy with
          | some m =>
              let ovf := bif Nat.blt a b then 1 else 0
              let diff := (a + m - (b % m)) % m
              some (.agg2 4 (.scalar diff) (.scalar ovf))
          | none => none
      | .mulWithOverflow =>
          match modulusForType dstTy with
          | some m =>
              let p := a * b
              let ovf := bif Nat.blt p m then 0 else 1
              some (.agg2 4 (.scalar (p % m)) (.scalar ovf))
          | none => none
  | _, _ => none

def evalAgg0Kind : Agg0Kind → Nat
  | .sizeError => 1
  | .optionNone => 2

def evalAgg1Kind : Agg1Kind → Nat
  | .okOrSome => 1
  | .resultErr => 2
  | .closureCapture1 => 3

def evalAgg2Kind : Agg2Kind → Nat
  | .guard => 1
  | .pairGuards => 2
  | .effectLog => 3
  | .tuple2 => 4

def evalAgg3Kind : Agg3Kind → Nat
  | .dstLayout => 1

def stepStmt
    (localTypes : List MirTypeTag)
    (st : WireStmt)
    (locals : List (Nat × RtVal))
    (heap : List HeapLogSlot) : Option (ExecStatus × List (Nat × RtVal) × List HeapLogSlot) :=
  match st with
  | .storageLive _ => some (.running, locals, heap)
  | .storageDead l => some (.running, eraseLocal locals l, heap)
  | .nop => some (.running, locals, heap)
  | .placeMention src =>
      match readPlace locals heap src with
      | .val _ => some (.running, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .retagStmt _ src =>
      match readPlace locals heap src with
      | .val _ => some (.running, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .assignUseNoRetag dst src =>
      match evalOperand locals heap src with
      | .val v =>
          match writePlace locals heap dst v with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .assignUseRetagYes dst src =>
      match evalOperand locals heap src with
      | .val v =>
          match writePlace locals heap dst v with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .assignCopyForDeref dst src =>
      match readPlace locals heap src with
      | .val v =>
          match writePlace locals heap dst v with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .assignRefOrPtr dst _ src =>
      match makeRef locals heap src with
      | .val rv =>
          match writePlace locals heap dst rv with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .assignDiscriminant dst src =>
      match readPlace locals heap src with
      | .val (.agg0 2) =>
          match writePlace locals heap dst (.scalar 0) with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .val (.agg1 1 _) =>
          match writePlace locals heap dst (.scalar 0) with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .val (.agg1 2 _) =>
          match writePlace locals heap dst (.scalar 1) with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | _ => some (.stuck, locals, heap)
  | .assignBinOp dst op lhs rhs =>
      match evalOperand locals heap lhs, evalOperand locals heap rhs with
      | .val lv, .val rv =>
          let dstTy := getLocalTypeAt localTypes dst.localIdx
          match evalBinOp dstTy op lv rv with
          | some res =>
              match writePlace locals heap dst res with
              | some (nl, nh) => some (.running, nl, nh)
              | none => some (.stuck, locals, heap)
          | none => some (.stuck, locals, heap)
      | .ub, _ => some (.ub, locals, heap)
      | _, .ub => some (.ub, locals, heap)
      | _, _ => some (.stuck, locals, heap)
  | .assignUnOp dst .notOp src =>
      match evalOperand locals heap src with
      | .val (.scalar v) =>
          let nv := bif Nat.beq v 0 then 1 else 0
          match writePlace locals heap dst (.scalar nv) with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | _ => some (.stuck, locals, heap)
  | .assignAgg0 dst k =>
      match writePlace locals heap dst (.agg0 (evalAgg0Kind k)) with
      | some (nl, nh) => some (.running, nl, nh)
      | none => some (.stuck, locals, heap)
  | .assignAgg1 dst k f0 =>
      match evalOperand locals heap f0 with
      | .val v0 =>
          match writePlace locals heap dst (.agg1 (evalAgg1Kind k) v0) with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .assignAgg2 dst k f0 f1 =>
      match evalOperand locals heap f0, evalOperand locals heap f1 with
      | .val v0, .val v1 =>
          match writePlace locals heap dst (.agg2 (evalAgg2Kind k) v0 v1) with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub, _ => some (.ub, locals, heap)
      | _, .ub => some (.ub, locals, heap)
      | _, _ => some (.stuck, locals, heap)
  | .assignAgg3 dst k f0 f1 f2 =>
      match evalOperand locals heap f0, evalOperand locals heap f1, evalOperand locals heap f2 with
      | .val v0, .val v1, .val v2 =>
          match writePlace locals heap dst (.agg3 (evalAgg3Kind k) v0 v1 v2) with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub, _, _ => some (.ub, locals, heap)
      | _, .ub, _ => some (.ub, locals, heap)
      | _, _, .ub => some (.ub, locals, heap)
      | _, _, _ => some (.stuck, locals, heap)

def jumpToBlock (fr : ExecFrame) (targetBb : Nat) : Option ExecFrame :=
  match getBlockAt fr.bodyBlocks targetBb with
  | none => none
  | some blk =>
      some { fr with bbIdx := targetBb, remStmts := blk.stmts, curTerm := blk.term }

def unwindFrames (stack : List ExecFrame) (heap : List HeapLogSlot) (obsEvents : List Nat) : ExecState :=
  match stack with
  | [] => { status := .unwoundTop, stack := [], heap := heap, obsEvents := obsEvents }
  | fr :: rest =>
      match fr.pending with
      | none => { status := .stuck, stack := stack, heap := heap, obsEvents := obsEvents }
      | some pend =>
          match pend.unwind with
          | .cleanup cbb =>
              match jumpToBlock { fr with pending := none } cbb with
              | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
              | none => { status := .stuck, stack := stack, heap := heap, obsEvents := obsEvents }
          | .continueUnwind => unwindFrames rest heap obsEvents
          | .terminateAbi => { status := .terminatedAbort 1, stack := stack, heap := heap, obsEvents := obsEvents }
          | .terminateCleanup => { status := .terminatedAbort 2, stack := stack, heap := heap, obsEvents := obsEvents }
          | .unreachableUnwind => { status := .ub, stack := stack, heap := heap, obsEvents := obsEvents }

def handleCallUnwind (fr : ExecFrame) (rest : List ExecFrame) (uw : UnwindSpec) (heap : List HeapLogSlot) (obsEvents : List Nat) : ExecState :=
  match uw with
  | .cleanup cbb =>
      match jumpToBlock fr cbb with
      | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
      | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .continueUnwind => unwindFrames rest heap obsEvents
  | .terminateAbi => { status := .terminatedAbort 1, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .terminateCleanup => { status := .terminatedAbort 2, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .unreachableUnwind => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }

inductive IntrinsicOutcome where
  | ret (val : RtVal)
  | unwindPanic
  | stuck
  deriving DecidableEq, Repr

/--
  Width-aware declared intrinsics (`R3`):
  - `20`: `u32::wrapping_add` (`mod 2^32`)
  - `21`: `u32::wrapping_mul` (`mod 2^32`)
  - `42`: `u32::checked_add` (`< 2^32`)
  - `40`: `usize::wrapping_add` (`mod 2^64`)
  - `41`: `usize::wrapping_mul` (`mod 2^64`)
  - `23`: `usize::checked_add` (`< 2^64`)
  - `22`: `Ord::max`
  - `25`: `core::mem::forget` (fallback when body `25` is not in `bodies`; `24` `core::mem::drop`
    is never an intrinsic and must always execute its decoded `WireBody`)
  - `26`: `core::fmt::Arguments::from_str` (normal return constructing `.opaqueFmtArgs`)
  - `27`: `core::panicking::panic_fmt` (initiates unwinding `.unwindPanic`)
  - `28..31`: `Option::ok_or`, `Try::branch`, `FromResidual::from_residual`, `Option::is_some`
-/
def isDeclaredIntrinsicSym (s : Nat) : Bool :=
  (Nat.ble 20 s && Nat.ble s 23) ||
  (Nat.ble 25 s && Nat.ble s 31) ||
  (Nat.ble 40 s && Nat.ble s 42)

def evalDeclaredIntrinsic (calleeSym : Nat) (args : List RtVal) : IntrinsicOutcome :=
  if Nat.beq calleeSym 20 then
    match args with
    | [.scalar a, .scalar b] => .ret (.scalar ((a + b) % u32Mod))
    | _ => .stuck
  else if Nat.beq calleeSym 21 then
    match args with
    | [.scalar a, .scalar b] => .ret (.scalar ((a * b) % u32Mod))
    | _ => .stuck
  else if Nat.beq calleeSym 42 then
    match args with
    | [.scalar a, .scalar b] =>
        let s := a + b
        bif Nat.blt s u32Mod then .ret (.agg1 1 (.scalar s)) else .ret (.agg0 2)
    | _ => .stuck
  else if Nat.beq calleeSym 40 then
    match args with
    | [.scalar a, .scalar b] => .ret (.scalar ((a + b) % usizeMod))
    | _ => .stuck
  else if Nat.beq calleeSym 41 then
    match args with
    | [.scalar a, .scalar b] => .ret (.scalar ((a * b) % usizeMod))
    | _ => .stuck
  else if Nat.beq calleeSym 23 then
    match args with
    | [.scalar a, .scalar b] =>
        let s := a + b
        bif Nat.blt s usizeMod then .ret (.agg1 1 (.scalar s)) else .ret (.agg0 2)
    | _ => .stuck
  else if Nat.beq calleeSym 22 then
    match args with
    | [.scalar a, .scalar b] =>
        .ret (.scalar (bif Nat.ble a b then b else a))
    | _ => .stuck
  else if Nat.beq calleeSym 25 then
    .ret (.agg0 1)
  else if Nat.beq calleeSym 26 then
    match args with
    | [.scalar s] => .ret (.opaqueFmtArgs s)
    | _ => .stuck
  else if Nat.beq calleeSym 27 then
    match args with
    | [.opaqueFmtArgs _] => .unwindPanic
    | [.scalar _] => .unwindPanic
    | _ => .stuck
  else if Nat.beq calleeSym 28 then
    match args with
    | [.agg1 1 v, _] => .ret (.agg1 1 v)
    | [.agg0 2, errVal] => .ret (.agg1 2 errVal)
    | _ => .stuck
  else if Nat.beq calleeSym 29 then
    match args with
    | [.agg1 1 v] => .ret (.agg1 1 v)
    | [.agg1 2 e] => .ret (.agg1 2 e)
    | _ => .stuck
  else if Nat.beq calleeSym 30 then
    match args with
    | [rv] => .ret (.agg1 2 rv)
    | _ => .stuck
  else if Nat.beq calleeSym 31 then
    match args with
    | [rv] =>
        match unwrapRef rv with
        | .agg1 1 _ => .ret (.scalar 1)
        | .agg0 2 => .ret (.scalar 0)
        | _ => .stuck
    | _ => .stuck
  else
    .stuck

def buildCalleeLocalsAux : Nat → List RtVal → List (Nat × RtVal)
  | _, [] => []
  | idx, a :: as => (idx, a) :: buildCalleeLocalsAux (idx + 1) as

def buildCalleeLocals (args : List RtVal) : List (Nat × RtVal) :=
  (0, .agg0 1) :: buildCalleeLocalsAux 1 args

def evalOperandList (locals : List (Nat × RtVal)) (heap : List HeapLogSlot) : List OperandSpec → Option (Option (List RtVal))
  | [] => some (some [])
  | op :: ops =>
      match evalOperand locals heap op with
      | .ub => some none
      | .stuck => none
      | .val v =>
          match evalOperandList locals heap ops with
          | none => none
          | some none => some none
          | some (some vs) => some (some (v :: vs))

def dispatchCall
    (bodies : List WireBody)
    (fr : ExecFrame)
    (rest : List ExecFrame)
    (heap : List HeapLogSlot)
    (obsEvents : List Nat)
    (calleeSym : Nat)
    (dst : PlaceSpec)
    (targetBbOpt : Option Nat)
    (uw : UnwindSpec)
    (argOps : List OperandSpec) : ExecState :=
  match evalOperandList fr.locals heap argOps with
  | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | some none => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | some (some argVals) =>
      let obsEvents' :=
        if Nat.beq calleeSym 1 then
          match argVals with
          | [.heapPtr _, .scalar tag] => obsEvents ++ [tag]
          | _ => obsEvents
        else
          obsEvents
      match findBodyBySym bodies calleeSym with
      | some cbody =>
          match getBlockAt cbody.blocks 0 with
          | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents' }
          | some blk0 =>
              let callerFr : ExecFrame :=
                { fr with pending := some { retDst := dst, targetBbOpt := targetBbOpt, unwind := uw, isDropGlue := false } }
              let calleeFr : ExecFrame :=
                { symId := calleeSym
                , localTypes := cbody.localTypes
                , bodyBlocks := cbody.blocks
                , bbIdx := 0
                , remStmts := blk0.stmts
                , curTerm := blk0.term
                , locals := buildCalleeLocals argVals
                , pending := none }
              { status := .running, stack := calleeFr :: callerFr :: rest, heap := heap, obsEvents := obsEvents' }
      | none =>
          if isDeclaredIntrinsicSym calleeSym then
            match evalDeclaredIntrinsic calleeSym argVals with
            | .stuck => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents' }
            | .unwindPanic => handleCallUnwind fr rest uw heap obsEvents'
            | .ret retVal =>
                match targetBbOpt with
                | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents' }
                | some tbb =>
                    match writePlace fr.locals heap dst retVal with
                    | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents' }
                    | some (nl, nh) =>
                        match jumpToBlock { fr with locals := nl } tbb with
                        | some nfr => { status := .running, stack := nfr :: rest, heap := nh, obsEvents := obsEvents' }
                        | none => { status := .stuck, stack := fr :: rest, heap := nh, obsEvents := obsEvents' }
          else
            { status := .missingBody calleeSym, stack := fr :: rest, heap := heap, obsEvents := obsEvents' }

def stepTerm
    (bodies : List WireBody)
    (fr : ExecFrame)
    (rest : List ExecFrame)
    (heap : List HeapLogSlot)
    (obsEvents : List Nat) : ExecState :=
  match fr.curTerm with
  | .ret =>
      let retVal :=
        match getLocal fr.locals 0 with
        | some v => v
        | none => .agg0 1
      match rest with
      | [] => { status := .returned retVal, stack := [], heap := heap, obsEvents := obsEvents }
      | callerFr :: restCaller =>
          match callerFr.pending with
          | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
          | some pend =>
              if pend.isDropGlue then
                match pend.targetBbOpt with
                | none => { status := .stuck, stack := callerFr :: restCaller, heap := heap, obsEvents := obsEvents }
                | some tbb =>
                    match jumpToBlock { callerFr with pending := none } tbb with
                    | some nfr => { status := .running, stack := nfr :: restCaller, heap := heap, obsEvents := obsEvents }
                    | none => { status := .stuck, stack := callerFr :: restCaller, heap := heap, obsEvents := obsEvents }
              else
                match pend.targetBbOpt with
                | none => { status := .stuck, stack := callerFr :: restCaller, heap := heap, obsEvents := obsEvents }
                | some tbb =>
                    match writePlace callerFr.locals heap pend.retDst retVal with
                    | none => { status := .stuck, stack := callerFr :: restCaller, heap := heap, obsEvents := obsEvents }
                    | some (nl, nh) =>
                        match jumpToBlock { callerFr with locals := nl, pending := none } tbb with
                        | some nfr => { status := .running, stack := nfr :: restCaller, heap := nh, obsEvents := obsEvents }
                        | none => { status := .stuck, stack := callerFr :: restCaller, heap := nh, obsEvents := obsEvents }
  | .unwindResume => unwindFrames rest heap obsEvents
  | .unwindTerminate r => { status := .terminatedAbort r, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .unreachable => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .goto tbb =>
      match jumpToBlock fr tbb with
      | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
      | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .switchInt1 discr v0 t0 other =>
      match evalOperand fr.locals heap discr with
      | .ub => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
      | .val (.scalar dv) =>
          let nextBb := bif Nat.beq dv v0 then t0 else other
          match jumpToBlock fr nextBb with
          | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
          | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
      | _ => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .switchInt2 discr v0 t0 v1 t1 other =>
      match evalOperand fr.locals heap discr with
      | .ub => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
      | .val (.scalar dv) =>
          let nextBb :=
            bif Nat.beq dv v0 then t0
            else bif Nat.beq dv v1 then t1
            else other
          match jumpToBlock fr nextBb with
          | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
          | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
      | _ => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .assertTerm cond expected tbb uw =>
      match evalOperand fr.locals heap cond with
      | .ub => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
      | .val (.scalar cv) =>
          let expNat := bif expected then 1 else 0
          if Nat.beq cv expNat then
            match jumpToBlock fr tbb with
            | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
            | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
          else
            handleCallUnwind fr rest uw heap obsEvents
      | _ => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .drop pl glueSym tbb uw =>
      if Nat.beq glueSym 0 then
        match jumpToBlock fr tbb with
        | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
        | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
      else
        match findBodyBySym bodies glueSym with
        | none => { status := .missingBody glueSym, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
        | some gbody =>
            match getBlockAt gbody.blocks 0, makeRef fr.locals heap pl with
            | some blk0, .val refArg =>
                let callerFr : ExecFrame :=
                  { fr with pending := some { retDst := { localIdx := 0, proj := .here }, targetBbOpt := some tbb, unwind := uw, isDropGlue := true } }
                let glueFr : ExecFrame :=
                  { symId := glueSym
                  , localTypes := gbody.localTypes
                  , bodyBlocks := gbody.blocks
                  , bbIdx := 0
                  , remStmts := blk0.stmts
                  , curTerm := blk0.term
                  , locals := [(0, .agg0 1), (1, refArg)]
                  , pending := none }
                { status := .running, stack := glueFr :: callerFr :: rest, heap := heap, obsEvents := obsEvents }
            | _, .ub => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
            | _, _ => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .call0 c dst t uw => dispatchCall bodies fr rest heap obsEvents c dst t uw []
  | .call1 c dst t uw a0 => dispatchCall bodies fr rest heap obsEvents c dst t uw [a0]
  | .call2 c dst t uw a0 a1 => dispatchCall bodies fr rest heap obsEvents c dst t uw [a0, a1]
  | .call3 c dst t uw a0 a1 a2 => dispatchCall bodies fr rest heap obsEvents c dst t uw [a0, a1, a2]
  | .call4 c dst t uw a0 a1 a2 a3 => dispatchCall bodies fr rest heap obsEvents c dst t uw [a0, a1, a2, a3]

def execBlockStmts
    (localTypes : List MirTypeTag)
    (stmts : List WireStmt)
    (locals : List (Nat × RtVal))
    (heap : List HeapLogSlot) : ExecStatus × List (Nat × RtVal) × List HeapLogSlot :=
  match stmts with
  | [] => (.running, locals, heap)
  | s :: ss =>
      match stepStmt localTypes s locals heap with
      | some (.running, nl, nh) => execBlockStmts localTypes ss nl nh
      | some (otherStatus, nl, nh) => (otherStatus, nl, nh)
      | none => (.stuck, locals, heap)

def stepState (bodies : List WireBody) (st : ExecState) : ExecState :=
  match st.status with
  | .running =>
      match st.stack with
      | [] => { st with status := .stuck }
      | fr :: rest =>
          match execBlockStmts fr.localTypes fr.remStmts fr.locals st.heap with
          | (.running, nl, nh) =>
              stepTerm bodies { fr with remStmts := [], locals := nl } rest nh st.obsEvents
          | (otherStatus, nl, nh) =>
              { status := otherStatus, stack := { fr with remStmts := [], locals := nl } :: rest, heap := nh, obsEvents := st.obsEvents }
  | _ => st

def runSteps (bodies : List WireBody) : Nat → ExecState → ExecState
  | 0, st => st
  | n + 1, st =>
      match st.status with
      | .running => runSteps bodies n (stepState bodies st)
      | _ => st

def initEntryStateWithHeap (bodies : List WireBody) (sym : Nat) (args : List RtVal) (initHeap : List HeapLogSlot) : ExecState :=
  match findBodyBySym bodies sym with
  | none => { status := .missingBody sym, stack := [], heap := initHeap, obsEvents := [] }
  | some body =>
      match getBlockAt body.blocks 0 with
      | none => { status := .stuck, stack := [], heap := initHeap, obsEvents := [] }
      | some blk0 =>
          let fr : ExecFrame :=
            { symId := sym
            , localTypes := body.localTypes
            , bodyBlocks := body.blocks
            , bbIdx := 0
            , remStmts := blk0.stmts
            , curTerm := blk0.term
            , locals := buildCalleeLocals args
            , pending := none }
          { status := .running, stack := [fr], heap := initHeap, obsEvents := [] }

def initEntryState (bodies : List WireBody) (sym : Nat) (args : List RtVal) : ExecState :=
  let emptySlot : HeapLogSlot := { stepCount := 0, traceAcc := 0 }
  initEntryStateWithHeap bodies sym args [emptySlot, emptySlot]

/-! ## Boundary 5: Frozen C0 Independent Endpoint Specifications & Evaluators (`R2` & `R3`) -/

inductive CleanupExecOutcome where
  | normalReturn (retVal : Nat) (log1 : Nat × Nat) (log2 : Nat × Nat) (obsEvents : List Nat)
  | unwoundWithCleanup (log1 : Nat × Nat) (log2 : Nat × Nat) (obsEvents : List Nat)
  | failed (status : ExecStatus)
  deriving DecidableEq, Repr

def summarizeTwoHeapLogs (heap : List HeapLogSlot) : (Nat × Nat) × (Nat × Nat) :=
  match heap with
  | h0 :: h1 :: _ => ((h0.stepCount, h0.traceAcc), (h1.stepCount, h1.traceAcc))
  | [h0] => ((h0.stepCount, h0.traceAcc), (0, 0))
  | [] => ((0, 0), (0, 0))

/--
  Executes `partial_init_move_cleanup` (`sym = 4`) with disjoint storage allocations
  `log1 = .heapPtr 0` and `log2 = .heapPtr 1` (`R2`).
-/
def evalPartialInitBodies (bodies : List WireBody) (moveFirstEarly triggerPanic : Bool) : CleanupExecOutcome :=
  let args : List RtVal :=
    [ .scalar (bif moveFirstEarly then 1 else 0)
    , .scalar (bif triggerPanic then 1 else 0)
    , .heapPtr 0
    , .heapPtr 1 ]
  let finalSt := runSteps bodies 60 (initEntryState bodies 4 args)
  let (l1, l2) := summarizeTwoHeapLogs finalSt.heap
  match finalSt.status with
  | .returned (.scalar rv) => .normalReturn rv l1 l2 finalSt.obsEvents
  | .unwoundTop => .unwoundWithCleanup l1 l2 finalSt.obsEvents
  | other => .failed other

/--
  Executes `partial_field_reinit_cleanup` (`sym = 5`) with disjoint storage allocations
  `log1 = .heapPtr 0` and `log2 = .heapPtr 1` (`R2`).
-/
def evalPartialFieldReinitBodies (bodies : List WireBody) (triggerPanic : Bool) : CleanupExecOutcome :=
  let args : List RtVal :=
    [ .scalar (bif triggerPanic then 1 else 0)
    , .heapPtr 0
    , .heapPtr 1 ]
  let finalSt := runSteps bodies 60 (initEntryState bodies 5 args)
  let (l1, l2) := summarizeTwoHeapLogs finalSt.heap
  match finalSt.status with
  | .returned (.scalar rv) => .normalReturn rv l1 l2 finalSt.obsEvents
  | .unwoundTop => .unwoundWithCleanup l1 l2 finalSt.obsEvents
  | other => .failed other

/-- Single-parse full 6-case cleanup suite evaluator on admitted canonical `.amir` v3 bytes (`B1`+`B2a`+`B2b`). -/
def evalCleanupSuiteOnBytes (bytes : List Nat) : Option (List CleanupExecOutcome) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let bodies := pkg.bodies
      some
        [ evalPartialInitBodies bodies false false
        , evalPartialInitBodies bodies false true
        , evalPartialInitBodies bodies true false
        , evalPartialInitBodies bodies true true
        , evalPartialFieldReinitBodies bodies false
        , evalPartialFieldReinitBodies bodies true ]
  | none => none

/-- Raw-syntax (pre-`B2b` closure) 6-case cleanup suite evaluator used to demonstrate runtime `.missingBody` faults when Stage `B2b` closure is bypassed on raw Charon ULLBC. -/
def evalCleanupSuiteUncheckedClosureOnBytes (bytes : List Nat) : Option (List CleanupExecOutcome) :=
  match parseRawPackageBytes bytes with
  | .ok (pkg, []) =>
      let bodies := pkg.bodies
      some
        [ evalPartialInitBodies bodies false false
        , evalPartialInitBodies bodies false true
        , evalPartialInitBodies bodies true false
        , evalPartialInitBodies bodies true true
        , evalPartialFieldReinitBodies bodies false
        , evalPartialFieldReinitBodies bodies true ]
  | _ => none

def evalPartialInitOnBytes (bytes : List Nat) (moveFirstEarly triggerPanic : Bool) : Option CleanupExecOutcome :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalPartialInitBodies pkg.bodies moveFirstEarly triggerPanic)
  | none => none

def evalPartialFieldReinitOnBytes (bytes : List Nat) (triggerPanic : Bool) : Option CleanupExecOutcome :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalPartialFieldReinitBodies pkg.bodies triggerPanic)
  | none => none

/--
  Frozen C0 specification for `partial_init_move_cleanup` (`docs/rust-opsem/c0-scope-and-frozen-endpoint.md` §3.1),
  checking both disjoint residual states `log1 = (step_count, trace_acc)` and `log2 = (step_count, trace_acc)`
  as well as the global chronological event trace `obsEvents` (`R2`).
-/
def c0SpecPartialInit (moveFirstEarly triggerPanic : Bool) : CleanupExecOutcome :=
  match moveFirstEarly, triggerPanic with
  | false, false => .normalReturn 105 (1, 1) (1, 2) [1, 2]
  | false, true  => .unwoundWithCleanup (1, 1) (1, 2) [1, 2]
  | true,  false => .normalReturn 105 (2, 161) (1, 2) [10, 1, 2]
  | true,  true  => .unwoundWithCleanup (2, 161) (1, 2) [10, 1, 2]

/--
  Frozen C0 specification for `partial_field_reinit_cleanup` (`docs/rust-opsem/c0-scope-and-frozen-endpoint.md` §3.1),
  checking both disjoint residual states `log1` and `log2` and the global chronological event trace (`R2`).
-/
def c0SpecPartialFieldReinit (triggerPanic : Bool) : CleanupExecOutcome :=
  match triggerPanic with
  | false => .normalReturn 107 (2, 163) (1, 2) [10, 3, 2]
  | true  => .unwoundWithCleanup (1, 10) (1, 2) [10, 2]

def c0SpecCleanupSuite : List CleanupExecOutcome :=
  [ c0SpecPartialInit false false
  , c0SpecPartialInit false true
  , c0SpecPartialInit true false
  , c0SpecPartialInit true true
  , c0SpecPartialFieldReinit false
  , c0SpecPartialFieldReinit true ]

/--
  R3 Wrapping Boundary Evaluator: executes `core::mem::drop::<Guard>(Guard { drop_tag: tag, log })`
  (`sym = 24` -> `Guard::drop_in_place` `sym = 7` -> `<Guard as Drop>::drop` `sym = 2` ->
  `EffectLog::record` `sym = 1`) from an arbitrary initial `HeapLogSlot` state to test 32-bit
  `u32::wrapping_add` (`sym = 20`) and `u32::wrapping_mul` (`sym = 21`) overflow wrapping.
-/
def evalEffectLogRecordWrappingOnBytes (bytes : List Nat) (initStep initTrace tag : Nat) : Option (HeapLogSlot × List Nat) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let initSlot : HeapLogSlot := { stepCount := initStep, traceAcc := initTrace }
      let guardVal : RtVal := .agg2 1 (.scalar tag) (.heapPtr 0)
      let st0 := initEntryStateWithHeap pkg.bodies 24 [guardVal] [initSlot]
      let stF := runSteps pkg.bodies 15 st0
      match stF.status, stF.heap with
      | .returned (.agg0 1), [finalSlot] => some (finalSlot, stF.obsEvents)
      | _, _ => none
  | none => none

/--
  R3 Formatting vs Panic Separation Evaluator: steps `may_unwind_op(true, 5)` (`sym = 3`)
  to inspect the intermediate state after `Arguments::from_str` (`sym = 26`, step 2 at `bb2`)
  versus the unwinding state after `panic_fmt` (`sym = 27`, step 3).
-/
def inspectMayUnwindFmtThenPanicOnBytes (bytes : List Nat) : Option (ExecStatus × Option RtVal × ExecStatus) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let st0 := initEntryState pkg.bodies 3 [.scalar 1, .scalar 5]
      let stAfterFmt := runSteps pkg.bodies 2 st0
      let fmtLocal8 :=
        match stAfterFmt.stack with
        | fr :: _ => getLocal fr.locals 8
        | [] => none
      let stAfterPanic := stepState pkg.bodies stAfterFmt
      some (stAfterFmt.status, fmtLocal8, stAfterPanic.status)
  | none => none

def evalPlaceMentionBodies (bodies : List WireBody) (symId : Nat) (ptrValid : Bool) : Option Nat :=
  let args : List RtVal :=
    if Nat.beq symId 10 then
      [.extPtr ptrValid]
    else
      [.extPtr ptrValid, .scalar 0]
  let finalSt := runSteps bodies 10 (initEntryState bodies symId args)
  match finalSt.status with
  | .returned (.scalar rv) => some rv
  | _ => none

def evalPlaceMentionSuiteOnBytes (bytes : List Nat) : Option (List (Option Nat)) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let bodies := pkg.bodies
      some
        [ evalPlaceMentionBodies bodies 6 true
        , evalPlaceMentionBodies bodies 6 false
        , evalPlaceMentionBodies bodies 9 true
        , evalPlaceMentionBodies bodies 9 false
        , evalPlaceMentionBodies bodies 10 true
        , evalPlaceMentionBodies bodies 10 false ]
  | none => none

def evalPlaceMentionOnBytes (bytes : List Nat) (symId : Nat) (ptrValid : Bool) : Option (Option Nat) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalPlaceMentionBodies pkg.bodies symId ptrValid)
  | none => none

/-- Frozen C0 specification for `place_mention_probe.rs` under `-Z mir-preserve-ub` (`c0-scope-and-frozen-endpoint.md` §3.2). -/
def c0SpecPlaceMentionPreserveUb (_symId : Nat) (ptrValid : Bool) : Option Nat :=
  bif ptrValid then some 0 else none

def c0SpecPlaceMentionSuite : List (Option Nat) :=
  [ c0SpecPlaceMentionPreserveUb 6 true
  , c0SpecPlaceMentionPreserveUb 6 false
  , c0SpecPlaceMentionPreserveUb 9 true
  , c0SpecPlaceMentionPreserveUb 9 false
  , c0SpecPlaceMentionPreserveUb 10 true
  , c0SpecPlaceMentionPreserveUb 10 false ]

def evalAlignToBodies (bodies : List WireBody) (size align : Nat) : Option Nat :=
  let finalSt := runSteps bodies 20 (initEntryState bodies 11 [.scalar size, .scalar align])
  match finalSt.status with
  | .returned (.agg1 1 (.scalar v)) => some v
  | _ => none

def evalAlignToOnBytes (bytes : List Nat) (size align : Nat) : Option (Option Nat) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalAlignToBodies pkg.bodies size align)
  | none => none

/--
  Finite-width 64-bit `usize` C0 specification for `align_to` (`R3`):
  returns `none` (`Err(SizeError)`) when `align == 0` or `size + (align - rem) >= 2^64`.
-/
def c0SpecAlignTo (size align : Nat) : Option Nat :=
  if Nat.beq align 0 then none
  else
    let rem := size % align
    if Nat.beq rem 0 then
      bif Nat.blt size usizeMod then some size else none
    else
      let pad := align - rem
      let sum := size + pad
      bif Nat.blt sum usizeMod then some sum else none

def evalExtendBodies
    (bodies : List WireBody)
    (selfAlign selfSize : Nat) (selfIsSlice : Bool)
    (nextAlign nextSize : Nat) (nextIsSlice : Bool) : Option (Nat × Nat × Bool × Nat) :=
  let selfVal : RtVal := .agg3 1 (.scalar selfAlign) (.scalar selfSize) (.scalar (bif selfIsSlice then 1 else 0))
  let nextVal : RtVal := .agg3 1 (.scalar nextAlign) (.scalar nextSize) (.scalar (bif nextIsSlice then 1 else 0))
  let finalSt := runSteps bodies 35 (initEntryState bodies 12 [selfVal, nextVal])
  match finalSt.status with
  | .returned (.agg1 1 (.agg2 4 (.agg3 1 (.scalar a) (.scalar s) (.scalar sl)) (.scalar off))) =>
      some (a, s, Nat.beq sl 1, off)
  | _ => none

def evalExtendOnBytes
    (bytes : List Nat)
    (selfAlign selfSize : Nat) (selfIsSlice : Bool)
    (nextAlign nextSize : Nat) (nextIsSlice : Bool) : Option (Option (Nat × Nat × Bool × Nat)) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalExtendBodies pkg.bodies selfAlign selfSize selfIsSlice nextAlign nextSize nextIsSlice)
  | none => none

def c0SpecExtend
    (selfAlign selfSize : Nat) (selfIsSlice : Bool)
    (nextAlign nextSize : Nat) (nextIsSlice : Bool) : Option (Nat × Nat × Bool × Nat) :=
  if selfIsSlice then none
  else
    match c0SpecAlignTo selfSize nextAlign with
    | none => none
    | some offset =>
        let maxAlign := bif Nat.ble selfAlign nextAlign then nextAlign else selfAlign
        if nextIsSlice then
          some (maxAlign, offset, true, offset)
        else
          let sum := offset + nextSize
          bif Nat.blt sum usizeMod then some (maxAlign, sum, false, offset) else none

def evalValidateCastBodies
    (bodies : List WireBody)
    (align sizeInfo : Nat) (isSlice : Bool)
    (addr bytesLen elemSize : Nat) : Option (Nat × Nat) :=
  let selfVal : RtVal := .agg3 1 (.scalar align) (.scalar sizeInfo) (.scalar (bif isSlice then 1 else 0))
  let finalSt :=
    runSteps bodies 30
      (initEntryState bodies 13 [selfVal, .scalar addr, .scalar bytesLen, .scalar elemSize])
  match finalSt.status with
  | .returned (.agg1 1 (.agg2 4 (.scalar elems) (.scalar splitAt))) => some (elems, splitAt)
  | _ => none

def evalValidateCastOnBytes
    (bytes : List Nat)
    (align sizeInfo : Nat) (isSlice : Bool)
    (addr bytesLen elemSize : Nat) : Option (Option (Nat × Nat)) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalValidateCastBodies (pkg.bodies.drop 6) align sizeInfo isSlice addr bytesLen elemSize)
  | none => none

def c0SpecValidateCast
    (align sizeInfo : Nat) (isSlice : Bool)
    (addr bytesLen elemSize : Nat) : Option (Nat × Nat) :=
  if Nat.beq align 0 || !(Nat.beq (addr % align) 0) then none
  else if !isSlice then
    if Nat.blt bytesLen sizeInfo then none else some (bytesLen - sizeInfo, 1)
  else
    if Nat.blt bytesLen sizeInfo || Nat.beq elemSize 0 then none
    else
      let trailing := bytesLen - sizeInfo
      let elems := trailing / elemSize
      let used := sizeInfo + elems * elemSize
      some (bytesLen - used, elems)

def evalCountValidPrefixesBodies (bodies : List WireBody) (addr maxBytes step : Nat) : Option Nat :=
  let finalSt :=
    runSteps bodies 110
      (initEntryState bodies 14 [.scalar addr, .scalar maxBytes, .scalar step])
  match finalSt.status with
  | .returned (.scalar vc) => some vc
  | _ => none

/--
  Part 1 of the C0 `zerocopy_layout_holdout.rs` result structure (`R3`): all `align_to`
  and `DstLayout::extend` vectors from `docs/rust-opsem/c0-scope-and-frozen-endpoint.md` §3.4.1,
  including the 64-bit checked-add overflow vector `alignMaxMinus1_4` (`align_to(usize::MAX - 1, 4) = Err(SizeError)`)
  and the sized-tail `checked_add` path `extendValidSized` (`header = (4, 6, false), tail = (8, 10, false) -> Ok(((8, 18, false), 8))`).
-/
structure ZerocopyAlignExtendSuiteResult where
  align6_0 : Option Nat
  align8_4 : Option Nat
  align6_4 : Option Nat
  align13_4 : Option Nat
  align16_4 : Option Nat
  align13_0 : Option Nat
  alignMaxMinus1_4 : Option Nat
  extendValidSlice : Option (Nat × Nat × Bool × Nat)
  extendValidSized : Option (Nat × Nat × Bool × Nat)
  extendErrAlreadySlice : Option (Nat × Nat × Bool × Nat)
  deriving DecidableEq, Repr

/--
  Part 2 of the C0 `zerocopy_layout_holdout.rs` result structure (`R3`): all
  `DstLayout::validate_cast_and_convert_metadata` and `count_valid_prefixes` vectors from
  `docs/rust-opsem/c0-scope-and-frozen-endpoint.md` §3.4.1, including the non-zero remainder
  vector `validateValidRem2` (`(0x1000, 22, 4) -> Some((2, 3))`), the `elem_size == 0` guard
  `validateElemSizeZero` (`(0x1000, 20, 0) -> None`), and the terminating zero-step vectors
  `countPrefixes20Step0` and `countPrefixes8Step0`.
-/
structure ZerocopyValidateCountSuiteResult where
  validateValid3 : Option (Nat × Nat)
  validateValidRem2 : Option (Nat × Nat)
  validateUnaligned : Option (Nat × Nat)
  validateTooSmall : Option (Nat × Nat)
  validateElemSizeZero : Option (Nat × Nat)
  countPrefixes20Step4 : Option Nat
  countPrefixes20Step0 : Option Nat
  countPrefixes8Step0 : Option Nat
  deriving DecidableEq, Repr

def evalZerocopyAlignExtendOnBytes (bytes : List Nat) : Option ZerocopyAlignExtendSuiteResult :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let bodies := pkg.bodies.drop 6
      some
        { align6_0 := evalAlignToBodies bodies 6 0
        , align8_4 := evalAlignToBodies bodies 8 4
        , align6_4 := evalAlignToBodies bodies 6 4
        , align13_4 := evalAlignToBodies bodies 13 4
        , align16_4 := evalAlignToBodies bodies 16 4
        , align13_0 := evalAlignToBodies bodies 13 0
        , alignMaxMinus1_4 := evalAlignToBodies bodies (usizeMax - 1) 4
        , extendValidSlice := evalExtendBodies bodies 4 6 false 4 4 true
        , extendValidSized := evalExtendBodies bodies 4 6 false 8 10 false
        , extendErrAlreadySlice := evalExtendBodies bodies 4 8 true 4 4 false }
  | _ => none

def evalZerocopyValidateCountOnBytes (bytes : List Nat) : Option ZerocopyValidateCountSuiteResult :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let bodies := pkg.bodies.drop 6
      some
        { validateValid3 := evalValidateCastBodies bodies 4 8 true 4096 20 4
        , validateValidRem2 := evalValidateCastBodies bodies 4 8 true 4096 22 4
        , validateUnaligned := evalValidateCastBodies bodies 4 8 true 4098 20 4
        , validateTooSmall := evalValidateCastBodies bodies 4 8 true 4096 4 4
        , validateElemSizeZero := evalValidateCastBodies bodies 4 8 true 4096 20 0
        , countPrefixes20Step4 := evalCountValidPrefixesBodies bodies 4096 20 4
        , countPrefixes20Step0 := evalCountValidPrefixesBodies bodies 4096 20 0
        , countPrefixes8Step0 := evalCountValidPrefixesBodies bodies 4096 8 0 }
  | _ => none

def c0SpecZerocopyAlignExtendSuite : ZerocopyAlignExtendSuiteResult :=
  { align6_0 := c0SpecAlignTo 6 0
  , align8_4 := c0SpecAlignTo 8 4
  , align6_4 := c0SpecAlignTo 6 4
  , align13_4 := c0SpecAlignTo 13 4
  , align16_4 := c0SpecAlignTo 16 4
  , align13_0 := c0SpecAlignTo 13 0
  , alignMaxMinus1_4 := c0SpecAlignTo (usizeMax - 1) 4
  , extendValidSlice := c0SpecExtend 4 6 false 4 4 true
  , extendValidSized := c0SpecExtend 4 6 false 8 10 false
  , extendErrAlreadySlice := c0SpecExtend 4 8 true 4 4 false }

def c0SpecZerocopyValidateCountSuite : ZerocopyValidateCountSuiteResult :=
  { validateValid3 := c0SpecValidateCast 4 8 true 4096 20 4
  , validateValidRem2 := c0SpecValidateCast 4 8 true 4096 22 4
  , validateUnaligned := c0SpecValidateCast 4 8 true 4098 20 4
  , validateTooSmall := c0SpecValidateCast 4 8 true 4096 4 4
  , validateElemSizeZero := c0SpecValidateCast 4 8 true 4096 20 0
  , countPrefixes20Step4 := some 4
  , countPrefixes20Step0 := some 1
  , countPrefixes8Step0 := some 1 }

/-! ## C2 Theorem 1 (`R2`): Decoded-AST Execution Satisfies Frozen C0 Disjoint Cleanup & Chronological Endpoint -/

theorem direct_mir_cleanup_suite_satisfies_c0_all_cases :
    evalCleanupSuiteOnBytes realCleanupSubjectPreserveUbBytes =
      some c0SpecCleanupSuite := by
  rfl

/-! ## C2 Theorem 1b (`R3`): 32-Bit `u32` Wrapping Boundary & `Arguments::from_str` vs `panic_fmt` Separation -/

theorem effect_log_record_u32_wrapping_boundary_verified :
    evalEffectLogRecordWrappingOnBytes realCleanupSubjectPreserveUbBytes u32Max 268435456 7 =
      some ({ stepCount := 0, traceAcc := 7 }, [7]) := by
  rfl

theorem may_unwind_op_fmt_vs_panic_transition_verified :
    inspectMayUnwindFmtThenPanicOnBytes realCleanupSubjectPreserveUbBytes =
      some (.running, some (.opaqueFmtArgs 999), .unwoundTop) := by
  rfl

/-! ## C2 Theorem 2: Decoded-AST Execution Satisfies Frozen C0 `PlaceMention` Endpoint -/

theorem direct_mir_place_mention_preserve_ub_satisfies_c0 :
    evalPlaceMentionSuiteOnBytes realPlaceMentionPreserveUbBytes =
      some c0SpecPlaceMentionSuite := by
  rfl

theorem direct_mir_place_mention_default_misses_wildcard_and_underscore_ub :
    evalPlaceMentionSuiteOnBytes realPlaceMentionDefaultBytes =
      some [some 0, none, some 0, some 0, some 0, some 0] := by
  rfl

/-! ## C2 Theorem 4 (`R4`): Unconditional All-Prefix Theorem for Unmodified Captured Loop (`unbounded_period4_probe`) -/

def extractBodiesFromBytes (bytes : List Nat) : List WireBody :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg => pkg.bodies
  | none => []

def realLoopPrefixBodies : List WireBody :=
  extractBodiesFromBytes realLoopPrefixProbePreserveUbBytes

def realLoopPrefixDefaultBodies : List WireBody :=
  extractBodiesFromBytes realLoopPrefixProbeDefaultBytes

def initLoopPeriod4State : ExecState :=
  initEntryState realLoopPrefixBodies 43 [.extPtr true, .scalar 0, .scalar 8, .scalar 0]

/--
  Canonical loop-header state at `bb4` of unmodified `unbounded_period4_probe` (`sym = 43`)
  in `realLoopPrefixProbePreserveUbBytes`, parameterized by the wrapped period-4 machine
  counter `ticks : Nat` (`_8`, where `ticks ∈ {0, 1, 2, 3}`) after at least one loop body
  iteration (`_10 = ()`).
-/
def loopPeriod4HeaderState (bodies : List WireBody) (ticks : Nat) : ExecState :=
  let (body43Types, body43Blocks) :=
    match findBodyBySym bodies 43 with
    | some body => (body.localTypes, body.blocks)
    | none => ([], [])
  let blk4 :=
    match getBlockAt body43Blocks 4 with
    | some blk => blk
    | none => { isCleanup := false, stmts := [], term := .unreachable }
  let emptySlot : HeapLogSlot := { stepCount := 0, traceAcc := 0 }
  let fr : ExecFrame :=
    { symId := 43
    , localTypes := body43Types
    , bodyBlocks := body43Blocks
    , bbIdx := 4
    , remStmts := blk4.stmts
    , curTerm := blk4.term
    , locals :=
        [ (0, .agg0 1)
        , (1, .extPtr true)
        , (2, .scalar 0)
        , (3, .scalar 8)
        , (4, .scalar 0)
        , (7, .scalar 0)
        , (8, .scalar ticks)
        , (10, .agg0 1) ]
    , pending := none }
  { status := .running, stack := [fr], heap := [emptySlot, emptySlot], obsEvents := [] }

def readLoopPeriod4Ticks (st : ExecState) : Option Nat :=
  match st.stack with
  | [fr] =>
      match getLocal fr.locals 8 with
      | some (.scalar t) => some t
      | _ => none
  | _ => none

theorem runSteps_succ (bodies : List WireBody) (k : Nat) (st : ExecState) :
    runSteps bodies (k + 1) st =
      match st.status with
      | .running => runSteps bodies k (stepState bodies st)
      | _ => st := rfl

theorem runSteps_nonRunning (bodies : List WireBody) (n : Nat) (st : ExecState)
    (h : st.status ≠ .running) :
    runSteps bodies n st = st := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [runSteps_succ]
      cases hst : st.status
      · exact False.elim (h hst)
      all_goals rfl

theorem runSteps_add (bodies : List WireBody) (m n : Nat) (st : ExecState) :
    runSteps bodies (m + n) st = runSteps bodies n (runSteps bodies m st) := by
  induction m generalizing st with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ m ih =>
      have h1 : m + 1 + n = (m + n) + 1 := by omega
      rw [h1, runSteps_succ, runSteps_succ]
      cases hst : st.status
      · exact ih (stepState bodies st)
      all_goals
        symm
        apply runSteps_nonRunning
        rw [hst]
        intro h; contradiction

/-- Entry prefix (7 steps: `bb0 -> bb2 -> bb3 -> bb4 -> bb5 -> bb6 -> bb7 -> bb4`) reaches `loopPeriod4HeaderState` with `ticks = 1`. -/
theorem unbounded_period4_entry_to_header :
    runSteps realLoopPrefixBodies 7 initLoopPeriod4State =
      loopPeriod4HeaderState realLoopPrefixBodies 1 := by
  rfl

/-- Concrete 4-step loop cycles (`bb4 -> bb5 -> bb6 -> bb7 -> bb4`) for all 4 period-4 states `ticks ∈ {0, 1, 2, 3}`. -/
theorem unbounded_period4_cycle_step_0 :
    runSteps realLoopPrefixBodies 4 (loopPeriod4HeaderState realLoopPrefixBodies 0) =
      loopPeriod4HeaderState realLoopPrefixBodies 1 := by rfl

theorem unbounded_period4_cycle_step_1 :
    runSteps realLoopPrefixBodies 4 (loopPeriod4HeaderState realLoopPrefixBodies 1) =
      loopPeriod4HeaderState realLoopPrefixBodies 2 := by rfl

theorem unbounded_period4_cycle_step_2 :
    runSteps realLoopPrefixBodies 4 (loopPeriod4HeaderState realLoopPrefixBodies 2) =
      loopPeriod4HeaderState realLoopPrefixBodies 3 := by rfl

theorem unbounded_period4_cycle_step_3 :
    runSteps realLoopPrefixBodies 4 (loopPeriod4HeaderState realLoopPrefixBodies 3) =
      loopPeriod4HeaderState realLoopPrefixBodies 0 := by rfl

/--
  Universal 4-step cycle preservation & progress lemma for `unbounded_period4_probe` (`sym = 43`),
  discharged unconditionally for every mathematical iteration index `k : Nat` without any
  unproved `hStep` hypothesis (`R4`).
-/
theorem unbounded_period4_cycle_step_all (k : Nat) :
    runSteps realLoopPrefixBodies 4
      (loopPeriod4HeaderState realLoopPrefixBodies ((k + 1) % 4)) =
        loopPeriod4HeaderState realLoopPrefixBodies ((k + 2) % 4) := by
  have hmod : (k + 1) % 4 = 0 ∨ (k + 1) % 4 = 1 ∨ (k + 1) % 4 = 2 ∨ (k + 1) % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · have hnext : (k + 2) % 4 = 1 := by omega
    rw [h0, hnext]
    exact unbounded_period4_cycle_step_0
  · have hnext : (k + 2) % 4 = 2 := by omega
    rw [h1, hnext]
    exact unbounded_period4_cycle_step_1
  · have hnext : (k + 2) % 4 = 3 := by omega
    rw [h2, hnext]
    exact unbounded_period4_cycle_step_2
  · have hnext : (k + 2) % 4 = 0 := by omega
    rw [h3, hnext]
    exact unbounded_period4_cycle_step_3

/--
  Unconditional inductive loop-header theorem for unmodified `unbounded_period4_probe` (`R4`):
  after `7 + 4 * k` interpreter steps, execution is at `bb4` in `loopPeriod4HeaderState` with
  `ticks = (k + 1) % 4`, `.status = .running`, and `readLoopPeriod4Ticks = some ((k + 1) % 4)`.
-/
theorem unbounded_period4_header_induction (k : Nat) :
    let stK := runSteps realLoopPrefixBodies (7 + 4 * k) initLoopPeriod4State
    stK = loopPeriod4HeaderState realLoopPrefixBodies ((k + 1) % 4) ∧
    stK.status = .running ∧
    readLoopPeriod4Ticks stK = some ((k + 1) % 4) := by
  induction k with
  | zero =>
      dsimp
      rw [unbounded_period4_entry_to_header]
      exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      rcases ih with ⟨ihSt, _, _⟩
      have hsplit : 7 + 4 * (k + 1) = (7 + 4 * k) + 4 := by omega
      dsimp
      rw [hsplit, runSteps_add, ihSt]
      have hstep := unbounded_period4_cycle_step_all k
      have hidx : k + 1 + 1 = k + 2 := by omega
      rw [hidx, hstep]
      exact ⟨rfl, rfl, rfl⟩

/-- Intermediate states (`r ∈ {0, 1, 2, 3}`) inside the 4-block cycle from any `ticks ∈ {0, 1, 2, 3}` are `.running` and enabled. -/
theorem unbounded_period4_intermediate_running_and_enabled
    (t r : Nat) (ht : t < 4) (hr : r < 4) :
    let st := runSteps realLoopPrefixBodies r (loopPeriod4HeaderState realLoopPrefixBodies t)
    st.status = .running ∧ (stepState realLoopPrefixBodies st).status = .running := by
  have ht4 : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases ht4 with rfl | rfl | rfl | rfl <;>
    rcases hr4 with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl⟩

/-- Entry prefix states (`n < 7`) are `.running` and enabled. -/
theorem unbounded_period4_entry_prefix_running_and_enabled
    (n : Nat) (hn : n < 7) :
    let st := runSteps realLoopPrefixBodies n initLoopPeriod4State
    st.status = .running ∧ (stepState realLoopPrefixBodies st).status = .running := by
  have hn7 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hn7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl⟩

/--
  Unconditional all-prefix safety and enabled-continuation theorem (`R4`):
  for EVERY finite step bound `n : Nat` (covering entry blocks `bb0, bb2, bb3`, loop header
  cuts `bb4`, and intermediate loop-body blocks `bb5, bb6, bb7`), the decoded-AST execution of
  unmodified `unbounded_period4_probe` (`realLoopPrefixProbePreserveUbBytes`) is `.running`
  (never `.ub`, `.stuck`, or `.missingBody`) and its next step `stepState` is also `.running`.
-/
theorem unbounded_period4_all_prefixes_running_and_enabled (n : Nat) :
    let st := runSteps realLoopPrefixBodies n initLoopPeriod4State
    st.status = .running ∧ (stepState realLoopPrefixBodies st).status = .running := by
  by_cases hn : n < 7
  · exact unbounded_period4_entry_prefix_running_and_enabled n hn
  · have hdecomp : n = (7 + 4 * ((n - 7) / 4)) + ((n - 7) % 4) := by omega
    let k := (n - 7) / 4
    let r := (n - 7) % 4
    have hr : r < 4 := by omega
    have ht : (k + 1) % 4 < 4 := by omega
    rcases unbounded_period4_header_induction k with ⟨hHdr, _, _⟩
    dsimp
    rw [hdecomp, runSteps_add, hHdr]
    exact unbounded_period4_intermediate_running_and_enabled ((k + 1) % 4) r ht hr

/--
  Finite bad-prefix UB witness and terminating witness on unmodified `unbounded_period4_probe` (`R4`):
  1. When `probe_ptr = true` and `ptrValid = false` (`[.extPtr false, .scalar 1, .scalar 8, .scalar 0]`),
     `realLoopPrefixProbePreserveUbBytes` detects UB (`.status = .ub`) at step 2 (`PlaceMention(*ptr)` in `bb1`),
     whereas `realLoopPrefixProbeDefaultBytes` (without `-Z mir-preserve-ub`) misses UB and stays `.running`.
  2. When `probe_ptr = true, ptrValid = true, target = 8, step = 4`, `realLoopPrefixProbePreserveUbBytes`
     terminates normally after 2 iterations and returns `.returned (.scalar 2)`.
-/
theorem unbounded_period4_bad_prefix_and_terminating_witnesses :
    (runSteps realLoopPrefixBodies 2
      (initEntryState realLoopPrefixBodies 43 [.extPtr false, .scalar 1, .scalar 8, .scalar 0])).status = .ub ∧
    (runSteps realLoopPrefixDefaultBodies 20
      (initEntryState realLoopPrefixDefaultBodies 43 [.extPtr false, .scalar 1, .scalar 8, .scalar 0])).status = .running ∧
    (runSteps realLoopPrefixBodies 25
      (initEntryState realLoopPrefixBodies 43 [.extPtr true, .scalar 1, .scalar 8, .scalar 4])).status = .returned (.scalar 2) := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Synthetic Guard-Mutated `count_valid_prefixes` Calibration Experiment (Preserved from #61) -/

/--
  Synthetic guard-mutated `.amir` v3 package (`zerocopyLoopContinueBytes`) where the `step == 0`
  break guard in `count_valid_prefixes` (`sym = 14`) was replaced by a continuation branch.
  Preserved explicitly per `#62` R4 as a synthetic semantic calibration experiment (distinct from
  the unmodified captured source loop `unbounded_period4_probe` proved unconditionally above).
-/
def zerocopyLoopContinueBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 52, 41, 2, 1, 13, 1, 3, 53, 4, 25, 13, 10, 4, 4, 4, 1, 2, 4, 2, 4, 4, 4, 2, 19, 2, 1, 2, 4, 4, 19, 17, 4, 4, 4, 16, 1, 2, 4, 4, 2, 4, 19, 4, 4, 4, 16, 4, 4, 4, 2, 4, 4, 4, 4, 4, 16, 16, 17, 4, 4, 4, 16, 4, 0, 5, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 1, 21, 6, 0, 1, 71, 0, 130, 0, 69, 70, 0, 0, 2, 1, 0, 1, 33, 7, 68, 5, 0, 8, 33, 7, 32, 8, 32, 9, 32, 10, 17, 10, 0, 2, 0, 32, 11, 17, 11, 0, 1, 1, 21, 12, 0, 1, 11, 0, 130, 0, 72, 76, 0, 0, 3, 252, 0, 4, 21, 9, 0, 11, 74, 0, 75, 0, 33, 11, 33, 10, 21, 8, 0, 2, 73, 0, 130, 0, 69, 72, 0, 0, 6, 4, 0, 1, 33, 9, 68, 5, 0, 4, 23, 0, 0, 2, 33, 8, 33, 6, 33, 5, 68, 24, 0, 7, 33, 9, 17, 5, 0, 131, 0, 33, 8, 33, 6, 33, 5, 32, 14, 17, 14, 0, 1, 3, 69, 78, 0, 0, 8, 7, 0, 7, 32, 25, 32, 26, 32, 27, 17, 27, 0, 3, 0, 32, 28, 17, 28, 0, 1, 2, 21, 26, 0, 3, 91, 0, 92, 0, 69, 90, 0, 0, 13, 12, 0, 7, 32, 15, 32, 16, 32, 17, 17, 17, 0, 3, 0, 32, 18, 17, 18, 0, 1, 2, 21, 16, 0, 3, 81, 0, 82, 0, 69, 80, 0, 0, 10, 9, 0, 5, 33, 18, 33, 17, 23, 0, 0, 2, 33, 16, 33, 15, 68, 23, 0, 12, 33, 18, 33, 17, 17, 15, 0, 131, 0, 33, 16, 33, 15, 32, 20, 32, 21, 32, 22, 17, 22, 0, 3, 0, 32, 23, 17, 23, 0, 1, 2, 21, 24, 0, 14, 22, 0, 23, 0, 72, 88, 2, 0, 11, 252, 0, 7, 17, 21, 0, 88, 1, 33, 23, 33, 22, 25, 20, 0, 4, 85, 0, 130, 1, 33, 21, 24, 0, 0, 1, 84, 0, 33, 20, 68, 22, 0, 2, 33, 28, 33, 27, 68, 16, 0, 6, 33, 28, 33, 27, 32, 29, 32, 30, 17, 30, 0, 4, 0, 21, 29, 0, 1, 94, 0, 130, 0, 69, 93, 0, 0, 15, 14, 0, 1, 33, 30, 68, 16, 0, 11, 33, 30, 17, 25, 0, 131, 0, 33, 29, 33, 26, 33, 25, 32, 32, 32, 33, 17, 33, 0, 3, 0, 32, 34, 17, 34, 0, 1, 2, 21, 35, 0, 14, 33, 0, 34, 0, 72, 99, 2, 0, 17, 252, 0, 4, 23, 0, 0, 2, 33, 29, 33, 26, 33, 25, 68, 23, 0, 9, 17, 32, 0, 99, 1, 33, 34, 33, 33, 32, 36, 32, 37, 17, 37, 0, 32, 0, 32, 38, 17, 38, 0, 4, 0, 21, 39, 0, 1, 38, 0, 130, 0, 72, 103, 0, 0, 18, 252, 0, 12, 21, 36, 0, 10, 101, 0, 102, 0, 33, 38, 33, 37, 32, 40, 32, 41, 17, 41, 0, 1, 2, 32, 42, 32, 43, 17, 43, 0, 36, 0, 32, 44, 17, 44, 0, 4, 0, 21, 45, 0, 15, 43, 0, 44, 0, 72, 109, 2, 0, 19, 252, 0, 4, 17, 42, 0, 109, 1, 33, 44, 33, 43, 21, 46, 0, 13, 41, 0, 42, 0, 72, 110, 2, 0, 20, 252, 0, 10, 17, 40, 0, 110, 1, 33, 42, 33, 41, 32, 47, 32, 48, 32, 49, 17, 49, 0, 3, 0, 32, 50, 17, 50, 0, 40, 0, 21, 51, 0, 14, 49, 0, 50, 0, 72, 115, 2, 0, 21, 252, 0, 13, 17, 48, 0, 115, 1, 33, 50, 33, 49, 32, 52, 17, 52, 0, 36, 0, 25, 47, 0, 4, 112, 0, 116, 0, 33, 52, 33, 48, 24, 0, 0, 1, 111, 0, 33, 47, 33, 40, 33, 36, 33, 32, 68, 22, 0, 1, 33, 14, 68, 24, 0, 1, 33, 14, 68, 24, 0, 0, 64, 2, 14, 1, 3, 31, 3, 14, 4, 4, 4, 4, 10, 4, 4, 1, 1, 2, 4, 4, 1, 2, 13, 13, 10, 4, 4, 4, 4, 1, 2, 4, 19, 4, 4, 4, 19, 1, 19, 0, 7, 32, 4, 26, 4, 0, 1, 130, 4, 130, 8, 128, 1, 32, 5, 17, 5, 0, 130, 8, 32, 6, 17, 6, 0, 130, 0, 32, 7, 68, 1, 0, 6, 32, 9, 32, 10, 17, 10, 0, 5, 0, 32, 11, 17, 11, 0, 2, 0, 21, 9, 0, 4, 74, 0, 75, 0, 69, 73, 0, 0, 12, 2, 0, 12, 33, 11, 33, 10, 32, 12, 32, 13, 32, 14, 32, 15, 32, 16, 17, 16, 0, 4, 0, 32, 17, 17, 17, 0, 1, 0, 32, 18, 17, 18, 0, 5, 0, 77, 13, 15, 0, 3, 252, 80, 0, 81, 0, 82, 0, 130, 4, 0, 4, 19, 14, 0, 0, 15, 0, 33, 18, 33, 17, 33, 16, 74, 31, 13, 0, 4, 252, 78, 0, 0, 0, 69, 77, 0, 0, 7, 5, 0, 5, 33, 15, 33, 14, 32, 19, 32, 20, 17, 20, 0, 6, 0, 75, 40, 19, 0, 6, 252, 84, 0, 130, 1, 0, 4, 33, 20, 17, 6, 0, 83, 0, 33, 19, 17, 12, 0, 131, 0, 68, 8, 0, 3, 33, 15, 33, 14, 17, 12, 0, 131, 0, 68, 8, 0, 7, 33, 13, 33, 12, 32, 21, 32, 22, 32, 23, 17, 23, 0, 3, 0, 21, 22, 0, 1, 87, 0, 130, 0, 69, 86, 0, 0, 10, 10, 0, 4, 33, 23, 17, 7, 0, 131, 0, 33, 22, 33, 21, 68, 13, 0, 9, 33, 23, 17, 21, 0, 131, 0, 33, 22, 33, 21, 32, 25, 32, 26, 17, 26, 0, 5, 0, 32, 27, 17, 27, 0, 3, 0, 75, 40, 25, 0, 11, 252, 90, 0, 91, 0, 0, 6, 33, 27, 33, 26, 17, 5, 0, 89, 0, 33, 25, 17, 8, 0, 131, 0, 33, 9, 68, 1, 0, 5, 33, 11, 33, 10, 32, 29, 17, 7, 0, 131, 0, 33, 29, 68, 13, 0, 6, 33, 9, 33, 7, 17, 0, 0, 6, 0, 33, 6, 33, 5, 33, 4, 64]

def readFrameValidCount (st : ExecState) : Option Nat :=
  match st.stack with
  | [fr] =>
      match getLocal fr.locals 6 with
      | some (.scalar vc) => some vc
      | _ => none
  | _ => none

def countValidLoopHeaderState (bodies : List WireBody) (vc : Nat) : ExecState :=
  let (body14Types, body14Blocks) :=
    match findBodyBySym bodies 14 with
    | some body => (body.localTypes, body.blocks)
    | none => ([], [])
  let blk1 :=
    match getBlockAt body14Blocks 1 with
    | some blk => blk
    | none => { isCleanup := false, stmts := [], term := .unreachable }
  let emptySlot : HeapLogSlot := { stepCount := 0, traceAcc := 0 }
  let fr : ExecFrame :=
    { symId := 14
    , localTypes := body14Types
    , bodyBlocks := body14Blocks
    , bbIdx := 1
    , remStmts := blk1.stmts
    , curTerm := blk1.term
    , locals :=
        [ (0, .agg0 1)
        , (1, .scalar 4096)
        , (2, .scalar 8)
        , (3, .scalar 0)
        , (4, .agg3 1 (.scalar 4) (.scalar 8) (.scalar 1))
        , (5, .scalar 8)
        , (6, .scalar vc)
        , (8, .agg0 1) ]
    , pending := none }
  { status := .running, stack := [fr], heap := [emptySlot, emptySlot], obsEvents := [] }

def checkProductiveStepBodies (bodies : List WireBody) (vc : Nat) : Bool :=
  let stCycle := runSteps bodies 23 (countValidLoopHeaderState bodies vc)
  let stHeaderNext := countValidLoopHeaderState bodies (vc + 1)
  decide (stCycle = stHeaderNext) &&
  decide (readFrameValidCount stCycle = some (vc + 1))

def checkLoopEntryAndProductiveStepOnBytes (bytes : List Nat) (vc : Nat) : Bool :=
  match parseRawPackageBytes bytes with
  | .ok (pkg, []) =>
      let bodies := pkg.bodies
      let stEntry := runSteps bodies 24 (initEntryState bodies 14 [.scalar 4096, .scalar 8, .scalar 0])
      let stHeader1 := countValidLoopHeaderState bodies 1
      decide (stEntry = stHeader1) &&
      checkProductiveStepBodies bodies vc &&
      checkProductiveStepBodies bodies (vc + 1)
  | _ => false

theorem count_valid_loop_entry_and_productive_step_verified :
    checkLoopEntryAndProductiveStepOnBytes zerocopyLoopContinueBytes 1 = true := by
  rfl

#print axioms accepted_bytes_raw_parse_sound
#print axioms direct_mir_cleanup_suite_satisfies_c0_all_cases
#print axioms effect_log_record_u32_wrapping_boundary_verified
#print axioms may_unwind_op_fmt_vs_panic_transition_verified
#print axioms direct_mir_place_mention_preserve_ub_satisfies_c0
#print axioms direct_mir_place_mention_default_misses_wildcard_and_underscore_ub
#print axioms unbounded_period4_entry_to_header
#print axioms unbounded_period4_cycle_step_all
#print axioms unbounded_period4_header_induction
#print axioms unbounded_period4_all_prefixes_running_and_enabled
#print axioms unbounded_period4_bad_prefix_and_terminating_witnesses
#print axioms count_valid_loop_entry_and_productive_step_verified

end AnnealResearch.SemanticVerticalSlice
