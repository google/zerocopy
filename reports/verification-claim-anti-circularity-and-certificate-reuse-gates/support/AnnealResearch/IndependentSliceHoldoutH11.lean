/-
  Experiment: experiments/opsem / Independent Holdout & Bug Localization (`H11`, `#64` §6.1, Updated under `#68` `N4`)
  Module: IndependentSliceHoldoutH11

  End-to-end byte-level admission (`SubstantiveMirByteParser.isAdmittedPackageBytes`),
  subject binding (`SemanticVerticalSlice.checkSubjectBinding`), decoded-AST execution
  (`SemanticVerticalSlice.runSteps`) with explicit non-status-erasing outcomes
  (`SliceWindowExecOutcome`), seeded off-by-one boundary bug localization
  (`bb7` statement 10 `BinOpTag.lt` vs `BinOpTag.le` on `_12` `end` and `_4` `cap`),
  and `N4` negative controls proving that structurally admitted mutations on an
  expected-`None` path (infinite self-loop `.fuelExhausted`, uninitialized return
  `.malformedOrStuck .stuck`, and invalid pointer dereference `.ubFault`) are
  strictly separated from `.normalNone` (`.returned (.agg0 2)`).
-/

import AnnealResearch.SubstantiveMirByteParser
import AnnealResearch.SemanticVerticalSliceCore

set_option autoImplicit false
set_option maxRecDepth 131072

namespace AnnealResearch.IndependentSliceHoldoutH11

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice

/-! ## 1. Captured `.amir` v3 Byte Arrays (`independent_slice_holdout.amir` & `independent_slice_holdout_buggy.amir`) -/

/--
  Captured `.amir` v3 package for `independent_slice_holdout.rs` (`936` bytes, `fp16 = [105, 210]`,
  `sha256 = e12e395747c1770be1f72d15773edb528fb3659e59609e6bf1a2a0f584738370`).
  Contains 8 bodies:
  - `symId = 1`: `EffectLog::record` (`LocalOwner`, `Runtime(PostCleanup)`)
  - `symId = 2`: `<Guard<'a> as Drop>::drop` (`LocalOwner`, `Runtime(PostCleanup)`)
  - `symId = 68`: `validate_slice_window` (`LocalOwner`, `Runtime(PostCleanup)`)
  - `symId = 69`: `guarded_window_commit` (`LocalOwner`, `Runtime(PostCleanup)`)
  - `symId = 7`: `DropGlue<Guard>` (`CompilerShim`, `Runtime(Optimized)`)
  - `symId = 29`: `<Option<usize> as Try>::branch` (`ExternalRlib`, `Runtime(Optimized)`)
  - `symId = 30`: `<Option<usize> as FromResidual>::from_residual` (`ExternalRlib`, `Runtime(Optimized)`)
  - `symId = 24`: `core::mem::drop::<Guard>` (`ExternalRlib`, `Runtime(Optimized)`)
-/
def realIndependentSliceHoldoutBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 105, 210, 8, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 68, 1, 3, 26, 4, 14, 12, 4, 4, 4, 4, 1, 2, 4, 19, 4, 4, 4, 4, 14, 12, 4, 4, 4, 12, 19, 12, 4, 2, 4, 4, 4, 0, 5, 32, 5, 32, 6, 32, 7, 17, 7, 0, 3, 0, 21, 6, 0, 1, 71, 0, 130, 0, 69, 70, 0, 0, 2, 1, 0, 4, 33, 7, 23, 0, 0, 2, 33, 6, 33, 5, 68, 13, 0, 9, 33, 7, 17, 5, 0, 131, 0, 33, 6, 33, 5, 32, 9, 32, 10, 17, 10, 0, 2, 0, 32, 11, 17, 11, 0, 3, 0, 75, 41, 9, 0, 3, 252, 74, 0, 75, 0, 0, 9, 33, 11, 33, 10, 32, 12, 32, 13, 32, 14, 32, 15, 17, 15, 0, 1, 0, 32, 16, 17, 16, 0, 9, 0, 75, 23, 14, 0, 4, 252, 79, 0, 80, 0, 0, 2, 33, 16, 33, 15, 74, 29, 13, 0, 5, 252, 78, 0, 0, 3, 33, 14, 48, 13, 0, 20, 17, 0, 13, 0, 70, 81, 0, 0, 7, 1, 8, 6, 0, 0, 67, 0, 11, 32, 21, 17, 21, 0, 13, 8, 17, 12, 0, 21, 0, 33, 21, 33, 13, 32, 22, 32, 23, 17, 23, 0, 12, 0, 32, 24, 17, 24, 0, 4, 0, 21, 22, 0, 4, 87, 0, 88, 0, 69, 86, 0, 0, 11, 10, 0, 4, 32, 18, 17, 18, 0, 13, 9, 32, 20, 17, 20, 0, 18, 0, 74, 30, 0, 0, 9, 252, 84, 0, 0, 5, 33, 20, 33, 18, 33, 13, 33, 12, 33, 9, 68, 13, 0, 6, 33, 24, 33, 23, 32, 25, 17, 25, 0, 12, 0, 24, 0, 0, 1, 89, 0, 33, 25, 68, 12, 0, 3, 33, 24, 33, 23, 23, 0, 0, 2, 68, 12, 0, 3, 33, 22, 33, 12, 33, 9, 68, 13, 0, 0, 64, 4, 69, 1, 3, 23, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 19, 1, 6, 1, 8, 1, 6, 1, 8, 6, 6, 2, 2, 0, 17, 17, 22, 0, 128, 0, 17, 21, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 22, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 21, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 4, 32, 11, 32, 12, 16, 19, 0, 4, 2, 19, 12, 0, 1, 19, 4, 75, 1, 11, 0, 2, 12, 76, 0, 129, 9, 0, 6, 33, 12, 33, 11, 32, 13, 32, 14, 17, 22, 0, 128, 0, 17, 14, 0, 68, 0, 74, 24, 13, 0, 3, 12, 78, 0, 0, 5, 33, 14, 33, 13, 17, 0, 0, 129, 0, 33, 9, 33, 8, 71, 6, 0, 7, 8, 14, 0, 7, 17, 8, 0, 131, 0, 33, 9, 33, 8, 32, 15, 32, 16, 16, 20, 0, 4, 2, 19, 16, 0, 1, 20, 4, 75, 1, 15, 0, 5, 12, 80, 0, 129, 5, 0, 6, 33, 16, 33, 15, 32, 17, 32, 18, 17, 21, 0, 128, 0, 17, 18, 0, 70, 0, 74, 24, 17, 0, 6, 12, 82, 0, 0, 5, 33, 18, 33, 17, 17, 0, 0, 129, 50, 17, 21, 0, 128, 0, 33, 6, 71, 4, 0, 7, 7, 10, 0, 2, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 4, 17, 21, 0, 128, 0, 33, 6, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 0, 64, 1, 0, 65, 1, 0, 71, 6, 0, 7, 14, 255, 1, 0, 69, 21, 0, 0, 14, 11, 1, 0, 71, 4, 0, 7, 10, 255, 1, 0, 69, 22, 0, 0, 10, 13, 5, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 6, 29, 3, 4, 3, 1, 2, 14, 12, 1, 0, 2, 32, 2, 23, 2, 0, 2, 75, 28, 0, 0, 1, 252, 65, 0, 66, 0, 0, 1, 33, 2, 64, 7, 30, 3, 4, 2, 1, 1, 12, 12, 0, 1, 23, 0, 0, 2, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/--
  Captured `.amir` v3 package for `independent_slice_holdout_buggy.rs` (`936` bytes, `fp16 = [121, 240]`,
  `sha256 = fa3220482623f471ad20c5ace230b61ff991775bf50a9775c21003cce074cbb8`),
  where `if end <= cap` in `validate_slice_window` is replaced by strict `if end < cap`
  (lowering `bb7` statement 10 from `BinOpTag.le` `0x04` to `BinOpTag.lt` `0x03` at byte offset `403`).
-/
def realIndependentSliceHoldoutBuggyBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 121, 240, 8, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 68, 1, 3, 26, 4, 14, 12, 4, 4, 4, 4, 1, 2, 4, 19, 4, 4, 4, 4, 14, 12, 4, 4, 4, 12, 19, 12, 4, 2, 4, 4, 4, 0, 5, 32, 5, 32, 6, 32, 7, 17, 7, 0, 3, 0, 21, 6, 0, 1, 71, 0, 130, 0, 69, 70, 0, 0, 2, 1, 0, 4, 33, 7, 23, 0, 0, 2, 33, 6, 33, 5, 68, 13, 0, 9, 33, 7, 17, 5, 0, 131, 0, 33, 6, 33, 5, 32, 9, 32, 10, 17, 10, 0, 2, 0, 32, 11, 17, 11, 0, 3, 0, 75, 41, 9, 0, 3, 252, 74, 0, 75, 0, 0, 9, 33, 11, 33, 10, 32, 12, 32, 13, 32, 14, 32, 15, 17, 15, 0, 1, 0, 32, 16, 17, 16, 0, 9, 0, 75, 23, 14, 0, 4, 252, 79, 0, 80, 0, 0, 2, 33, 16, 33, 15, 74, 29, 13, 0, 5, 252, 78, 0, 0, 3, 33, 14, 48, 13, 0, 20, 17, 0, 13, 0, 70, 81, 0, 0, 7, 1, 8, 6, 0, 0, 67, 0, 11, 32, 21, 17, 21, 0, 13, 8, 17, 12, 0, 21, 0, 33, 21, 33, 13, 32, 22, 32, 23, 17, 23, 0, 12, 0, 32, 24, 17, 24, 0, 4, 0, 21, 22, 0, 3, 87, 0, 88, 0, 69, 86, 0, 0, 11, 10, 0, 4, 32, 18, 17, 18, 0, 13, 9, 32, 20, 17, 20, 0, 18, 0, 74, 30, 0, 0, 9, 252, 84, 0, 0, 5, 33, 20, 33, 18, 33, 13, 33, 12, 33, 9, 68, 13, 0, 6, 33, 24, 33, 23, 32, 25, 17, 25, 0, 12, 0, 24, 0, 0, 1, 89, 0, 33, 25, 68, 12, 0, 3, 33, 24, 33, 23, 23, 0, 0, 2, 68, 12, 0, 3, 33, 22, 33, 12, 33, 9, 68, 13, 0, 0, 64, 4, 69, 1, 3, 23, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 19, 1, 6, 1, 8, 1, 6, 1, 8, 6, 6, 2, 2, 0, 17, 17, 22, 0, 128, 0, 17, 21, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 22, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 21, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 4, 32, 11, 32, 12, 16, 19, 0, 4, 2, 19, 12, 0, 1, 19, 4, 75, 1, 11, 0, 2, 12, 76, 0, 129, 9, 0, 6, 33, 12, 33, 11, 32, 13, 32, 14, 17, 22, 0, 128, 0, 17, 14, 0, 68, 0, 74, 24, 13, 0, 3, 12, 78, 0, 0, 5, 33, 14, 33, 13, 17, 0, 0, 129, 0, 33, 9, 33, 8, 71, 6, 0, 7, 8, 14, 0, 7, 17, 8, 0, 131, 0, 33, 9, 33, 8, 32, 15, 32, 16, 16, 20, 0, 4, 2, 19, 16, 0, 1, 20, 4, 75, 1, 15, 0, 5, 12, 80, 0, 129, 5, 0, 6, 33, 16, 33, 15, 32, 17, 32, 18, 17, 21, 0, 128, 0, 17, 18, 0, 70, 0, 74, 24, 17, 0, 6, 12, 82, 0, 0, 5, 33, 18, 33, 17, 17, 0, 0, 129, 50, 17, 21, 0, 128, 0, 33, 6, 71, 4, 0, 7, 7, 10, 0, 2, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 4, 17, 21, 0, 128, 0, 33, 6, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 0, 64, 1, 0, 65, 1, 0, 71, 6, 0, 7, 14, 255, 1, 0, 69, 21, 0, 0, 14, 11, 1, 0, 71, 4, 0, 7, 10, 255, 1, 0, 69, 22, 0, 0, 10, 13, 5, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 6, 29, 3, 4, 3, 1, 2, 14, 12, 1, 0, 2, 32, 2, 23, 2, 0, 2, 75, 28, 0, 0, 1, 252, 65, 0, 66, 0, 0, 1, 33, 2, 64, 7, 30, 3, 4, 2, 1, 1, 12, 12, 0, 1, 23, 0, 0, 2, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/-! ## 2. Boundary 1–3 Admission and Subject-Binding Contracts -/

def independentSliceHoldoutBindingContract : SubjectBindingContract :=
  { expectedVersion := 3
  , expectedPhase := .runtimePostCleanup
  , requireMonoComplete := true
  , requirePreserveUb := true
  , requireUbChecks := true
  , expectedFpHi := 105
  , expectedFpLo := 210
  , requiredSymIds := [1, 2, 68, 69, 7, 29, 30, 24] }

def independentSliceHoldoutBuggyBindingContract : SubjectBindingContract :=
  { expectedVersion := 3
  , expectedPhase := .runtimePostCleanup
  , requireMonoComplete := true
  , requirePreserveUb := true
  , requireUbChecks := true
  , expectedFpHi := 121
  , expectedFpLo := 240
  , requiredSymIds := [1, 2, 68, 69, 7, 29, 30, 24] }

def checkAdmittedAndBound (contract : SubjectBindingContract) (bytes : List Nat) : Bool :=
  match parseAdmittedPackageBytes bytes with
  | some pkg => checkSubjectBinding contract pkg
  | none => false

theorem independent_holdout_packages_admitted_and_bound :
    isAdmittedPackageBytes realIndependentSliceHoldoutBytes = true ∧
    isAdmittedPackageBytes realIndependentSliceHoldoutBuggyBytes = true ∧
    checkAdmittedAndBound independentSliceHoldoutBindingContract realIndependentSliceHoldoutBytes = true ∧
    checkAdmittedAndBound independentSliceHoldoutBuggyBindingContract realIndependentSliceHoldoutBuggyBytes = true := by
  decide

/-! ## 3. Explicit Non-Status-Erasing Outcomes (`#68` `N4`) and Decoded-AST Evaluators -/

/--
  Explicit execution outcome for `validate_slice_window` (`#68` §§4.6, 6 N4).
  Strictly separates normal `Option::Some(endOff)` (`.returned (.agg1 1 (.scalar endOff))`)
  and normal `Option::None` (`.returned (.agg0 2)`) from UB faults, unwinds, aborts,
  missing bodies, stuck/malformed states, and fuel exhaustion (`.running`).
-/
inductive SliceWindowExecOutcome where
  | normalSome (endOff : Nat)
  | normalNone
  | ubFault
  | unwound
  | terminatedAbort (reason : Nat)
  | missingBody (symId : Nat)
  | malformedOrStuck (st : ExecStatus)
  | fuelExhausted
  deriving DecidableEq, Repr

def classifySliceWindowStatus (st : ExecStatus) : SliceWindowExecOutcome :=
  match st with
  | .returned (.agg1 1 (.scalar endOff)) => .normalSome endOff
  | .returned (.agg0 2) => .normalNone
  | .ub => .ubFault
  | .unwoundTop => .unwound
  | .terminatedAbort r => .terminatedAbort r
  | .missingBody symId => .missingBody symId
  | .running => .fuelExhausted
  | other => .malformedOrStuck other

theorem classifySliceWindowStatus_normalNone_iff (st : ExecStatus) :
    classifySliceWindowStatus st = .normalNone ↔ st = .returned (.agg0 2) := by
  constructor
  · intro h
    cases st with
    | running => contradiction
    | unwinding => contradiction
    | unwoundTop => contradiction
    | terminatedAbort _ => contradiction
    | ub => contradiction
    | missingBody _ => contradiction
    | stuck => contradiction
    | returned rv =>
        cases rv with
        | scalar _ => contradiction
        | agg0 k =>
            dsimp [classifySliceWindowStatus] at h
            cases k with
            | zero => contradiction
            | succ k1 =>
                cases k1 with
                | zero => contradiction
                | succ k2 =>
                    cases k2 with
                    | zero => rfl
                    | succ _ => contradiction
        | agg1 k f0 =>
            cases k with
            | zero => contradiction
            | succ k1 =>
                cases k1 with
                | zero =>
                    cases f0 <;> contradiction
                | succ _ => contradiction
        | agg2 _ _ _ => contradiction
        | agg3 _ _ _ _ => contradiction
        | heapPtr _ => contradiction
        | extPtr _ => contradiction
        | refVal _ => contradiction
        | opaqueFmtArgs _ => contradiction
  · intro h
    subst h
    rfl

/--
  Executes `validate_slice_window(base_offset, elem_count, elem_size, cap)` (`symId = 68`)
  directly on the decoded `WireBody` list from an admitted `.amir` v3 byte stream via
  `SemanticVerticalSlice.runSteps`, preserving the exact `SliceWindowExecOutcome`.
-/
def evalValidateSliceWindowBodies
    (bodies : List WireBody)
    (baseOffset elemCount elemSize cap : Nat) : SliceWindowExecOutcome :=
  let args : List RtVal :=
    [ .scalar baseOffset
    , .scalar elemCount
    , .scalar elemSize
    , .scalar cap ]
  let finalSt := runSteps bodies 25 (initEntryState bodies 68 args)
  classifySliceWindowStatus finalSt.status

def evalValidateSliceWindowOnBytes
    (bytes : List Nat)
    (baseOffset elemCount elemSize cap : Nat) : Option SliceWindowExecOutcome :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalValidateSliceWindowBodies pkg.bodies baseOffset elemCount elemSize cap)
  | none => none

/--
  Legacy status-erasing projection from `#67` (`e3c1e59`, `L92–103`), retained solely as a
  documented negative baseline for `#68` `N4` to prove that collapsing non-`Some` statuses
  to `none` conflates `.fuelExhausted`, `.malformedOrStuck`, and `.ubFault` with `.normalNone`.
-/
def legacyStatusErasingEvalValidateSliceWindowBodies
    (bodies : List WireBody)
    (baseOffset elemCount elemSize cap : Nat) : Option Nat :=
  let args : List RtVal :=
    [ .scalar baseOffset
    , .scalar elemCount
    , .scalar elemSize
    , .scalar cap ]
  let finalSt := runSteps bodies 25 (initEntryState bodies 68 args)
  match finalSt.status with
  | .returned (.agg1 1 (.scalar endOff)) => some endOff
  | _ => none

def legacyStatusErasingEvalValidateSliceWindowOnBytes
    (bytes : List Nat)
    (baseOffset elemCount elemSize cap : Nat) : Option (Option Nat) :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (legacyStatusErasingEvalValidateSliceWindowBodies pkg.bodies baseOffset elemCount elemSize cap)
  | none => none

/--
  Frozen H11 specification for `validate_slice_window(base_offset, elem_count, elem_size, cap)`
  with explicit `SliceWindowExecOutcome`:
  - When `elem_size == 0`, returns `.normalNone`.
  - Otherwise `byte_len = (elem_count * elem_size) % usizeMod`; if `base_offset + byte_len >= usizeMod`,
    returns `.normalNone`; else `end = base_offset + byte_len`, returning `.normalSome end` iff `end <= cap`.
-/
def h11SpecValidateSliceWindow (baseOffset elemCount elemSize cap : Nat) : SliceWindowExecOutcome :=
  if Nat.beq elemSize 0 then .normalNone
  else
    let byteLen := (elemCount * elemSize) % usizeMod
    let sum := baseOffset + byteLen
    if Nat.blt sum usizeMod then
      bif Nat.ble sum cap then .normalSome sum else .normalNone
    else
      .normalNone

structure ValidateSliceWindowSuiteResult where
  elemSizeZero : SliceWindowExecOutcome
  exactCapBoundary : SliceWindowExecOutcome
  exceedsCapBoundary : SliceWindowExecOutcome
  checkedAddOverflow : SliceWindowExecOutcome
  deriving DecidableEq, Repr

def evalValidateSliceWindowSuiteOnBytes (bytes : List Nat) : Option ValidateSliceWindowSuiteResult :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let bodies := pkg.bodies
      some
        { elemSizeZero := evalValidateSliceWindowBodies bodies 16 4 0 48
        , exactCapBoundary := evalValidateSliceWindowBodies bodies 16 4 8 48
        , exceedsCapBoundary := evalValidateSliceWindowBodies bodies 16 4 8 47
        , checkedAddOverflow := evalValidateSliceWindowBodies bodies (usizeMax - 8) 4 4 usizeMax }
  | none => none

def h11SpecValidateSliceWindowSuite : ValidateSliceWindowSuiteResult :=
  { elemSizeZero := h11SpecValidateSliceWindow 16 4 0 48
  , exactCapBoundary := h11SpecValidateSliceWindow 16 4 8 48
  , exceedsCapBoundary := h11SpecValidateSliceWindow 16 4 8 47
  , checkedAddOverflow := h11SpecValidateSliceWindow (usizeMax - 8) 4 4 usizeMax }

/--
  Executes `guarded_window_commit(log1, log2, abort_early)` (`symId = 69`) with disjoint
  `EffectLog` heap allocations (`log1 = .heapPtr 0`, `log2 = .heapPtr 1`) via
  `SemanticVerticalSlice.runSteps`.
-/
def evalGuardedWindowCommitBodies (bodies : List WireBody) (abortEarly : Bool) : CleanupExecOutcome :=
  let args : List RtVal :=
    [ .heapPtr 0
    , .heapPtr 1
    , .scalar (bif abortEarly then 1 else 0) ]
  let finalSt := runSteps bodies 40 (initEntryState bodies 69 args)
  let (l1, l2) := summarizeTwoHeapLogs finalSt.heap
  match finalSt.status with
  | .returned (.scalar rv) => .normalReturn rv l1 l2 finalSt.obsEvents
  | .unwoundTop => .unwoundWithCleanup l1 l2 finalSt.obsEvents
  | other => .failed other

def evalGuardedWindowCommitOnBytes (bytes : List Nat) (abortEarly : Bool) : Option CleanupExecOutcome :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      some (evalGuardedWindowCommitBodies pkg.bodies abortEarly)
  | none => none

/--
  Frozen H11 specification for `guarded_window_commit(log1, log2, abort_early)`:
  - `abort_early = true`: records `9` on `log1`, drops `g1` early (`1` on `log1`), drops `g2` at
    scope exit (`2` on `log2`), returning `0` with `log1 = (2, 145)`, `log2 = (1, 2)`, `obsEvents = [9, 1, 2]`.
  - `abort_early = false`: records `5` on `log1`, drops `g2` early (`2` on `log2`), drops `g1` at
    scope exit (`1` on `log1`), returning `50` with `log1 = (2, 81)`, `log2 = (1, 2)`, `obsEvents = [5, 2, 1]`.
-/
def h11SpecGuardedWindowCommit (abortEarly : Bool) : CleanupExecOutcome :=
  match abortEarly with
  | true  => .normalReturn 0 (2, 145) (1, 2) [9, 1, 2]
  | false => .normalReturn 50 (2, 81) (1, 2) [5, 2, 1]

/-! ## 4. Main H11 Holdout Theorems & Seeded Bug Localization -/

/--
  H11 Theorem 1 (Repaired under `#68` `N4`): `validate_slice_window` (`symId = 68`) in
  `realIndependentSliceHoldoutBytes` satisfies all 4 frozen specification vectors with
  explicit `SliceWindowExecOutcome` statuses when executed through `SemanticVerticalSlice.runSteps`:
  - `elem_size == 0` `(16, 4, 0, 48) -> .normalNone` (`.returned (.agg0 2)`)
  - exact boundary `(16, 4, 8, 48) -> .normalSome 48` (`.returned (.agg1 1 (.scalar 48))`)
  - over-capacity `(16, 4, 8, 47) -> .normalNone` (`.returned (.agg0 2)`)
  - 64-bit `checked_add` overflow `(usizeMax - 8, 4, 4, usizeMax) -> .normalNone` (`.returned (.agg0 2)`)
-/
theorem independent_holdout_validate_slice_window_satisfies_spec :
    evalValidateSliceWindowSuiteOnBytes realIndependentSliceHoldoutBytes =
      some h11SpecValidateSliceWindowSuite ∧
    h11SpecValidateSliceWindowSuite =
      { elemSizeZero := .normalNone
      , exactCapBoundary := .normalSome 48
      , exceedsCapBoundary := .normalNone
      , checkedAddOverflow := .normalNone } := by
  refine ⟨rfl, rfl⟩

/--
  H11 Theorem 2: The seeded off-by-one boundary bug in `realIndependentSliceHoldoutBuggyBytes`
  (`if end < cap` instead of `if end <= cap`) falsifies the exact capacity boundary vector
  `(16, 4, 8, 48)`, evaluating to `some .normalNone` instead of `some (.normalSome 48)`.
-/
theorem independent_holdout_buggy_falsifies_exact_cap_boundary :
    evalValidateSliceWindowOnBytes realIndependentSliceHoldoutBuggyBytes 16 4 8 48 = some .normalNone ∧
    evalValidateSliceWindowOnBytes realIndependentSliceHoldoutBytes 16 4 8 48 = some (.normalSome 48) ∧
    evalValidateSliceWindowOnBytes realIndependentSliceHoldoutBuggyBytes 16 4 8 48 ≠
      some (h11SpecValidateSliceWindow 16 4 8 48) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/--
  Extracts a specific statement `(symId, bbIdx, stmtIdx)` from a decoded `.amir` v3 package
  for structural fault localization.
-/
def inspectDecodedStmtAt (bytes : List Nat) (symId bbIdx stmtIdx : Nat) : Option WireStmt :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      match findBodyBySym pkg.bodies symId with
      | some body =>
          match getBlockAt body.blocks bbIdx with
          | some blk =>
              match blk.stmts.drop stmtIdx with
              | st :: _ => some st
              | [] => none
          | none => none
      | none => none
  | none => none

/--
  H11 Theorem 2b (Diagnostic Bug Localization at `symId = 68`, `bb7`, statement `10`):
  In `validate_slice_window` (`symId = 68`), `var_debug_join` binds `_12` to `UniqueUserVar "end"`
  and `_4` to `UniqueUserVar "cap"`. In basic block `bb7`:
  - statement `7` copies `_12` (`end`) into `_23`,
  - statement `9` copies `_4` (`cap`) into `_24`, and
  - statement `10` computes `_22 = BinOp(move _23, move _24)` using `.lt` (`0x03`) in
    `realIndependentSliceHoldoutBuggyBytes` versus `.le` (`0x04`) in
    `realIndependentSliceHoldoutBytes`.
-/
theorem independent_holdout_buggy_bb7_localized_lt_vs_le :
    inspectDecodedStmtAt realIndependentSliceHoldoutBuggyBytes 68 7 7 =
      some (.assignUseRetagYes { localIdx := 23, proj := .here } (.copy { localIdx := 12, proj := .here })) ∧
    inspectDecodedStmtAt realIndependentSliceHoldoutBuggyBytes 68 7 9 =
      some (.assignUseRetagYes { localIdx := 24, proj := .here } (.copy { localIdx := 4, proj := .here })) ∧
    inspectDecodedStmtAt realIndependentSliceHoldoutBuggyBytes 68 7 10 =
      some (.assignBinOp { localIdx := 22, proj := .here } .lt
        (.move { localIdx := 23, proj := .here })
        (.move { localIdx := 24, proj := .here })) ∧
    inspectDecodedStmtAt realIndependentSliceHoldoutBytes 68 7 10 =
      some (.assignBinOp { localIdx := 22, proj := .here } .le
        (.move { localIdx := 23, proj := .here })
        (.move { localIdx := 24, proj := .here })) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/--
  H11 Theorem 3: `guarded_window_commit` (`symId = 69`) in `realIndependentSliceHoldoutBytes`
  satisfies both branches of the frozen specification when executed through
  `SemanticVerticalSlice.runSteps`:
  - `abort_early = true`: `.normalReturn 0 (2, 145) (1, 2) [9, 1, 2]`
  - `abort_early = false`: `.normalReturn 50 (2, 81) (1, 2) [5, 2, 1]`
-/
theorem independent_holdout_guarded_window_commit_satisfies_spec :
    evalGuardedWindowCommitOnBytes realIndependentSliceHoldoutBytes true =
      some (h11SpecGuardedWindowCommit true) ∧
    evalGuardedWindowCommitOnBytes realIndependentSliceHoldoutBytes false =
      some (h11SpecGuardedWindowCommit false) ∧
    h11SpecGuardedWindowCommit true = .normalReturn 0 (2, 145) (1, 2) [9, 1, 2] ∧
    h11SpecGuardedWindowCommit false = .normalReturn 50 (2, 81) (1, 2) [5, 2, 1] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## 5. `#68` `N4` Negative Controls: Rejection of Expected-`None` Path Mutations -/

/--
  `N4` Mutant 1 (`936` bytes, `fp16 = [120, 105]`): Structurally admitted `.amir` v3 package
  identical to `realIndependentSliceHoldoutBytes` except that in `validate_slice_window`
  (`symId = 68`) basic block `bb1` (the `elem_size == 0` rejection path), terminator
  `Goto(bb13)` (`68, 13, 0`) at byte offset `252..254` is mutated to `Goto(bb1)` (`68, 1, 0`),
  creating a nonterminating self-loop on the `elem_size == 0` path.
-/
def mutantValidateSliceWindowElemZeroInfiniteLoopBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 120, 105, 8, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 68, 1, 3, 26, 4, 14, 12, 4, 4, 4, 4, 1, 2, 4, 19, 4, 4, 4, 4, 14, 12, 4, 4, 4, 12, 19, 12, 4, 2, 4, 4, 4, 0, 5, 32, 5, 32, 6, 32, 7, 17, 7, 0, 3, 0, 21, 6, 0, 1, 71, 0, 130, 0, 69, 70, 0, 0, 2, 1, 0, 4, 33, 7, 23, 0, 0, 2, 33, 6, 33, 5, 68, 1, 0, 9, 33, 7, 17, 5, 0, 131, 0, 33, 6, 33, 5, 32, 9, 32, 10, 17, 10, 0, 2, 0, 32, 11, 17, 11, 0, 3, 0, 75, 41, 9, 0, 3, 252, 74, 0, 75, 0, 0, 9, 33, 11, 33, 10, 32, 12, 32, 13, 32, 14, 32, 15, 17, 15, 0, 1, 0, 32, 16, 17, 16, 0, 9, 0, 75, 23, 14, 0, 4, 252, 79, 0, 80, 0, 0, 2, 33, 16, 33, 15, 74, 29, 13, 0, 5, 252, 78, 0, 0, 3, 33, 14, 48, 13, 0, 20, 17, 0, 13, 0, 70, 81, 0, 0, 7, 1, 8, 6, 0, 0, 67, 0, 11, 32, 21, 17, 21, 0, 13, 8, 17, 12, 0, 21, 0, 33, 21, 33, 13, 32, 22, 32, 23, 17, 23, 0, 12, 0, 32, 24, 17, 24, 0, 4, 0, 21, 22, 0, 4, 87, 0, 88, 0, 69, 86, 0, 0, 11, 10, 0, 4, 32, 18, 17, 18, 0, 13, 9, 32, 20, 17, 20, 0, 18, 0, 74, 30, 0, 0, 9, 252, 84, 0, 0, 5, 33, 20, 33, 18, 33, 13, 33, 12, 33, 9, 68, 13, 0, 6, 33, 24, 33, 23, 32, 25, 17, 25, 0, 12, 0, 24, 0, 0, 1, 89, 0, 33, 25, 68, 12, 0, 3, 33, 24, 33, 23, 23, 0, 0, 2, 68, 12, 0, 3, 33, 22, 33, 12, 33, 9, 68, 13, 0, 0, 64, 4, 69, 1, 3, 23, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 19, 1, 6, 1, 8, 1, 6, 1, 8, 6, 6, 2, 2, 0, 17, 17, 22, 0, 128, 0, 17, 21, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 22, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 21, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 4, 32, 11, 32, 12, 16, 19, 0, 4, 2, 19, 12, 0, 1, 19, 4, 75, 1, 11, 0, 2, 12, 76, 0, 129, 9, 0, 6, 33, 12, 33, 11, 32, 13, 32, 14, 17, 22, 0, 128, 0, 17, 14, 0, 68, 0, 74, 24, 13, 0, 3, 12, 78, 0, 0, 5, 33, 14, 33, 13, 17, 0, 0, 129, 0, 33, 9, 33, 8, 71, 6, 0, 7, 8, 14, 0, 7, 17, 8, 0, 131, 0, 33, 9, 33, 8, 32, 15, 32, 16, 16, 20, 0, 4, 2, 19, 16, 0, 1, 20, 4, 75, 1, 15, 0, 5, 12, 80, 0, 129, 5, 0, 6, 33, 16, 33, 15, 32, 17, 32, 18, 17, 21, 0, 128, 0, 17, 18, 0, 70, 0, 74, 24, 17, 0, 6, 12, 82, 0, 0, 5, 33, 18, 33, 17, 17, 0, 0, 129, 50, 17, 21, 0, 128, 0, 33, 6, 71, 4, 0, 7, 7, 10, 0, 2, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 4, 17, 21, 0, 128, 0, 33, 6, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 0, 64, 1, 0, 65, 1, 0, 71, 6, 0, 7, 14, 255, 1, 0, 69, 21, 0, 0, 14, 11, 1, 0, 71, 4, 0, 7, 10, 255, 1, 0, 69, 22, 0, 0, 10, 13, 5, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 6, 29, 3, 4, 3, 1, 2, 14, 12, 1, 0, 2, 32, 2, 23, 2, 0, 2, 75, 28, 0, 0, 1, 252, 65, 0, 66, 0, 0, 1, 33, 2, 64, 7, 30, 3, 4, 2, 1, 1, 12, 12, 0, 1, 23, 0, 0, 2, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/--
  `N4` Mutant 2 (`936` bytes, `fp16 = [201, 11]`): Structurally admitted `.amir` v3 package
  identical to `realIndependentSliceHoldoutBytes` except that in `validate_slice_window`
  (`symId = 68`) basic block `bb1` (the `elem_size == 0` rejection path), `_0 = Option::None`
  (`23, 0, 0, 2`) at byte offset `244..248` is replaced by `_7 = Option::None` (`23, 7, 0, 2`),
  leaving return local `_0` uninitialized when `bb13` executes `Return` (`ExecStatus.stuck`).
-/
def mutantValidateSliceWindowElemZeroStuckReturnBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 201, 11, 8, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 68, 1, 3, 26, 4, 14, 12, 4, 4, 4, 4, 1, 2, 4, 19, 4, 4, 4, 4, 14, 12, 4, 4, 4, 12, 19, 12, 4, 2, 4, 4, 4, 0, 5, 32, 5, 32, 6, 32, 7, 17, 7, 0, 3, 0, 21, 6, 0, 1, 71, 0, 130, 0, 69, 70, 0, 0, 2, 1, 0, 4, 33, 7, 23, 7, 0, 2, 33, 6, 33, 5, 68, 13, 0, 9, 33, 7, 17, 5, 0, 131, 0, 33, 6, 33, 5, 32, 9, 32, 10, 17, 10, 0, 2, 0, 32, 11, 17, 11, 0, 3, 0, 75, 41, 9, 0, 3, 252, 74, 0, 75, 0, 0, 9, 33, 11, 33, 10, 32, 12, 32, 13, 32, 14, 32, 15, 17, 15, 0, 1, 0, 32, 16, 17, 16, 0, 9, 0, 75, 23, 14, 0, 4, 252, 79, 0, 80, 0, 0, 2, 33, 16, 33, 15, 74, 29, 13, 0, 5, 252, 78, 0, 0, 3, 33, 14, 48, 13, 0, 20, 17, 0, 13, 0, 70, 81, 0, 0, 7, 1, 8, 6, 0, 0, 67, 0, 11, 32, 21, 17, 21, 0, 13, 8, 17, 12, 0, 21, 0, 33, 21, 33, 13, 32, 22, 32, 23, 17, 23, 0, 12, 0, 32, 24, 17, 24, 0, 4, 0, 21, 22, 0, 4, 87, 0, 88, 0, 69, 86, 0, 0, 11, 10, 0, 4, 32, 18, 17, 18, 0, 13, 9, 32, 20, 17, 20, 0, 18, 0, 74, 30, 0, 0, 9, 252, 84, 0, 0, 5, 33, 20, 33, 18, 33, 13, 33, 12, 33, 9, 68, 13, 0, 6, 33, 24, 33, 23, 32, 25, 17, 25, 0, 12, 0, 24, 0, 0, 1, 89, 0, 33, 25, 68, 12, 0, 3, 33, 24, 33, 23, 23, 0, 0, 2, 68, 12, 0, 3, 33, 22, 33, 12, 33, 9, 68, 13, 0, 0, 64, 4, 69, 1, 3, 23, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 19, 1, 6, 1, 8, 1, 6, 1, 8, 6, 6, 2, 2, 0, 17, 17, 22, 0, 128, 0, 17, 21, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 22, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 21, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 4, 32, 11, 32, 12, 16, 19, 0, 4, 2, 19, 12, 0, 1, 19, 4, 75, 1, 11, 0, 2, 12, 76, 0, 129, 9, 0, 6, 33, 12, 33, 11, 32, 13, 32, 14, 17, 22, 0, 128, 0, 17, 14, 0, 68, 0, 74, 24, 13, 0, 3, 12, 78, 0, 0, 5, 33, 14, 33, 13, 17, 0, 0, 129, 0, 33, 9, 33, 8, 71, 6, 0, 7, 8, 14, 0, 7, 17, 8, 0, 131, 0, 33, 9, 33, 8, 32, 15, 32, 16, 16, 20, 0, 4, 2, 19, 16, 0, 1, 20, 4, 75, 1, 15, 0, 5, 12, 80, 0, 129, 5, 0, 6, 33, 16, 33, 15, 32, 17, 32, 18, 17, 21, 0, 128, 0, 17, 18, 0, 70, 0, 74, 24, 17, 0, 6, 12, 82, 0, 0, 5, 33, 18, 33, 17, 17, 0, 0, 129, 50, 17, 21, 0, 128, 0, 33, 6, 71, 4, 0, 7, 7, 10, 0, 2, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 4, 17, 21, 0, 128, 0, 33, 6, 17, 22, 0, 128, 0, 33, 4, 68, 9, 0, 0, 64, 1, 0, 65, 1, 0, 71, 6, 0, 7, 14, 255, 1, 0, 69, 21, 0, 0, 14, 11, 1, 0, 71, 4, 0, 7, 10, 255, 1, 0, 69, 22, 0, 0, 10, 13, 5, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 6, 29, 3, 4, 3, 1, 2, 14, 12, 1, 0, 2, 32, 2, 23, 2, 0, 2, 75, 28, 0, 0, 1, 252, 65, 0, 66, 0, 0, 1, 33, 2, 64, 7, 30, 3, 4, 2, 1, 1, 12, 12, 0, 1, 23, 0, 0, 2, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/--
  `N4` Negative Control Theorem (`#68` §§4.6, 6 N4):
  1. Both `mutantValidateSliceWindowElemZeroInfiniteLoopBytes` (infinite self-loop `Goto(bb1)` on
     the `elem_size == 0` path) and `mutantValidateSliceWindowElemZeroStuckReturnBytes`
     (uninitialized `_0` on the `elem_size == 0` path) are structurally admitted `.amir` v3 packages
     (`isAdmittedPackageBytes = true`).
  2. Under the legacy status-erasing projection (`legacyStatusErasingEvalValidateSliceWindowOnBytes`),
     both mutants return `some none` on `(16, 4, 0, 48)`, falsely matching `Option::None`!
  3. Under the repaired `evalValidateSliceWindowOnBytes` (`SliceWindowExecOutcome`), the self-loop
     mutant evaluates to `some .fuelExhausted` (`≠ some .normalNone`) and the uninitialized-return
     mutant evaluates to `some (.malformedOrStuck .stuck)` (`≠ some .normalNone`), so both are
     rejected by the specification check `evalValidateSliceWindowSuiteOnBytes bytes = some h11SpecValidateSliceWindowSuite`.
-/
theorem control_n4_status_erasing_projection_accepts_faulting_and_nonterminating_none_mutants_while_explicit_outcome_rejects :
    isAdmittedPackageBytes mutantValidateSliceWindowElemZeroInfiniteLoopBytes = true ∧
    isAdmittedPackageBytes mutantValidateSliceWindowElemZeroStuckReturnBytes = true ∧
    legacyStatusErasingEvalValidateSliceWindowOnBytes mutantValidateSliceWindowElemZeroInfiniteLoopBytes 16 4 0 48 = some none ∧
    legacyStatusErasingEvalValidateSliceWindowOnBytes mutantValidateSliceWindowElemZeroStuckReturnBytes 16 4 0 48 = some none ∧
    evalValidateSliceWindowOnBytes mutantValidateSliceWindowElemZeroInfiniteLoopBytes 16 4 0 48 = some .fuelExhausted ∧
    evalValidateSliceWindowOnBytes mutantValidateSliceWindowElemZeroStuckReturnBytes 16 4 0 48 = some (.malformedOrStuck (.returned (.agg0 1))) ∧
    evalValidateSliceWindowSuiteOnBytes mutantValidateSliceWindowElemZeroInfiniteLoopBytes ≠ some h11SpecValidateSliceWindowSuite ∧
    evalValidateSliceWindowSuiteOnBytes mutantValidateSliceWindowElemZeroStuckReturnBytes ≠ some h11SpecValidateSliceWindowSuite := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

#print axioms independent_holdout_packages_admitted_and_bound
#print axioms classifySliceWindowStatus_normalNone_iff
#print axioms independent_holdout_validate_slice_window_satisfies_spec
#print axioms independent_holdout_buggy_falsifies_exact_cap_boundary
#print axioms independent_holdout_buggy_bb7_localized_lt_vs_le
#print axioms independent_holdout_guarded_window_commit_satisfies_spec
#print axioms control_n4_status_erasing_projection_accepts_faulting_and_nonterminating_none_mutants_while_explicit_outcome_rejects

end AnnealResearch.IndependentSliceHoldoutH11
