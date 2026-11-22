/-!
# StableMIR (`rustc_public`) vs `rustc_middle::mir` Capture Seam Soundness

Standalone Lean v4.34.1 mechanization (core `Init` only; zero Mathlib, zero
`sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero
`native_decide`, zero `partial def`, zero `._unsafe_rec`) formalizing:

1. A concrete operational MIR capture model (`MiddleMir`, `TargetMir`,
   `CaptureBridge : MiddleMir -> Except CaptureError TargetMir`) with
   two-surface completeness (`no_silent_drop`, `fail_closed_on_unmodeled`,
   `phase_preserves_ub`).
2. An explicit capture-seam failure taxonomy (`CaptureFailureClass`) separating:
   - UB-erasing phase shift (`instance_mir` -> `Runtime(Optimized)` vs
     `Runtime(PostCleanup)`),
   - lossy metadata/field erasure (`BasicBlockData::is_cleanup`,
     `UnwindTerminateReason`, multi-label `InlineAsm` targets),
   - `opaque` debug-string loss,
   - panic/ICE traps (`unimplemented!`, `bug!`, `unreachable!`), and
   - swallowed const-evaluation errors (`ErrorHandled::Reported => return`).
3. Core theorems:
   - `failClosed_postCleanup_capture_preserves_ub_and_specs`
   - `captureBridge_sound_of_twoSurfaceCompleteness`
   - `dropping_isCleanup_or_terminateReason_breaks_unwind_determinism`
   - `postOpt_capture_unsound_for_ub_checking_under_ub_erasing_pass`
4. Constructive counterexamples:
   - `ce1_optimized_mir_capture_hides_remove_zsts_ub`
   - `ce2_dropping_is_cleanup_confuses_normal_and_cleanup_unwind`
   - `ce3_swallowing_const_eval_error_passes_broken_const_to_verifier`
   - `ce4_gvn_zero_div_hides_div_by_zero_ub`
   - `ce5_remove_place_mention_without_preserve_ub_hides_place_ub`
   - `ce6_opaque_inline_asm_under_noop_reading_hides_effect`

Scope note: This module formalizes a self-contained operational model of the
MIR capture seam rather than importing `rustc`'s Rust source or Anneal's
`Trusted.MirSemantics`. The correspondence between each modeled construct and
upstream `rust-lang/rust` code is established externally by primary-source
inspection and live `rustc` MIR dump probes in `REPORT.md`.
-/

namespace StableMirCaptureSeam

/-! ## 1. Core MIR Phases, Failure Taxonomy, and Observable Outcomes -/

/-- Subset of `rustc_middle::mir::MirPhase` relevant to capture soundness. -/
inductive MirPhase where
  | analysisPostCleanup
  | runtimeInitial
  | runtimePostCleanup (preserveUb : Bool)
  | runtimeOptimized
  deriving DecidableEq, Repr

/-- Exact upstream `rustc_middle::mir::UnwindTerminateReason`. -/
inductive UnwindTerminateReason where
  | abi
  | inCleanup
  deriving DecidableEq, Repr

/-- Exact failure taxonomy contrasting `rustc_public` capture defects against
a sound fail-closed 1:1 `Runtime(PostCleanup)` capture seam. -/
inductive CaptureFailureClass where
  | ubErasingPhaseShift
  | lossyFieldErasure
  | opaqueLoss
  | panicOrIceTrap
  | swallowedConstEvalError
  | soundFailClosedPostCleanup
  deriving DecidableEq, Repr

/-- Typed fail-closed capture errors emitted by a sound capture bridge. -/
inductive CaptureError where
  | unsupportedPhase (phase : MirPhase)
  | taintedBodyByErrors
  | constEvalReportedError
  | constEvalTooGeneric
  | unmodeledStatement
  | unmodeledTerminator
  | unmodeledInlineAsm
  | unmodeledOpaqueConstruct
  deriving DecidableEq, Repr

/-- Observable execution outcome of a MIR body. -/
inductive Outcome where
  | ret (val : Nat)
  | unwind
  | abort (reason : UnwindTerminateReason)
  | ub
  | constEvalFailure
  | asmSideEffect (tag : Nat)
  | unmodeledRuntimeTrap
  | outOfFuel
  deriving DecidableEq, Repr

/-- Standard UB-freedom specification over outcomes. -/
def ubFree (o : Outcome) : Prop :=
  o ≠ Outcome.ub

/-- Specification requiring that a program never aborts the process. -/
def noAbort (o : Outcome) : Prop :=
  ∀ r, o ≠ Outcome.abort r

/-- Specification requiring no ABI-boundary unwind abort. -/
def noAbiAbort (o : Outcome) : Prop :=
  o ≠ Outcome.abort UnwindTerminateReason.abi

/-- Specification requiring no double-panic-in-cleanup abort. -/
def noCleanupAbort (o : Outcome) : Prop :=
  o ≠ Outcome.abort UnwindTerminateReason.inCleanup

/-- Specification requiring no compile-time constant evaluation failure. -/
def noConstEvalFailure (o : Outcome) : Prop :=
  o ≠ Outcome.constEvalFailure

/-! ## 2. Source `MiddleMir` Syntax (Modeling `rustc_middle::mir`) -/

/-- Constant operands in `rustc_middle::mir::ConstOperand`. -/
inductive MiddleConst where
  | scalar (v : Nat)
  | evalErrorReported
  | evalErrorTooGeneric
  deriving DecidableEq, Repr

/-- Statements in `MiddleMir`. -/
inductive MiddleStmt where
  | assignConst (c : MiddleConst)
  | assignZeroDiv (divisorIsZero : Bool)
  | zstDeref
  | placeMention
  | storageLive
  | storageDead
  | coverage (id : Nat)
  | wrapUnsafeBinder
  | inlineAsmEffect (tag : Nat)
  | nop
  deriving DecidableEq, Repr

/-- Unwind actions in `rustc_middle::mir::UnwindAction`. -/
inductive MiddleUnwindAction where
  | continue_
  | unreachable_
  | terminate (reason : UnwindTerminateReason)
  | cleanup (bb : Nat)
  deriving DecidableEq, Repr

/-- Terminators in `rustc_middle::mir::TerminatorKind`. -/
inductive MiddleTerminator where
  | goto (target : Nat)
  | ret
  | unreachable_
  | unwindResume
  | unwindTerminate (reason : UnwindTerminateReason)
  | panickingCall (unwind : MiddleUnwindAction)
  | tailCall
  | yield_
  deriving DecidableEq, Repr

/-- A basic block in `rustc_middle::mir::BasicBlockData`, carrying `isCleanup`. -/
structure MiddleBlock where
  stmts : List MiddleStmt
  term : MiddleTerminator
  isCleanup : Bool
  deriving DecidableEq, Repr

/-- A `rustc_middle::mir::Body` with phase and error-taint metadata. -/
structure MiddleMir where
  phase : MirPhase
  taintedByErrors : Bool
  blocks : List MiddleBlock
  deriving DecidableEq, Repr

/-! ## 3. Target `TargetMir` Syntax (Verifier IR) -/

/-- Statements in `TargetMir` (plus an optional `opaqueStub` to model
`rustc_public`'s `Opaque(String)` erasure). -/
inductive TargetStmt where
  | assignScalar (v : Nat)
  | assignZeroDiv (divisorIsZero : Bool)
  | zstDeref
  | placeMention
  | storageLive
  | storageDead
  | opaqueStub (tag : Nat)
  | brokenUnevaluatedConst
  | nop
  deriving DecidableEq, Repr

/-- Unwind actions in `TargetMir`; `reason` is optional so we can model both
exact metadata-preserving seams (`some r`) and `rustc_public`'s lossy seam (`none`). -/
inductive TargetUnwindAction where
  | continue_
  | unreachable_
  | terminate (reason : Option UnwindTerminateReason)
  | cleanup (bb : Nat)
  deriving DecidableEq, Repr

/-- Terminators in `TargetMir`. -/
inductive TargetTerminator where
  | goto (target : Nat)
  | ret
  | unreachable_
  | unwindResume
  | unwindTerminate (reason : Option UnwindTerminateReason)
  | panickingCall (unwind : TargetUnwindAction)
  deriving DecidableEq, Repr

/-- A basic block in `TargetMir`; `isCleanup` is `Option Bool` so `some b`
represents an exact capture seam while `none` represents `rustc_public::mir::BasicBlock`
which drops `is_cleanup`. -/
structure TargetBlock where
  stmts : List TargetStmt
  term : TargetTerminator
  isCleanup : Option Bool
  deriving DecidableEq, Repr

/-- A captured verifier IR body. -/
structure TargetMir where
  blocks : List TargetBlock
  deriving DecidableEq, Repr

/-- A capture bridge maps `MiddleMir` to `TargetMir` or fails closed with `CaptureError`. -/
abbrev CaptureBridge := MiddleMir → Except CaptureError TargetMir

/-! ## 4. Operational Semantics (Total, Fuel-Indexed, Zero `._unsafe_rec`) -/

/-- Execution state threaded through statements and basic blocks. -/
structure ExecState where
  retVal : Nat
  ptrValid : Bool
  storageLiveFlag : Bool
  deriving DecidableEq, Repr

/-- Step result while executing statements in a single basic block. -/
inductive StmtStepResult where
  | cont (st : ExecState)
  | halt (out : Outcome)
  deriving DecidableEq, Repr

/-- Execute one `MiddleStmt`. -/
def stepMiddleStmt (s : MiddleStmt) (st : ExecState) : StmtStepResult :=
  match s with
  | .assignConst (.scalar v) => .cont { st with retVal := v }
  | .assignConst .evalErrorReported => .halt .constEvalFailure
  | .assignConst .evalErrorTooGeneric => .halt .constEvalFailure
  | .assignZeroDiv divisorIsZero =>
      if divisorIsZero then .halt .ub else .cont { st with retVal := 0 }
  | .zstDeref =>
      if st.ptrValid then .cont st else .halt .ub
  | .placeMention =>
      if st.ptrValid then .cont st else .halt .ub
  | .storageLive =>
      if st.storageLiveFlag then .halt .ub else .cont { st with storageLiveFlag := true }
  | .storageDead =>
      if st.storageLiveFlag then .cont { st with storageLiveFlag := false } else .halt .ub
  | .coverage _ => .halt .unmodeledRuntimeTrap
  | .wrapUnsafeBinder => .halt .unmodeledRuntimeTrap
  | .inlineAsmEffect tag => .halt (.asmSideEffect tag)
  | .nop => .cont st

/-- Execute a list of `MiddleStmt`s via `List.foldl` (zero `._unsafe_rec`). -/
def runMiddleStmts (stmts : List MiddleStmt) (st : ExecState) : StmtStepResult :=
  stmts.foldl
    (fun acc stmt =>
      match acc with
      | .halt o => .halt o
      | .cont st' => stepMiddleStmt stmt st')
    (.cont st)

/-- Next-step outcome after a terminator. -/
inductive TermStepResult where
  | jump (bb : Nat) (st : ExecState)
  | halt (out : Outcome)
  deriving DecidableEq, Repr

/-- Execute a `MiddleTerminator` in a block whose cleanup marker is `inCleanup`.
Crucially, in Rust MIR unwinding, a panic occurring inside a cleanup block
(`isCleanup = true`) whose unwind action is `Continue` triggers a double-panic
process abort (`Outcome.abort .inCleanup`), whereas in a normal block
(`isCleanup = false`) it propagates unwinding (`Outcome.unwind`). -/
def stepMiddleTerm (inCleanup : Bool) (term : MiddleTerminator) (st : ExecState) : TermStepResult :=
  match term with
  | .goto target => .jump target st
  | .ret => .halt (.ret st.retVal)
  | .unreachable_ => .halt .ub
  | .unwindResume =>
      if inCleanup then .halt .unwind else .halt .ub
  | .unwindTerminate r => .halt (.abort r)
  | .panickingCall unwind =>
      match unwind with
      | .continue_ =>
          if inCleanup then .halt (.abort .inCleanup) else .halt .unwind
      | .unreachable_ => .halt .ub
      | .terminate r => .halt (.abort r)
      | .cleanup target => .jump target st
  | .tailCall => .halt .unmodeledRuntimeTrap
  | .yield_ => .halt .unmodeledRuntimeTrap

/-- Lookup block `idx` in a list using `List.get?`-equivalent `blocks[idx]?`. -/
def getMiddleBlock? (blocks : List MiddleBlock) (idx : Nat) : Option MiddleBlock :=
  blocks[idx]?

/-- Execute a single basic block of `MiddleMir` starting at `(bb, st)`. -/
def stepMiddleBlock (m : MiddleMir) (bb : Nat) (st : ExecState) : TermStepResult :=
  match getMiddleBlock? m.blocks bb with
  | none => .halt .ub
  | some blk =>
      match runMiddleStmts blk.stmts st with
      | .halt o => .halt o
      | .cont st' => stepMiddleTerm blk.isCleanup blk.term st'

/-- Fuel-bounded execution of `MiddleMir` using `Nat.rec` (zero `._unsafe_rec`). -/
def evalMiddleAt (fuel : Nat) (m : MiddleMir) (bb : Nat) (st : ExecState) : Outcome :=
  Nat.rec
    (motive := fun _ => Nat → ExecState → Outcome)
    (fun _ _ => .outOfFuel)
    (fun _ ih curBb curSt =>
      match stepMiddleBlock m curBb curSt with
      | .halt o => o
      | .jump nextBb nextSt => ih nextBb nextSt)
    fuel bb st

/-- Entry-point execution of `MiddleMir` at block `0`.
A body marked `taintedByErrors = true` fails compilation/evaluation with
`Outcome.constEvalFailure` rather than executing as a valid Rust program. -/
def evalMiddle (fuel : Nat) (m : MiddleMir) (st : ExecState) : Outcome :=
  if m.taintedByErrors then .constEvalFailure else evalMiddleAt fuel m 0 st

/-- Configurable interpretation of lossy `TargetMir` artifacts when a non-exact
bridge erases metadata or stringifies constructs into `opaqueStub`. -/
structure TargetSemConfig where
  defaultCleanup : Bool
  defaultTerminateReason : UnwindTerminateReason
  opaqueIsNoop : Bool
  brokenConstAsZero : Bool
  deriving DecidableEq, Repr

/-- Exact verifier semantics configuration (used when `TargetMir` retains full
metadata and never contains `opaqueStub` or `brokenUnevaluatedConst`). -/
def exactTargetConfig : TargetSemConfig :=
  { defaultCleanup := false
    defaultTerminateReason := .abi
    opaqueIsNoop := true
    brokenConstAsZero := true }

/-- Execute one `TargetStmt` under `cfg`. -/
def stepTargetStmt (cfg : TargetSemConfig) (s : TargetStmt) (st : ExecState) : StmtStepResult :=
  match s with
  | .assignScalar v => .cont { st with retVal := v }
  | .assignZeroDiv divisorIsZero =>
      if divisorIsZero then .halt .ub else .cont { st with retVal := 0 }
  | .zstDeref =>
      if st.ptrValid then .cont st else .halt .ub
  | .placeMention =>
      if st.ptrValid then .cont st else .halt .ub
  | .storageLive =>
      if st.storageLiveFlag then .halt .ub else .cont { st with storageLiveFlag := true }
  | .storageDead =>
      if st.storageLiveFlag then .cont { st with storageLiveFlag := false } else .halt .ub
  | .opaqueStub tag =>
      if cfg.opaqueIsNoop then .cont st else .halt (.asmSideEffect tag)
  | .brokenUnevaluatedConst =>
      if cfg.brokenConstAsZero then .cont { st with retVal := 0 } else .halt .constEvalFailure
  | .nop => .cont st

/-- Execute a list of `TargetStmt`s via `List.foldl` (zero `._unsafe_rec`). -/
def runTargetStmts (cfg : TargetSemConfig) (stmts : List TargetStmt) (st : ExecState) : StmtStepResult :=
  stmts.foldl
    (fun acc stmt =>
      match acc with
      | .halt o => .halt o
      | .cont st' => stepTargetStmt cfg stmt st')
    (.cont st)

/-- Execute a `TargetTerminator` under `cfg`. -/
def stepTargetTerm (cfg : TargetSemConfig) (inCleanupOpt : Option Bool) (term : TargetTerminator)
    (st : ExecState) : TermStepResult :=
  let inCleanup := inCleanupOpt.getD cfg.defaultCleanup
  match term with
  | .goto target => .jump target st
  | .ret => .halt (.ret st.retVal)
  | .unreachable_ => .halt .ub
  | .unwindResume =>
      if inCleanup then .halt .unwind else .halt .ub
  | .unwindTerminate rOpt =>
      .halt (.abort (rOpt.getD cfg.defaultTerminateReason))
  | .panickingCall unwind =>
      match unwind with
      | .continue_ =>
          if inCleanup then .halt (.abort .inCleanup) else .halt .unwind
      | .unreachable_ => .halt .ub
      | .terminate rOpt =>
          .halt (.abort (rOpt.getD cfg.defaultTerminateReason))
      | .cleanup target => .jump target st

/-- Lookup block `idx` in `TargetMir`. -/
def getTargetBlock? (blocks : List TargetBlock) (idx : Nat) : Option TargetBlock :=
  blocks[idx]?

/-- Execute a single basic block of `TargetMir`. -/
def stepTargetBlock (cfg : TargetSemConfig) (t : TargetMir) (bb : Nat) (st : ExecState) : TermStepResult :=
  match getTargetBlock? t.blocks bb with
  | none => .halt .ub
  | some blk =>
      match runTargetStmts cfg blk.stmts st with
      | .halt o => .halt o
      | .cont st' => stepTargetTerm cfg blk.isCleanup blk.term st'

/-- Fuel-bounded execution of `TargetMir` using `Nat.rec` (zero `._unsafe_rec`). -/
def evalTargetAt (cfg : TargetSemConfig) (fuel : Nat) (t : TargetMir) (bb : Nat) (st : ExecState) : Outcome :=
  Nat.rec
    (motive := fun _ => Nat → ExecState → Outcome)
    (fun _ _ => .outOfFuel)
    (fun _ ih curBb curSt =>
      match stepTargetBlock cfg t curBb curSt with
      | .halt o => o
      | .jump nextBb nextSt => ih nextBb nextSt)
    fuel bb st

/-- Entry-point execution of `TargetMir` at block `0`. -/
def evalTarget (cfg : TargetSemConfig) (fuel : Nat) (t : TargetMir) (st : ExecState) : Outcome :=
  evalTargetAt cfg fuel t 0 st

/-! ## 5. Helper: Monadic `List.map` over `Except` via `List.foldr` (Zero `._unsafe_rec`) -/

/-- Traverse a list with a fallible function, failing closed on the first error. -/
def mapExcept {α β ε : Type} (f : α → Except ε β) (xs : List α) : Except ε (List β) :=
  xs.foldr
    (fun a ih =>
      match f a with
      | Except.error e => Except.error e
      | Except.ok b =>
          match ih with
          | Except.error e => Except.error e
          | Except.ok bs => Except.ok (b :: bs))
    (Except.ok [])

theorem mapExcept_cons {α β ε : Type} (f : α → Except ε β) (a : α) (as : List α) :
    mapExcept f (a :: as) =
      match f a with
      | Except.error e => Except.error e
      | Except.ok b =>
          match mapExcept f as with
          | Except.error e => Except.error e
          | Except.ok bs => Except.ok (b :: bs) := rfl

theorem mapExcept_length {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), mapExcept f xs = Except.ok ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases h
      rfl
  | cons a as ih =>
      intro ys h
      change (match f a with
        | Except.error e => Except.error e
        | Except.ok b => match mapExcept f as with
          | Except.error e => Except.error e
          | Except.ok bs => Except.ok (b :: bs)) = Except.ok ys at h
      cases hfa : f a with
      | error e => rw [hfa] at h; cases h
      | ok b =>
          rw [hfa] at h
          cases hrest : mapExcept f as with
          | error e => rw [hrest] at h; cases h
          | ok bs =>
              rw [hrest] at h
              cases h
              exact congrArg Nat.succ (ih bs hrest)

theorem mapExcept_getElem? {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), mapExcept f xs = Except.ok ys →
      ∀ (i : Nat),
        (xs[i]? = none ∧ ys[i]? = none) ∨
        (∃ a b, xs[i]? = some a ∧ ys[i]? = some b ∧ f a = Except.ok b) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h i
      cases h
      left
      exact ⟨rfl, rfl⟩
  | cons a as ih =>
      intro ys h i
      change (match f a with
        | Except.error e => Except.error e
        | Except.ok b => match mapExcept f as with
          | Except.error e => Except.error e
          | Except.ok bs => Except.ok (b :: bs)) = Except.ok ys at h
      cases hfa : f a with
      | error e => rw [hfa] at h; cases h
      | ok b =>
          rw [hfa] at h
          cases hrest : mapExcept f as with
          | error e => rw [hrest] at h; cases h
          | ok bs =>
              rw [hrest] at h
              cases h
              cases i with
              | zero =>
                  right
                  exact ⟨a, b, rfl, rfl, hfa⟩
              | succ j =>
                  exact ih bs hrest j

/-! ## 6. Modeled Fragment, Two-Surface Completeness, and Capture Bridges -/

/-- Predicate characterizing whether a `MiddleStmt` lies in the modeled fragment. -/
def isModeledStmt : MiddleStmt → Bool
  | .assignConst (.scalar _) => true
  | .assignConst .evalErrorReported => false
  | .assignConst .evalErrorTooGeneric => false
  | .assignZeroDiv _ => true
  | .zstDeref => true
  | .placeMention => true
  | .storageLive => true
  | .storageDead => true
  | .coverage _ => false
  | .wrapUnsafeBinder => false
  | .inlineAsmEffect _ => false
  | .nop => true

/-- Predicate characterizing whether a `MiddleTerminator` lies in the modeled fragment. -/
def isModeledTerm : MiddleTerminator → Bool
  | .goto _ => true
  | .ret => true
  | .unreachable_ => true
  | .unwindResume => true
  | .unwindTerminate _ => true
  | .panickingCall _ => true
  | .tailCall => false
  | .yield_ => false

/-- Predicate characterizing whether a `MiddleBlock` lies in the modeled fragment. -/
def isModeledBlock (blk : MiddleBlock) : Bool :=
  blk.stmts.all isModeledStmt && isModeledTerm blk.term

/-- Predicate characterizing whether a `MiddleMir` body is an admissible,
untainted, UB-preserving `Runtime(PostCleanup)` body in the modeled fragment. -/
def isModeledPostCleanupBody (m : MiddleMir) : Bool :=
  match m.phase, m.taintedByErrors with
  | .runtimePostCleanup true, false => m.blocks.all isModeledBlock
  | _, _ => false

/-- Unwind-action translation preserving `UnwindTerminateReason` exactly. -/
def translateUnwindExact : MiddleUnwindAction → TargetUnwindAction
  | .continue_ => .continue_
  | .unreachable_ => .unreachable_
  | .terminate r => .terminate (some r)
  | .cleanup bb => .cleanup bb

/-- Fail-closed statement translation (rejects const-eval errors, `Coverage`,
`WrapUnsafeBinder`, and `InlineAsm`). -/
def translateStmtFailClosed : MiddleStmt → Except CaptureError TargetStmt
  | .assignConst (.scalar v) => .ok (.assignScalar v)
  | .assignConst .evalErrorReported => .error .constEvalReportedError
  | .assignConst .evalErrorTooGeneric => .error .constEvalTooGeneric
  | .assignZeroDiv z => .ok (.assignZeroDiv z)
  | .zstDeref => .ok .zstDeref
  | .placeMention => .ok .placeMention
  | .storageLive => .ok .storageLive
  | .storageDead => .ok .storageDead
  | .coverage _ => .error .unmodeledOpaqueConstruct
  | .wrapUnsafeBinder => .error .unmodeledStatement
  | .inlineAsmEffect _ => .error .unmodeledInlineAsm
  | .nop => .ok .nop

/-- Fail-closed terminator translation (rejects `TailCall` and `Yield`, preserves
`UnwindTerminateReason` on both `UnwindTerminate` and `UnwindAction::Terminate`). -/
def translateTermFailClosed : MiddleTerminator → Except CaptureError TargetTerminator
  | .goto target => .ok (.goto target)
  | .ret => .ok .ret
  | .unreachable_ => .ok .unreachable_
  | .unwindResume => .ok .unwindResume
  | .unwindTerminate r => .ok (.unwindTerminate (some r))
  | .panickingCall u => .ok (.panickingCall (translateUnwindExact u))
  | .tailCall => .error .unmodeledTerminator
  | .yield_ => .error .unmodeledTerminator

/-- Fail-closed block translation preserving `isCleanup` exactly as `some blk.isCleanup`. -/
def translateBlockFailClosed (blk : MiddleBlock) : Except CaptureError TargetBlock :=
  match mapExcept translateStmtFailClosed blk.stmts with
  | .error e => .error e
  | .ok stmts =>
      match translateTermFailClosed blk.term with
      | .error e => .error e
      | .ok term => .ok { stmts := stmts, term := term, isCleanup := some blk.isCleanup }

/-- Sound fail-closed 1:1 `Runtime(PostCleanup)` (`-Zmir-preserve-ub`) capture bridge. -/
def failClosedPostCleanupBridge : CaptureBridge := fun m =>
  match m.phase with
  | .runtimePostCleanup true =>
      if m.taintedByErrors then
        .error .taintedBodyByErrors
      else
        match mapExcept translateBlockFailClosed m.blocks with
        | .error e => .error e
        | .ok blocks => .ok { blocks := blocks }
  | other => .error (.unsupportedPhase other)

/-- Lossy bridge modeling `rustc_public::mir::BasicBlock` dropping `is_cleanup`
(`compiler/rustc_public/src/unstable/convert/stable/mir.rs:29-36`). -/
def translateBlockDropCleanup (blk : MiddleBlock) : Except CaptureError TargetBlock :=
  match mapExcept translateStmtFailClosed blk.stmts with
  | .error e => .error e
  | .ok stmts =>
      match translateTermFailClosed blk.term with
      | .error e => .error e
      | .ok term => .ok { stmts := stmts, term := term, isCleanup := none }

def lossyDropCleanupBridge : CaptureBridge := fun m =>
  if m.taintedByErrors then
    .error .taintedBodyByErrors
  else
    match mapExcept translateBlockDropCleanup m.blocks with
    | .error e => .error e
    | .ok blocks => .ok { blocks := blocks }

/-- Lossy unwind translation modeling `rustc_public` dropping `UnwindTerminateReason`
(`compiler/rustc_public/src/unstable/convert/stable/mir.rs:507,749`). -/
def translateUnwindDropReason : MiddleUnwindAction → TargetUnwindAction
  | .continue_ => .continue_
  | .unreachable_ => .unreachable_
  | .terminate _ => .terminate none
  | .cleanup bb => .cleanup bb

def translateTermDropReason : MiddleTerminator → Except CaptureError TargetTerminator
  | .goto target => .ok (.goto target)
  | .ret => .ok .ret
  | .unreachable_ => .ok .unreachable_
  | .unwindResume => .ok .unwindResume
  | .unwindTerminate _ => .ok (.unwindTerminate none)
  | .panickingCall u => .ok (.panickingCall (translateUnwindDropReason u))
  | .tailCall => .error .unmodeledTerminator
  | .yield_ => .error .unmodeledTerminator

def translateBlockDropReason (blk : MiddleBlock) : Except CaptureError TargetBlock :=
  match mapExcept translateStmtFailClosed blk.stmts with
  | .error e => .error e
  | .ok stmts =>
      match translateTermDropReason blk.term with
      | .error e => .error e
      | .ok term => .ok { stmts := stmts, term := term, isCleanup := some blk.isCleanup }

def lossyDropTerminateReasonBridge : CaptureBridge := fun m =>
  if m.taintedByErrors then
    .error .taintedBodyByErrors
  else
    match mapExcept translateBlockDropReason m.blocks with
    | .error e => .error e
    | .ok blocks => .ok { blocks := blocks }

/-- Swallowing const-eval error bridge modeling `BodyBuilder::visit_const_operand`
(`compiler/rustc_public_bridge/src/builder.rs:63`:
`Err(mir::interpret::ErrorHandled::Reported(..)) => return`). -/
def translateStmtSwallowConstErr : MiddleStmt → Except CaptureError TargetStmt
  | .assignConst .evalErrorReported => .ok .brokenUnevaluatedConst
  | other => translateStmtFailClosed other

def translateBlockSwallowConstErr (blk : MiddleBlock) : Except CaptureError TargetBlock :=
  match mapExcept translateStmtSwallowConstErr blk.stmts with
  | .error e => .error e
  | .ok stmts =>
      match translateTermFailClosed blk.term with
      | .error e => .error e
      | .ok term => .ok { stmts := stmts, term := term, isCleanup := some blk.isCleanup }

def swallowingConstErrorBridge : CaptureBridge := fun m =>
  if m.taintedByErrors then
    .error .taintedBodyByErrors
  else
    match mapExcept translateBlockSwallowConstErr m.blocks with
    | .error e => .error e
    | .ok blocks => .ok { blocks := blocks }

/-- Stringifying `opaque(...)` bridge modeling `rustc_public` lowering
`InlineAsmOperand` / `Coverage` via `opaque(format!("{:?}"))`. -/
def translateStmtOpaqueAsm : MiddleStmt → Except CaptureError TargetStmt
  | .inlineAsmEffect tag => .ok (.opaqueStub tag)
  | other => translateStmtFailClosed other

def translateBlockOpaqueAsm (blk : MiddleBlock) : Except CaptureError TargetBlock :=
  match mapExcept translateStmtOpaqueAsm blk.stmts with
  | .error e => .error e
  | .ok stmts =>
      match translateTermFailClosed blk.term with
      | .error e => .error e
      | .ok term => .ok { stmts := stmts, term := term, isCleanup := some blk.isCleanup }

def opaqueStringifyAsmBridge : CaptureBridge := fun m =>
  if m.taintedByErrors then
    .error .taintedBodyByErrors
  else
    match mapExcept translateBlockOpaqueAsm m.blocks with
    | .error e => .error e
    | .ok blocks => .ok { blocks := blocks }

/-- A post-optimization capture seam runs a MIR optimization pass `optPass`
before invoking the capture bridge (modeling `tcx.instance_mir` -> `optimized_mir`). -/
def postOptCapture (optPass : MiddleMir → MiddleMir) (bridge : CaptureBridge) : CaptureBridge :=
  fun m => bridge (optPass m)

/-! ## 7. MIR Optimization Passes Modeling Upstream UB-Erasing Transforms -/

/-- Models `compiler/rustc_mir_transform/src/remove_zsts.rs:118-145`:
replaces ZST place accesses with `Nop` and transitions to `Runtime(Optimized)`. -/
def removeZstsStmt : MiddleStmt → MiddleStmt
  | .zstDeref => .nop
  | s => s

def runRemoveZsts (m : MiddleMir) : MiddleMir :=
  { phase := .runtimeOptimized
    taintedByErrors := m.taintedByErrors
    blocks := m.blocks.map (fun b => { b with stmts := b.stmts.map removeZstsStmt }) }

/-- Models `compiler/rustc_mir_transform/src/gvn.rs:1508-1518`:
folds `0 / x` to constant `0` regardless of whether `x == 0`, erasing division-by-zero UB. -/
def gvnZeroDivStmt : MiddleStmt → MiddleStmt
  | .assignZeroDiv _ => .assignConst (.scalar 0)
  | s => s

def runGvnZeroDiv (m : MiddleMir) : MiddleMir :=
  { phase := .runtimeOptimized
    taintedByErrors := m.taintedByErrors
    blocks := m.blocks.map (fun b => { b with stmts := b.stmts.map gvnZeroDivStmt }) }

/-- Models `compiler/rustc_mir_transform/src/remove_place_mention.rs:11-24`:
deletes `PlaceMention` during `run_runtime_cleanup_passes` whenever
`-Zmir-preserve-ub` is `false`. -/
def removePlaceMentionStmt : MiddleStmt → MiddleStmt
  | .placeMention => .nop
  | s => s

def runRemovePlaceMention (preserveUb : Bool) (m : MiddleMir) : MiddleMir :=
  if preserveUb then
    { m with phase := .runtimePostCleanup true }
  else
    { phase := .runtimePostCleanup false
      taintedByErrors := m.taintedByErrors
      blocks := m.blocks.map (fun b => { b with stmts := b.stmts.map removePlaceMentionStmt }) }

/-- A bridge that accepts `Runtime(Optimized)` directly (as `rustc_public` does),
even when exact on every statement/terminator/metadata field. -/
def acceptOptimizedExactBridge : CaptureBridge := fun m =>
  if m.taintedByErrors then
    .error .taintedBodyByErrors
  else
    match mapExcept translateBlockFailClosed m.blocks with
    | .error e => .error e
    | .ok blocks => .ok { blocks := blocks }

/-! ## 8. Two-Surface Completeness Predicates -/

/-- Surface 1 (`no_silent_drop`): Every successfully captured `TargetMir` retains
explicit `isCleanup` and `UnwindTerminateReason` metadata on all blocks and
terminators and preserves exact step semantics for every `TargetSemConfig`. -/
def no_silent_drop (bridge : CaptureBridge) : Prop :=
  ∀ m t, bridge m = .ok t →
    ∀ cfg fuel st, evalTarget cfg fuel t st = evalMiddle fuel m st

/-- Surface 2 (`fail_closed_on_unmodeled`): Any `MiddleMir` body outside the
modeled `Runtime(PostCleanup)` (`-Zmir-preserve-ub`, untainted) fragment is
rejected with `Except.error`. -/
def fail_closed_on_unmodeled (bridge : CaptureBridge) : Prop :=
  ∀ m, isModeledPostCleanupBody m = false → ∃ e, bridge m = .error e

/-- Pre-capture phase-preservation obligation (`phase_preserves_ub`): Every pass `optPass`
applied prior to capture preserves all behaviors (in particular UB) of every
input `MiddleMir`. -/
def phase_preserves_ub (optPass : MiddleMir → MiddleMir) : Prop :=
  ∀ fuel m st, evalMiddle fuel m st = .ub → evalMiddle fuel (optPass m) st = .ub

/-- Stronger full-behavior preservation of a pre-capture pass. -/
def phase_preserves_all_outcomes (optPass : MiddleMir → MiddleMir) : Prop :=
  ∀ fuel m st, evalMiddle fuel (optPass m) st = evalMiddle fuel m st

/-- Verifier soundness for a capture bridge against arbitrary outcome specs. -/
def SoundForSpecs (cfg : TargetSemConfig) (bridge : CaptureBridge) : Prop :=
  ∀ m t fuel st (spec : Outcome → Prop),
    bridge m = .ok t →
    spec (evalTarget cfg fuel t st) →
    spec (evalMiddle fuel m st)

/-- Verifier soundness specifically for UB-freedom checking. -/
def SoundForUbChecking (cfg : TargetSemConfig) (bridge : CaptureBridge) : Prop :=
  ∀ m t fuel st,
    bridge m = .ok t →
    ubFree (evalTarget cfg fuel t st) →
    ubFree (evalMiddle fuel m st)

/-! ## 9. Theorem 1: Soundness of Fail-Closed 1:1 `PostCleanup` Capture -/

theorem stepStmt_failClosed_exact (cfg : TargetSemConfig) (ms : MiddleStmt) (ts : TargetStmt)
    (st : ExecState) (h : translateStmtFailClosed ms = .ok ts) :
    stepTargetStmt cfg ts st = stepMiddleStmt ms st := by
  cases ms with
  | assignConst c =>
      cases c with
      | scalar v => cases h; rfl
      | evalErrorReported => cases h
      | evalErrorTooGeneric => cases h
  | assignZeroDiv z => cases h; rfl
  | zstDeref => cases h; rfl
  | placeMention => cases h; rfl
  | storageLive => cases h; rfl
  | storageDead => cases h; rfl
  | coverage _ => cases h
  | wrapUnsafeBinder => cases h
  | inlineAsmEffect _ => cases h
  | nop => cases h; rfl

theorem runStmts_failClosed_exact_acc (cfg : TargetSemConfig) :
    ∀ (ms : List MiddleStmt) (ts : List TargetStmt),
      mapExcept translateStmtFailClosed ms = .ok ts →
      ∀ (acc : StmtStepResult),
        ts.foldl
          (fun a s => match a with | .halt o => .halt o | .cont st' => stepTargetStmt cfg s st')
          acc
        =
        ms.foldl
          (fun a s => match a with | .halt o => .halt o | .cont st' => stepMiddleStmt s st')
          acc := by
  intro ms
  induction ms with
  | nil =>
      intro ts h acc
      cases h
      rfl
  | cons m rest ih =>
      intro ts h acc
      rw [mapExcept_cons] at h
      cases hm : translateStmtFailClosed m with
      | error e => rw [hm] at h; cases h
      | ok b =>
          rw [hm] at h
          cases hr : mapExcept translateStmtFailClosed rest with
          | error e => rw [hr] at h; cases h
          | ok bs =>
              rw [hr] at h
              cases h
              cases acc with
              | halt o =>
                  exact ih bs hr (.halt o)
              | cont st' =>
                  change List.foldl _ (stepTargetStmt cfg b st') bs =
                         List.foldl _ (stepMiddleStmt m st') rest
                  rw [stepStmt_failClosed_exact cfg m b st' hm]
                  exact ih bs hr (stepMiddleStmt m st')

theorem runStmts_failClosed_exact (cfg : TargetSemConfig) (ms : List MiddleStmt)
    (ts : List TargetStmt) (st : ExecState)
    (h : mapExcept translateStmtFailClosed ms = .ok ts) :
    runTargetStmts cfg ts st = runMiddleStmts ms st :=
  runStmts_failClosed_exact_acc cfg ms ts h (.cont st)

theorem stepTerm_failClosed_exact (cfg : TargetSemConfig) (inCleanup : Bool)
    (mt : MiddleTerminator) (tt : TargetTerminator) (st : ExecState)
    (h : translateTermFailClosed mt = .ok tt) :
    stepTargetTerm cfg (some inCleanup) tt st = stepMiddleTerm inCleanup mt st := by
  cases mt with
  | goto target => cases h; rfl
  | ret => cases h; rfl
  | unreachable_ => cases h; rfl
  | unwindResume => cases h; rfl
  | unwindTerminate r => cases h; rfl
  | panickingCall u =>
      cases h
      cases u <;> rfl
  | tailCall => cases h
  | yield_ => cases h

theorem stepBlock_failClosed_exact (cfg : TargetSemConfig)
    (m : MiddleMir) (t : TargetMir) (bb : Nat) (st : ExecState)
    (hBlocks : mapExcept translateBlockFailClosed m.blocks = .ok t.blocks) :
    stepTargetBlock cfg t bb st = stepMiddleBlock m bb st := by
  unfold stepTargetBlock stepMiddleBlock getTargetBlock? getMiddleBlock?
  cases mapExcept_getElem? translateBlockFailClosed m.blocks t.blocks hBlocks bb with
  | inl hNone =>
      rw [hNone.1, hNone.2]
  | inr hSome =>
      rcases hSome with ⟨mb, tb, hm, ht, htr⟩
      rw [hm, ht]
      unfold translateBlockFailClosed at htr
      cases hst : mapExcept translateStmtFailClosed mb.stmts with
      | error e => rw [hst] at htr; cases htr
      | ok tstmts =>
          rw [hst] at htr
          cases htm : translateTermFailClosed mb.term with
          | error e => rw [htm] at htr; cases htr
          | ok tterm =>
              rw [htm] at htr
              cases htr
              dsimp only
              rw [runStmts_failClosed_exact cfg mb.stmts tstmts st hst]
              cases runMiddleStmts mb.stmts st with
              | halt o => rfl
              | cont st' => exact stepTerm_failClosed_exact cfg mb.isCleanup mb.term tterm st' htm

theorem evalAt_failClosed_exact (cfg : TargetSemConfig)
    (m : MiddleMir) (t : TargetMir)
    (hBlocks : mapExcept translateBlockFailClosed m.blocks = .ok t.blocks) :
    ∀ (fuel : Nat) (bb : Nat) (st : ExecState),
      evalTargetAt cfg fuel t bb st = evalMiddleAt fuel m bb st := by
  intro fuel
  induction fuel with
  | zero =>
      intro bb st
      rfl
  | succ n ih =>
      intro bb st
      change (match stepTargetBlock cfg t bb st with
        | .halt o => o
        | .jump nextBb nextSt => evalTargetAt cfg n t nextBb nextSt) =
        (match stepMiddleBlock m bb st with
        | .halt o => o
        | .jump nextBb nextSt => evalMiddleAt n m nextBb nextSt)
      rw [stepBlock_failClosed_exact cfg m t bb st hBlocks]
      cases stepMiddleBlock m bb st with
      | halt o => rfl
      | jump nextBb nextSt => exact ih nextBb nextSt

/-- Main Theorem 1: Soundness of Fail-Closed 1:1 `Runtime(PostCleanup)` Capture.
Whenever `failClosedPostCleanupBridge` accepts a `MiddleMir` body `m` producing `t`,
target execution matches source execution identically under EVERY `TargetSemConfig`,
preserving UB exact equivalence and transferring every behavioral specification `spec`. -/
theorem failClosed_postCleanup_capture_preserves_ub_and_specs
    (m : MiddleMir) (t : TargetMir) (cfg : TargetSemConfig) (fuel : Nat) (st : ExecState)
    (hCap : failClosedPostCleanupBridge m = .ok t) :
    (evalTarget cfg fuel t st = evalMiddle fuel m st) ∧
    (evalMiddle fuel m st = .ub ↔ evalTarget cfg fuel t st = .ub) ∧
    (∀ spec : Outcome → Prop, spec (evalTarget cfg fuel t st) → spec (evalMiddle fuel m st)) := by
  unfold failClosedPostCleanupBridge at hCap
  cases hPhase : m.phase with
  | analysisPostCleanup => rw [hPhase] at hCap; cases hCap
  | runtimeInitial => rw [hPhase] at hCap; cases hCap
  | runtimeOptimized => rw [hPhase] at hCap; cases hCap
  | runtimePostCleanup pres =>
      rw [hPhase] at hCap
      cases pres with
      | false => cases hCap
      | true =>
          cases hTaint : m.taintedByErrors with
          | true => rw [hTaint] at hCap; cases hCap
          | false =>
              rw [hTaint] at hCap
              cases hBlks : mapExcept translateBlockFailClosed m.blocks with
              | error e => rw [hBlks] at hCap; cases hCap
              | ok tblks =>
                  rw [hBlks] at hCap
                  cases hCap
                  have hEq : evalTarget cfg fuel { blocks := tblks } st = evalMiddle fuel m st := by
                    unfold evalTarget evalMiddle
                    rw [hTaint]
                    exact evalAt_failClosed_exact cfg m { blocks := tblks } hBlks fuel 0 st
                  refine ⟨hEq, ?_, ?_⟩
                  · rw [hEq]
                  · intro spec hSpec
                    rw [← hEq]
                    exact hSpec

/-- Helper lemmas establishing `fail_closed_on_unmodeled` for `failClosedPostCleanupBridge`. -/
theorem translateStmt_err_of_unmodeled (s : MiddleStmt) (h : isModeledStmt s = false) :
    ∃ e, translateStmtFailClosed s = .error e := by
  cases s with
  | assignConst c =>
      cases c with
      | scalar _ => cases h
      | evalErrorReported => exact ⟨.constEvalReportedError, rfl⟩
      | evalErrorTooGeneric => exact ⟨.constEvalTooGeneric, rfl⟩
  | assignZeroDiv _ => cases h
  | zstDeref => cases h
  | placeMention => cases h
  | storageLive => cases h
  | storageDead => cases h
  | coverage _ => exact ⟨.unmodeledOpaqueConstruct, rfl⟩
  | wrapUnsafeBinder => exact ⟨.unmodeledStatement, rfl⟩
  | inlineAsmEffect _ => exact ⟨.unmodeledInlineAsm, rfl⟩
  | nop => cases h

theorem mapExcept_err_of_all_false {α β ε : Type} (f : α → Except ε β) (p : α → Bool)
    (hFail : ∀ a, p a = false → ∃ e, f a = .error e) :
    ∀ (xs : List α), xs.all p = false → ∃ e, mapExcept f xs = .error e := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons a rest ih =>
      intro h
      change (p a && rest.all p) = false at h
      cases hpa : p a with
      | false =>
          rcases hFail a hpa with ⟨e, he⟩
          refine ⟨e, ?_⟩
          change (match f a with
            | Except.error e => Except.error e
            | Except.ok b => match mapExcept f rest with
              | Except.error e => Except.error e
              | Except.ok bs => Except.ok (b :: bs)) = Except.error e
          rw [he]
      | true =>
          rw [hpa] at h
          rcases ih h with ⟨e, he⟩
          cases hfa : f a with
          | error e' =>
              refine ⟨e', ?_⟩
              change (match f a with
                | Except.error e => Except.error e
                | Except.ok b => match mapExcept f rest with
                  | Except.error e => Except.error e
                  | Except.ok bs => Except.ok (b :: bs)) = Except.error e'
              rw [hfa]
          | ok b =>
              refine ⟨e, ?_⟩
              change (match f a with
                | Except.error e => Except.error e
                | Except.ok b => match mapExcept f rest with
                  | Except.error e => Except.error e
                  | Except.ok bs => Except.ok (b :: bs)) = Except.error e
              rw [hfa, he]

theorem translateTerm_err_of_unmodeled (t : MiddleTerminator) (h : isModeledTerm t = false) :
    ∃ e, translateTermFailClosed t = .error e := by
  cases t with
  | goto _ => cases h
  | ret => cases h
  | unreachable_ => cases h
  | unwindResume => cases h
  | unwindTerminate _ => cases h
  | panickingCall _ => cases h
  | tailCall => exact ⟨.unmodeledTerminator, rfl⟩
  | yield_ => exact ⟨.unmodeledTerminator, rfl⟩

theorem translateBlock_err_of_unmodeled (b : MiddleBlock) (h : isModeledBlock b = false) :
    ∃ e, translateBlockFailClosed b = .error e := by
  unfold isModeledBlock at h
  unfold translateBlockFailClosed
  cases hs : b.stmts.all isModeledStmt with
  | false =>
      rcases mapExcept_err_of_all_false translateStmtFailClosed isModeledStmt
        translateStmt_err_of_unmodeled b.stmts hs with ⟨e, he⟩
      rw [he]
      exact ⟨e, rfl⟩
  | true =>
      rw [hs] at h
      cases hst : mapExcept translateStmtFailClosed b.stmts with
      | error e => exact ⟨e, rfl⟩
      | ok _ =>
          rcases translateTerm_err_of_unmodeled b.term h with ⟨e, he⟩
          rw [he]
          exact ⟨e, rfl⟩

/-- `failClosedPostCleanupBridge` satisfies Surface 1 (`no_silent_drop`),
Surface 2 (`fail_closed_on_unmodeled`), and `phase_preserves_ub` for the
identity `PostCleanup` pass. -/
theorem failClosedPostCleanupBridge_twoSurfaceComplete :
    no_silent_drop failClosedPostCleanupBridge ∧
    fail_closed_on_unmodeled failClosedPostCleanupBridge ∧
    phase_preserves_ub (fun m => m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m t hCap cfg fuel st
    exact (failClosed_postCleanup_capture_preserves_ub_and_specs m t cfg fuel st hCap).1
  · intro m hUnmod
    unfold isModeledPostCleanupBody at hUnmod
    unfold failClosedPostCleanupBridge
    cases hPhase : m.phase with
    | analysisPostCleanup => exact ⟨.unsupportedPhase .analysisPostCleanup, rfl⟩
    | runtimeInitial => exact ⟨.unsupportedPhase .runtimeInitial, rfl⟩
    | runtimeOptimized => exact ⟨.unsupportedPhase .runtimeOptimized, rfl⟩
    | runtimePostCleanup pres =>
        rw [hPhase] at hUnmod
        cases pres with
        | false => exact ⟨.unsupportedPhase (.runtimePostCleanup false), rfl⟩
        | true =>
            cases hTaint : m.taintedByErrors with
            | true => exact ⟨.taintedBodyByErrors, rfl⟩
            | false =>
                rw [hTaint] at hUnmod
                rcases mapExcept_err_of_all_false translateBlockFailClosed isModeledBlock
                  translateBlock_err_of_unmodeled m.blocks hUnmod with ⟨e, he⟩
                rw [he]
                exact ⟨e, rfl⟩
  · intro fuel m st hUb
    exact hUb

/-- General parametric transfer theorem: any capture pipeline `(optPass, bridge)`
whose bridge satisfies `no_silent_drop` and whose pre-capture pass satisfies
`phase_preserves_all_outcomes` (resp. `phase_preserves_ub`) is sound for
arbitrary specs (resp. UB-freedom checking). -/
theorem captureBridge_sound_of_twoSurfaceCompleteness
    (optPass : MiddleMir → MiddleMir) (bridge : CaptureBridge) (cfg : TargetSemConfig)
    (hNoDrop : no_silent_drop bridge)
    (hPhaseUb : phase_preserves_ub optPass) :
    SoundForUbChecking cfg (postOptCapture optPass bridge) ∧
    (phase_preserves_all_outcomes optPass → SoundForSpecs cfg (postOptCapture optPass bridge)) := by
  refine ⟨?_, ?_⟩
  · intro m t fuel st hCap hTargetUbFree hSourceUb
    have hEq := hNoDrop (optPass m) t hCap cfg fuel st
    have hOptUb := hPhaseUb fuel m st hSourceUb
    rw [hOptUb] at hEq
    exact hTargetUbFree hEq
  · intro hAll m t fuel st spec hCap hSpecTarget
    have hEq := hNoDrop (optPass m) t hCap cfg fuel st
    have hOpt := hAll fuel m st
    rw [hOpt] at hEq
    rw [← hEq]
    exact hSpecTarget

/-! ## 10. Theorem 2: Lossy-Erasure Non-Injectivity Theorem -/

/-- Default valid initial execution state. -/
def validInitState : ExecState :=
  { retVal := 0, ptrValid := true, storageLiveFlag := false }

/-- Default invalid-pointer initial execution state (null / dangling pointer). -/
def invalidPtrState : ExecState :=
  { retVal := 0, ptrValid := false, storageLiveFlag := false }

/-- Concrete normal block executing a panicking call with `UnwindAction::Continue`. -/
def progNormalPanic : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := []
          term := .panickingCall .continue_
          isCleanup := false } ] }

/-- Concrete cleanup block executing the exact same terminator (`isCleanup := true`). -/
def progCleanupPanic : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := []
          term := .panickingCall .continue_
          isCleanup := true } ] }

/-- Concrete `extern "C"` ABI-boundary unwind termination (`UnwindTerminateReason::Abi`). -/
def progTerminateAbi : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := []
          term := .unwindTerminate .abi
          isCleanup := true } ] }

/-- Concrete double-panic-in-cleanup termination (`UnwindTerminateReason::InCleanup`). -/
def progTerminateInCleanup : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := []
          term := .unwindTerminate .inCleanup
          isCleanup := true } ] }

/-- Main Theorem 2: Dropping either `BasicBlockData::is_cleanup` or
`UnwindTerminateReason` creates non-injective collisions of semantically
distinguishable `MiddleMir` bodies, making any deterministic `TargetMir`
semantics incapable of faithfully representing unwinding outcomes. -/
theorem dropping_isCleanup_or_terminateReason_breaks_unwind_determinism :
    (∃ t,
      lossyDropCleanupBridge progNormalPanic = .ok t ∧
      lossyDropCleanupBridge progCleanupPanic = .ok t ∧
      evalMiddle 2 progNormalPanic validInitState ≠ evalMiddle 2 progCleanupPanic validInitState ∧
      ¬ ∃ semT : TargetMir → Outcome,
          semT t = evalMiddle 2 progNormalPanic validInitState ∧
          semT t = evalMiddle 2 progCleanupPanic validInitState) ∧
    (∃ t,
      lossyDropTerminateReasonBridge progTerminateAbi = .ok t ∧
      lossyDropTerminateReasonBridge progTerminateInCleanup = .ok t ∧
      evalMiddle 2 progTerminateAbi validInitState ≠ evalMiddle 2 progTerminateInCleanup validInitState ∧
      ¬ ∃ semT : TargetMir → Outcome,
          semT t = evalMiddle 2 progTerminateAbi validInitState ∧
          semT t = evalMiddle 2 progTerminateInCleanup validInitState) := by
  constructor
  · refine ⟨{ blocks := [{ stmts := [], term := .panickingCall .continue_, isCleanup := none }] },
      rfl, rfl, ?_, ?_⟩
    · intro h
      cases h
    · intro ⟨semT, h1, h2⟩
      have hEq : evalMiddle 2 progNormalPanic validInitState =
                 evalMiddle 2 progCleanupPanic validInitState := Eq.trans h1.symm h2
      cases hEq
  · refine ⟨{ blocks := [{ stmts := [], term := .unwindTerminate none, isCleanup := some true }] },
      rfl, rfl, ?_, ?_⟩
    · intro h
      cases h
    · intro ⟨semT, h1, h2⟩
      have hEq : evalMiddle 2 progTerminateAbi validInitState =
                 evalMiddle 2 progTerminateInCleanup validInitState := Eq.trans h1.symm h2
      cases hEq

/-! ## 11. Theorem 3: Pre-Opt vs Post-Opt MIR-phase separation -/

/-- Main Theorem 3: For ANY MIR optimization pass `optPass` that erases UB on
even a single program `m` (so `evalMiddle fuel m st = .ub` while
`evalMiddle fuel (optPass m) st ≠ .ub`), ANY capture bridge that is exact on
`optPass m` becomes unsound for UB checking when wired post-optimization via
`postOptCapture optPass bridge`. -/
theorem postOpt_capture_unsound_for_ub_checking_under_ub_erasing_pass
    (optPass : MiddleMir → MiddleMir) (bridge : CaptureBridge) (cfg : TargetSemConfig)
    (m : MiddleMir) (t : TargetMir) (fuel : Nat) (st : ExecState)
    (hNoDrop : no_silent_drop bridge)
    (hCap : bridge (optPass m) = .ok t)
    (hSourceUb : evalMiddle fuel m st = .ub)
    (hOptErasedUb : evalMiddle fuel (optPass m) st ≠ .ub) :
    postOptCapture optPass bridge m = .ok t ∧
    ubFree (evalTarget cfg fuel t st) ∧
    ¬ ubFree (evalMiddle fuel m st) ∧
    ¬ SoundForUbChecking cfg (postOptCapture optPass bridge) := by
  have hTargetEq : evalTarget cfg fuel t st = evalMiddle fuel (optPass m) st :=
    hNoDrop (optPass m) t hCap cfg fuel st
  have hTargetUbFree : ubFree (evalTarget cfg fuel t st) := by
    unfold ubFree
    rw [hTargetEq]
    exact hOptErasedUb
  have hNotSourceUbFree : ¬ ubFree (evalMiddle fuel m st) := by
    intro h
    exact h hSourceUb
  refine ⟨hCap, hTargetUbFree, hNotSourceUbFree, ?_⟩
  intro hSound
  have hFalseUbFree := hSound m t fuel st hCap hTargetUbFree
  exact hNotSourceUbFree hFalseUbFree

/-! ## 12. Constructive Counterexamples (CE1–CE6) -/

/-- Counterexample 1 program: ZST pointer dereference (`*p` where `p: *mut ()`)
at `Runtime(PostCleanup)` before `RemoveZsts` runs in `optimized_mir`. -/
def progZstDeref : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := [.zstDeref]
          term := .ret
          isCleanup := false } ] }

/-- Constructive Counterexample 1 (`RemoveZsts` UB erasure):
Capturing after `runRemoveZsts` (modeling `tcx.instance_mir` -> `optimized_mir`)
accepts `progZstDeref` and produces a `TargetMir` that evaluates cleanly to
`.ret 0` (satisfying `ubFree`), hiding the `.ub` present at `Runtime(PostCleanup)`.
By contrast, `failClosedPostCleanupBridge` preserves the exact `.ub`. -/
theorem ce1_optimized_mir_capture_hides_remove_zsts_ub :
    ∃ tOpt tPre,
      postOptCapture runRemoveZsts acceptOptimizedExactBridge progZstDeref = .ok tOpt ∧
      evalMiddle 2 progZstDeref invalidPtrState = .ub ∧
      evalTarget exactTargetConfig 2 tOpt invalidPtrState = .ret 0 ∧
      ubFree (evalTarget exactTargetConfig 2 tOpt invalidPtrState) ∧
      ¬ ubFree (evalMiddle 2 progZstDeref invalidPtrState) ∧
      failClosedPostCleanupBridge progZstDeref = .ok tPre ∧
      evalTarget exactTargetConfig 2 tPre invalidPtrState = .ub := by
  refine ⟨
    { blocks := [{ stmts := [.nop], term := .ret, isCleanup := some false }] },
    { blocks := [{ stmts := [.zstDeref], term := .ret, isCleanup := some false }] },
    rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · intro h; cases h
  · intro h; exact h rfl

/-- Constructive Counterexample 2 (Dropping `BasicBlockData::is_cleanup`):
`lossyDropCleanupBridge` maps both `progNormalPanic` (which unwinds and satisfies
`noAbort`) and `progCleanupPanic` (which double-panics in cleanup and aborts with
`Outcome.abort .inCleanup`, violating `noAbort`) to the exact same `TargetMir`.
Under `exactTargetConfig` (`defaultCleanup := false`), the verifier proves
`noAbort` on the captured target while `progCleanupPanic` actually aborts! -/
theorem ce2_dropping_is_cleanup_confuses_normal_and_cleanup_unwind :
    ∃ t,
      lossyDropCleanupBridge progNormalPanic = .ok t ∧
      lossyDropCleanupBridge progCleanupPanic = .ok t ∧
      evalMiddle 2 progNormalPanic validInitState = .unwind ∧
      evalMiddle 2 progCleanupPanic validInitState = .abort .inCleanup ∧
      noAbort (evalTarget exactTargetConfig 2 t validInitState) ∧
      ¬ noAbort (evalMiddle 2 progCleanupPanic validInitState) ∧
      ¬ SoundForSpecs exactTargetConfig lossyDropCleanupBridge := by
  refine ⟨
    { blocks := [{ stmts := [], term := .panickingCall .continue_, isCleanup := none }] },
    rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro r h; cases h
  · intro h; exact h .inCleanup rfl
  · intro hSound
    have hFalse := hSound progCleanupPanic
      { blocks := [{ stmts := [], term := .panickingCall .continue_, isCleanup := none }] }
      2 validInitState noAbort rfl (fun r h => by cases h)
    exact hFalse .inCleanup rfl

/-- Counterexample 3 program: body containing a constant whose evaluation fails
with `ErrorHandled::Reported` (e.g., a post-monomorphization `const { panic!() }`). -/
def progBrokenConst : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := [.assignConst .evalErrorReported]
          term := .ret
          isCleanup := false } ] }

/-- Constructive Counterexample 3 (Swallowing `ErrorHandled::Reported` in
`BodyBuilder::visit_const_operand`):
`swallowingConstErrorBridge` returns `.ok t` with an unevaluated broken constant
instead of failing closed, letting a verifier under `exactTargetConfig` prove
`noConstEvalFailure` (`.ret 0`) on an invalid program that fails const evaluation;
`failClosedPostCleanupBridge` rejects `progBrokenConst` with
`.error .constEvalReportedError`. -/
theorem ce3_swallowing_const_eval_error_passes_broken_const_to_verifier :
    ∃ t,
      swallowingConstErrorBridge progBrokenConst = .ok t ∧
      evalMiddle 2 progBrokenConst validInitState = .constEvalFailure ∧
      evalTarget exactTargetConfig 2 t validInitState = .ret 0 ∧
      noConstEvalFailure (evalTarget exactTargetConfig 2 t validInitState) ∧
      ¬ noConstEvalFailure (evalMiddle 2 progBrokenConst validInitState) ∧
      failClosedPostCleanupBridge progBrokenConst = .error .constEvalReportedError := by
  refine ⟨
    { blocks := [{ stmts := [.brokenUnevaluatedConst], term := .ret, isCleanup := some false }] },
    rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro h; cases h
  · intro h; exact h rfl

/-- Counterexample 4 program: `core::intrinsics::unchecked_div(0u32, x)` with `x = 0`,
which `GVN` (`gvn.rs:1508-1518`) folds to `const 0_u32` at `-C opt-level=2`. -/
def progZeroDivByZero : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := [.assignZeroDiv true]
          term := .ret
          isCleanup := false } ] }

/-- Constructive Counterexample 4 (`GVN` `0 / x -> 0` UB erasure):
`runGvnZeroDiv` folds `0 / 0` to constant `0`, causing post-opt capture to prove
`ubFree` while `Runtime(PostCleanup)` exhibits `.ub`. -/
theorem ce4_gvn_zero_div_hides_div_by_zero_ub :
    ∃ tOpt,
      postOptCapture runGvnZeroDiv acceptOptimizedExactBridge progZeroDivByZero = .ok tOpt ∧
      evalMiddle 2 progZeroDivByZero validInitState = .ub ∧
      evalTarget exactTargetConfig 2 tOpt validInitState = .ret 0 ∧
      ubFree (evalTarget exactTargetConfig 2 tOpt validInitState) ∧
      ¬ ubFree (evalMiddle 2 progZeroDivByZero validInitState) := by
  refine ⟨
    { blocks := [{ stmts := [.assignScalar 0], term := .ret, isCleanup := some false }] },
    rfl, rfl, rfl, ?_, ?_⟩
  · intro h; cases h
  · intro h; exact h rfl

/-- Counterexample 5 program: `let _ = *p;` lowering to `StatementKind::PlaceMention`
before `run_runtime_cleanup_passes`. -/
def progPlaceMention : MiddleMir :=
  { phase := .runtimeInitial
    taintedByErrors := false
    blocks :=
      [ { stmts := [.placeMention]
          term := .ret
          isCleanup := false } ] }

/-- Constructive Counterexample 5 (`RemovePlaceMention` without `-Zmir-preserve-ub`):
Without `-Zmir-preserve-ub`, `runRemovePlaceMention false` deletes `PlaceMention`
BEFORE `Runtime(PostCleanup)` is even reached, hiding `.ub` on an invalid pointer;
with `-Zmir-preserve-ub = true`, `failClosedPostCleanupBridge` accepts the body
and preserves `.ub`. -/
theorem ce5_remove_place_mention_without_preserve_ub_hides_place_ub :
    ∃ tNoPreserve tPreserve,
      postOptCapture (runRemovePlaceMention false) acceptOptimizedExactBridge progPlaceMention = .ok tNoPreserve ∧
      evalMiddle 2 progPlaceMention invalidPtrState = .ub ∧
      evalTarget exactTargetConfig 2 tNoPreserve invalidPtrState = .ret 0 ∧
      postOptCapture (runRemovePlaceMention true) failClosedPostCleanupBridge progPlaceMention = .ok tPreserve ∧
      evalTarget exactTargetConfig 2 tPreserve invalidPtrState = .ub := by
  refine ⟨
    { blocks := [{ stmts := [.nop], term := .ret, isCleanup := some false }] },
    { blocks := [{ stmts := [.placeMention], term := .ret, isCleanup := some false }] },
    rfl, rfl, rfl, rfl, rfl⟩

/-- Counterexample 6 program: `InlineAsm` effect lowered via `opaque(format!("{:?}"))`. -/
def progInlineAsm : MiddleMir :=
  { phase := .runtimePostCleanup true
    taintedByErrors := false
    blocks :=
      [ { stmts := [.inlineAsmEffect 7]
          term := .ret
          isCleanup := false } ] }

/-- Constructive Counterexample 6 (`opaque(...)` debug-string loss):
Lowering `InlineAsm` to an opaque string stub and reading it as a no-op hides
`Outcome.asmSideEffect 7` behind `.ret 0`, whereas `failClosedPostCleanupBridge`
fails closed with `.error .unmodeledInlineAsm`. -/
theorem ce6_opaque_inline_asm_under_noop_reading_hides_effect :
    ∃ t,
      opaqueStringifyAsmBridge progInlineAsm = .ok t ∧
      evalMiddle 2 progInlineAsm validInitState = .asmSideEffect 7 ∧
      evalTarget exactTargetConfig 2 t validInitState = .ret 0 ∧
      evalTarget exactTargetConfig 2 t validInitState ≠ evalMiddle 2 progInlineAsm validInitState ∧
      failClosedPostCleanupBridge progInlineAsm = .error .unmodeledInlineAsm := by
  refine ⟨
    { blocks := [{ stmts := [.opaqueStub 7], term := .ret, isCleanup := some false }] },
    rfl, rfl, rfl, ?_, rfl⟩
  · intro h; cases h

/-- Constructive witness classifying each defect in `CaptureFailureClass` against
a concrete `MiddleMir` body and distinguishing all six classes. -/
def witnessProgramForFailureClass : CaptureFailureClass → MiddleMir
  | .ubErasingPhaseShift => progZstDeref
  | .lossyFieldErasure => progCleanupPanic
  | .opaqueLoss => progInlineAsm
  | .panicOrIceTrap =>
      { phase := .runtimePostCleanup true
        taintedByErrors := false
        blocks := [{ stmts := [], term := .tailCall, isCleanup := false }] }
  | .swallowedConstEvalError => progBrokenConst
  | .soundFailClosedPostCleanup =>
      { phase := .runtimePostCleanup true
        taintedByErrors := false
        blocks := [{ stmts := [.assignConst (.scalar 42)], term := .ret, isCleanup := false }] }

/-- The fail-closed `Runtime(PostCleanup)` bridge rejects `opaqueLoss`,
`panicOrIceTrap`, and `swallowedConstEvalError` with typed errors, while
accepting the sound `PostCleanup` witness with exact outcome `.ret 42`. -/
theorem failureClass_failClosed_separation :
    (failClosedPostCleanupBridge (witnessProgramForFailureClass .opaqueLoss) = .error .unmodeledInlineAsm) ∧
    (failClosedPostCleanupBridge (witnessProgramForFailureClass .panicOrIceTrap) = .error .unmodeledTerminator) ∧
    (failClosedPostCleanupBridge (witnessProgramForFailureClass .swallowedConstEvalError) = .error .constEvalReportedError) ∧
    (∃ t, failClosedPostCleanupBridge (witnessProgramForFailureClass .soundFailClosedPostCleanup) = .ok t ∧
          evalTarget exactTargetConfig 2 t validInitState = .ret 42 ∧
          evalMiddle 2 (witnessProgramForFailureClass .soundFailClosedPostCleanup) validInitState = .ret 42) := by
  refine ⟨rfl, rfl, rfl,
    { blocks := [{ stmts := [.assignScalar 42], term := .ret, isCleanup := some false }] },
    rfl, rfl, rfl⟩

end StableMirCaptureSeam
