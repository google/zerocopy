/-!
# Formal Model of `CleanupPostBorrowck` and `AbortUnwindingCalls`

Zero outside imports (Lean `v4.34.1` `Init` only), total functions only, and zero trusted escapes.

Covers:
1. Analysis-to-Runtime MIR syntax (`FalseEdge`, `FalseUnwind`, `FakeRead`,
   `AscribeUserType`, `BorrowKind::Fake`, `PointerCoercion::{ArrayToPointer, MutToConstPointer}`,
   `CoverageKind`, `BackwardIncompatibleDropHint`, `PlaceMention`, and `UnwindAction`).
2. `CleanupPostBorrowck`: unconditional exact equivalence over unguarded MIR and certified
   bidirectional equivalence under `FakeRead` validity and fake-borrow immutability.
3. `PlaceMention` vs value-loading reads, and `RemovePlaceMention` (`-Zmir-preserve-ub`)
   refinement for UB-free executions.
4. `AbortUnwindingCalls`: exact model of `fn_can_unwind`, `call_can_unwind`, `Continue ->
   Terminate(Abi)`, `Cleanup` preservation + `UnwindResume -> Terminate(Abi)`, `Unreachable`
   marking for non-unwinding callees, dead cleanup block compaction (`remove_dead_blocks`),
   non-panicking lockstep equivalence, and panicking ABI-abort refinement.
5. End-to-end composition theorem and 5 kernel-checked sharpness counterexamples.
-/

namespace MirCleanupLowering

/-! ## 1. Syntax, Configuration, and ABI Unwindability -/

inductive AbiKind where
  | rust
  | cNounwind
  | cUnwind
  deriving DecidableEq, Repr

structure CalleeSpec where
  abi : AbiKind
  isForeign : Bool
  isFnPtr : Bool
  deriving DecidableEq, Repr

structure CompileCfg where
  panicAborts : Bool
  targetSupportsUnwinding : Bool
  panicInDropUnwinds : Bool
  deriving DecidableEq, Repr

/-- Mirrors `rustc_middle::ty::layout::fn_can_unwind`.
When `panicAborts = true`, every non-foreign item (`isForeign = false`)
has `fnCanUnwind = false`, even if declared with `cUnwind`. -/
def fnCanUnwind (cfg : CompileCfg) (isForeign : Bool) (abi : AbiKind) : Bool :=
  if !isForeign && cfg.panicAborts then
    false
  else
    match abi with
    | .rust => !cfg.panicAborts
    | .cNounwind => false
    | .cUnwind => true

/-- Mirrors `AbortUnwindingCalls`'s per-call unwindability check (`fn_def_id = None` for
function pointers, so `isFnPtr = true` evaluates as `isForeign = true`). -/
def callCanUnwind (cfg : CompileCfg) (c : CalleeSpec) : Bool :=
  if c.isFnPtr then
    fnCanUnwind cfg true c.abi
  else
    fnCanUnwind cfg c.isForeign c.abi

def dropCanUnwind (cfg : CompileCfg) : Bool :=
  cfg.panicInDropUnwinds && fnCanUnwind cfg true .rust

def assertCanUnwind (cfg : CompileCfg) : Bool :=
  fnCanUnwind cfg true .rust

inductive SlotVal where
  | dead
  | uninit
  | scalar (v : Nat)
  | ptr (addr : Nat)
  | enumVal (tag : Nat) (numVariants : Nat)
  deriving DecidableEq, Repr

inductive Place where
  | localSlot (id : Nat)
  | derefSlot (ptrLocal : Nat)
  deriving DecidableEq, Repr

inductive FakeBorrowKind where
  | shallow
  | deep
  deriving DecidableEq, Repr

inductive FakeReadCause where
  | forMatchGuard
  | forMatchedPlace
  | forGuardBinding
  | forLet
  | forIndex
  deriving DecidableEq, Repr

inductive PtrCoercion where
  | arrayToPtr
  | mutToConstPtr
  | ptrToPtr
  deriving DecidableEq, Repr

inductive Stmt where
  | assignConst (dst : Nat) (val : Nat)
  | assignPtr (dst : Nat) (addr : Nat)
  | assignEnum (dst : Nat) (tag : Nat) (numVariants : Nat)
  | assignCopy (dst : Nat) (src : Place)
  | assignDiscr (dst : Nat) (src : Place)
  | assignFakeBorrow (dst : Nat) (kind : FakeBorrowKind) (src : Place)
  | assignPtrCoercion (dst : Nat) (kind : PtrCoercion) (srcLocal : Nat)
  | fakeRead (cause : FakeReadCause) (place : Place)
  | ascribeUserType (place : Place)
  | coverageMarker (removedAfterAnalysis : Bool) (id : Nat)
  | dropHint (place : Place)
  | placeMention (place : Place)
  | storageLive (id : Nat)
  | storageDead (id : Nat)
  | recordDrop (tag : Nat)
  | nop
  deriving DecidableEq, Repr

inductive UnwindTerminateReason where
  | abi
  | inCleanup
  deriving DecidableEq, Repr

inductive UnwindAction where
  | continue_
  | unreachable
  | terminate (reason : UnwindTerminateReason)
  | cleanup (bb : Nat)
  deriving DecidableEq, Repr

inductive Term where
  | goto (target : Nat)
  | switchInt (discrLocal : Nat) (cases : List (Nat × Nat)) (otherwise : Nat)
  | falseEdge (realTarget : Nat) (imagTarget : Nat)
  | falseUnwind (realTarget : Nat) (unwind : UnwindAction)
  | call (callee : CalleeSpec) (dst : Nat) (target : Nat) (unwind : UnwindAction)
  | drop (localId : Nat) (dropTag : Nat) (target : Nat) (unwind : UnwindAction)
  | assert (condLocal : Nat) (expected : Bool) (target : Nat) (unwind : UnwindAction)
  | inlineAsm (mayUnwind : Bool) (target : Nat) (unwind : UnwindAction)
  | return_ (retLocal : Nat)
  | unwindResume
  | unwindTerminate (reason : UnwindTerminateReason)
  | unreachable
  deriving DecidableEq, Repr

structure BasicBlock where
  stmts : List Stmt
  term : Term
  isCleanup : Bool
  deriving DecidableEq, Repr

structure Body where
  blocks : List BasicBlock
  bodyAbi : AbiKind
  bodyIsForeign : Bool
  hasUserTypeAnnots : Bool
  deriving DecidableEq, Repr

def bodyCanUnwind (cfg : CompileCfg) (b : Body) : Bool :=
  fnCanUnwind cfg b.bodyIsForeign b.bodyAbi

/-! ## 2. Transformations (`CleanupPostBorrowck`, `RemovePlaceMention`, `AbortUnwindingCalls`) -/

def cleanupStmt (s : Stmt) : Stmt :=
  match s with
  | .ascribeUserType _ => .nop
  | .assignFakeBorrow _ _ _ => .nop
  | .coverageMarker true _ => .nop
  | .fakeRead _ _ => .nop
  | .dropHint _ => .nop
  | .assignPtrCoercion dst .arrayToPtr src => .assignPtrCoercion dst .ptrToPtr src
  | .assignPtrCoercion dst .mutToConstPtr src => .assignPtrCoercion dst .ptrToPtr src
  | other => other

def cleanupTerm (t : Term) : Term :=
  match t with
  | .falseEdge realTarget _ => .goto realTarget
  | .falseUnwind realTarget _ => .goto realTarget
  | other => other

def cleanupBlock (bb : BasicBlock) : BasicBlock :=
  { bb with
    stmts := bb.stmts.map cleanupStmt
    term := cleanupTerm bb.term }

def cleanupPostBorrowck (b : Body) : Body :=
  { b with
    blocks := b.blocks.map cleanupBlock
    hasUserTypeAnnots := false }

def keepNonPlaceMention (s : Stmt) : Bool :=
  match s with
  | .placeMention _ => false
  | .nop => false
  | _ => true

def removePlaceMention (mirPreserveUb : Bool) (b : Body) : Body :=
  if mirPreserveUb then
    b
  else
    { b with
      blocks := b.blocks.map fun bb => { bb with stmts := bb.stmts.filter keepNonPlaceMention } }

def termCanUnwind (cfg : CompileCfg) (t : Term) : Option Bool :=
  match t with
  | .call callee _ _ _ => some (callCanUnwind cfg callee)
  | .drop _ _ _ _ => some (dropCanUnwind cfg)
  | .assert _ _ _ _ => some (assertCanUnwind cfg)
  | .falseUnwind _ _ => some (assertCanUnwind cfg)
  | .inlineAsm mayUnwind _ _ => some mayUnwind
  | _ => none

def termWithUnwind (t : Term) (u : UnwindAction) : Term :=
  match t with
  | .call callee dst target _ => .call callee dst target u
  | .drop localId dropTag target _ => .drop localId dropTag target u
  | .assert condLocal expected target _ => .assert condLocal expected target u
  | .falseUnwind realTarget _ => .falseUnwind realTarget u
  | .inlineAsm mayUnwind target _ => .inlineAsm mayUnwind target u
  | other => other

def termUnwind (t : Term) : Option UnwindAction :=
  match t with
  | .call _ _ _ u => some u
  | .drop _ _ _ u => some u
  | .assert _ _ _ u => some u
  | .falseUnwind _ u => some u
  | .inlineAsm _ _ u => some u
  | _ => none

def abortRewriteTerm (cfg : CompileCfg) (bCanUnwind isCleanup : Bool) (t : Term) : Term :=
  let t1 :=
    match t with
    | .unwindResume =>
      match !cfg.targetSupportsUnwinding with
      | true => .unreachable
      | false =>
        match !bCanUnwind with
        | true => .unwindTerminate .abi
        | false => .unwindResume
    | other => other
  match isCleanup with
  | true => t1
  | false =>
    match termCanUnwind cfg t1, termUnwind t1 with
    | some cCanUnwind, some u =>
      match !cCanUnwind || !cfg.targetSupportsUnwinding with
      | true => termWithUnwind t1 .unreachable
      | false =>
        match !bCanUnwind && u == .continue_ with
        | true => termWithUnwind t1 (.terminate .abi)
        | false => t1
    | _, _ => t1

def abortRewriteBlock (cfg : CompileCfg) (bCanUnwind : Bool) (bb : BasicBlock) : BasicBlock :=
  { bb with term := abortRewriteTerm cfg bCanUnwind bb.isCleanup bb.term }

def abortRewriteOnly (cfg : CompileCfg) (b : Body) : Body :=
  { b with blocks := b.blocks.map (abortRewriteBlock cfg (bodyCanUnwind cfg b)) }

def termSuccs (t : Term) : List Nat :=
  match t with
  | .goto tgt => [tgt]
  | .switchInt _ cases otherwise => cases.map Prod.snd ++ [otherwise]
  | .falseEdge realTgt imagTgt => [realTgt, imagTgt]
  | .falseUnwind realTgt u =>
    match u with
    | .cleanup bb => [realTgt, bb]
    | _ => [realTgt]
  | .call _ _ tgt u =>
    match u with
    | .cleanup bb => [tgt, bb]
    | _ => [tgt]
  | .drop _ _ tgt u =>
    match u with
    | .cleanup bb => [tgt, bb]
    | _ => [tgt]
  | .assert _ _ tgt u =>
    match u with
    | .cleanup bb => [tgt, bb]
    | _ => [tgt]
  | .inlineAsm _ tgt u =>
    match u with
    | .cleanup bb => [tgt, bb]
    | _ => [tgt]
  | .return_ _ | .unwindResume | .unwindTerminate _ | .unreachable => []

noncomputable def getNatBool (xs : List Bool) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun _ => false)
    (fun x _ rec n => match n with | 0 => x | k + 1 => rec k)
    xs i

noncomputable def setNatBool (xs : List Bool) (i : Nat) (v : Bool) : List Bool :=
  List.rec (motive := fun _ => Nat → List Bool)
    (fun _ => [])
    (fun x rest rec n => match n with | 0 => v :: rest | k + 1 => x :: rec k)
    xs i

noncomputable def markSuccs (blocks : List BasicBlock) (reach : List Bool) (idx : Nat) : List Bool :=
  match blocks[idx]? with
  | none => reach
  | some bb => (termSuccs bb.term).foldl (fun acc s => setNatBool acc s true) reach

noncomputable def reachStepAux (blocks : List BasicBlock) (seed : List Bool)
    (k : Nat) (acc : List Bool) : List Bool :=
  Nat.rec (motive := fun _ => List Bool → List Bool)
    (fun a => a)
    (fun k' rec a =>
      let acc' := rec a
      match getNatBool seed k' with
      | true => markSuccs blocks acc' k'
      | false => acc')
    k acc

noncomputable def reachStep (blocks : List BasicBlock) (reach : List Bool) : List Bool :=
  reachStepAux blocks reach blocks.length reach

noncomputable def iterReach (n : Nat) (blocks : List BasicBlock) (reach : List Bool) : List Bool :=
  Nat.rec (motive := fun _ => List Bool → List Bool)
    (fun r => r)
    (fun _ rec r => rec (reachStep blocks r))
    n reach

noncomputable def computeReachable (blocks : List BasicBlock) : List Bool :=
  let init := setNatBool (List.replicate blocks.length false) 0 true
  iterReach blocks.length blocks init

noncomputable def buildRemapAux (reach : List Bool) (nextNew : Nat) : List (Option Nat) :=
  List.rec (motive := fun _ => Nat → List (Option Nat))
    (fun _ => [])
    (fun b _ rec n =>
      match b with
      | true => some n :: rec (n + 1)
      | false => none :: rec n)
    reach nextNew

def remapIdx (remap : List (Option Nat)) (oldIdx : Nat) : Nat :=
  match remap[oldIdx]? with
  | some (some newIdx) => newIdx
  | _ => oldIdx

def remapUnwind (remap : List (Option Nat)) (u : UnwindAction) : UnwindAction :=
  match u with
  | .cleanup bb => .cleanup (remapIdx remap bb)
  | other => other

def remapTerm (remap : List (Option Nat)) (t : Term) : Term :=
  match t with
  | .goto tgt => .goto (remapIdx remap tgt)
  | .switchInt d cases oth =>
    .switchInt d (cases.map fun (v, tgt) => (v, remapIdx remap tgt)) (remapIdx remap oth)
  | .falseEdge rt it => .falseEdge (remapIdx remap rt) (remapIdx remap it)
  | .falseUnwind rt u => .falseUnwind (remapIdx remap rt) (remapUnwind remap u)
  | .call c dst tgt u => .call c dst (remapIdx remap tgt) (remapUnwind remap u)
  | .drop l tag tgt u => .drop l tag (remapIdx remap tgt) (remapUnwind remap u)
  | .assert c e tgt u => .assert c e (remapIdx remap tgt) (remapUnwind remap u)
  | .inlineAsm m tgt u => .inlineAsm m (remapIdx remap tgt) (remapUnwind remap u)
  | other => other

noncomputable def filterCompactBlocks (blocks : List BasicBlock) (reach : List Bool)
    (remap : List (Option Nat)) : List BasicBlock :=
  List.rec (motive := fun _ => List Bool → List BasicBlock)
    (fun _ => [])
    (fun bb _ rec rs =>
      match rs with
      | [] => []
      | true :: rrest => { bb with term := remapTerm remap bb.term } :: rec rrest
      | false :: rrest => rec rrest)
    blocks reach

noncomputable def compactReachableBody (b : Body) : Body :=
  let reach := computeReachable b.blocks
  let remap := buildRemapAux reach 0
  { b with blocks := filterCompactBlocks b.blocks reach remap }

/-- Complete `AbortUnwindingCalls` pass: rewrites terminators and invokes dead-block compaction
(matching `abort_unwinding_calls.rs` calling `super::simplify::remove_dead_blocks`). -/
noncomputable def abortUnwindingCalls (cfg : CompileCfg) (b : Body) : Body :=
  compactReachableBody (abortRewriteOnly cfg b)

private theorem buildRemapAux_cons_false (rs : List Bool) (nextNew : Nat) :
    buildRemapAux (false :: rs) nextNew = none :: buildRemapAux rs nextNew := rfl

private theorem buildRemapAux_cons_true (rs : List Bool) (nextNew : Nat) :
    buildRemapAux (true :: rs) nextNew = some nextNew :: buildRemapAux rs (nextNew + 1) := rfl

private theorem filterCompactBlocks_cons_true (bb : BasicBlock) (bbs : List BasicBlock)
    (rs : List Bool) (remap : List (Option Nat)) :
    filterCompactBlocks (bb :: bbs) (true :: rs) remap =
      { bb with term := remapTerm remap bb.term } :: filterCompactBlocks bbs rs remap := rfl

/-! ## 3. Runtime-MIR Validity Predicates -/

def stmtAllowedInRuntime (s : Stmt) : Bool :=
  match s with
  | .ascribeUserType _ => false
  | .assignFakeBorrow _ _ _ => false
  | .coverageMarker true _ => false
  | .fakeRead _ _ => false
  | .dropHint _ => false
  | .assignPtrCoercion _ .arrayToPtr _ => false
  | .assignPtrCoercion _ .mutToConstPtr _ => false
  | _ => true

def termAllowedInRuntime (t : Term) : Bool :=
  match t with
  | .falseEdge _ _ => false
  | .falseUnwind _ _ => false
  | _ => true

def validRuntimeSyntax (b : Body) : Bool :=
  !b.hasUserTypeAnnots &&
  b.blocks.all fun bb => bb.stmts.all stmtAllowedInRuntime && termAllowedInRuntime bb.term

/-! ## 4. Operational Semantics (Analysis-Guarded, Analysis-Unguarded, Runtime) -/

inductive EvalMode where
  | analysisUnguarded
  | analysisGuarded
  | analysisPostCleanup
  | runtime
  deriving DecidableEq, Repr

def EvalMode.forbidsAnalysis (m : EvalMode) : Bool :=
  match m with
  | .analysisPostCleanup | .runtime => true
  | .analysisUnguarded | .analysisGuarded => false

def EvalMode.isRuntimeUnwind (m : EvalMode) : Bool :=
  match m with
  | .runtime => true
  | _ => false

inductive FaultKind where
  | malformedRuntimeMir
  | ubInvalidPtrDeref
  | ubInvalidValue
  | ubDeadOrUninitRead
  | ubUnreachable
  | ubUnreachableUnwind
  | ubUnwindPastNounwindAbi
  | ubFakeReadViolation
  | outOfBlocks
  deriving DecidableEq, Repr

inductive Outcome where
  | returned (val : Nat)
  | propagatedUnwind
  | aborted (reason : UnwindTerminateReason)
  | fault (k : FaultKind)
  | outOfFuel
  deriving DecidableEq, Repr

structure EvalState where
  bb : Nat
  stmtIdx : Nat
  store : List SlotVal
  fakeBorrows : List (Nat × SlotVal × FakeBorrowKind)
  trace : List Nat
  deriving DecidableEq, Repr

structure ObsResult where
  outcome : Outcome
  store : List SlotVal
  trace : List Nat
  deriving DecidableEq, Repr

structure StepEvent where
  unwind : Bool
  retVal : Nat
  deriving DecidableEq, Repr

def getSlot (store : List SlotVal) (i : Nat) : SlotVal :=
  match store[i]? with
  | some v => v
  | none => .dead

noncomputable def setSlot (store : List SlotVal) (i : Nat) (v : SlotVal) : List SlotVal :=
  List.rec (motive := fun _ => Nat → List SlotVal)
    (fun _ => [])
    (fun x rest rec n => match n with | 0 => v :: rest | k + 1 => x :: rec k)
    store i

def slotValid (v : SlotVal) : Bool :=
  match v with
  | .dead => false
  | .uninit => false
  | .scalar _ => true
  | .ptr _ => true
  | .enumVal tag nv => Nat.ble (tag + 1) nv

def evalPlaceAddr (store : List SlotVal) (p : Place) : Except FaultKind Nat :=
  match p with
  | .localSlot i =>
    match getSlot store i with
    | .dead => .error .ubDeadOrUninitRead
    | _ => .ok i
  | .derefSlot ptrLocal =>
    match getSlot store ptrLocal with
    | .ptr addr => .ok addr
    | _ => .error .ubInvalidPtrDeref

def checkFakeReadPlace (store : List SlotVal) (fakeBorrows : List (Nat × SlotVal × FakeBorrowKind))
    (_cause : FakeReadCause) (p : Place) : Except FaultKind Unit :=
  match evalPlaceAddr store p with
  | .error k => .error k
  | .ok addr =>
    let v := getSlot store addr
    if !slotValid v then
      .error .ubFakeReadViolation
    else
      match fakeBorrows.find? (fun entry => entry.1 == addr) with
      | none => .ok ()
      | some (_, expectedVal, _) =>
        if v == expectedVal then .ok () else .error .ubFakeReadViolation

def readValueFromPlace (store : List SlotVal) (p : Place) : Except FaultKind SlotVal :=
  match evalPlaceAddr store p with
  | .error k => .error k
  | .ok addr =>
    let v := getSlot store addr
    match slotValid v with
    | true => .ok v
    | false => .error .ubInvalidValue

def readDiscrFromPlace (store : List SlotVal) (p : Place) : Except FaultKind Nat :=
  match readValueFromPlace store p with
  | .error k => .error k
  | .ok (.enumVal tag _) => .ok tag
  | .ok (.scalar v) => .ok v
  | .ok _ => .error .ubInvalidValue

noncomputable def stepStmt (mode : EvalMode) (st : EvalState) (s : Stmt) : Except FaultKind EvalState :=
  match s with
  | .nop => .ok { st with stmtIdx := st.stmtIdx + 1 }
  | .recordDrop tag =>
    .ok { st with stmtIdx := st.stmtIdx + 1, trace := st.trace ++ [tag] }
  | .storageLive id =>
    .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store id .uninit }
  | .storageDead id =>
    .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store id .dead }
  | .assignConst dst val =>
    .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store dst (.scalar val) }
  | .assignPtr dst addr =>
    .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store dst (.ptr addr) }
  | .assignEnum dst tag nv =>
    .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store dst (.enumVal tag nv) }
  | .assignCopy dst src =>
    match readValueFromPlace st.store src with
    | .error k => .error k
    | .ok v => .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store dst v }
  | .assignDiscr dst src =>
    match readDiscrFromPlace st.store src with
    | .error k => .error k
    | .ok tag => .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store dst (.scalar tag) }
  | .assignPtrCoercion dst kind srcLocal =>
    match mode.forbidsAnalysis && kind != .ptrToPtr with
    | true => .error .malformedRuntimeMir
    | false =>
      match readValueFromPlace st.store (.localSlot srcLocal) with
      | .error k => .error k
      | .ok v => .ok { st with stmtIdx := st.stmtIdx + 1, store := setSlot st.store dst v }
  | .placeMention p =>
    match evalPlaceAddr st.store p with
    | .error k => .error k
    | .ok _ => .ok { st with stmtIdx := st.stmtIdx + 1 }
  | .coverageMarker removed _ =>
    match mode.forbidsAnalysis && removed with
    | true => .error .malformedRuntimeMir
    | false => .ok { st with stmtIdx := st.stmtIdx + 1 }
  | .ascribeUserType _ | .dropHint _ =>
    match mode.forbidsAnalysis with
    | true => .error .malformedRuntimeMir
    | false => .ok { st with stmtIdx := st.stmtIdx + 1 }
  | .assignFakeBorrow dst kind src =>
    match mode.forbidsAnalysis with
    | true => .error .malformedRuntimeMir
    | false =>
      match mode with
      | .analysisUnguarded => .ok { st with stmtIdx := st.stmtIdx + 1 }
      | _ =>
        match evalPlaceAddr st.store src with
        | .error _ => .error .ubFakeReadViolation
        | .ok addr =>
          let snapVal := getSlot st.store addr
          .ok { st with
            stmtIdx := st.stmtIdx + 1
            store := setSlot st.store dst (.ptr addr)
            fakeBorrows := (addr, snapVal, kind) :: st.fakeBorrows }
  | .fakeRead cause p =>
    match mode.forbidsAnalysis with
    | true => .error .malformedRuntimeMir
    | false =>
      match mode with
      | .analysisUnguarded => .ok { st with stmtIdx := st.stmtIdx + 1 }
      | _ =>
        match checkFakeReadPlace st.store st.fakeBorrows cause p with
        | .error _ => .error .ubFakeReadViolation
        | .ok () => .ok { st with stmtIdx := st.stmtIdx + 1 }

noncomputable def lookupSwitchTarget (v : Nat) (cases : List (Nat × Nat)) (otherwise : Nat) : Nat :=
  List.rec otherwise (fun entry _ rec => match v == entry.1 with | true => entry.2 | false => rec) cases

private theorem lookupSwitchTarget_cons (v k tgt : Nat) (rest : List (Nat × Nat)) (otherwise : Nat) :
    lookupSwitchTarget v ((k, tgt) :: rest) otherwise =
      match v == k with | true => tgt | false => lookupSwitchTarget v rest otherwise := rfl

inductive TermStep where
  | nextState (st : EvalState)
  | finished (out : Outcome) (st : EvalState)
  deriving DecidableEq, Repr

def takeUnwind (mode : EvalMode) (bCanUnwind : Bool) (st : EvalState) (u : UnwindAction) : TermStep :=
  match u with
  | .cleanup bb => .nextState { st with bb := bb, stmtIdx := 0 }
  | .terminate r => .finished (.aborted r) st
  | .unreachable => .finished (.fault .ubUnreachableUnwind) st
  | .continue_ =>
    match bCanUnwind with
    | true => .finished .propagatedUnwind st
    | false =>
      match mode.isRuntimeUnwind with
      | true => .finished (.fault .ubUnwindPastNounwindAbi) st
      | false => .finished (.aborted .abi) st

noncomputable def stepTerm (cfg : CompileCfg) (mode : EvalMode) (b : Body) (st : EvalState)
    (t : Term) (ev : StepEvent) : TermStep :=
  let bCanUnwind := bodyCanUnwind cfg b
  match t with
  | .goto tgt => .nextState { st with bb := tgt, stmtIdx := 0 }
  | .switchInt dLocal cases otherwise =>
    match readDiscrFromPlace st.store (.localSlot dLocal) with
    | .error k => .finished (.fault k) st
    | .ok d => .nextState { st with bb := lookupSwitchTarget d cases otherwise, stmtIdx := 0 }
  | .falseEdge realTgt _ =>
    match mode.forbidsAnalysis with
    | true => .finished (.fault .malformedRuntimeMir) st
    | false => .nextState { st with bb := realTgt, stmtIdx := 0 }
  | .falseUnwind realTgt _ =>
    match mode.forbidsAnalysis with
    | true => .finished (.fault .malformedRuntimeMir) st
    | false => .nextState { st with bb := realTgt, stmtIdx := 0 }
  | .call _ dst tgt u =>
    match ev.unwind with
    | true => takeUnwind mode bCanUnwind st u
    | false =>
      .nextState { st with
        bb := tgt
        stmtIdx := 0
        store := setSlot st.store dst (.scalar ev.retVal) }
  | .drop _ dropTag tgt u =>
    let st' := { st with trace := st.trace ++ [dropTag] }
    match ev.unwind with
    | true => takeUnwind mode bCanUnwind st' u
    | false => .nextState { st' with bb := tgt, stmtIdx := 0 }
  | .assert condLocal expected tgt u =>
    match readDiscrFromPlace st.store (.localSlot condLocal) with
    | .error k => .finished (.fault k) st
    | .ok d =>
      let bVal := d != 0
      match bVal == expected with
      | true => .nextState { st with bb := tgt, stmtIdx := 0 }
      | false => takeUnwind mode bCanUnwind st u
  | .inlineAsm _ tgt u =>
    match ev.unwind with
    | true => takeUnwind mode bCanUnwind st u
    | false => .nextState { st with bb := tgt, stmtIdx := 0 }
  | .return_ retLocal =>
    match readValueFromPlace st.store (.localSlot retLocal) with
    | .error k => .finished (.fault k) st
    | .ok (.scalar v) => .finished (.returned v) st
    | .ok (.enumVal tag _) => .finished (.returned tag) st
    | .ok _ => .finished (.fault .ubInvalidValue) st
  | .unwindResume =>
    match bCanUnwind with
    | true => .finished .propagatedUnwind st
    | false =>
      match mode.isRuntimeUnwind with
      | true => .finished (.fault .ubUnwindPastNounwindAbi) st
      | false => .finished (.aborted .abi) st
  | .unwindTerminate r => .finished (.aborted r) st
  | .unreachable => .finished (.fault .ubUnreachable) st

noncomputable def runEval (cfg : CompileCfg) (mode : EvalMode) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0) : EvalState × Outcome :=
  Nat.rec (motive := fun _ => EvalState → Nat → EvalState × Outcome)
    (fun st _ => (st, .outOfFuel))
    (fun _ rec st stepIdx =>
      match b.blocks[st.bb]? with
      | none => (st, .fault .outOfBlocks)
      | some bbData =>
        match bbData.stmts[st.stmtIdx]? with
        | some s =>
          match stepStmt mode st s with
          | .error k => (st, .fault k)
          | .ok st' => rec st' (stepIdx + 1)
        | none =>
          match stepTerm cfg mode b st bbData.term (oracle stepIdx) with
          | .finished out st' => (st', out)
          | .nextState st' => rec st' (stepIdx + 1))
    fuel st stepIdx

noncomputable def runObs (cfg : CompileCfg) (mode : EvalMode) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0) : ObsResult :=
  let (st', out) := runEval cfg mode fuel b st oracle stepIdx
  { outcome := out, store := st'.store, trace := st'.trace }

private theorem runEval_zero (cfg : CompileCfg) (mode : EvalMode) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat) :
    runEval cfg mode 0 b st oracle stepIdx = (st, .outOfFuel) := rfl

private theorem runEval_succ (cfg : CompileCfg) (mode : EvalMode) (f : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat) :
    runEval cfg mode (f + 1) b st oracle stepIdx =
      match b.blocks[st.bb]? with
      | none => (st, .fault .outOfBlocks)
      | some bbData =>
        match bbData.stmts[st.stmtIdx]? with
        | some s =>
          match stepStmt mode st s with
          | .error k => (st, .fault k)
          | .ok st' => runEval cfg mode f b st' oracle (stepIdx + 1)
        | none =>
          match stepTerm cfg mode b st bbData.term (oracle stepIdx) with
          | .finished out st' => (st', out)
          | .nextState st' => runEval cfg mode f b st' oracle (stepIdx + 1) := rfl

/-! ## 5. Helper Lemmas -/

private theorem list_all_map_true {α : Type} (f : α → Bool) (g : α → α) (xs : List α)
    (h : ∀ x, f (g x) = true) : (xs.map g).all f = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f (g x) && (xs.map g).all f) = true
    rw [h x, ih]
    rfl

private theorem list_getElem?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    (xs.map f)[i]? = (xs[i]?).map f := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

private theorem list_getElem?_mem {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil => cases i <;> simp at h
  | cons y ys ih =>
    cases i with
    | zero =>
      cases h
      exact List.Mem.head _
    | succ k =>
      exact List.Mem.tail _ (ih h)

private theorem setSlot_preserves_other (xs : List SlotVal) (i j : Nat) (v : SlotVal)
    (hNe : i ≠ j) :
    getSlot (setSlot xs i v) j = getSlot xs j := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => contradiction
      | succ k => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' =>
        apply ih
        intro hEq
        apply hNe
        rw [hEq]

private theorem setSlot_getSlot_cases (xs : List SlotVal) (i j : Nat) (v : SlotVal) :
    (i = j ∧ (match xs[i]? with | some _ => getSlot (setSlot xs i v) j = v | none => getSlot (setSlot xs i v) j = getSlot xs j)) ∨
    (i ≠ j ∧ getSlot (setSlot xs i v) j = getSlot xs j) := by
  induction xs generalizing i j with
  | nil =>
    cases Nat.decEq i j with
    | isTrue hEq => exact Or.inl ⟨hEq, rfl⟩
    | isFalse hNe => exact Or.inr ⟨hNe, rfl⟩
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact Or.inl ⟨rfl, rfl⟩
      | succ k => exact Or.inr ⟨Nat.noConfusion, rfl⟩
    | succ i' =>
      cases j with
      | zero => exact Or.inr ⟨Nat.noConfusion, rfl⟩
      | succ j' =>
        rcases ih i' j' with ⟨hEq, hVal⟩ | ⟨hNe, hPres⟩
        · exact Or.inl ⟨congrArg Nat.succ hEq, hVal⟩
        · exact Or.inr ⟨fun h => hNe (Nat.succ.inj h), hPres⟩

private theorem setSlot_length (xs : List SlotVal) (i : Nat) (v : SlotVal) :
    (setSlot xs i v).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact congrArg Nat.succ (ih k)

private theorem bool_not_true_eq_false {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> first | rfl | exact absurd h Bool.noConfusion

private theorem list_all_mem_true {α : Type} {f : α → Bool} {xs : List α} {x : α}
    (hAll : xs.all f = true) (hMem : x ∈ xs) : f x = true := by
  induction xs with
  | nil => cases hMem
  | cons y ys ih =>
    have hPair : f y = true ∧ ys.all f = true := by
      cases hy : f y <;> cases hys : ys.all f
      · exfalso; have h1 : (f y && ys.all f) = true := hAll; rw [hy, hys] at h1; exact Bool.noConfusion h1
      · exfalso; have h1 : (f y && ys.all f) = true := hAll; rw [hy, hys] at h1; exact Bool.noConfusion h1
      · exfalso; have h1 : (f y && ys.all f) = true := hAll; rw [hy, hys] at h1; exact Bool.noConfusion h1
      · exact ⟨rfl, rfl⟩
    cases hMem with
    | head _ => exact hPair.1
    | tail _ hm => exact ih hPair.2 hm

/-! ## 6. `CleanupPostBorrowck`: Syntax Validity & Unguarded Exact Equivalence -/

private theorem cleanupStmt_allowed (s : Stmt) : stmtAllowedInRuntime (cleanupStmt s) = true := by
  cases s with
  | assignPtrCoercion dst kind src => cases kind <;> rfl
  | coverageMarker rem id => cases rem <;> rfl
  | _ => rfl

private theorem cleanupTerm_allowed (t : Term) : termAllowedInRuntime (cleanupTerm t) = true := by
  cases t <;> rfl

theorem cleanupPostBorrowck_syntax_valid (b : Body) :
    validRuntimeSyntax (cleanupPostBorrowck b) = true := by
  unfold validRuntimeSyntax cleanupPostBorrowck
  dsimp only
  have h1 : (b.blocks.map cleanupBlock).all
      (fun bb => bb.stmts.all stmtAllowedInRuntime && termAllowedInRuntime bb.term) = true := by
    apply list_all_map_true
    intro bb
    unfold cleanupBlock
    dsimp only
    rw [list_all_map_true stmtAllowedInRuntime cleanupStmt bb.stmts cleanupStmt_allowed]
    rw [cleanupTerm_allowed bb.term]
    rfl
  exact h1

private theorem stepStmt_cleanup_unguarded (st : EvalState) (s : Stmt) :
    stepStmt .analysisPostCleanup st (cleanupStmt s) = stepStmt .analysisUnguarded st s := by
  cases s with
  | assignPtrCoercion dst kind src => cases kind <;> rfl
  | coverageMarker rem id => cases rem <;> rfl
  | _ => rfl

private theorem stepTerm_cleanup_unguarded (cfg : CompileCfg) (b : Body) (st : EvalState)
    (t : Term) (ev : StepEvent) :
    stepTerm cfg .analysisPostCleanup (cleanupPostBorrowck b) st (cleanupTerm t) ev =
      stepTerm cfg .analysisUnguarded b st t ev := by
  have hAbi : bodyCanUnwind cfg (cleanupPostBorrowck b) = bodyCanUnwind cfg b := rfl
  cases t with
  | falseEdge _ _ => rfl
  | falseUnwind _ _ => rfl
  | call _ _ _ u => cases ev.unwind <;> cases u <;> rfl
  | drop _ _ _ u => cases ev.unwind <;> cases u <;> rfl
  | assert cond exp _ u =>
    unfold stepTerm
    dsimp only [cleanupTerm]
    rw [hAbi]
    cases readDiscrFromPlace st.store (.localSlot cond) with
    | error _ => rfl
    | ok d => cases (d != 0) == exp <;> cases u <;> rfl
  | inlineAsm _ _ u => cases ev.unwind <;> cases u <;> rfl
  | unwindResume =>
    unfold stepTerm
    dsimp only [cleanupTerm]
    rw [hAbi]
    cases bodyCanUnwind cfg b <;> rfl
  | _ => rfl

theorem cleanupPostBorrowck_unguarded_exact_equiv (cfg : CompileCfg) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0) :
    runEval cfg .analysisPostCleanup fuel (cleanupPostBorrowck b) st oracle stepIdx =
      runEval cfg .analysisUnguarded fuel b st oracle stepIdx := by
  induction fuel generalizing st stepIdx with
  | zero => rfl
  | succ f ih =>
    unfold runEval
    dsimp only [cleanupPostBorrowck]
    rw [list_getElem?_map]
    cases hbb : b.blocks[st.bb]? with
    | none => rfl
    | some bbData =>
      dsimp only [Option.map, cleanupBlock]
      rw [list_getElem?_map]
      cases hst : bbData.stmts[st.stmtIdx]? with
      | some s =>
        dsimp only [Option.map]
        rw [stepStmt_cleanup_unguarded]
        cases stepStmt .analysisUnguarded st s with
        | error _ => rfl
        | ok st' => exact ih st' (stepIdx + 1)
      | none =>
        dsimp only [Option.map]
        have hTerm := stepTerm_cleanup_unguarded cfg b st bbData.term (oracle stepIdx)
        dsimp only [cleanupPostBorrowck] at hTerm
        rw [hTerm]
        cases stepTerm cfg .analysisUnguarded b st bbData.term (oracle stepIdx) with
        | finished _ _ => rfl
        | nextState st' => exact ih st' (stepIdx + 1)

/-! ## 7. Certified Bidirectional Equivalence of `FakeRead` & Fake-Borrow Erasure -/

private theorem bool_and_left_true {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> first | rfl | exact absurd h Bool.noConfusion

private theorem bool_and_right_true {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> first | rfl | exact absurd h Bool.noConfusion

private theorem evalPlaceAddr_ne_fakeReadUb (store : List SlotVal) (p : Place) (k : FaultKind)
    (h : evalPlaceAddr store p = .error k) : k ≠ .ubFakeReadViolation := by
  unfold evalPlaceAddr at h
  cases p with
  | localSlot i =>
    dsimp only at h
    cases hGet : getSlot store i <;> rw [hGet] at h <;> cases h <;> exact FaultKind.noConfusion
  | derefSlot i =>
    dsimp only at h
    cases hGet : getSlot store i <;> rw [hGet] at h <;> cases h <;> exact FaultKind.noConfusion

private theorem readValueFromPlace_ne_fakeReadUb (store : List SlotVal) (p : Place) (k : FaultKind)
    (h : readValueFromPlace store p = .error k) : k ≠ .ubFakeReadViolation := by
  unfold readValueFromPlace at h
  cases hEv : evalPlaceAddr store p with
  | error k' =>
    rw [hEv] at h
    dsimp only at h
    cases h
    exact evalPlaceAddr_ne_fakeReadUb store p k hEv
  | ok addr =>
    rw [hEv] at h
    dsimp only at h
    cases hsv : slotValid (getSlot store addr) <;> rw [hsv] at h <;> cases h
    exact FaultKind.noConfusion

private theorem readDiscrFromPlace_ne_fakeReadUb (store : List SlotVal) (p : Place) (k : FaultKind)
    (h : readDiscrFromPlace store p = .error k) : k ≠ .ubFakeReadViolation := by
  unfold readDiscrFromPlace at h
  cases hRd : readValueFromPlace store p with
  | error k' =>
    rw [hRd] at h
    dsimp only at h
    cases h
    exact readValueFromPlace_ne_fakeReadUb store p k hRd
  | ok v =>
    rw [hRd] at h
    cases v with
    | dead | uninit | ptr _ => cases h; exact FaultKind.noConfusion
    | scalar _ | enumVal _ _ => cases h

def Stmt.isFakeOp : Stmt → Bool
  | .fakeRead _ _ => true
  | .assignFakeBorrow _ _ _ => true
  | _ => false

private theorem stepStmt_nonFake_ne_fakeReadUb (st : EvalState) (s : Stmt) (k : FaultKind)
    (hFake : s.isFakeOp = false) (hSt : stepStmt .analysisGuarded st s = .error k) :
    k ≠ .ubFakeReadViolation := by
  cases s with
  | fakeRead _ _ => cases hFake
  | assignFakeBorrow _ _ _ => cases hFake
  | nop | recordDrop _ | storageLive _ | storageDead _
  | assignConst _ _ | assignPtr _ _ | assignEnum _ _ _
  | coverageMarker _ _ | ascribeUserType _ | dropHint _ =>
    unfold stepStmt at hSt; dsimp only at hSt; cases hSt
  | assignCopy _ src =>
    unfold stepStmt at hSt; dsimp only at hSt
    cases hRd : readValueFromPlace st.store src <;> rw [hRd] at hSt <;> cases hSt
    exact readValueFromPlace_ne_fakeReadUb st.store src k hRd
  | assignDiscr _ src =>
    unfold stepStmt at hSt; dsimp only at hSt
    cases hRd : readDiscrFromPlace st.store src <;> rw [hRd] at hSt <;> cases hSt
    exact readDiscrFromPlace_ne_fakeReadUb st.store src k hRd
  | assignPtrCoercion _ kind src =>
    unfold stepStmt at hSt; dsimp only at hSt
    cases hRd : readValueFromPlace st.store (.localSlot src) <;> rw [hRd] at hSt <;> cases hSt
    exact readValueFromPlace_ne_fakeReadUb st.store (.localSlot src) k hRd
  | placeMention p =>
    unfold stepStmt at hSt; dsimp only at hSt
    cases hEv : evalPlaceAddr st.store p <;> rw [hEv] at hSt <;> cases hSt
    exact evalPlaceAddr_ne_fakeReadUb st.store p k hEv

def placeNonFake (isFake : Nat → Bool) (p : Place) : Bool :=
  match p with
  | .localSlot i => !isFake i
  | .derefSlot ptrLocal => !isFake ptrLocal

def stmtUsesFakeCleanly (isFake : Nat → Bool) (s : Stmt) : Bool :=
  match s with
  | .assignFakeBorrow dst _ src => isFake dst && placeNonFake isFake src
  | .fakeRead _ _ => true
  | .assignConst dst _ => !isFake dst
  | .assignPtr dst addr => !isFake dst && !isFake addr
  | .assignEnum dst _ _ => !isFake dst
  | .assignCopy dst src => !isFake dst && placeNonFake isFake src
  | .assignDiscr dst src => !isFake dst && placeNonFake isFake src
  | .assignPtrCoercion dst _ src => !isFake dst && !isFake src
  | .placeMention src => placeNonFake isFake src
  | .storageLive _ => true
  | .storageDead _ => true
  | .ascribeUserType _ | .coverageMarker _ _ | .dropHint _ | .recordDrop _ | .nop => true

def termUsesFakeCleanly (isFake : Nat → Bool) (t : Term) : Bool :=
  match t with
  | .switchInt d _ _ => !isFake d
  | .call _ dst _ _ => !isFake dst
  | .assert cond _ _ _ => !isFake cond
  | .return_ ret => !isFake ret
  | _ => true

def bodyUsesFakeCleanly (isFake : Nat → Bool) (b : Body) : Bool :=
  b.blocks.all fun bb => bb.stmts.all (stmtUsesFakeCleanly isFake) && termUsesFakeCleanly isFake bb.term

def StoresAgreeNonFake (isFake : Nat → Bool) (s1 s2 : List SlotVal) : Prop :=
  ∀ i, isFake i = false → getSlot s1 i = getSlot s2 i

def PtrsNonFake (isFake : Nat → Bool) (store : List SlotVal) : Prop :=
  ∀ i, isFake i = false → ∀ addr, getSlot store i = .ptr addr → isFake addr = false

def CertifiedForFakeRead (cfg : CompileCfg) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0) : Prop :=
  Nat.rec (motive := fun _ => EvalState → Nat → Prop)
    (fun _ _ => True)
    (fun _ rec st stepIdx =>
      match b.blocks[st.bb]? with
      | none => True
      | some bbData =>
        match bbData.stmts[st.stmtIdx]? with
        | some (.fakeRead cause p) =>
          (∃ u, checkFakeReadPlace st.store st.fakeBorrows cause p = .ok u) ∧
          rec { st with stmtIdx := st.stmtIdx + 1 } (stepIdx + 1)
        | some (.assignFakeBorrow dst kind src) =>
          match evalPlaceAddr st.store src with
          | .error _ => False
          | .ok addr =>
            let snapVal := getSlot st.store addr
            let st' := { st with
              stmtIdx := st.stmtIdx + 1
              store := setSlot st.store dst (.ptr addr)
              fakeBorrows := (addr, snapVal, kind) :: st.fakeBorrows }
            rec st' (stepIdx + 1)
        | some s =>
          match stepStmt .analysisGuarded st s with
          | .error _ => True
          | .ok st' => rec st' (stepIdx + 1)
        | none =>
          match stepTerm cfg .analysisGuarded b st bbData.term (oracle stepIdx) with
          | .finished _ _ => True
          | .nextState st' => rec st' (stepIdx + 1))
    fuel st stepIdx

private theorem CertifiedForFakeRead_succ (cfg : CompileCfg) (f : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat) :
    CertifiedForFakeRead cfg (f + 1) b st oracle stepIdx =
      (match b.blocks[st.bb]? with
       | none => True
       | some bbData =>
         match bbData.stmts[st.stmtIdx]? with
         | some (.fakeRead cause p) =>
           (∃ u, checkFakeReadPlace st.store st.fakeBorrows cause p = .ok u) ∧
           CertifiedForFakeRead cfg f b { st with stmtIdx := st.stmtIdx + 1 } oracle (stepIdx + 1)
         | some (.assignFakeBorrow dst kind src) =>
           match evalPlaceAddr st.store src with
           | .error _ => False
           | .ok addr =>
             let snapVal := getSlot st.store addr
             let st' := { st with
               stmtIdx := st.stmtIdx + 1
               store := setSlot st.store dst (.ptr addr)
               fakeBorrows := (addr, snapVal, kind) :: st.fakeBorrows }
             CertifiedForFakeRead cfg f b st' oracle (stepIdx + 1)
         | some s =>
           match stepStmt .analysisGuarded st s with
           | .error _ => True
           | .ok st' => CertifiedForFakeRead cfg f b st' oracle (stepIdx + 1)
         | none =>
           match stepTerm cfg .analysisGuarded b st bbData.term (oracle stepIdx) with
           | .finished _ _ => True
           | .nextState st' => CertifiedForFakeRead cfg f b st' oracle (stepIdx + 1)) := rfl

private theorem setSlot_nonFake_agree (isFake : Nat → Bool) (s1 s2 : List SlotVal)
    (hAg : StoresAgreeNonFake isFake s1 s2) (dst : Nat) (v : SlotVal)
    (hLen : s1.length = s2.length) :
    StoresAgreeNonFake isFake (setSlot s1 dst v) (setSlot s2 dst v) := by
  intro i hi
  induction s1 generalizing isFake s2 dst i with
  | nil =>
    cases s2 with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons x xs ih =>
    cases s2 with
    | nil => cases hLen
    | cons y ys =>
      have hLen' : xs.length = ys.length := Nat.succ.inj hLen
      cases dst with
      | zero =>
        cases i with
        | zero => rfl
        | succ k => exact hAg (k + 1) hi
      | succ dst' =>
        cases i with
        | zero => exact hAg 0 hi
        | succ k =>
          exact ih (fun j => isFake (j + 1)) ys (fun j hj => hAg (j + 1) hj) dst' hLen' k hi

private theorem setSlot_fake_preserves_agree (isFake : Nat → Bool) (s1 s2 : List SlotVal)
    (hAg : StoresAgreeNonFake isFake s1 s2) (dst : Nat) (hFake : isFake dst = true) (v : SlotVal) :
    StoresAgreeNonFake isFake s1 (setSlot s2 dst v) := by
  intro i hi
  rw [hAg i hi]
  have hNe : dst ≠ i := by
    intro hEq
    rw [hEq, hi] at hFake
    exact Bool.noConfusion hFake
  rw [setSlot_preserves_other s2 dst i v hNe]

private theorem setSlot_nonFake_preserves_ptrs (isFake : Nat → Bool) (store : List SlotVal)
    (hPtr : PtrsNonFake isFake store) (dst : Nat) (v : SlotVal)
    (hv : ∀ addr, v = .ptr addr → isFake addr = false) :
    PtrsNonFake isFake (setSlot store dst v) := by
  intro i hi addr hGet
  rcases setSlot_getSlot_cases store dst i v with ⟨_, hSame⟩ | ⟨_, hOld⟩
  · cases hAt : store[dst]? with
    | none =>
      rw [hAt] at hSame; dsimp only at hSame; rw [hSame] at hGet
      exact hPtr i hi addr hGet
    | some _ =>
      rw [hAt] at hSame; dsimp only at hSame; rw [hSame] at hGet
      exact hv addr hGet
  · rw [hOld] at hGet
    exact hPtr i hi addr hGet

private theorem setSlot_fake_preserves_ptrs (isFake : Nat → Bool) (store : List SlotVal)
    (hPtr : PtrsNonFake isFake store) (dst : Nat) (hFake : isFake dst = true) (v : SlotVal) :
    PtrsNonFake isFake (setSlot store dst v) := by
  intro i hi addr hGet
  have hNe : dst ≠ i := by
    intro hEq
    rw [hEq, hi] at hFake
    exact Bool.noConfusion hFake
  rw [setSlot_preserves_other store dst i v hNe] at hGet
  exact hPtr i hi addr hGet

private theorem evalPlaceAddr_agree (isFake : Nat → Bool) (s1 s2 : List SlotVal)
    (hAg : StoresAgreeNonFake isFake s1 s2) (p : Place) (hp : placeNonFake isFake p = true) :
    evalPlaceAddr s1 p = evalPlaceAddr s2 p := by
  cases p with
  | localSlot q =>
    have hq := bool_not_true_eq_false hp
    unfold evalPlaceAddr
    dsimp only
    rw [hAg q hq]
  | derefSlot q =>
    have hq := bool_not_true_eq_false hp
    unfold evalPlaceAddr
    dsimp only
    rw [hAg q hq]

private theorem readValue_agree (isFake : Nat → Bool) (s1 s2 : List SlotVal)
    (hAg : StoresAgreeNonFake isFake s1 s2) (hPtr1 : PtrsNonFake isFake s1)
    (p : Place) (hp : placeNonFake isFake p = true) :
    readValueFromPlace s1 p = readValueFromPlace s2 p := by
  cases p with
  | localSlot q =>
    have hq := bool_not_true_eq_false hp
    unfold readValueFromPlace evalPlaceAddr
    dsimp only
    rw [hAg q hq]
    cases getSlot s2 q with
    | dead => rfl
    | uninit => dsimp only; rw [hAg q hq]
    | scalar _ => dsimp only; rw [hAg q hq]
    | ptr _ => dsimp only; rw [hAg q hq]
    | enumVal _ _ => dsimp only; rw [hAg q hq]
  | derefSlot q =>
    have hq := bool_not_true_eq_false hp
    unfold readValueFromPlace evalPlaceAddr
    dsimp only
    rw [hAg q hq]
    cases hGet : getSlot s2 q with
    | ptr addr =>
      dsimp only
      have hGet1 : getSlot s1 q = .ptr addr := by rw [hAg q hq]; exact hGet
      have hAddr : isFake addr = false := hPtr1 q hq addr hGet1
      rw [hAg addr hAddr]
    | dead => rfl
    | uninit => rfl
    | scalar _ => rfl
    | enumVal _ _ => rfl

private theorem readValueFromPlace_ptr_nonFake (isFake : Nat → Bool) (store : List SlotVal)
    (hPtr : PtrsNonFake isFake store) (p : Place) (hp : placeNonFake isFake p = true)
    (a : Nat) (hRd : readValueFromPlace store p = .ok (.ptr a)) :
    isFake a = false := by
  cases p with
  | localSlot q =>
    have hq := bool_not_true_eq_false hp
    unfold readValueFromPlace evalPlaceAddr at hRd
    dsimp only at hRd
    cases hgp : getSlot store q with
    | dead => rw [hgp] at hRd; cases hRd
    | uninit => rw [hgp] at hRd; dsimp only at hRd; rw [hgp] at hRd; cases hRd
    | scalar _ => rw [hgp] at hRd; dsimp only at hRd; rw [hgp] at hRd; cases hRd
    | enumVal tag nv =>
      rw [hgp] at hRd; dsimp only at hRd; rw [hgp] at hRd
      cases hsv : slotValid (SlotVal.enumVal tag nv) <;> rw [hsv] at hRd <;> cases hRd
    | ptr addr =>
      rw [hgp] at hRd; dsimp only at hRd; rw [hgp] at hRd
      cases hRd
      exact hPtr q hq a hgp
  | derefSlot q =>
    have hq := bool_not_true_eq_false hp
    unfold readValueFromPlace evalPlaceAddr at hRd
    dsimp only at hRd
    cases hgp : getSlot store q with
    | dead => rw [hgp] at hRd; cases hRd
    | uninit => rw [hgp] at hRd; cases hRd
    | scalar _ => rw [hgp] at hRd; cases hRd
    | enumVal _ _ => rw [hgp] at hRd; cases hRd
    | ptr addr =>
      rw [hgp] at hRd; dsimp only at hRd
      cases hsv : slotValid (getSlot store addr) <;> rw [hsv] at hRd
      · cases hRd
      · exact hPtr addr (hPtr q hq addr hgp) a (Except.ok.inj hRd)

private theorem readDiscr_agree (isFake : Nat → Bool) (s1 s2 : List SlotVal)
    (hAg : StoresAgreeNonFake isFake s1 s2) (hPtr1 : PtrsNonFake isFake s1)
    (p : Place) (hp : placeNonFake isFake p = true) :
    readDiscrFromPlace s1 p = readDiscrFromPlace s2 p := by
  unfold readDiscrFromPlace
  rw [readValue_agree isFake s1 s2 hAg hPtr1 p hp]

theorem cleanupPostBorrowck_certified_equiv (isFake : Nat → Bool) (cfg : CompileCfg)
    (fuel : Nat) (b : Body) (stRt stAn : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat)
    (hClean : bodyUsesFakeCleanly isFake b = true)
    (hCert : CertifiedForFakeRead cfg fuel b stAn oracle stepIdx)
    (hBb : stRt.bb = stAn.bb) (hIdx : stRt.stmtIdx = stAn.stmtIdx)
    (hTr : stRt.trace = stAn.trace)
    (hLen : stRt.store.length = stAn.store.length)
    (hAg : StoresAgreeNonFake isFake stRt.store stAn.store)
    (hPtrRt : PtrsNonFake isFake stRt.store)
    (hPtrAn : PtrsNonFake isFake stAn.store) :
    let rRt := runEval cfg .analysisPostCleanup fuel (cleanupPostBorrowck b) stRt oracle stepIdx
    let rAn := runEval cfg .analysisGuarded fuel b stAn oracle stepIdx
    rRt.2 = rAn.2 ∧ rRt.1.trace = rAn.1.trace ∧
    StoresAgreeNonFake isFake rRt.1.store rAn.1.store := by
  induction fuel generalizing stRt stAn stepIdx with
  | zero =>
    exact ⟨rfl, hTr, hAg⟩
  | succ f ih =>
    rw [runEval_succ, runEval_succ]
    dsimp only [cleanupPostBorrowck]
    rw [list_getElem?_map, hBb]
    cases hbb : b.blocks[stAn.bb]? with
    | none =>
      exact ⟨rfl, hTr, hAg⟩
    | some bbData =>
      have hBbClean : bbData.stmts.all (stmtUsesFakeCleanly isFake) = true ∧
          termUsesFakeCleanly isFake bbData.term = true := by
        have hMem := list_getElem?_mem hbb
        have hBlk := list_all_mem_true hClean hMem
        cases hs : bbData.stmts.all (stmtUsesFakeCleanly isFake) <;>
        cases ht : termUsesFakeCleanly isFake bbData.term
        · exfalso; have h1 : (bbData.stmts.all (stmtUsesFakeCleanly isFake) && termUsesFakeCleanly isFake bbData.term) = true := hBlk; rw [hs, ht] at h1; exact Bool.noConfusion h1
        · exfalso; have h1 : (bbData.stmts.all (stmtUsesFakeCleanly isFake) && termUsesFakeCleanly isFake bbData.term) = true := hBlk; rw [hs, ht] at h1; exact Bool.noConfusion h1
        · exfalso; have h1 : (bbData.stmts.all (stmtUsesFakeCleanly isFake) && termUsesFakeCleanly isFake bbData.term) = true := hBlk; rw [hs, ht] at h1; exact Bool.noConfusion h1
        · exact ⟨rfl, rfl⟩
      dsimp only [Option.map, cleanupBlock]
      rw [list_getElem?_map, hIdx]
      cases hst : bbData.stmts[stAn.stmtIdx]? with
      | some s =>
        have hsClean : stmtUsesFakeCleanly isFake s = true :=
          list_all_mem_true hBbClean.1 (list_getElem?_mem hst)
        dsimp only [Option.map]
        cases s with
        | fakeRead cause p =>
          have hCert' : (∃ u, checkFakeReadPlace stAn.store stAn.fakeBorrows cause p = .ok u) ∧
              CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1 } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          rcases hCert'.1 with ⟨u, hu⟩
          cases u
          unfold stepStmt
          dsimp only [cleanupStmt]
          rw [hu]
          dsimp only
          exact ih { stRt with stmtIdx := stRt.stmtIdx + 1 } { stAn with stmtIdx := stAn.stmtIdx + 1 }
            (stepIdx + 1) hCert'.2 hBb (congrArg Nat.succ hIdx) hTr hLen hAg hPtrRt hPtrAn
        | assignFakeBorrow dst kind src =>
          have hSplit : isFake dst = true ∧ placeNonFake isFake src = true := by
            unfold stmtUsesFakeCleanly at hsClean
            dsimp only at hsClean
            exact ⟨bool_and_left_true hsClean, bool_and_right_true hsClean⟩
          have hCert' := hCert
          rw [CertifiedForFakeRead_succ] at hCert'
          rw [hbb] at hCert'; dsimp only at hCert'; rw [hst] at hCert'; dsimp only at hCert'
          cases hev : evalPlaceAddr stAn.store src with
          | error k =>
            rw [hev] at hCert'
            exact False.elim hCert'
          | ok addr =>
            rw [hev] at hCert'
            dsimp only at hCert'
            unfold stepStmt
            dsimp only [cleanupStmt]
            rw [hev]
            dsimp only
            apply ih { stRt with stmtIdx := stRt.stmtIdx + 1 }
              { stAn with
                stmtIdx := stAn.stmtIdx + 1
                store := setSlot stAn.store dst (.ptr addr)
                fakeBorrows := (addr, getSlot stAn.store addr, kind) :: stAn.fakeBorrows }
              (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
            · rw [setSlot_length]; exact hLen
            · exact setSlot_fake_preserves_agree isFake stRt.store stAn.store hAg dst hSplit.1 (.ptr addr)
            · exact hPtrRt
            · exact setSlot_fake_preserves_ptrs isFake stAn.store hPtrAn dst hSplit.1 (.ptr addr)
        | ascribeUserType _ | dropHint _ =>
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1 } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          exact ih { stRt with stmtIdx := stRt.stmtIdx + 1 } { stAn with stmtIdx := stAn.stmtIdx + 1 }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr hLen hAg hPtrRt hPtrAn
        | coverageMarker rem id =>
          cases rem with
          | true =>
            have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1 } oracle (stepIdx + 1) := by
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              exact hCert
            exact ih { stRt with stmtIdx := stRt.stmtIdx + 1 } { stAn with stmtIdx := stAn.stmtIdx + 1 }
              (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr hLen hAg hPtrRt hPtrAn
          | false =>
            have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1 } oracle (stepIdx + 1) := by
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              exact hCert
            exact ih { stRt with stmtIdx := stRt.stmtIdx + 1 } { stAn with stmtIdx := stAn.stmtIdx + 1 }
              (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr hLen hAg hPtrRt hPtrAn
        | nop =>
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1 } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          exact ih { stRt with stmtIdx := stRt.stmtIdx + 1 } { stAn with stmtIdx := stAn.stmtIdx + 1 }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr hLen hAg hPtrRt hPtrAn
        | recordDrop tag =>
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, trace := stAn.trace ++ [tag] } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          exact ih { stRt with stmtIdx := stRt.stmtIdx + 1, trace := stRt.trace ++ [tag] }
            { stAn with stmtIdx := stAn.stmtIdx + 1, trace := stAn.trace ++ [tag] }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) (by rw [hTr]) hLen hAg hPtrRt hPtrAn
        | storageLive id =>
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store id .uninit } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store id .uninit }
            { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store id .uninit }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
          · rw [setSlot_length, setSlot_length]; exact hLen
          · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg id .uninit hLen
          · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt id .uninit (fun _ h => SlotVal.noConfusion h)
          · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn id .uninit (fun _ h => SlotVal.noConfusion h)
        | storageDead id =>
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store id .dead } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store id .dead }
            { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store id .dead }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
          · rw [setSlot_length, setSlot_length]; exact hLen
          · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg id .dead hLen
          · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt id .dead (fun _ h => SlotVal.noConfusion h)
          · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn id .dead (fun _ h => SlotVal.noConfusion h)
        | assignConst dst val =>
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.scalar val) } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store dst (.scalar val) }
            { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.scalar val) }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
          · rw [setSlot_length, setSlot_length]; exact hLen
          · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg dst (.scalar val) hLen
          · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt dst (.scalar val) (fun _ h => SlotVal.noConfusion h)
          · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn dst (.scalar val) (fun _ h => SlotVal.noConfusion h)
        | assignPtr dst addr =>
          have hSplit : isFake dst = false ∧ isFake addr = false := by
            unfold stmtUsesFakeCleanly at hsClean
            dsimp only at hsClean
            exact ⟨bool_not_true_eq_false (bool_and_left_true hsClean), bool_not_true_eq_false (bool_and_right_true hsClean)⟩
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.ptr addr) } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store dst (.ptr addr) }
            { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.ptr addr) }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
          · rw [setSlot_length, setSlot_length]; exact hLen
          · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg dst (.ptr addr) hLen
          · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt dst (.ptr addr) (fun a hEq => by cases hEq; exact hSplit.2)
          · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn dst (.ptr addr) (fun a hEq => by cases hEq; exact hSplit.2)
        | assignEnum dst tag nv =>
          have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.enumVal tag nv) } oracle (stepIdx + 1) := by
            rw [CertifiedForFakeRead_succ] at hCert
            rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
            exact hCert
          apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store dst (.enumVal tag nv) }
            { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.enumVal tag nv) }
            (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
          · rw [setSlot_length, setSlot_length]; exact hLen
          · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg dst (.enumVal tag nv) hLen
          · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt dst (.enumVal tag nv) (fun _ h => SlotVal.noConfusion h)
          · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn dst (.enumVal tag nv) (fun _ h => SlotVal.noConfusion h)
        | assignCopy dst src =>
          have hSrc : placeNonFake isFake src = true := by
            unfold stmtUsesFakeCleanly at hsClean
            dsimp only at hsClean
            exact bool_and_right_true hsClean
          have hReadEq := readValue_agree isFake stRt.store stAn.store hAg hPtrRt src hSrc
          unfold stepStmt
          dsimp only [cleanupStmt]
          rw [hReadEq]
          cases hRd : readValueFromPlace stAn.store src with
          | error k => exact ⟨rfl, hTr, hAg⟩
          | ok v =>
            have hvSafe : ∀ a, v = .ptr a → isFake a = false :=
              fun a hv => readValueFromPlace_ptr_nonFake isFake stAn.store hPtrAn src hSrc a (by rw [hv] at hRd; exact hRd)
            have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst v } oracle (stepIdx + 1) := by
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              unfold stepStmt at hCert
              dsimp only at hCert
              rw [hRd] at hCert
              exact hCert
            apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store dst v }
              { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst v }
              (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
            · rw [setSlot_length, setSlot_length]; exact hLen
            · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg dst v hLen
            · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt dst v hvSafe
            · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn dst v hvSafe
        | assignDiscr dst src =>
          have hSrc : placeNonFake isFake src = true := by
            unfold stmtUsesFakeCleanly at hsClean
            dsimp only at hsClean
            exact bool_and_right_true hsClean
          have hReadEq := readDiscr_agree isFake stRt.store stAn.store hAg hPtrRt src hSrc
          unfold stepStmt
          dsimp only [cleanupStmt]
          rw [hReadEq]
          cases hRd : readDiscrFromPlace stAn.store src with
          | error k => exact ⟨rfl, hTr, hAg⟩
          | ok tag =>
            have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.scalar tag) } oracle (stepIdx + 1) := by
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              unfold stepStmt at hCert
              dsimp only at hCert
              rw [hRd] at hCert
              exact hCert
            apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store dst (.scalar tag) }
              { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst (.scalar tag) }
              (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
            · rw [setSlot_length, setSlot_length]; exact hLen
            · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg dst (.scalar tag) hLen
            · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt dst (.scalar tag) (fun _ h => SlotVal.noConfusion h)
            · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn dst (.scalar tag) (fun _ h => SlotVal.noConfusion h)
        | assignPtrCoercion dst kind srcLocal =>
          have hSrc : placeNonFake isFake (.localSlot srcLocal) = true := by
            unfold stmtUsesFakeCleanly at hsClean
            dsimp only at hsClean
            exact bool_and_right_true hsClean
          have hSrcNonFake := bool_not_true_eq_false hSrc
          have hReadEq := readValue_agree isFake stRt.store stAn.store hAg hPtrRt (.localSlot srcLocal) hSrc
          have hCleanKind : cleanupStmt (Stmt.assignPtrCoercion dst kind srcLocal) = Stmt.assignPtrCoercion dst .ptrToPtr srcLocal := by
            cases kind <;> rfl
          unfold stepStmt
          rw [hCleanKind]
          dsimp only
          rw [hReadEq]
          cases hRd : readValueFromPlace stAn.store (.localSlot srcLocal) with
          | error k => exact ⟨rfl, hTr, hAg⟩
          | ok v =>
            have hvSafe : ∀ a, v = .ptr a → isFake a = false :=
              fun a hv => readValueFromPlace_ptr_nonFake isFake stAn.store hPtrAn (.localSlot srcLocal) hSrc a (by rw [hv] at hRd; exact hRd)
            have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst v } oracle (stepIdx + 1) := by
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              unfold stepStmt at hCert
              dsimp only at hCert
              rw [hRd] at hCert
              exact hCert
            apply ih { stRt with stmtIdx := stRt.stmtIdx + 1, store := setSlot stRt.store dst v }
              { stAn with stmtIdx := stAn.stmtIdx + 1, store := setSlot stAn.store dst v }
              (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr
            · rw [setSlot_length, setSlot_length]; exact hLen
            · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg dst v hLen
            · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt dst v hvSafe
            · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn dst v hvSafe
        | placeMention p =>
          have hP : placeNonFake isFake p = true := hsClean
          have hAddrEq := evalPlaceAddr_agree isFake stRt.store stAn.store hAg p hP
          unfold stepStmt
          dsimp only [cleanupStmt]
          rw [hAddrEq]
          cases hEv : evalPlaceAddr stAn.store p with
          | error k => exact ⟨rfl, hTr, hAg⟩
          | ok _ =>
            have hCert' : CertifiedForFakeRead cfg f b { stAn with stmtIdx := stAn.stmtIdx + 1 } oracle (stepIdx + 1) := by
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              unfold stepStmt at hCert
              dsimp only at hCert
              rw [hEv] at hCert
              exact hCert
            exact ih { stRt with stmtIdx := stRt.stmtIdx + 1 } { stAn with stmtIdx := stAn.stmtIdx + 1 }
              (stepIdx + 1) hCert' hBb (congrArg Nat.succ hIdx) hTr hLen hAg hPtrRt hPtrAn
      | none =>
        dsimp only [Option.map]
        have hTermClean := hBbClean.2
        have hCert' := hCert
        rw [CertifiedForFakeRead_succ] at hCert'
        rw [hbb] at hCert'; dsimp only at hCert'; rw [hst] at hCert'; dsimp only at hCert'
        have hAbi : bodyCanUnwind cfg { blocks := b.blocks.map cleanupBlock, bodyAbi := b.bodyAbi, bodyIsForeign := b.bodyIsForeign, hasUserTypeAnnots := false } = bodyCanUnwind cfg b := rfl
        cases hT : bbData.term with
        | goto tgt =>
          rw [hT] at hCert'
          unfold stepTerm at hCert'; dsimp only at hCert'
          exact ih { stRt with bb := tgt, stmtIdx := 0 } { stAn with bb := tgt, stmtIdx := 0 }
            (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
        | falseEdge rt it =>
          rw [hT] at hCert'
          unfold stepTerm at hCert'; dsimp only at hCert'
          exact ih { stRt with bb := rt, stmtIdx := 0 } { stAn with bb := rt, stmtIdx := 0 }
            (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
        | falseUnwind rt u =>
          rw [hT] at hCert'
          unfold stepTerm at hCert'; dsimp only at hCert'
          exact ih { stRt with bb := rt, stmtIdx := 0 } { stAn with bb := rt, stmtIdx := 0 }
            (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
        | switchInt d cases otherwise =>
          have hdNonFake : placeNonFake isFake (.localSlot d) = true := by
            rw [hT] at hTermClean; exact hTermClean
          have hRdEq := readDiscr_agree isFake stRt.store stAn.store hAg hPtrRt (.localSlot d) hdNonFake
          unfold stepTerm
          dsimp only [cleanupTerm]
          rw [hRdEq]
          cases hRd : readDiscrFromPlace stAn.store (.localSlot d) with
          | error _ => exact ⟨rfl, hTr, hAg⟩
          | ok dv =>
            rw [hT] at hCert'
            unfold stepTerm at hCert'
            dsimp only at hCert'
            rw [hRd] at hCert'
            exact ih { stRt with bb := lookupSwitchTarget dv cases otherwise, stmtIdx := 0 }
              { stAn with bb := lookupSwitchTarget dv cases otherwise, stmtIdx := 0 }
              (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
        | call c dst tgt u =>
          rw [hT] at hCert'
          unfold stepTerm
          dsimp only [cleanupTerm]
          rw [hAbi]
          cases hUnw : (oracle stepIdx).unwind with
          | true =>
            cases u with
            | cleanup pad =>
              unfold takeUnwind
              dsimp only
              unfold stepTerm at hCert'
              dsimp only at hCert'
              rw [hUnw] at hCert'
              exact ih { stRt with bb := pad, stmtIdx := 0 } { stAn with bb := pad, stmtIdx := 0 }
                (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
            | terminate r => exact ⟨rfl, hTr, hAg⟩
            | unreachable => exact ⟨rfl, hTr, hAg⟩
            | continue_ =>
              cases bodyCanUnwind cfg b <;> exact ⟨rfl, hTr, hAg⟩
          | false =>
            unfold stepTerm at hCert'
            dsimp only at hCert'
            rw [hUnw] at hCert'
            apply ih { stRt with bb := tgt, stmtIdx := 0, store := setSlot stRt.store dst (.scalar (oracle stepIdx).retVal) }
              { stAn with bb := tgt, stmtIdx := 0, store := setSlot stAn.store dst (.scalar (oracle stepIdx).retVal) }
              (stepIdx + 1) hCert' rfl rfl hTr
            · rw [setSlot_length, setSlot_length]; exact hLen
            · exact setSlot_nonFake_agree isFake stRt.store stAn.store hAg dst (.scalar (oracle stepIdx).retVal) hLen
            · exact setSlot_nonFake_preserves_ptrs isFake stRt.store hPtrRt dst (.scalar (oracle stepIdx).retVal) (fun _ h => SlotVal.noConfusion h)
            · exact setSlot_nonFake_preserves_ptrs isFake stAn.store hPtrAn dst (.scalar (oracle stepIdx).retVal) (fun _ h => SlotVal.noConfusion h)
        | drop lId tag tgt u =>
          rw [hT] at hCert'
          unfold stepTerm
          dsimp only [cleanupTerm]
          rw [hAbi]
          cases hUnw : (oracle stepIdx).unwind with
          | true =>
            dsimp only
            cases u with
            | cleanup pad =>
              unfold takeUnwind
              dsimp only
              unfold stepTerm at hCert'
              dsimp only at hCert'
              rw [hUnw] at hCert'
              exact ih { stRt with bb := pad, stmtIdx := 0, trace := stRt.trace ++ [tag] }
                { stAn with bb := pad, stmtIdx := 0, trace := stAn.trace ++ [tag] }
                (stepIdx + 1) hCert' rfl rfl (by rw [hTr]) hLen hAg hPtrRt hPtrAn
            | terminate r => unfold takeUnwind; dsimp only; exact ⟨rfl, by rw [hTr], hAg⟩
            | unreachable => unfold takeUnwind; dsimp only; exact ⟨rfl, by rw [hTr], hAg⟩
            | continue_ =>
              unfold takeUnwind; dsimp only [EvalMode.isRuntimeUnwind]
              cases bodyCanUnwind cfg b <;> dsimp only <;> exact ⟨rfl, by rw [hTr], hAg⟩
          | false =>
            unfold stepTerm at hCert'
            dsimp only at hCert'
            rw [hUnw] at hCert'
            exact ih { stRt with bb := tgt, stmtIdx := 0, trace := stRt.trace ++ [tag] }
              { stAn with bb := tgt, stmtIdx := 0, trace := stAn.trace ++ [tag] }
              (stepIdx + 1) hCert' rfl rfl (by rw [hTr]) hLen hAg hPtrRt hPtrAn
        | assert cond exp tgt u =>
          have hcNonFake : placeNonFake isFake (.localSlot cond) = true := by
            rw [hT] at hTermClean; exact hTermClean
          have hRdEq := readDiscr_agree isFake stRt.store stAn.store hAg hPtrRt (.localSlot cond) hcNonFake
          unfold stepTerm
          dsimp only [cleanupTerm]
          rw [hAbi, hRdEq]
          cases hRd : readDiscrFromPlace stAn.store (.localSlot cond) with
          | error _ => exact ⟨rfl, hTr, hAg⟩
          | ok dv =>
            dsimp only
            cases hCond : ((dv != 0) == exp) with
            | true =>
              dsimp only
              rw [hT] at hCert'
              unfold stepTerm at hCert'
              dsimp only at hCert'
              rw [hRd] at hCert'
              dsimp only at hCert'
              rw [hCond] at hCert'
              exact ih { stRt with bb := tgt, stmtIdx := 0 } { stAn with bb := tgt, stmtIdx := 0 }
                (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
            | false =>
              dsimp only
              cases u with
              | cleanup pad =>
                rw [hT] at hCert'
                unfold stepTerm takeUnwind at hCert'
                dsimp only at hCert'
                rw [hRd] at hCert'
                dsimp only at hCert'
                rw [hCond] at hCert'
                exact ih { stRt with bb := pad, stmtIdx := 0 } { stAn with bb := pad, stmtIdx := 0 }
                  (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
              | terminate _ => unfold takeUnwind; dsimp only; exact ⟨rfl, hTr, hAg⟩
              | unreachable => unfold takeUnwind; dsimp only; exact ⟨rfl, hTr, hAg⟩
              | continue_ =>
                unfold takeUnwind; dsimp only [EvalMode.isRuntimeUnwind]
                cases bodyCanUnwind cfg b <;> dsimp only <;> exact ⟨rfl, hTr, hAg⟩
        | inlineAsm m tgt u =>
          rw [hT] at hCert'
          unfold stepTerm
          dsimp only [cleanupTerm]
          rw [hAbi]
          cases hUnw : (oracle stepIdx).unwind with
          | true =>
            cases u with
            | cleanup pad =>
              unfold takeUnwind
              dsimp only
              unfold stepTerm at hCert'
              dsimp only at hCert'
              rw [hUnw] at hCert'
              exact ih { stRt with bb := pad, stmtIdx := 0 } { stAn with bb := pad, stmtIdx := 0 }
                (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
            | terminate _ => exact ⟨rfl, hTr, hAg⟩
            | unreachable => exact ⟨rfl, hTr, hAg⟩
            | continue_ => cases bodyCanUnwind cfg b <;> exact ⟨rfl, hTr, hAg⟩
          | false =>
            unfold stepTerm at hCert'
            dsimp only at hCert'
            rw [hUnw] at hCert'
            exact ih { stRt with bb := tgt, stmtIdx := 0 } { stAn with bb := tgt, stmtIdx := 0 }
              (stepIdx + 1) hCert' rfl rfl hTr hLen hAg hPtrRt hPtrAn
        | return_ ret =>
          have hrNonFake : placeNonFake isFake (.localSlot ret) = true := by
            rw [hT] at hTermClean; exact hTermClean
          have hRdEq := readValue_agree isFake stRt.store stAn.store hAg hPtrRt (.localSlot ret) hrNonFake
          unfold stepTerm
          dsimp only [cleanupTerm]
          rw [hRdEq]
          cases readValueFromPlace stAn.store (.localSlot ret) with
          | error _ => exact ⟨rfl, hTr, hAg⟩
          | ok v => cases v <;> exact ⟨rfl, hTr, hAg⟩
        | unwindResume =>
          unfold stepTerm
          dsimp only [cleanupTerm]
          rw [hAbi]
          cases bodyCanUnwind cfg b <;> exact ⟨rfl, hTr, hAg⟩
        | unwindTerminate r => exact ⟨rfl, hTr, hAg⟩
        | unreachable => exact ⟨rfl, hTr, hAg⟩

private theorem certified_succ_some_nonFake (cfg : CompileCfg) (f : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat)
    (bbData : BasicBlock) (hbb : b.blocks[st.bb]? = some bbData)
    (s : Stmt) (hst : bbData.stmts[st.stmtIdx]? = some s) (hFake : s.isFakeOp = false)
    (hOk : match stepStmt .analysisGuarded st s with
           | .error _ => True
           | .ok st' => CertifiedForFakeRead cfg f b st' oracle (stepIdx + 1)) :
    CertifiedForFakeRead cfg (f + 1) b st oracle stepIdx := by
  rw [CertifiedForFakeRead_succ]
  rw [hbb]; dsimp only; rw [hst]
  cases s with
  | fakeRead _ _ => cases hFake
  | assignFakeBorrow _ _ _ => cases hFake
  | _ => exact hOk

theorem cleanupPostBorrowck_certified_iff (cfg : CompileCfg) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0) :
    CertifiedForFakeRead cfg fuel b st oracle stepIdx ↔
      (runEval cfg .analysisGuarded fuel b st oracle stepIdx).2 ≠ .fault .ubFakeReadViolation := by
  constructor
  · intro hCert
    induction fuel generalizing st stepIdx with
    | zero =>
      rw [runEval_zero]
      exact Outcome.noConfusion
    | succ f ih =>
      rw [runEval_succ]
      cases hbb : b.blocks[st.bb]? with
      | none =>
        dsimp only
        exact fun h => FaultKind.noConfusion (Outcome.fault.inj h)
      | some bbData =>
        dsimp only
        cases hst : bbData.stmts[st.stmtIdx]? with
        | some s =>
          dsimp only
          cases hFake : s.isFakeOp with
          | true =>
            cases s with
            | fakeRead cause p =>
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              rcases hCert with ⟨⟨u, hu⟩, hCert'⟩
              cases u
              unfold stepStmt
              dsimp only
              rw [hu]
              exact ih _ _ hCert'
            | assignFakeBorrow dst kind src =>
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
              cases hev : evalPlaceAddr st.store src with
              | error k =>
                rw [hev] at hCert
                exact False.elim hCert
              | ok addr =>
                rw [hev] at hCert
                dsimp only at hCert
                unfold stepStmt
                dsimp only
                rw [hev]
                dsimp only
                exact ih _ _ hCert
            | _ => cases hFake
          | false =>
            have hCert' :
                (match stepStmt .analysisGuarded st s with
                 | .error _ => True
                 | .ok st' => CertifiedForFakeRead cfg f b st' oracle (stepIdx + 1)) := by
              rw [CertifiedForFakeRead_succ] at hCert
              rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert
              cases s with
              | fakeRead _ _ => cases hFake
              | assignFakeBorrow _ _ _ => cases hFake
              | _ => dsimp only at hCert; exact hCert
            cases hSt : stepStmt .analysisGuarded st s with
            | error k =>
              have hk := stepStmt_nonFake_ne_fakeReadUb st s k hFake hSt
              intro hEq
              exact hk (Outcome.fault.inj hEq)
            | ok st' =>
              rw [hSt] at hCert'
              exact ih st' (stepIdx + 1) hCert'
        | none =>
          dsimp only
          rw [CertifiedForFakeRead_succ] at hCert
          rw [hbb] at hCert; dsimp only at hCert; rw [hst] at hCert; dsimp only at hCert
          cases hTm : stepTerm cfg .analysisGuarded b st bbData.term (oracle stepIdx) with
          | finished out st' =>
            cases hTerm : bbData.term with
            | goto _ | falseEdge _ _ | falseUnwind _ _ =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm; cases hTm
            | switchInt d cases oth =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm
              cases hRd : readDiscrFromPlace st.store (.localSlot d) with
              | error k =>
                rw [hRd] at hTm; dsimp only at hTm; cases hTm
                intro hEq; exact readDiscrFromPlace_ne_fakeReadUb st.store (.localSlot d) k hRd (Outcome.fault.inj hEq)
              | ok _ => rw [hRd] at hTm; dsimp only at hTm; cases hTm
            | call _ _ _ u =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm
              cases hUnw : (oracle stepIdx).unwind <;> rw [hUnw] at hTm <;> dsimp only at hTm
              · cases hTm
              · unfold takeUnwind at hTm
                cases u with
                | cleanup _ => dsimp only at hTm; cases hTm
                | terminate _ => dsimp only at hTm; cases hTm; exact Outcome.noConfusion
                | unreachable => dsimp only at hTm; cases hTm; exact fun h => FaultKind.noConfusion (Outcome.fault.inj h)
                | continue_ =>
                  dsimp only at hTm
                  cases hBcu : bodyCanUnwind cfg b <;> rw [hBcu] at hTm <;> dsimp only at hTm <;>
                    cases hTm <;> exact Outcome.noConfusion
            | drop _ _ _ u =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm
              cases hUnw : (oracle stepIdx).unwind <;> rw [hUnw] at hTm <;> dsimp only at hTm
              · cases hTm
              · unfold takeUnwind at hTm
                cases u with
                | cleanup _ => dsimp only at hTm; cases hTm
                | terminate _ => dsimp only at hTm; cases hTm; exact Outcome.noConfusion
                | unreachable => dsimp only at hTm; cases hTm; exact fun h => FaultKind.noConfusion (Outcome.fault.inj h)
                | continue_ =>
                  dsimp only at hTm
                  cases hBcu : bodyCanUnwind cfg b <;> rw [hBcu] at hTm <;> dsimp only at hTm <;>
                    cases hTm <;> exact Outcome.noConfusion
            | assert cond exp _ u =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm
              cases hRd : readDiscrFromPlace st.store (.localSlot cond) with
              | error k =>
                rw [hRd] at hTm; cases hTm
                intro hEq; exact readDiscrFromPlace_ne_fakeReadUb st.store (.localSlot cond) k hRd (Outcome.fault.inj hEq)
              | ok dv =>
                rw [hRd] at hTm; dsimp only at hTm
                cases hC : ((dv != 0) == exp) <;> rw [hC] at hTm <;> dsimp only at hTm
                · unfold takeUnwind at hTm
                  cases u with
                  | cleanup _ => dsimp only at hTm; cases hTm
                  | terminate _ => dsimp only at hTm; cases hTm; exact Outcome.noConfusion
                  | unreachable => dsimp only at hTm; cases hTm; exact fun h => FaultKind.noConfusion (Outcome.fault.inj h)
                  | continue_ =>
                    dsimp only at hTm
                    cases hBcu : bodyCanUnwind cfg b <;> rw [hBcu] at hTm <;> dsimp only at hTm <;>
                      cases hTm <;> exact Outcome.noConfusion
                · cases hTm
            | inlineAsm _ _ u =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm
              cases hUnw : (oracle stepIdx).unwind <;> rw [hUnw] at hTm <;> dsimp only at hTm
              · cases hTm
              · unfold takeUnwind at hTm
                cases u with
                | cleanup _ => dsimp only at hTm; cases hTm
                | terminate _ => dsimp only at hTm; cases hTm; exact Outcome.noConfusion
                | unreachable => dsimp only at hTm; cases hTm; exact fun h => FaultKind.noConfusion (Outcome.fault.inj h)
                | continue_ =>
                  dsimp only at hTm
                  cases hBcu : bodyCanUnwind cfg b <;> rw [hBcu] at hTm <;> dsimp only at hTm <;>
                    cases hTm <;> exact Outcome.noConfusion
            | return_ ret =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm
              cases hRv : readValueFromPlace st.store (.localSlot ret) with
              | error k =>
                rw [hRv] at hTm; cases hTm
                intro hEq; exact readValueFromPlace_ne_fakeReadUb st.store (.localSlot ret) k hRv (Outcome.fault.inj hEq)
              | ok v =>
                rw [hRv] at hTm
                cases v with
                | scalar _ | enumVal _ _ => dsimp only at hTm; cases hTm; exact Outcome.noConfusion
                | dead | uninit | ptr _ => dsimp only at hTm; cases hTm; exact fun h => FaultKind.noConfusion (Outcome.fault.inj h)
            | unwindResume =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; dsimp only at hTm
              cases hBcu : bodyCanUnwind cfg b <;> rw [hBcu] at hTm <;> dsimp only at hTm <;>
                cases hTm <;> exact Outcome.noConfusion
            | unwindTerminate _ => rw [hTerm] at hTm; unfold stepTerm at hTm; cases hTm; exact Outcome.noConfusion
            | unreachable =>
              rw [hTerm] at hTm; unfold stepTerm at hTm; cases hTm
              exact fun h => FaultKind.noConfusion (Outcome.fault.inj h)
          | nextState st' =>
            rw [hTm] at hCert
            exact ih st' (stepIdx + 1) hCert
  · intro hNoUb
    induction fuel generalizing st stepIdx with
    | zero => trivial
    | succ f ih =>
      cases hbb : b.blocks[st.bb]? with
      | none => rw [CertifiedForFakeRead_succ, hbb]; trivial
      | some bbData =>
        cases hst : bbData.stmts[st.stmtIdx]? with
        | some s =>
          have hRun := hNoUb
          rw [runEval_succ] at hRun
          rw [hbb] at hRun; dsimp only at hRun; rw [hst] at hRun; dsimp only at hRun
          cases hFake : s.isFakeOp with
          | true =>
            rw [CertifiedForFakeRead_succ]
            rw [hbb]; dsimp only; rw [hst]
            cases s with
            | fakeRead cause p =>
              dsimp only
              unfold stepStmt at hRun
              dsimp only at hRun
              cases hChk : checkFakeReadPlace st.store st.fakeBorrows cause p with
              | error _ =>
                rw [hChk] at hRun
                exact False.elim (hRun rfl)
              | ok u =>
                cases u
                rw [hChk] at hRun
                exact ⟨⟨(), rfl⟩, ih _ _ hRun⟩
            | assignFakeBorrow dst kind src =>
              dsimp only
              unfold stepStmt at hRun
              dsimp only at hRun
              cases hEv : evalPlaceAddr st.store src with
              | error _ =>
                rw [hEv] at hRun
                exact False.elim (hRun rfl)
              | ok addr =>
                rw [hEv] at hRun
                exact ih _ _ hRun
            | _ => cases hFake
          | false =>
            have hRunStep :
                (match stepStmt .analysisGuarded st s with
                 | .error k => (st, Outcome.fault k)
                 | .ok st' => runEval cfg .analysisGuarded f b st' oracle (stepIdx + 1)).2 ≠ .fault .ubFakeReadViolation := hRun
            apply certified_succ_some_nonFake cfg f b st oracle stepIdx bbData hbb s hst hFake
            cases hSt : stepStmt .analysisGuarded st s with
            | error _ => trivial
            | ok st' =>
              rw [hSt] at hRunStep
              exact ih st' (stepIdx + 1) hRunStep
        | none =>
          rw [CertifiedForFakeRead_succ]
          rw [hbb]; dsimp only; rw [hst]; dsimp only
          have hRun := hNoUb
          rw [runEval_succ] at hRun
          rw [hbb] at hRun; dsimp only at hRun; rw [hst] at hRun; dsimp only at hRun
          cases hTm : stepTerm cfg .analysisGuarded b st bbData.term (oracle stepIdx) with
          | finished _ _ => trivial
          | nextState st' =>
            rw [hTm] at hRun
            exact ih st' (stepIdx + 1) hRun

/-! ## 8. `PlaceMention` Semantics & `RemovePlaceMention` (`-Zmir-preserve-ub`) -/

theorem placeMention_ignores_invalid_pointee :
    stepStmt .runtime
      { bb := 0, stmtIdx := 0, store := [.ptr 1, .enumVal 2 2], fakeBorrows := [], trace := [] }
      (.placeMention (.derefSlot 0))
    = .ok { bb := 0, stmtIdx := 1, store := [.ptr 1, .enumVal 2 2], fakeBorrows := [], trace := [] } := rfl

theorem assignCopy_rejects_invalid_pointee :
    stepStmt .runtime
      { bb := 0, stmtIdx := 0, store := [.ptr 1, .enumVal 2 2, .dead], fakeBorrows := [], trace := [] }
      (.assignCopy 2 (.derefSlot 0))
    = .error .ubInvalidValue := rfl

theorem placeMention_checks_pointer_local :
    stepStmt .runtime
      { bb := 0, stmtIdx := 0, store := [.uninit], fakeBorrows := [], trace := [] }
      (.placeMention (.derefSlot 0))
    = .error .ubInvalidPtrDeref := rfl

/-- Step-level statement-list refinement for `RemovePlaceMention`:
if executing all statements of a block in `.runtime` mode (under `-Zmir-preserve-ub=yes`,
i.e., `removePlaceMention true`) succeeds without faulting, then executing the
`RemovePlaceMention`-filtered statements (`removePlaceMention false`) produces the
exact same final `store`, `trace`, and `bb`! -/
noncomputable def execStmtList (mode : EvalMode) (st : EvalState) (stmts : List Stmt) : Except FaultKind EvalState :=
  List.rec (motive := fun _ => EvalState → Except FaultKind EvalState)
    (fun st => .ok st)
    (fun s _ rec st =>
      match stepStmt mode st s with
      | .error k => .error k
      | .ok st' => rec st')
    stmts st

private theorem execStmtList_cons (mode : EvalMode) (st : EvalState) (s : Stmt) (rest : List Stmt) :
    execStmtList mode st (s :: rest) =
      match stepStmt mode st s with
      | .error k => .error k
      | .ok st' => execStmtList mode st' rest := rfl

private theorem stepStmt_runtime_congr (st1 st2 st1' : EvalState) (s : Stmt)
    (hSame : st1.store = st2.store ∧ st1.trace = st2.trace ∧ st1.bb = st2.bb)
    (hOk : stepStmt .runtime st1 s = .ok st1') :
    ∃ st2', stepStmt .runtime st2 s = .ok st2' ∧
      st1'.store = st2'.store ∧ st1'.trace = st2'.trace ∧ st1'.bb = st2'.bb := by
  cases s with
  | nop | storageLive _ | storageDead _ | assignConst _ _ | assignPtr _ _ | assignEnum _ _ _ =>
    unfold stepStmt at hOk ⊢; cases hOk
    exact ⟨_, rfl, by rw [hSame.1], hSame.2.1, hSame.2.2⟩
  | recordDrop tag =>
    unfold stepStmt at hOk ⊢; cases hOk
    exact ⟨_, rfl, hSame.1, by rw [hSame.2.1], hSame.2.2⟩
  | assignCopy dst src =>
    unfold stepStmt at hOk ⊢; dsimp only at hOk ⊢
    rw [hSame.1] at hOk
    cases hRd : readValueFromPlace st2.store src <;> rw [hRd] at hOk <;> cases hOk
    exact ⟨_, rfl, rfl, hSame.2.1, hSame.2.2⟩
  | assignDiscr dst src =>
    unfold stepStmt at hOk ⊢; dsimp only at hOk ⊢
    rw [hSame.1] at hOk
    cases hRd : readDiscrFromPlace st2.store src <;> rw [hRd] at hOk <;> cases hOk
    exact ⟨_, rfl, rfl, hSame.2.1, hSame.2.2⟩
  | assignPtrCoercion dst kind srcLocal =>
    unfold stepStmt at hOk ⊢; dsimp only at hOk ⊢
    cases kind with
    | arrayToPtr | mutToConstPtr => cases hOk
    | ptrToPtr =>
      rw [hSame.1] at hOk
      cases hRd : readValueFromPlace st2.store (.localSlot srcLocal) <;> rw [hRd] at hOk <;> cases hOk
      exact ⟨_, rfl, rfl, hSame.2.1, hSame.2.2⟩
  | placeMention p =>
    unfold stepStmt at hOk ⊢; dsimp only at hOk ⊢
    rw [hSame.1] at hOk
    cases hEv : evalPlaceAddr st2.store p <;> rw [hEv] at hOk <;> cases hOk
    exact ⟨_, rfl, rfl, hSame.2.1, hSame.2.2⟩
  | coverageMarker rem _ =>
    unfold stepStmt at hOk ⊢; dsimp only at hOk ⊢
    cases rem with
    | true => cases hOk
    | false =>
      cases hOk
      exact ⟨_, rfl, hSame.1, hSame.2.1, hSame.2.2⟩
  | ascribeUserType _ | dropHint _ | assignFakeBorrow _ _ _ | fakeRead _ _ =>
    unfold stepStmt at hOk; dsimp only at hOk; cases hOk

theorem execStmtList_removePlaceMention_refines (st1 st2 : EvalState) (stmts : List Stmt)
    (hSame : st1.store = st2.store ∧ st1.trace = st2.trace ∧ st1.bb = st2.bb)
    (hOk : ∃ st1', execStmtList .runtime st1 stmts = .ok st1') :
    ∃ st2',
      execStmtList .runtime st2 (stmts.filter keepNonPlaceMention) = .ok st2' ∧
      (match execStmtList .runtime st1 stmts with
       | .ok final1 => final1.store = st2'.store ∧ final1.trace = st2'.trace ∧ final1.bb = st2'.bb
       | .error _ => False) := by
  induction stmts generalizing st1 st2 with
  | nil =>
    exact ⟨st2, rfl, hSame⟩
  | cons s rest ih =>
    rcases hOk with ⟨st1Final, hOk⟩
    rw [execStmtList_cons] at hOk
    cases hStep : stepStmt .runtime st1 s with
    | error k =>
      rw [hStep] at hOk
      cases hOk
    | ok st1' =>
      rw [hStep] at hOk
      cases hKeep : keepNonPlaceMention s with
      | false =>
        have hEqState : st1'.store = st2.store ∧ st1'.trace = st2.trace ∧ st1'.bb = st2.bb := by
          cases s with
          | placeMention p =>
            unfold stepStmt at hStep
            dsimp only at hStep
            cases hEv : evalPlaceAddr st1.store p <;> rw [hEv] at hStep
            · cases hStep
            · cases hStep; exact hSame
          | nop =>
            unfold stepStmt at hStep
            cases hStep; exact hSame
          | _ => cases hKeep
        have hNext := ih st1' st2 hEqState ⟨st1Final, hOk⟩
        rcases hNext with ⟨st2', hFilt, hRel⟩
        refine ⟨st2', ?_, ?_⟩
        · simp only [List.filter, hKeep]
          exact hFilt
        · rw [execStmtList_cons]
          rw [hStep]
          exact hRel
      | true =>
        rcases stepStmt_runtime_congr st1 st2 st1' s hSame hStep with ⟨st2Mid, hS2, hEqMid⟩
        have hNext := ih st1' st2Mid hEqMid ⟨st1Final, hOk⟩
        rcases hNext with ⟨st2', hFilt, hRel⟩
        refine ⟨st2', ?_, ?_⟩
        · simp only [List.filter, hKeep]
          rw [execStmtList_cons]
          rw [hS2]
          exact hFilt
        · rw [execStmtList_cons]
          rw [hStep]
          exact hRel

/-! ## 9. `AbortUnwindingCalls`: Non-Panicking Equivalence, Panicking Subsumption, & Dead-Block Compaction -/

def termNormalTarget (t : Term) : Option Nat :=
  match t with
  | .goto tgt => some tgt
  | .call _ _ tgt _ => some tgt
  | .drop _ _ tgt _ => some tgt
  | .assert _ _ tgt _ => some tgt
  | .inlineAsm _ tgt _ => some tgt
  | _ => none

/-- Well-formedness of runtime MIR entering `AbortUnwindingCalls` (reflecting `validate.rs` L140–276):
- Every normal block's normal targets are non-cleanup in-bounds blocks, and its unwind edges (`cleanup bb`)
  target in-bounds cleanup blocks (`isCleanup = true`); normal blocks never terminate in `unwindResume`;
- Every cleanup block stays inside cleanup blocks (`isCleanup = true`), never ends in `.return_`,
  and has `.unreachable` or `.terminate .inCleanup` on any inner unwind action. -/
def wfBlockForAbort (blocks : List BasicBlock) (bb : BasicBlock) : Bool :=
  let n := blocks.length
  let inBounds (i : Nat) : Bool := Nat.ble (i + 1) n
  let checkNormal (i : Nat) : Bool :=
    match blocks[i]? with
    | some b => !b.isCleanup
    | none => false
  let checkCleanup (i : Nat) : Bool :=
    match blocks[i]? with
    | some b => b.isCleanup
    | none => false
  let termInBounds := (termSuccs bb.term).all inBounds
  match !termInBounds with
  | true => false
  | false =>
    match bb.isCleanup with
    | true =>
      match bb.term with
      | .return_ _ => false
      | .goto tgt => checkCleanup tgt
      | .switchInt _ cases oth => (cases.map Prod.snd).all checkCleanup && checkCleanup oth
      | .call _ _ tgt u => checkCleanup tgt && (u == .unreachable || u == .terminate .inCleanup)
      | .drop _ _ tgt u => checkCleanup tgt && (u == .unreachable || u == .terminate .inCleanup)
      | .assert _ _ tgt u => checkCleanup tgt && (u == .unreachable || u == .terminate .inCleanup)
      | .inlineAsm _ tgt u => checkCleanup tgt && (u == .unreachable || u == .terminate .inCleanup)
      | .unwindResume | .unwindTerminate _ | .unreachable => true
      | .falseEdge _ _ | .falseUnwind _ _ => false
    | false =>
    match bb.term with
    | .unwindResume | .unwindTerminate _ | .falseEdge _ _ | .falseUnwind _ _ => false
    | .goto tgt => checkNormal tgt
    | .switchInt _ cases oth => (cases.map Prod.snd).all checkNormal && checkNormal oth
    | .call _ _ tgt u =>
      checkNormal tgt && match u with | .cleanup pad => checkCleanup pad | _ => true
    | .drop _ _ tgt u =>
      checkNormal tgt && match u with | .cleanup pad => checkCleanup pad | _ => true
    | .assert _ _ tgt u =>
      checkNormal tgt && match u with | .cleanup pad => checkCleanup pad | _ => true
    | .inlineAsm _ tgt u =>
      checkNormal tgt && match u with | .cleanup pad => checkCleanup pad | _ => true
    | .return_ _ | .unreachable => true

def wfBodyForAbort (b : Body) : Bool :=
  b.blocks.all (wfBlockForAbort b.blocks)

/-- ABI-respecting execution environment:
any `call`, `drop`, `assert`, or `inlineAsm` whose `termCanUnwind cfg t = some false`
(e.g., non-unwinding C-ABI callee, or Rust `FnDef` under `-C panic=abort`)
does not unwind across that call boundary (and if `!cfg.targetSupportsUnwinding`, nothing unwinds). -/
def OracleRespectsAbi (cfg : CompileCfg) (b : Body) (st : EvalState)
    (oracle : Nat → StepEvent) (stepIdx : Nat := 0) (fuel : Nat := 0) : Prop :=
  Nat.rec (motive := fun _ => EvalState → Nat → Prop)
    (fun _ _ => True)
    (fun _ rec st stepIdx =>
      match b.blocks[st.bb]? with
      | none => True
      | some bbData =>
        match bbData.stmts[st.stmtIdx]? with
        | some s =>
          match stepStmt .runtime st s with
          | .error _ => True
          | .ok st' => rec st' (stepIdx + 1)
        | none =>
          let ev := oracle stepIdx
          (match termCanUnwind cfg bbData.term with
           | some false => ev.unwind = false ∧
             (match bbData.term with
              | .assert cond exp _ _ =>
                match readDiscrFromPlace st.store (.localSlot cond) with
                | .ok d => (d != 0) == exp
                | .error _ => True
              | _ => True)
           | some true => cfg.targetSupportsUnwinding = false → ev.unwind = false ∧
             (match bbData.term with
              | .assert cond exp _ _ =>
                match readDiscrFromPlace st.store (.localSlot cond) with
                | .ok d => (d != 0) == exp
                | .error _ => True
              | _ => True)
           | none => True) ∧
          match stepTerm cfg .runtime b st bbData.term ev with
          | .finished _ _ => True
          | .nextState st' => rec st' (stepIdx + 1))
    fuel st stepIdx

def NonPanickingRun (b : Body) (st : EvalState) (oracle : Nat → StepEvent)
    (stepIdx : Nat := 0) (fuel : Nat := 0) : Prop :=
  Nat.rec (motive := fun _ => EvalState → Nat → Prop)
    (fun _ _ => True)
    (fun _ rec st stepIdx =>
      match b.blocks[st.bb]? with
      | none => True
      | some bbData =>
        match bbData.stmts[st.stmtIdx]? with
        | some s =>
          match stepStmt .runtime st s with
          | .error _ => True
          | .ok st' => rec st' (stepIdx + 1)
        | none =>
          let ev := oracle stepIdx
          ev.unwind = false ∧
          (match bbData.term with
           | .assert cond exp _ _ =>
             match readDiscrFromPlace st.store (.localSlot cond) with
             | .ok d => (d != 0) == exp
             | .error _ => True
           | _ => True) ∧
          match stepTerm { panicAborts := false, targetSupportsUnwinding := true, panicInDropUnwinds := true } .runtime b st bbData.term ev with
          | .finished _ _ => True
          | .nextState st' => rec st' (stepIdx + 1))
    fuel st stepIdx

private theorem OracleRespectsAbi_succ (cfg : CompileCfg) (b : Body) (st : EvalState)
    (oracle : Nat → StepEvent) (stepIdx f : Nat) :
    OracleRespectsAbi cfg b st oracle stepIdx (f + 1) =
      (match b.blocks[st.bb]? with
       | none => True
       | some bbData =>
         match bbData.stmts[st.stmtIdx]? with
         | some s =>
           match stepStmt .runtime st s with
           | .error _ => True
           | .ok st' => OracleRespectsAbi cfg b st' oracle (stepIdx + 1) f
         | none =>
           let ev := oracle stepIdx
           (match termCanUnwind cfg bbData.term with
            | some false => ev.unwind = false ∧
              (match bbData.term with
               | .assert cond exp _ _ =>
                 match readDiscrFromPlace st.store (.localSlot cond) with
                 | .ok d => (d != 0) == exp
                 | .error _ => True
               | _ => True)
            | some true => cfg.targetSupportsUnwinding = false → ev.unwind = false ∧
              (match bbData.term with
               | .assert cond exp _ _ =>
                 match readDiscrFromPlace st.store (.localSlot cond) with
                 | .ok d => (d != 0) == exp
                 | .error _ => True
               | _ => True)
            | none => True) ∧
           match stepTerm cfg .runtime b st bbData.term ev with
           | .finished _ _ => True
           | .nextState st' => OracleRespectsAbi cfg b st' oracle (stepIdx + 1) f) := rfl

private theorem NonPanickingRun_succ (b : Body) (st : EvalState) (oracle : Nat → StepEvent)
    (stepIdx f : Nat) :
    NonPanickingRun b st oracle stepIdx (f + 1) =
      (match b.blocks[st.bb]? with
       | none => True
       | some bbData =>
         match bbData.stmts[st.stmtIdx]? with
         | some s =>
           match stepStmt .runtime st s with
           | .error _ => True
           | .ok st' => NonPanickingRun b st' oracle (stepIdx + 1) f
         | none =>
           let ev := oracle stepIdx
           ev.unwind = false ∧
           (match bbData.term with
            | .assert cond exp _ _ =>
              match readDiscrFromPlace st.store (.localSlot cond) with
              | .ok d => (d != 0) == exp
              | .error _ => True
            | _ => True) ∧
           match stepTerm { panicAborts := false, targetSupportsUnwinding := true, panicInDropUnwinds := true } .runtime b st bbData.term ev with
           | .finished _ _ => True
           | .nextState st' => NonPanickingRun b st' oracle (stepIdx + 1) f) := rfl

private theorem abortRewriteBlock_preserves_stmts_and_cleanup (cfg : CompileCfg)
    (bCanUnwind : Bool) (bb : BasicBlock) :
    (abortRewriteBlock cfg bCanUnwind bb).stmts = bb.stmts ∧
    (abortRewriteBlock cfg bCanUnwind bb).isCleanup = bb.isCleanup :=
  ⟨rfl, rfl⟩

private theorem termWithUnwind_self (t : Term) (u : UnwindAction)
    (h : termUnwind t = some u) : termWithUnwind t u = t := by
  cases t <;> unfold termUnwind at h <;> cases h <;> rfl

private theorem stepTerm_withUnwind_nonpanicking (cfg1 cfg2 : CompileCfg) (mode : EvalMode)
    (b1 b2 : Body) (st : EvalState) (t : Term) (u : UnwindAction) (ev : StepEvent)
    (hNoUnw : ev.unwind = false)
    (hAss : match t with
            | .assert cond exp _ _ =>
              match readDiscrFromPlace st.store (.localSlot cond) with
              | .ok d => (d != 0) == exp
              | .error _ => True
            | _ => True)
    (hNotResume : t ≠ .unwindResume) :
    stepTerm cfg1 mode b1 st (termWithUnwind t u) ev = stepTerm cfg2 mode b2 st t ev := by
  cases t with
  | call c dst tgt _ =>
    unfold stepTerm termWithUnwind
    dsimp only
    rw [hNoUnw]
  | drop l tag tgt _ =>
    unfold stepTerm termWithUnwind
    dsimp only
    rw [hNoUnw]
  | assert cond exp tgt _ =>
    unfold stepTerm termWithUnwind
    dsimp only
    dsimp only at hAss
    cases hRd : readDiscrFromPlace st.store (.localSlot cond) with
    | error k => rfl
    | ok d =>
      dsimp only
      rw [hRd] at hAss
      dsimp only at hAss
      rw [hAss]
  | falseUnwind rt _ => rfl
  | inlineAsm m tgt _ =>
    unfold stepTerm termWithUnwind
    dsimp only
    rw [hNoUnw]
  | switchInt d cases oth =>
    unfold stepTerm termWithUnwind; rfl
  | return_ r =>
    unfold stepTerm termWithUnwind; rfl
  | unwindResume => exact absurd rfl hNotResume
  | _ => rfl

/-- When no unwind occurs, `abortRewriteOnly cfg b` executes in 1-to-1 lockstep with `b`
(and if `b` enters only non-cleanup blocks, `unwindResume` is never hit). -/
private theorem lookupSwitchTarget_mem (v : Nat) (cases : List (Nat × Nat)) (otherwise : Nat) :
    lookupSwitchTarget v cases otherwise ∈ cases.map Prod.snd ++ [otherwise] := by
  induction cases with
  | nil => exact List.Mem.head _
  | cons hd tl ih =>
    rw [lookupSwitchTarget_cons]
    cases hEq : (v == hd.1) with
    | true => exact List.Mem.head _
    | false => exact List.Mem.tail _ ih

private theorem lookupSwitchTarget_checkNormal (blocks : List BasicBlock)
    (v : Nat) (cases : List (Nat × Nat)) (otherwise : Nat)
    (hCases : (cases.map Prod.snd).all (fun i => match blocks[i]? with | some b => !b.isCleanup | none => false) = true)
    (hOth : (match blocks[otherwise]? with | some b => !b.isCleanup | none => false) = true) :
    (match blocks[lookupSwitchTarget v cases otherwise]? with | some b => !b.isCleanup | none => false) = true := by
  induction cases with
  | nil => exact hOth
  | cons hd tl ih =>
    rw [lookupSwitchTarget_cons]
    cases hEq : (v == hd.1) with
    | true => exact bool_and_left_true hCases
    | false => exact ih (bool_and_right_true hCases)

private theorem stepStmt_preserves_bb (mode : EvalMode) (st st' : EvalState) (s : Stmt)
    (h : stepStmt mode st s = .ok st') : st'.bb = st.bb := by
  cases s with
  | nop | recordDrop _ | storageLive _ | storageDead _
  | assignConst _ _ | assignPtr _ _ | assignEnum _ _ _ =>
    unfold stepStmt at h; cases h; rfl
  | assignCopy _ src =>
    unfold stepStmt at h; dsimp only at h
    cases hRd : readValueFromPlace st.store src <;> rw [hRd] at h <;> cases h; rfl
  | assignDiscr _ src =>
    unfold stepStmt at h; dsimp only at h
    cases hRd : readDiscrFromPlace st.store src <;> rw [hRd] at h <;> cases h; rfl
  | assignPtrCoercion _ kind src =>
    unfold stepStmt at h; dsimp only at h
    cases hB : (mode.forbidsAnalysis && kind != .ptrToPtr) <;> rw [hB] at h <;> dsimp only at h
    · cases hRd : readValueFromPlace st.store (.localSlot src) <;> rw [hRd] at h <;> cases h; rfl
    · cases h
  | placeMention p =>
    unfold stepStmt at h; dsimp only at h
    cases hEv : evalPlaceAddr st.store p <;> rw [hEv] at h <;> cases h; rfl
  | coverageMarker rem _ =>
    unfold stepStmt at h; dsimp only at h
    cases hB : (mode.forbidsAnalysis && rem) <;> rw [hB] at h <;> dsimp only at h <;> cases h; rfl
  | ascribeUserType _ | dropHint _ =>
    unfold stepStmt at h; dsimp only at h
    cases hB : mode.forbidsAnalysis <;> rw [hB] at h <;> dsimp only at h <;> cases h; rfl
  | assignFakeBorrow _ _ src =>
    unfold stepStmt at h; dsimp only at h
    cases hB : mode.forbidsAnalysis <;> rw [hB] at h <;> dsimp only at h
    · cases mode with
      | analysisUnguarded => cases h; rfl
      | _ => dsimp only at h; cases hEv : evalPlaceAddr st.store src <;> rw [hEv] at h <;> cases h; rfl
    · cases h
  | fakeRead cause p =>
    unfold stepStmt at h; dsimp only at h
    cases hB : mode.forbidsAnalysis <;> rw [hB] at h <;> dsimp only at h
    · cases mode with
      | analysisUnguarded => cases h; rfl
      | _ => dsimp only at h; cases hChk : checkFakeReadPlace st.store st.fakeBorrows cause p <;> rw [hChk] at h <;> cases h; rfl
    · cases h

theorem abortRewriteOnly_nonpanicking_equiv (cfg cfg0 : CompileCfg) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat)
    (hWf : wfBodyForAbort b = true)
    (hInBounds : match b.blocks[st.bb]? with | some bb => bb.isCleanup = false | none => True)
    (hNoPanic : NonPanickingRun b st oracle stepIdx fuel) :
    runEval cfg .runtime fuel (abortRewriteOnly cfg b) st oracle stepIdx =
      runEval cfg0 .runtime fuel b st oracle stepIdx := by
  induction fuel generalizing st stepIdx with
  | zero => rfl
  | succ f ih =>
    rw [runEval_succ, runEval_succ]
    dsimp only [abortRewriteOnly]
    rw [list_getElem?_map]
    cases hbb : b.blocks[st.bb]? with
    | none => rfl
    | some bbData =>
      have hNotCleanup : bbData.isCleanup = false := by rw [hbb] at hInBounds; exact hInBounds
      have hBbWf : wfBlockForAbort b.blocks bbData = true :=
        list_all_mem_true hWf (list_getElem?_mem hbb)
      have hRewrite := abortRewriteBlock_preserves_stmts_and_cleanup cfg (bodyCanUnwind cfg b) bbData
      dsimp only [Option.map]
      rw [hRewrite.1]
      cases hst : bbData.stmts[st.stmtIdx]? with
      | some s =>
        dsimp only
        rw [NonPanickingRun_succ] at hNoPanic
        rw [hbb] at hNoPanic; dsimp only at hNoPanic; rw [hst] at hNoPanic; dsimp only at hNoPanic
        cases hSt : stepStmt .runtime st s with
        | error k => rfl
        | ok st' =>
          rw [hSt] at hNoPanic
          apply ih st' (stepIdx + 1)
          · rw [stepStmt_preserves_bb .runtime st st' s hSt, hbb]
            exact hNotCleanup
          · exact hNoPanic
      | none =>
        dsimp only
        rw [NonPanickingRun_succ] at hNoPanic
        rw [hbb] at hNoPanic; dsimp only at hNoPanic; rw [hst] at hNoPanic; dsimp only at hNoPanic
        rcases hNoPanic with ⟨hEvUnw, hAss, hNpNext⟩
        have hNoResume : bbData.term ≠ .unwindResume := by
          intro hRes
          unfold wfBlockForAbort at hBbWf
          rw [hRes, hNotCleanup] at hBbWf
          dsimp only at hBbWf
          exact Bool.noConfusion hBbWf
        have hTermEq :
            stepTerm cfg .runtime (abortRewriteOnly cfg b) st
              (abortRewriteBlock cfg (bodyCanUnwind cfg b) bbData).term (oracle stepIdx) =
            stepTerm cfg0 .runtime b st bbData.term (oracle stepIdx) := by
          unfold abortRewriteBlock abortRewriteTerm
          rw [hNotCleanup]
          dsimp only
          have hT1 : (match bbData.term with
            | .unwindResume =>
              match !cfg.targetSupportsUnwinding with
              | true => Term.unreachable
              | false =>
                match !bodyCanUnwind cfg b with
                | true => .unwindTerminate .abi
                | false => .unwindResume
            | other => other) = bbData.term := by
            cases hT : bbData.term with
            | unwindResume => exact absurd hT hNoResume
            | _ => rfl
          rw [hT1]
          cases hTcu : termCanUnwind cfg bbData.term with
          | none =>
            dsimp only
            cases hT : bbData.term with
            | call _ _ _ _ | drop _ _ _ _ | assert _ _ _ _ | inlineAsm _ _ _ =>
              rw [hT] at hTcu; cases hTcu
            | switchInt d _ _ => unfold stepTerm; cases readDiscrFromPlace st.store (.localSlot d) <;> rfl
            | return_ r =>
              unfold stepTerm
              cases readValueFromPlace st.store (.localSlot r) with
              | error _ => rfl
              | ok v => cases v <;> rfl
            | unwindResume => exact absurd hT hNoResume
            | _ => rfl
          | some cCan =>
            cases hTu : termUnwind bbData.term with
            | none =>
              dsimp only
              cases hT : bbData.term with
              | call _ _ _ _ | drop _ _ _ _ | assert _ _ _ _ | inlineAsm _ _ _ | falseUnwind _ _ =>
                rw [hT] at hTu; cases hTu
              | switchInt d _ _ => unfold stepTerm; cases readDiscrFromPlace st.store (.localSlot d) <;> rfl
              | return_ r =>
                unfold stepTerm
                cases readValueFromPlace st.store (.localSlot r) with
                | error _ => rfl
                | ok v => cases v <;> rfl
              | unwindResume => exact absurd hT hNoResume
              | _ => rfl
            | some u =>
              dsimp only
              cases (!cCan || !cfg.targetSupportsUnwinding) <;> dsimp only
              · cases (!bodyCanUnwind cfg b && (u == .continue_)) <;> dsimp only
                · have hStepSelf := stepTerm_withUnwind_nonpanicking cfg cfg0 .runtime (abortRewriteOnly cfg b) b st bbData.term u (oracle stepIdx) hEvUnw hAss hNoResume
                  rw [termWithUnwind_self bbData.term u hTu] at hStepSelf
                  exact hStepSelf
                · exact stepTerm_withUnwind_nonpanicking cfg cfg0 .runtime (abortRewriteOnly cfg b) b st bbData.term (.terminate .abi) (oracle stepIdx) hEvUnw hAss hNoResume
              · exact stepTerm_withUnwind_nonpanicking cfg cfg0 .runtime (abortRewriteOnly cfg b) b st bbData.term .unreachable (oracle stepIdx) hEvUnw hAss hNoResume
        dsimp only [abortRewriteOnly] at hTermEq
        rw [hTermEq]
        have hTermClean :
            stepTerm cfg0 .runtime b st bbData.term (oracle stepIdx) =
            stepTerm { panicAborts := false, targetSupportsUnwinding := true, panicInDropUnwinds := true } .runtime b st bbData.term (oracle stepIdx) := by
          cases hT : bbData.term with
          | call _ _ _ _ => unfold stepTerm; dsimp only; rw [hEvUnw]
          | drop _ _ _ _ => unfold stepTerm; dsimp only; rw [hEvUnw]
          | assert cond exp _ _ =>
            unfold stepTerm
            dsimp only
            rw [hT] at hAss
            dsimp only at hAss
            cases hRd : readDiscrFromPlace st.store (.localSlot cond) with
            | error _ => rfl
            | ok d =>
              dsimp only
              rw [hRd] at hAss; dsimp only at hAss; rw [hAss]
          | inlineAsm _ _ _ => unfold stepTerm; dsimp only; rw [hEvUnw]
          | unwindResume => exact absurd hT hNoResume
          | switchInt d _ _ => unfold stepTerm; cases readDiscrFromPlace st.store (.localSlot d) <;> rfl
          | return_ r =>
            unfold stepTerm
            cases readValueFromPlace st.store (.localSlot r) with
            | error _ => rfl
            | ok v => cases v <;> rfl
          | _ => rfl
        rw [hTermClean]
        cases hRes : stepTerm { panicAborts := false, targetSupportsUnwinding := true, panicInDropUnwinds := true } .runtime b st bbData.term (oracle stepIdx) with
        | finished out st' => rfl
        | nextState st' =>
          rw [hRes] at hNpNext
          apply ih st' (stepIdx + 1) _ hNpNext
          unfold wfBlockForAbort at hBbWf
          rw [hNotCleanup] at hBbWf
          dsimp only at hBbWf
          cases hSuccs : (termSuccs bbData.term).all (fun i => Nat.ble (i + 1) b.blocks.length)
          · rw [hSuccs] at hBbWf; exact absurd hBbWf Bool.noConfusion
          · rw [hSuccs] at hBbWf
            cases hT : bbData.term with
            | falseEdge _ _ | falseUnwind _ _ | unwindTerminate _ =>
              rw [hT] at hBbWf; exact absurd hBbWf Bool.noConfusion
            | unwindResume => exact absurd hT hNoResume
            | unreachable =>
              rw [hT] at hRes; unfold stepTerm at hRes; cases hRes
            | return_ ret =>
              rw [hT] at hRes; unfold stepTerm at hRes; dsimp only at hRes
              cases hRv : readValueFromPlace st.store (.localSlot ret) with
              | error _ => rw [hRv] at hRes; cases hRes
              | ok v => rw [hRv] at hRes; cases v <;> cases hRes
            | goto tgt =>
              rw [hT] at hRes hBbWf; dsimp only at hBbWf
              unfold stepTerm at hRes; dsimp only at hRes; cases hRes
              cases hG : b.blocks[tgt]? with
              | none => trivial
              | some nb => rw [hG] at hBbWf; exact bool_not_true_eq_false hBbWf
            | switchInt d cases oth =>
              rw [hT] at hRes hBbWf; dsimp only at hBbWf
              unfold stepTerm at hRes; dsimp only at hRes
              cases hRd : readDiscrFromPlace st.store (.localSlot d) with
              | error _ => rw [hRd] at hRes; cases hRes
              | ok dv =>
                rw [hRd] at hRes; dsimp only at hRes; cases hRes
                cases hG : b.blocks[lookupSwitchTarget dv cases oth]? with
                | none => trivial
                | some nb =>
                  have hChk := lookupSwitchTarget_checkNormal b.blocks dv cases oth
                    (bool_and_left_true hBbWf) (bool_and_right_true hBbWf)
                  rw [hG] at hChk
                  exact bool_not_true_eq_false hChk
            | call _ _ tgt _ =>
              rw [hT] at hRes hBbWf; dsimp only at hBbWf
              unfold stepTerm at hRes; dsimp only at hRes; rw [hEvUnw] at hRes; dsimp only at hRes; cases hRes
              have hLeft := bool_and_left_true hBbWf
              cases hG : b.blocks[tgt]? with
              | none => trivial
              | some nb => rw [hG] at hLeft; exact bool_not_true_eq_false hLeft
            | drop _ _ tgt _ =>
              rw [hT] at hRes hBbWf; dsimp only at hBbWf
              unfold stepTerm at hRes; dsimp only at hRes; rw [hEvUnw] at hRes; dsimp only at hRes; cases hRes
              have hLeft := bool_and_left_true hBbWf
              cases hG : b.blocks[tgt]? with
              | none => trivial
              | some nb => rw [hG] at hLeft; exact bool_not_true_eq_false hLeft
            | assert cond exp tgt _ =>
              rw [hT] at hRes hBbWf hAss; dsimp only at hBbWf hAss
              unfold stepTerm at hRes; dsimp only at hRes
              cases hRd : readDiscrFromPlace st.store (.localSlot cond) with
              | error _ => rw [hRd] at hRes; cases hRes
              | ok dv =>
                rw [hRd] at hRes hAss; dsimp only at hRes hAss; rw [hAss] at hRes; dsimp only at hRes; cases hRes
                have hLeft := bool_and_left_true hBbWf
                cases hG : b.blocks[tgt]? with
                | none => trivial
                | some nb => rw [hG] at hLeft; exact bool_not_true_eq_false hLeft
            | inlineAsm _ tgt _ =>
              rw [hT] at hRes hBbWf; dsimp only at hBbWf
              unfold stepTerm at hRes; dsimp only at hRes; rw [hEvUnw] at hRes; dsimp only at hRes; cases hRes
              have hLeft := bool_and_left_true hBbWf
              cases hG : b.blocks[tgt]? with
              | none => trivial
              | some nb => rw [hG] at hLeft; exact bool_not_true_eq_false hLeft


/-! ## 9.2 `AbortUnwindingCalls`: Exact Equivalence to `.analysisPostCleanup` under `OracleRespectsAbi` -/

private theorem beq_unwind_continue_eq {u : UnwindAction} (h : (u == .continue_) = true) :
    u = .continue_ := by
  cases u with
  | continue_ => rfl
  | _ => cases h

private theorem nat_lt_of_ble_succ {a b : Nat} (h : Nat.ble (a + 1) b = true) : a < b := by
  have h1 := Nat.le_of_ble_eq_true h
  exact h1

private theorem ble_succ_of_lt {a b : Nat} (h : a < b) : Nat.ble (a + 1) b = true :=
  Nat.ble_eq_true_of_le h

private theorem stepStmt_runtime_eq_postCleanup (st : EvalState) (s : Stmt) :
    stepStmt .runtime st s = stepStmt .analysisPostCleanup st s := by
  cases s <;> rfl

private theorem takeUnwind_runtime_nextState_to_postCleanup (bCanUnwind : Bool) (st st' : EvalState)
    (u : UnwindAction) (h : takeUnwind .runtime bCanUnwind st u = .nextState st') :
    takeUnwind .analysisPostCleanup bCanUnwind st u = .nextState st' := by
  cases u with
  | cleanup bb => exact h
  | terminate r => unfold takeUnwind at h; cases h
  | unreachable => unfold takeUnwind at h; cases h
  | continue_ =>
    unfold takeUnwind at h
    cases hBcu : bCanUnwind <;> rw [hBcu] at h <;> dsimp only at h
    · cases h
    · cases h

private theorem stepTerm_runtime_nextState_to_postCleanup (cfg : CompileCfg) (b : Body)
    (st st' : EvalState) (t : Term) (ev : StepEvent)
    (h : stepTerm cfg .runtime b st t ev = .nextState st') :
    stepTerm cfg .analysisPostCleanup b st t ev = .nextState st' := by
  cases t with
  | goto tgt => exact h
  | switchInt d cases oth => exact h
  | falseEdge _ _ => exact h
  | falseUnwind _ _ => exact h
  | call _ _ tgt u =>
    unfold stepTerm at h ⊢; dsimp only at h ⊢
    cases hU : ev.unwind with
    | false =>
      rw [hU] at h; dsimp only at h
      exact h
    | true =>
      rw [hU] at h; dsimp only at h
      exact takeUnwind_runtime_nextState_to_postCleanup (bodyCanUnwind cfg b) st st' u h
  | drop _ tag tgt u =>
    unfold stepTerm at h ⊢; dsimp only at h ⊢
    cases hU : ev.unwind with
    | false =>
      rw [hU] at h; dsimp only at h
      exact h
    | true =>
      rw [hU] at h; dsimp only at h
      exact takeUnwind_runtime_nextState_to_postCleanup (bodyCanUnwind cfg b) _ st' u h
  | assert cond exp tgt u =>
    unfold stepTerm at h ⊢; dsimp only at h ⊢
    revert h
    cases readDiscrFromPlace st.store (.localSlot cond) with
    | error _ => intro h; cases h
    | ok d =>
      dsimp only
      cases ((d != 0) == exp) with
      | false =>
        intro h
        exact takeUnwind_runtime_nextState_to_postCleanup (bodyCanUnwind cfg b) st st' u h
      | true =>
        intro h
        exact h
  | inlineAsm _ tgt u =>
    unfold stepTerm at h ⊢; dsimp only at h ⊢
    cases hU : ev.unwind with
    | false =>
      rw [hU] at h; dsimp only at h
      exact h
    | true =>
      rw [hU] at h; dsimp only at h
      exact takeUnwind_runtime_nextState_to_postCleanup (bodyCanUnwind cfg b) st st' u h
  | return_ ret =>
    unfold stepTerm at h; dsimp only at h
    revert h
    cases readValueFromPlace st.store (.localSlot ret) with
    | error _ => intro h; cases h
    | ok v => cases v <;> (intro h; cases h)
  | unwindResume =>
    unfold stepTerm at h; dsimp only at h
    revert h
    cases bodyCanUnwind cfg b <;> (intro h; cases h)
  | unwindTerminate _ => unfold stepTerm at h; cases h
  | unreachable => unfold stepTerm at h; cases h

private theorem wf_cleanup_block_unwind_ok {u : UnwindAction}
    (h : (u == .unreachable || u == .terminate .inCleanup) = true) :
    ∀ m bCan st, takeUnwind m bCan st u = takeUnwind .analysisPostCleanup bCan st u := by
  intro m bCan st
  cases u with
  | unreachable => rfl
  | terminate r => rfl
  | cleanup bb => exact absurd h Bool.noConfusion
  | continue_ => exact absurd h Bool.noConfusion

private theorem takeUnwind_postCleanup_eq_of_ok (bCan : Bool) (st : EvalState) (u : UnwindAction)
    (hOk : (!bCan && (u == .continue_)) = false) :
    takeUnwind .runtime bCan st u = takeUnwind .analysisPostCleanup bCan st u := by
  cases u with
  | cleanup _ => rfl
  | terminate _ => rfl
  | unreachable => rfl
  | continue_ =>
    unfold takeUnwind
    cases hB : bCan with
    | true => rfl
    | false =>
      rw [hB] at hOk
      cases hOk

private theorem wfBlockForAbort_cleanup_next (blocks : List BasicBlock) (bb : BasicBlock)
    (cfg : CompileCfg) (b : Body) (st st' : EvalState) (ev : StepEvent)
    (hWf : wfBlockForAbort blocks bb = true)
    (hEntry : cfg.targetSupportsUnwinding = false → bb.isCleanup = false)
    (hStep : stepTerm cfg .runtime b st bb.term ev = .nextState st')
    (hAbi : (match termCanUnwind cfg bb.term with
             | some false => ev.unwind = false ∧
               (match bb.term with
                | .assert cond exp _ _ =>
                  match readDiscrFromPlace st.store (.localSlot cond) with
                  | .ok d => (d != 0) == exp
                  | .error _ => True
                | _ => True)
             | some true => cfg.targetSupportsUnwinding = false → ev.unwind = false ∧
               (match bb.term with
                | .assert cond exp _ _ =>
                  match readDiscrFromPlace st.store (.localSlot cond) with
                  | .ok d => (d != 0) == exp
                  | .error _ => True
                | _ => True)
             | none => True)) :
    match blocks[st'.bb]? with
    | some nb => cfg.targetSupportsUnwinding = false → nb.isCleanup = false
    | none => True := by
  cases hTsu : cfg.targetSupportsUnwinding with
  | true =>
    cases blocks[st'.bb]? with
    | none => trivial
    | some _ => exact fun h => Bool.noConfusion h
  | false =>
    have hNc : bb.isCleanup = false := hEntry hTsu
    unfold wfBlockForAbort at hWf
    rw [hNc] at hWf
    dsimp only at hWf
    cases hSuccs : (termSuccs bb.term).all (fun i => Nat.ble (i + 1) blocks.length)
    · rw [hSuccs] at hWf; exact absurd hWf Bool.noConfusion
    · rw [hSuccs] at hWf; rw [Bool.not_true] at hWf; dsimp only at hWf
      cases hT : bb.term with
      | falseEdge _ _ | falseUnwind _ _ | unwindResume | unwindTerminate _ =>
        rw [hT] at hWf; exact absurd hWf Bool.noConfusion
      | unreachable => rw [hT] at hStep; unfold stepTerm at hStep; cases hStep
      | return_ ret =>
        rw [hT] at hStep; unfold stepTerm at hStep; dsimp only at hStep
        revert hStep
        cases readValueFromPlace st.store (.localSlot ret) with
        | error _ => intro hS; cases hS
        | ok v => cases v <;> (intro hS; cases hS)
      | goto tgt =>
        rw [hT] at hWf hStep; dsimp only at hWf; unfold stepTerm at hStep; dsimp only at hStep; cases hStep
        cases hG : blocks[tgt]? with
        | none => exact absurd (by rw [hG] at hWf; exact hWf) Bool.noConfusion
        | some nb => intro _; rw [hG] at hWf; exact bool_not_true_eq_false hWf
      | switchInt d cases oth =>
        rw [hT] at hWf hStep; dsimp only at hWf; unfold stepTerm at hStep; dsimp only at hStep
        revert hStep
        cases hRd : readDiscrFromPlace st.store (.localSlot d) with
        | error _ => intro hS; cases hS
        | ok dv =>
          dsimp only; intro hS; cases hS
          have hChk := lookupSwitchTarget_checkNormal blocks dv cases oth
            (bool_and_left_true hWf) (bool_and_right_true hWf)
          cases hG : blocks[lookupSwitchTarget dv cases oth]? with
          | none => rw [hG] at hChk; exact absurd hChk Bool.noConfusion
          | some nb => intro _; rw [hG] at hChk; exact bool_not_true_eq_false hChk
      | call c dst tgt u =>
        rw [hT] at hWf hStep hAbi; dsimp only at hWf; dsimp only [termCanUnwind] at hAbi
        have hEvFalse : ev.unwind = false := by
          revert hAbi
          cases callCanUnwind cfg c with
          | false => intro hA; exact hA.1
          | true => intro hA; exact (hA hTsu).1
        unfold stepTerm at hStep; dsimp only at hStep; rw [hEvFalse] at hStep; dsimp only at hStep; cases hStep
        have hLeft := bool_and_left_true hWf
        cases hG : blocks[tgt]? with
        | none => rw [hG] at hLeft; exact absurd hLeft Bool.noConfusion
        | some nb => intro _; rw [hG] at hLeft; exact bool_not_true_eq_false hLeft
      | drop l tag tgt u =>
        rw [hT] at hWf hStep hAbi; dsimp only at hWf; dsimp only [termCanUnwind] at hAbi
        have hEvFalse : ev.unwind = false := by
          revert hAbi
          cases dropCanUnwind cfg with
          | false => intro hA; exact hA.1
          | true => intro hA; exact (hA hTsu).1
        unfold stepTerm at hStep; dsimp only at hStep; rw [hEvFalse] at hStep; dsimp only at hStep; cases hStep
        have hLeft := bool_and_left_true hWf
        cases hG : blocks[tgt]? with
        | none => rw [hG] at hLeft; exact absurd hLeft Bool.noConfusion
        | some nb => intro _; rw [hG] at hLeft; exact bool_not_true_eq_false hLeft
      | assert cond exp tgt u =>
        rw [hT] at hWf hStep hAbi; dsimp only at hWf; dsimp only [termCanUnwind] at hAbi
        have hAssOk : match readDiscrFromPlace st.store (.localSlot cond) with | .ok d => (d != 0) == exp | .error _ => True := by
          revert hAbi
          cases assertCanUnwind cfg with
          | false => intro hA; exact hA.2
          | true => intro hA; exact (hA hTsu).2
        unfold stepTerm at hStep; dsimp only at hStep
        cases hRd : readDiscrFromPlace st.store (.localSlot cond) with
        | error _ => rw [hRd] at hStep; cases hStep
        | ok dv =>
          rw [hRd] at hStep hAssOk; dsimp only at hStep hAssOk; rw [hAssOk] at hStep; dsimp only at hStep; cases hStep
          have hLeft := bool_and_left_true hWf
          cases hG : blocks[tgt]? with
          | none => rw [hG] at hLeft; exact absurd hLeft Bool.noConfusion
          | some nb => intro _; rw [hG] at hLeft; exact bool_not_true_eq_false hLeft
      | inlineAsm mayUnw tgt u =>
        rw [hT] at hWf hStep hAbi; dsimp only at hWf; dsimp only [termCanUnwind] at hAbi
        have hEvFalse : ev.unwind = false := by
          revert hAbi
          cases mayUnw with
          | false => intro hA; exact hA.1
          | true => intro hA; exact (hA hTsu).1
        unfold stepTerm at hStep; dsimp only at hStep; rw [hEvFalse] at hStep; dsimp only at hStep; cases hStep
        have hLeft := bool_and_left_true hWf
        cases hG : blocks[tgt]? with
        | none => rw [hG] at hLeft; exact absurd hLeft Bool.noConfusion
        | some nb => intro _; rw [hG] at hLeft; exact bool_not_true_eq_false hLeft

private theorem abortRewriteTerm_exact_step (cfg : CompileCfg) (b : Body) (bb : BasicBlock)
    (st : EvalState) (ev : StepEvent)
    (hWf : wfBlockForAbort b.blocks bb = true)
    (hEntry : cfg.targetSupportsUnwinding = false → bb.isCleanup = false)
    (hAbi : (match termCanUnwind cfg bb.term with
             | some false => ev.unwind = false ∧
               (match bb.term with
                | .assert cond exp _ _ =>
                  match readDiscrFromPlace st.store (.localSlot cond) with
                  | .ok d => (d != 0) == exp
                  | .error _ => True
                | _ => True)
             | some true => cfg.targetSupportsUnwinding = false → ev.unwind = false ∧
               (match bb.term with
                | .assert cond exp _ _ =>
                  match readDiscrFromPlace st.store (.localSlot cond) with
                  | .ok d => (d != 0) == exp
                  | .error _ => True
                | _ => True)
             | none => True)) :
    stepTerm cfg .runtime (abortRewriteOnly cfg b) st
        (abortRewriteTerm cfg (bodyCanUnwind cfg b) bb.isCleanup bb.term) ev =
      stepTerm cfg .analysisPostCleanup b st bb.term ev := by
  have hBodyEq : bodyCanUnwind cfg (abortRewriteOnly cfg b) = bodyCanUnwind cfg b := rfl
  unfold abortRewriteTerm
  cases hCl : bb.isCleanup with
  | true =>
    have hTsu : cfg.targetSupportsUnwinding = true := by
      cases hT : cfg.targetSupportsUnwinding with
      | false => exact absurd (hEntry hT) (by rw [hCl]; exact Bool.noConfusion)
      | true => rfl
    rw [hTsu]
    dsimp only
    unfold wfBlockForAbort at hWf
    rw [hCl] at hWf
    dsimp only at hWf
    cases hSuccs : (termSuccs bb.term).all (fun i => Nat.ble (i + 1) b.blocks.length)
    · rw [hSuccs] at hWf; exact absurd hWf Bool.noConfusion
    · rw [hSuccs] at hWf
      cases hT : bb.term with
      | return_ _ | falseEdge _ _ | falseUnwind _ _ =>
        rw [hT] at hWf; exact absurd hWf Bool.noConfusion
      | unwindResume =>
        unfold stepTerm
        dsimp only
        rw [hBodyEq]
        cases hBcu : bodyCanUnwind cfg b <;> dsimp only
        · rfl
        · rfl
      | unwindTerminate _ | unreachable | goto _ => rfl
      | switchInt d _ _ =>
        unfold stepTerm
        cases readDiscrFromPlace st.store (.localSlot d) <;> rfl
      | call _ _ _ u =>
        rw [hT] at hWf
        have hUok := bool_and_right_true hWf
        unfold stepTerm
        dsimp only
        rw [hBodyEq]
        cases ev.unwind with
        | false => rfl
        | true => exact wf_cleanup_block_unwind_ok hUok .runtime (bodyCanUnwind cfg b) st
      | drop _ tag _ u =>
        rw [hT] at hWf
        have hUok := bool_and_right_true hWf
        unfold stepTerm
        dsimp only
        rw [hBodyEq]
        cases ev.unwind with
        | false => rfl
        | true => exact wf_cleanup_block_unwind_ok hUok .runtime (bodyCanUnwind cfg b) { st with trace := st.trace ++ [tag] }
      | assert cond exp _ u =>
        rw [hT] at hWf
        have hUok := bool_and_right_true hWf
        unfold stepTerm
        dsimp only
        rw [hBodyEq]
        cases readDiscrFromPlace st.store (.localSlot cond) with
        | error _ => rfl
        | ok dv =>
          dsimp only
          cases ((dv != 0) == exp) with
          | true => rfl
          | false => exact wf_cleanup_block_unwind_ok hUok .runtime (bodyCanUnwind cfg b) st
      | inlineAsm _ _ u =>
        rw [hT] at hWf
        have hUok := bool_and_right_true hWf
        unfold stepTerm
        dsimp only
        rw [hBodyEq]
        cases ev.unwind with
        | false => rfl
        | true => exact wf_cleanup_block_unwind_ok hUok .runtime (bodyCanUnwind cfg b) st
  | false =>
    unfold wfBlockForAbort at hWf
    rw [hCl] at hWf
    dsimp only at hWf
    cases hSuccs : (termSuccs bb.term).all (fun i => Nat.ble (i + 1) b.blocks.length)
    · rw [hSuccs] at hWf; exact absurd hWf Bool.noConfusion
    · rw [hSuccs] at hWf
      cases hT : bb.term with
      | unwindResume | unwindTerminate _ | falseEdge _ _ | falseUnwind _ _ =>
        rw [hT] at hWf; exact absurd hWf Bool.noConfusion
      | goto _ | unreachable => rfl
      | switchInt d _ _ =>
        unfold stepTerm
        cases readDiscrFromPlace st.store (.localSlot d) <;> rfl
      | return_ r =>
        unfold stepTerm
        cases readValueFromPlace st.store (.localSlot r) with
        | error _ => rfl
        | ok v => cases v <;> rfl
      | call c dst tgt u =>
        dsimp only [termCanUnwind, termUnwind]
        cases hAbort : (!callCanUnwind cfg c || !cfg.targetSupportsUnwinding) with
        | true =>
          dsimp only
          have hEvFalse : ev.unwind = false := by
            rw [hT] at hAbi; dsimp only [termCanUnwind] at hAbi
            revert hAbort
            revert hAbi
            cases callCanUnwind cfg c with
            | false => intro hA _; exact hA.1
            | true =>
              cases cfg.targetSupportsUnwinding with
              | true => intro _ hAb; rw [Bool.not_true] at hAb; cases hAb
              | false => intro hA _; exact (hA rfl).1
          unfold stepTerm termWithUnwind
          dsimp only
          rw [hEvFalse]
        | false =>
          dsimp only
          cases hCont : (!bodyCanUnwind cfg b && (u == .continue_)) with
          | true =>
            have hBcu : bodyCanUnwind cfg b = false := bool_not_true_eq_false (bool_and_left_true hCont)
            have hU : u = .continue_ := beq_unwind_continue_eq (bool_and_right_true hCont)
            subst hU
            unfold stepTerm termWithUnwind
            dsimp only
            rw [hBodyEq, hBcu]
            cases ev.unwind with
            | false => rfl
            | true => rfl
          | false =>
            unfold stepTerm
            dsimp only
            rw [hBodyEq]
            cases ev.unwind with
            | false => rfl
            | true => exact takeUnwind_postCleanup_eq_of_ok (bodyCanUnwind cfg b) st u hCont
      | drop l tag tgt u =>
        dsimp only [termCanUnwind, termUnwind]
        cases hAbort : (!dropCanUnwind cfg || !cfg.targetSupportsUnwinding) with
        | true =>
          dsimp only
          have hEvFalse : ev.unwind = false := by
            rw [hT] at hAbi; dsimp only [termCanUnwind] at hAbi
            revert hAbort
            revert hAbi
            cases dropCanUnwind cfg with
            | false => intro hA _; exact hA.1
            | true =>
              cases cfg.targetSupportsUnwinding with
              | true => intro _ hAb; rw [Bool.not_true] at hAb; cases hAb
              | false => intro hA _; exact (hA rfl).1
          unfold stepTerm termWithUnwind
          dsimp only
          rw [hEvFalse]
        | false =>
          dsimp only
          cases hCont : (!bodyCanUnwind cfg b && (u == .continue_)) with
          | true =>
            have hBcu : bodyCanUnwind cfg b = false := bool_not_true_eq_false (bool_and_left_true hCont)
            have hU : u = .continue_ := beq_unwind_continue_eq (bool_and_right_true hCont)
            subst hU
            unfold stepTerm termWithUnwind
            dsimp only
            rw [hBodyEq, hBcu]
            cases ev.unwind with
            | false => rfl
            | true => rfl
          | false =>
            unfold stepTerm
            dsimp only
            rw [hBodyEq]
            cases ev.unwind with
            | false => rfl
            | true => exact takeUnwind_postCleanup_eq_of_ok (bodyCanUnwind cfg b) { st with trace := st.trace ++ [tag] } u hCont
      | assert cond exp tgt u =>
        dsimp only [termCanUnwind, termUnwind]
        cases hAbort : (!assertCanUnwind cfg || !cfg.targetSupportsUnwinding) with
        | true =>
          dsimp only
          have hAssOk : match readDiscrFromPlace st.store (.localSlot cond) with | .ok d => (d != 0) == exp | .error _ => True := by
            rw [hT] at hAbi; dsimp only [termCanUnwind] at hAbi
            revert hAbort
            revert hAbi
            cases assertCanUnwind cfg with
            | false => intro hA _; exact hA.2
            | true =>
              cases cfg.targetSupportsUnwinding with
              | true => intro _ hAb; rw [Bool.not_true] at hAb; cases hAb
              | false => intro hA _; exact (hA rfl).2
          unfold stepTerm termWithUnwind
          dsimp only
          cases hRd : readDiscrFromPlace st.store (.localSlot cond) with
          | error _ => rfl
          | ok dv =>
            dsimp only
            rw [hRd] at hAssOk; dsimp only at hAssOk; rw [hAssOk]
        | false =>
          dsimp only
          cases hCont : (!bodyCanUnwind cfg b && (u == .continue_)) with
          | true =>
            have hBcu : bodyCanUnwind cfg b = false := bool_not_true_eq_false (bool_and_left_true hCont)
            have hU : u = .continue_ := beq_unwind_continue_eq (bool_and_right_true hCont)
            subst hU
            unfold stepTerm termWithUnwind
            dsimp only
            rw [hBodyEq, hBcu]
            cases readDiscrFromPlace st.store (.localSlot cond) with
            | error _ => rfl
            | ok dv =>
              dsimp only
              cases ((dv != 0) == exp) <;> rfl
          | false =>
            unfold stepTerm
            dsimp only
            rw [hBodyEq]
            cases readDiscrFromPlace st.store (.localSlot cond) with
            | error _ => rfl
            | ok dv =>
              dsimp only
              cases ((dv != 0) == exp) with
              | true => rfl
              | false => exact takeUnwind_postCleanup_eq_of_ok (bodyCanUnwind cfg b) st u hCont
      | inlineAsm mayUnw tgt u =>
        dsimp only [termCanUnwind, termUnwind]
        cases hAbort : (!mayUnw || !cfg.targetSupportsUnwinding) with
        | true =>
          dsimp only
          have hEvFalse : ev.unwind = false := by
            rw [hT] at hAbi; dsimp only [termCanUnwind] at hAbi
            revert hAbort
            revert hAbi
            cases mayUnw with
            | false => intro hA _; exact hA.1
            | true =>
              cases cfg.targetSupportsUnwinding with
              | true => intro _ hAb; rw [Bool.not_true] at hAb; cases hAb
              | false => intro hA _; exact (hA rfl).1
          unfold stepTerm termWithUnwind
          dsimp only
          rw [hEvFalse]
        | false =>
          dsimp only
          cases hCont : (!bodyCanUnwind cfg b && (u == .continue_)) with
          | true =>
            have hBcu : bodyCanUnwind cfg b = false := bool_not_true_eq_false (bool_and_left_true hCont)
            have hU : u = .continue_ := beq_unwind_continue_eq (bool_and_right_true hCont)
            subst hU
            unfold stepTerm termWithUnwind
            dsimp only
            rw [hBodyEq, hBcu]
            cases ev.unwind with
            | false => rfl
            | true => rfl
          | false =>
            unfold stepTerm
            dsimp only
            rw [hBodyEq]
            cases ev.unwind with
            | false => rfl
            | true => exact takeUnwind_postCleanup_eq_of_ok (bodyCanUnwind cfg b) st u hCont

theorem abortRewriteOnly_exact_analysis_equiv (cfg : CompileCfg) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0)
    (hWf : wfBodyForAbort b = true)
    (hEntry : match b.blocks[st.bb]? with | some bb => cfg.targetSupportsUnwinding = false → bb.isCleanup = false | none => True)
    (hAbi : OracleRespectsAbi cfg b st oracle stepIdx fuel) :
    runEval cfg .runtime fuel (abortRewriteOnly cfg b) st oracle stepIdx =
      runEval cfg .analysisPostCleanup fuel b st oracle stepIdx := by
  induction fuel generalizing st stepIdx with
  | zero => rfl
  | succ f ih =>
    rw [runEval_succ, runEval_succ]
    dsimp only [abortRewriteOnly]
    rw [list_getElem?_map]
    cases hbb : b.blocks[st.bb]? with
    | none => rfl
    | some bbData =>
      have hEn : cfg.targetSupportsUnwinding = false → bbData.isCleanup = false := by
        rw [hbb] at hEntry; exact hEntry
      have hBbWf : wfBlockForAbort b.blocks bbData = true :=
        list_all_mem_true hWf (list_getElem?_mem hbb)
      dsimp only [Option.map, abortRewriteBlock]
      cases hst : bbData.stmts[st.stmtIdx]? with
      | some s =>
        dsimp only
        rw [OracleRespectsAbi_succ] at hAbi
        rw [hbb] at hAbi; dsimp only at hAbi; rw [hst] at hAbi; dsimp only at hAbi
        rw [stepStmt_runtime_eq_postCleanup]
        cases hSt : stepStmt .analysisPostCleanup st s with
        | error k => rfl
        | ok st' =>
          have hStRt : stepStmt .runtime st s = .ok st' := by
            rw [stepStmt_runtime_eq_postCleanup]; exact hSt
          rw [hStRt] at hAbi
          apply ih st' (stepIdx + 1)
          · rw [stepStmt_preserves_bb .analysisPostCleanup st st' s hSt, hbb]
            exact hEn
          · exact hAbi
      | none =>
        dsimp only
        rw [OracleRespectsAbi_succ] at hAbi
        rw [hbb] at hAbi; dsimp only at hAbi; rw [hst] at hAbi; dsimp only at hAbi
        rcases hAbi with ⟨hAbiStep, hAbiNext⟩
        have hTermEq := abortRewriteTerm_exact_step cfg b bbData st (oracle stepIdx) hBbWf hEn hAbiStep
        dsimp only [abortRewriteOnly] at hTermEq
        rw [hTermEq]
        cases hRes : stepTerm cfg .analysisPostCleanup b st bbData.term (oracle stepIdx) with
        | finished out st' => rfl
        | nextState st' =>
          have hRuntimeNext : ∃ stR, stepTerm cfg .runtime b st bbData.term (oracle stepIdx) = .nextState stR ∧ stR = st' := by
            cases hResR : stepTerm cfg .runtime b st bbData.term (oracle stepIdx) with
            | nextState stR =>
              have hEq := stepTerm_runtime_nextState_to_postCleanup cfg b st stR bbData.term (oracle stepIdx) hResR
              rw [hRes] at hEq
              cases hEq
              exact ⟨st', rfl, rfl⟩
            | finished outR stR =>
              exfalso
              cases hT : bbData.term with
              | goto _ => rw [hT] at hResR; unfold stepTerm at hResR; cases hResR
              | falseEdge _ _ | falseUnwind _ _ => rw [hT] at hRes; unfold stepTerm at hRes; cases hRes
              | switchInt d _ _ =>
                rw [hT] at hResR hRes; unfold stepTerm at hResR hRes; dsimp only at hResR hRes
                revert hResR hRes
                cases readDiscrFromPlace st.store (.localSlot d) with
                | error _ => intro hR _; cases hR
                | ok _ => intro _ hRR; cases hRR
              | call _ _ _ u =>
                rw [hT] at hResR hRes; unfold stepTerm at hResR hRes; dsimp only at hResR hRes
                revert hResR hRes
                cases (oracle stepIdx).unwind with
                | false => intro _ hRR; cases hRR
                | true =>
                  cases u with
                  | cleanup _ => intro _ hRR; cases hRR
                  | terminate _ => intro hR _; cases hR
                  | unreachable => intro hR _; cases hR
                  | continue_ =>
                    intro hR _
                    unfold takeUnwind at hR
                    revert hR
                    cases bodyCanUnwind cfg b <;> (intro hR; cases hR)
              | drop _ _ _ u =>
                rw [hT] at hResR hRes; unfold stepTerm at hResR hRes; dsimp only at hResR hRes
                revert hResR hRes
                cases (oracle stepIdx).unwind with
                | false => intro _ hRR; cases hRR
                | true =>
                  cases u with
                  | cleanup _ => intro _ hRR; cases hRR
                  | terminate _ => intro hR _; cases hR
                  | unreachable => intro hR _; cases hR
                  | continue_ =>
                    intro hR _
                    unfold takeUnwind at hR
                    revert hR
                    cases bodyCanUnwind cfg b <;> (intro hR; cases hR)
              | assert cond exp _ u =>
                rw [hT] at hResR hRes; unfold stepTerm at hResR hRes; dsimp only at hResR hRes
                revert hResR hRes
                cases readDiscrFromPlace st.store (.localSlot cond) with
                | error _ => intro hR _; cases hR
                | ok dv =>
                  dsimp only
                  cases ((dv != 0) == exp) with
                  | false =>
                    cases u with
                    | cleanup _ => intro _ hRR; cases hRR
                    | terminate _ => intro hR _; cases hR
                    | unreachable => intro hR _; cases hR
                    | continue_ =>
                      intro hR _
                      unfold takeUnwind at hR
                      revert hR
                      cases bodyCanUnwind cfg b <;> (intro hR; cases hR)
                  | true => intro _ hRR; cases hRR
              | inlineAsm _ _ u =>
                rw [hT] at hResR hRes; unfold stepTerm at hResR hRes; dsimp only at hResR hRes
                revert hResR hRes
                cases (oracle stepIdx).unwind with
                | false => intro _ hRR; cases hRR
                | true =>
                  cases u with
                  | cleanup _ => intro _ hRR; cases hRR
                  | terminate _ => intro hR _; cases hR
                  | unreachable => intro hR _; cases hR
                  | continue_ =>
                    intro hR _
                    unfold takeUnwind at hR
                    revert hR
                    cases bodyCanUnwind cfg b <;> (intro hR; cases hR)
              | return_ r =>
                rw [hT] at hRes; unfold stepTerm at hRes; dsimp only at hRes
                revert hRes
                cases readValueFromPlace st.store (.localSlot r) with
                | error _ => intro hR; cases hR
                | ok v => cases v <;> (intro hR; cases hR)
              | unwindResume =>
                rw [hT] at hRes; unfold stepTerm at hRes; dsimp only at hRes
                revert hRes
                cases bodyCanUnwind cfg b <;> (intro hR; cases hR)
              | unwindTerminate _ => rw [hT] at hRes; unfold stepTerm at hRes; cases hRes
              | unreachable => rw [hT] at hRes; unfold stepTerm at hRes; cases hRes
          rcases hRuntimeNext with ⟨stR, hResR, hEqR⟩
          subst hEqR
          rw [hResR] at hAbiNext
          apply ih stR (stepIdx + 1) _ hAbiNext
          exact wfBlockForAbort_cleanup_next b.blocks bbData cfg b st stR (oracle stepIdx) hBbWf hEn hResR hAbiStep

/-! ## 9.3 Reachability Closure, Dead-Block Compaction, & Complete `AbortUnwindingCalls` Soundness -/

noncomputable def countTrue (xs : List Bool) : Nat :=
  List.rec 0 (fun b _ rec => match b with | true => rec + 1 | false => rec) xs

noncomputable def reachClosedAux (blocks : List BasicBlock) (reach : List Bool) (k : Nat) : Bool :=
  Nat.rec true
    (fun k' rec =>
      rec &&
      match getNatBool reach k' with
      | false => true
      | true =>
        match blocks[k']? with
        | some bb => (termSuccs bb.term).all (fun s => !Nat.ble (s + 1) blocks.length || getNatBool reach s)
        | none => true)
    k

noncomputable def reachClosedBool (blocks : List BasicBlock) (reach : List Bool) : Bool :=
  reachClosedAux blocks reach blocks.length

private theorem reachStepAux_succ (blocks : List BasicBlock) (seed : List Bool)
    (k : Nat) (acc : List Bool) :
    reachStepAux blocks seed (k + 1) acc =
      let acc' := reachStepAux blocks seed k acc
      match getNatBool seed k with
      | true => markSuccs blocks acc' k
      | false => acc' := rfl

private theorem iterReach_succ (n : Nat) (blocks : List BasicBlock) (reach : List Bool) :
    iterReach (n + 1) blocks reach = iterReach n blocks (reachStep blocks reach) := rfl

private theorem reachClosedAux_succ (blocks : List BasicBlock) (reach : List Bool) (k : Nat) :
    reachClosedAux blocks reach (k + 1) =
      (reachClosedAux blocks reach k &&
       match getNatBool reach k with
       | false => true
       | true =>
         match blocks[k]? with
         | some bb => (termSuccs bb.term).all (fun s => !Nat.ble (s + 1) blocks.length || getNatBool reach s)
         | none => true) := rfl

private theorem countTrue_le_length (xs : List Bool) : countTrue xs ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons b bs ih =>
    cases b <;> unfold countTrue <;> simp only [List.length]
    · exact Nat.le_trans ih (Nat.le_succ _)
    · exact Nat.succ_le_succ ih

private theorem setNatBool_length (xs : List Bool) (i : Nat) (v : Bool) :
    (setNatBool xs i v).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero => rfl
    | succ k => exact congrArg Nat.succ (ih k)

private theorem getNatBool_setNatBool_eq (xs : List Bool) (i : Nat) (v : Bool)
    (hi : i < xs.length) : getNatBool (setNatBool xs i v) i = v := by
  induction xs generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons _ _ ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ hi)

private theorem getNatBool_setNatBool_ne (xs : List Bool) (i j : Nat) (v : Bool)
    (hNe : i ≠ j) : getNatBool (setNatBool xs i v) j = getNatBool xs j := by
  induction xs generalizing i j with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hNe
      | succ k => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' => exact ih i' j' (fun h => hNe (congrArg Nat.succ h))

private theorem setNatBool_true_eq_self (xs : List Bool) (i : Nat)
    (h : getNatBool xs i = true) : setNatBool xs i true = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero =>
      cases x with
      | true => rfl
      | false => cases h
    | succ k => exact congrArg (List.cons x) (ih k h)

private theorem setNatBool_oob_eq_self (xs : List Bool) (i : Nat) (v : Bool)
    (h : xs.length ≤ i) : setNatBool xs i v = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero => cases h
    | succ k => exact congrArg (List.cons x) (ih k (Nat.le_of_succ_le_succ h))

private theorem countTrue_setNatBool_mono (xs : List Bool) (i : Nat) :
    countTrue xs ≤ countTrue (setNatBool xs i true) := by
  induction xs generalizing i with
  | nil => exact Nat.le_refl 0
  | cons x rest ih =>
    cases i with
    | zero =>
      cases x <;> unfold setNatBool countTrue
      · exact Nat.le_succ _
      · exact Nat.le_refl _
    | succ k =>
      cases x <;> unfold setNatBool countTrue
      · exact ih k
      · exact Nat.succ_le_succ (ih k)

private theorem countTrue_setNatBool_lt (xs : List Bool) (i : Nat)
    (hi : i < xs.length) (hFalse : getNatBool xs i = false) :
    countTrue xs + 1 ≤ countTrue (setNatBool xs i true) := by
  induction xs generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x rest ih =>
    cases i with
    | zero =>
      cases x with
      | false => exact Nat.le_refl _
      | true => cases hFalse
    | succ k =>
      have hk := Nat.lt_of_succ_lt_succ hi
      cases x <;> unfold setNatBool countTrue
      · exact ih k hk hFalse
      · exact Nat.succ_le_succ (ih k hk hFalse)

private theorem foldl_setNatBool_length (ss : List Nat) (r : List Bool) :
    (ss.foldl (fun acc s => setNatBool acc s true) r).length = r.length := by
  induction ss generalizing r with
  | nil => rfl
  | cons s rest ih =>
    dsimp only [List.foldl]
    rw [ih (setNatBool r s true), setNatBool_length]

private theorem foldl_setNatBool_mono_count (ss : List Nat) (r : List Bool) :
    countTrue r ≤ countTrue (ss.foldl (fun acc s => setNatBool acc s true) r) := by
  induction ss generalizing r with
  | nil => exact Nat.le_refl _
  | cons s rest ih =>
    exact Nat.le_trans (countTrue_setNatBool_mono r s) (ih (setNatBool r s true))

private theorem getNatBool_true_lt_length (r : List Bool) (j : Nat)
    (h : getNatBool r j = true) : j < r.length := by
  induction r generalizing j with
  | nil => cases h
  | cons x xs ihR =>
    cases j with
    | zero => exact Nat.succ_pos _
    | succ j' => exact Nat.succ_lt_succ (ihR j' h)

private theorem foldl_setNatBool_mono_get (ss : List Nat) (r : List Bool) (j : Nat)
    (h : getNatBool r j = true) :
    getNatBool (ss.foldl (fun acc s => setNatBool acc s true) r) j = true := by
  induction ss generalizing r with
  | nil => exact h
  | cons s rest ih =>
    apply ih
    cases (Decidable.em (s = j)) with
    | inl hEq =>
      subst hEq
      exact getNatBool_setNatBool_eq r s true (getNatBool_true_lt_length r s h)
    | inr hNe =>
      rw [getNatBool_setNatBool_ne r s j true hNe]
      exact h

private theorem foldl_setNatBool_witness (ss : List Nat) (r : List Bool) (x : Nat)
    (hMem : x ∈ ss) (hx : x < r.length) (hFalse : getNatBool r x = false) :
    countTrue r + 1 ≤ countTrue (ss.foldl (fun acc s => setNatBool acc s true) r) := by
  induction ss generalizing r with
  | nil => cases hMem
  | cons hd tl ih =>
    cases hMem with
    | head _ =>
      exact Nat.le_trans (countTrue_setNatBool_lt r x hx hFalse) (foldl_setNatBool_mono_count tl (setNatBool r x true))
    | tail _ hTl =>
      cases hCur : getNatBool (setNatBool r hd true) x with
      | true =>
        have hJump : countTrue r + 1 ≤ countTrue (setNatBool r hd true) := by
          cases (Decidable.em (hd = x)) with
          | inl hEq =>
            have hDone : countTrue r + 1 ≤ countTrue (setNatBool r hd true) := by
              rw [hEq]
              exact countTrue_setNatBool_lt r x hx hFalse
            exact hDone
          | inr hNe => rw [getNatBool_setNatBool_ne r hd x true hNe, hFalse] at hCur; cases hCur
        exact Nat.le_trans hJump (foldl_setNatBool_mono_count tl (setNatBool r hd true))
      | false =>
        have hx' : x < (setNatBool r hd true).length := by rw [setNatBool_length]; exact hx
        exact Nat.le_trans (Nat.add_le_add_right (countTrue_setNatBool_mono r hd) 1) (ih (setNatBool r hd true) hTl hx' hCur)

private theorem foldl_setNatBool_eq_self (ss : List Nat) (r : List Bool)
    (hClosed : (ss.all fun s => !Nat.ble (s + 1) r.length || getNatBool r s) = true) :
    ss.foldl (fun acc s => setNatBool acc s true) r = r := by
  induction ss with
  | nil => rfl
  | cons hd tl ih =>
    have hHd := bool_and_left_true hClosed
    have hTl := bool_and_right_true hClosed
    dsimp only at hHd
    have hStep : setNatBool r hd true = r := by
      cases hLe : Nat.ble (hd + 1) r.length with
      | false =>
        have hGe : r.length ≤ hd := by
          cases (Nat.lt_or_ge hd r.length) with
          | inl hLt => rw [ble_succ_of_lt hLt] at hLe; cases hLe
          | inr hGe => exact hGe
        exact setNatBool_oob_eq_self r hd true hGe
      | true =>
        rw [hLe] at hHd
        have hGet : getNatBool r hd = true := by
          revert hHd
          cases getNatBool r hd <;> intro hA <;> first | rfl | exact absurd hA Bool.noConfusion
        exact setNatBool_true_eq_self r hd hGet
    dsimp only [List.foldl]
    rw [hStep]
    exact ih hTl

private theorem reachStepAux_length (blocks : List BasicBlock) (seed : List Bool)
    (k : Nat) (acc : List Bool) :
    (reachStepAux blocks seed k acc).length = acc.length := by
  induction k generalizing acc with
  | zero => rfl
  | succ k' ih =>
    rw [reachStepAux_succ]
    cases getNatBool seed k' with
    | false => exact ih acc
    | true =>
      dsimp only
      unfold markSuccs
      cases blocks[k']? with
      | none => exact ih acc
      | some bb =>
        dsimp only
        rw [foldl_setNatBool_length]
        exact ih acc

private theorem reachStepAux_mono_count (blocks : List BasicBlock) (seed : List Bool)
    (k : Nat) (acc : List Bool) :
    countTrue acc ≤ countTrue (reachStepAux blocks seed k acc) := by
  induction k generalizing acc with
  | zero => exact Nat.le_refl _
  | succ k' ih =>
    rw [reachStepAux_succ]
    cases getNatBool seed k' with
    | false => exact ih acc
    | true =>
      dsimp only
      unfold markSuccs
      cases blocks[k']? with
      | none => exact ih acc
      | some bb =>
        exact Nat.le_trans (ih acc) (foldl_setNatBool_mono_count _ _)

private theorem reachStepAux_mono_get (blocks : List BasicBlock) (seed : List Bool)
    (k : Nat) (acc : List Bool) (j : Nat) (h : getNatBool acc j = true) :
    getNatBool (reachStepAux blocks seed k acc) j = true := by
  induction k with
  | zero => exact h
  | succ k' ih =>
    rw [reachStepAux_succ]
    cases getNatBool seed k' with
    | false => exact ih
    | true =>
      dsimp only
      unfold markSuccs
      cases blocks[k']? with
      | none => exact ih
      | some bb => exact foldl_setNatBool_mono_get _ _ j ih

private theorem reachStepAux_noop_of_closed (blocks : List BasicBlock) (r : List Bool)
    (k : Nat) (hLen : r.length = blocks.length) (hClosed : reachClosedAux blocks r k = true) :
    reachStepAux blocks r k r = r := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    rw [reachClosedAux_succ] at hClosed
    have hPre := ih (bool_and_left_true hClosed)
    have hCur := bool_and_right_true hClosed
    rw [reachStepAux_succ]
    rw [hPre]
    cases hSeed : getNatBool r k' with
    | false => rfl
    | true =>
      rw [hSeed] at hCur
      dsimp only at hCur
      unfold markSuccs
      cases hBb : blocks[k']? with
      | none => rfl
      | some bb =>
        rw [hBb] at hCur
        dsimp only
        rw [← hLen] at hCur
        exact foldl_setNatBool_eq_self (termSuccs bb.term) r hCur

private theorem list_all_false_witness {α : Type} {f : α → Bool} {xs : List α}
    (h : xs.all f = false) : ∃ x ∈ xs, f x = false := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    cases hy : f y with
    | false => exact ⟨y, List.Mem.head _, hy⟩
    | true =>
      rw [List.all_cons, hy, Bool.true_and] at h
      rcases ih h with ⟨x, hMem, hFx⟩
      exact ⟨x, List.Mem.tail _ hMem, hFx⟩

private theorem reachStepAux_grows_of_unclosed (blocks : List BasicBlock) (r : List Bool)
    (k : Nat) (hLen : r.length = blocks.length) (hUnc : reachClosedAux blocks r k = false) :
    countTrue r + 1 ≤ countTrue (reachStepAux blocks r k r) := by
  induction k with
  | zero => cases hUnc
  | succ k' ih =>
    rw [reachClosedAux_succ] at hUnc
    cases hPre : reachClosedAux blocks r k' with
    | false =>
      have hGrow := ih hPre
      rw [reachStepAux_succ]
      cases getNatBool r k' with
      | false => exact hGrow
      | true =>
        dsimp only
        unfold markSuccs
        cases blocks[k']? with
        | none => exact hGrow
        | some bb => exact Nat.le_trans hGrow (foldl_setNatBool_mono_count _ _)
    | true =>
      rw [hPre, Bool.true_and] at hUnc
      have hPreEq := reachStepAux_noop_of_closed blocks r k' hLen hPre
      rw [reachStepAux_succ]
      rw [hPreEq]
      cases hSeed : getNatBool r k' with
      | false => rw [hSeed] at hUnc; cases hUnc
      | true =>
        rw [hSeed] at hUnc
        dsimp only at hUnc
        unfold markSuccs
        cases hBb : blocks[k']? with
        | none => rw [hBb] at hUnc; cases hUnc
        | some bb =>
          rw [hBb] at hUnc
          rcases list_all_false_witness hUnc with ⟨s, hMem, hsFalse⟩
          have hsBound : Nat.ble (s + 1) blocks.length = true := by
            cases hB : Nat.ble (s + 1) blocks.length with
            | true => rfl
            | false => rw [hB] at hsFalse; cases hsFalse
          rw [hsBound] at hsFalse
          have hsLt : s < r.length := by rw [hLen]; exact nat_lt_of_ble_succ hsBound
          exact foldl_setNatBool_witness (termSuccs bb.term) r s hMem hsLt hsFalse

private theorem iterReach_length (n : Nat) (blocks : List BasicBlock) (r : List Bool) :
    (iterReach n blocks r).length = r.length := by
  induction n generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [iterReach_succ]
    unfold reachStep
    rw [ih (reachStepAux blocks r blocks.length r), reachStepAux_length]

private theorem iterReach_mono_get (n : Nat) (blocks : List BasicBlock) (r : List Bool) (j : Nat)
    (h : getNatBool r j = true) :
    getNatBool (iterReach n blocks r) j = true := by
  induction n generalizing r with
  | zero => exact h
  | succ k ih =>
    rw [iterReach_succ]
    unfold reachStep
    exact ih (reachStepAux blocks r blocks.length r) (reachStepAux_mono_get blocks r blocks.length r j h)

private theorem iterReach_noop_of_closed (n : Nat) (blocks : List BasicBlock) (r : List Bool)
    (hLen : r.length = blocks.length) (hClosed : reachClosedBool blocks r = true) :
    iterReach n blocks r = r := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [iterReach_succ]
    unfold reachStep
    rw [reachStepAux_noop_of_closed blocks r blocks.length hLen hClosed]
    exact ih

private theorem iterReach_closed_or_count_grows (n : Nat) (blocks : List BasicBlock) (r : List Bool)
    (hLen : r.length = blocks.length) :
    reachClosedBool blocks (iterReach n blocks r) = true ∨
    countTrue r + n ≤ countTrue (iterReach n blocks r) := by
  induction n generalizing r with
  | zero => exact Or.inr (Nat.le_refl _)
  | succ k ih =>
    cases hCl : reachClosedBool blocks r with
    | true =>
      rw [iterReach_noop_of_closed (k + 1) blocks r hLen hCl]
      exact Or.inl hCl
    | false =>
      have hGrow := reachStepAux_grows_of_unclosed blocks r blocks.length hLen hCl
      have hLen' : (reachStep blocks r).length = blocks.length := by
        unfold reachStep; rw [reachStepAux_length]; exact hLen
      cases ih (reachStep blocks r) hLen' with
      | inl hNextCl => exact Or.inl hNextCl
      | inr hNextCnt =>
        apply Or.inr
        have hStep1 : countTrue r + (k + 1) = (countTrue r + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc]
        rw [iterReach_succ]
        rw [hStep1]
        exact Nat.le_trans (Nat.add_le_add_right hGrow k) hNextCnt

private theorem getNatBool_replicate_false (n i : Nat) :
    getNatBool (List.replicate n false) i = false := by
  induction n generalizing i with
  | zero => rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i' => exact ih i'

private theorem countTrue_replicate_false (n : Nat) : countTrue (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

private theorem computeReachable_closed (blocks : List BasicBlock) (hNonEmpty : 0 < blocks.length) :
    reachClosedBool blocks (computeReachable blocks) = true ∧
    getNatBool (computeReachable blocks) 0 = true ∧
    (computeReachable blocks).length = blocks.length := by
  unfold computeReachable
  have hInitLen : (setNatBool (List.replicate blocks.length false) 0 true).length = blocks.length := by
    rw [setNatBool_length, List.length_replicate]
  have hInit0 : getNatBool (setNatBool (List.replicate blocks.length false) 0 true) 0 = true := by
    apply getNatBool_setNatBool_eq
    rw [List.length_replicate]
    exact hNonEmpty
  have hInitCnt : 1 ≤ countTrue (setNatBool (List.replicate blocks.length false) 0 true) := by
    have h0Lt : 0 < (List.replicate blocks.length false).length := by rw [List.length_replicate]; exact hNonEmpty
    have hF : getNatBool (List.replicate blocks.length false) 0 = false := getNatBool_replicate_false blocks.length 0
    have hC := countTrue_setNatBool_lt (List.replicate blocks.length false) 0 h0Lt hF
    rw [countTrue_replicate_false] at hC
    exact hC
  have hFinalLen : (iterReach blocks.length blocks (setNatBool (List.replicate blocks.length false) 0 true)).length = blocks.length := by
    rw [iterReach_length]; exact hInitLen
  have hFinal0 : getNatBool (iterReach blocks.length blocks (setNatBool (List.replicate blocks.length false) 0 true)) 0 = true :=
    iterReach_mono_get blocks.length blocks _ 0 hInit0
  have hCl : reachClosedBool blocks (iterReach blocks.length blocks (setNatBool (List.replicate blocks.length false) 0 true)) = true := by
    cases iterReach_closed_or_count_grows blocks.length blocks _ hInitLen with
    | inl hT => exact hT
    | inr hCnt =>
      exfalso
      have hLe : countTrue (iterReach blocks.length blocks (setNatBool (List.replicate blocks.length false) 0 true)) ≤
          (iterReach blocks.length blocks (setNatBool (List.replicate blocks.length false) 0 true)).length :=
        countTrue_le_length _
      rw [hFinalLen] at hLe
      have hContr : 1 + blocks.length ≤ blocks.length :=
        Nat.le_trans (Nat.le_trans (Nat.add_le_add_right hInitCnt blocks.length) hCnt) hLe
      exact Nat.not_succ_le_self blocks.length (by rw [Nat.add_comm 1 blocks.length] at hContr; exact hContr)
  exact ⟨hCl, hFinal0, hFinalLen⟩

private theorem reachClosedBool_step_true {blocks : List BasicBlock} {reach : List Bool} {i : Nat} {bb : BasicBlock} {s : Nat}
    (hCl : reachClosedBool blocks reach = true)
    (hi : getNatBool reach i = true) (hBb : blocks[i]? = some bb) (hsMem : s ∈ termSuccs bb.term)
    (hsLt : s < blocks.length) : getNatBool reach s = true := by
  have hiLt : i < blocks.length := by
    cases (Nat.lt_or_ge i blocks.length) with
    | inl h => exact h
    | inr hGe =>
      have hNone : blocks[i]? = none := List.getElem?_eq_none hGe
      rw [hNone] at hBb; cases hBb
  have hAux : ∀ k, k ≤ blocks.length → reachClosedAux blocks reach k = true →
      i < k → getNatBool reach s = true := by
    intro k hk hC hiK
    induction k with
    | zero => exact absurd hiK (Nat.not_lt_zero _)
    | succ k' ih =>
      unfold reachClosedAux at hC
      have hPre := bool_and_left_true hC
      have hCur := bool_and_right_true hC
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hiK) with
      | inl hLt' => exact ih (Nat.le_trans (Nat.le_succ _) hk) hPre hLt'
      | inr hEq =>
        subst hEq
        rw [hi, hBb] at hCur
        dsimp only at hCur
        have hOne := list_all_mem_true hCur hsMem
        rw [ble_succ_of_lt hsLt] at hOne
        exact hOne
  exact hAux blocks.length (Nat.le_refl _) hCl hiLt

private theorem buildRemapAux_length (reach : List Bool) (nextNew : Nat) :
    (buildRemapAux reach nextNew).length = reach.length := by
  induction reach generalizing nextNew with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> unfold buildRemapAux <;> simp only [List.length] <;> exact congrArg Nat.succ (ih _)

private theorem getNatBool_true_implies_remap_some (reach : List Bool) (nextNew i : Nat)
    (h : getNatBool reach i = true) :
    ∃ newIdx, (buildRemapAux reach nextNew)[i]? = some (some newIdx) ∧ nextNew ≤ newIdx := by
  induction reach generalizing nextNew i with
  | nil => cases h
  | cons b bs ih =>
    cases i with
    | zero =>
      cases b with
      | false => cases h
      | true => exact ⟨nextNew, rfl, Nat.le_refl _⟩
    | succ i' =>
      cases b with
      | false =>
        rcases ih nextNew i' h with ⟨newIdx, hRm, hLe⟩
        exact ⟨newIdx, hRm, hLe⟩
      | true =>
        rcases ih (nextNew + 1) i' h with ⟨newIdx, hRm, hLe⟩
        exact ⟨newIdx, hRm, Nat.le_trans (Nat.le_succ _) hLe⟩

private theorem getNatBool_false_implies_remap_none (reach : List Bool) (nextNew i : Nat)
    (hi : i < reach.length) (h : getNatBool reach i = false) :
    (buildRemapAux reach nextNew)[i]? = some none := by
  induction reach generalizing nextNew i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons b bs ih =>
    cases i with
    | zero =>
      cases b with
      | false => rfl
      | true => cases h
    | succ i' =>
      have hi' := Nat.lt_of_succ_lt_succ hi
      cases b with
      | false => exact ih nextNew i' hi' h
      | true => exact ih (nextNew + 1) i' hi' h

private theorem filterCompactBlocks_length_le (blocks : List BasicBlock) (reach : List Bool)
    (remap : List (Option Nat)) :
    (filterCompactBlocks blocks reach remap).length ≤ blocks.length := by
  induction blocks generalizing reach with
  | nil => cases reach <;> exact Nat.le_refl _
  | cons bb bbs ih =>
    cases reach with
    | nil => exact Nat.zero_le _
    | cons r rs =>
      cases r <;> unfold filterCompactBlocks
      · exact Nat.le_trans (ih rs) (Nat.le_succ _)
      · exact Nat.succ_le_succ (ih rs)

private theorem filterCompactBlocks_getElem_of_remap (blocks : List BasicBlock) (reach : List Bool)
    (remap : List (Option Nat)) (nextNew i newIdx : Nat)
    (hLen : blocks.length = reach.length)
    (hRemap : (buildRemapAux reach nextNew)[i]? = some (some newIdx)) :
    (filterCompactBlocks blocks reach remap)[newIdx - nextNew]? =
      blocks[i]?.map (fun bb => { bb with term := remapTerm remap bb.term }) := by
  induction blocks generalizing reach nextNew i with
  | nil =>
    have hNil : reach = [] := List.eq_nil_of_length_eq_zero hLen.symm
    subst hNil
    cases hRemap
  | cons bb bbs ih =>
    cases reach with
    | nil => cases hLen
    | cons r rs =>
      have hLen' : bbs.length = rs.length := Nat.succ.inj hLen
      cases i with
      | zero =>
        cases r with
        | false => cases hRemap
        | true =>
          rw [buildRemapAux_cons_true] at hRemap
          cases hRemap
          rw [Nat.sub_self]
          rfl
      | succ i' =>
        cases r with
        | false =>
          rw [buildRemapAux_cons_false] at hRemap
          rw [List.getElem?_cons_succ] at hRemap
          exact ih rs nextNew i' hLen' hRemap
        | true =>
          rw [buildRemapAux_cons_true] at hRemap
          rw [List.getElem?_cons_succ] at hRemap
          rcases getNatBool_true_implies_remap_some rs (nextNew + 1) i' (by
            cases hG : getNatBool rs i' with
            | true => rfl
            | false =>
              cases (Nat.lt_or_ge i' rs.length) with
              | inl hLt =>
                rw [getNatBool_false_implies_remap_none rs (nextNew + 1) i' hLt hG] at hRemap
                cases hRemap
              | inr hGe =>
                have hNone : (buildRemapAux rs (nextNew + 1))[i']? = none := by
                  apply List.getElem?_eq_none; rw [buildRemapAux_length]; exact hGe
                rw [hNone] at hRemap; cases hRemap) with ⟨m, hm, hmLe⟩
          rw [hm] at hRemap
          cases hRemap
          have hDiff : newIdx - nextNew = (newIdx - (nextNew + 1)) + 1 := by
            cases hmLe' : newIdx - (nextNew + 1) with
            | zero =>
              have hEq : newIdx = nextNew + 1 := Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hmLe') hmLe
              rw [hEq, Nat.add_sub_cancel_left]
            | succ d =>
              have h1 : newIdx = (nextNew + 1) + (d + 1) := by
                rw [← hmLe', Nat.add_sub_of_le hmLe]
              rw [h1, Nat.add_assoc, Nat.add_comm 1 (d + 1), Nat.add_sub_cancel_left]
          rw [filterCompactBlocks_cons_true]
          rw [hDiff]
          exact ih rs (nextNew + 1) i' hLen' hm

private theorem remapIdx_lt_eq {reach : List Bool} {i newIdx : Nat}
    (hRemap : (buildRemapAux reach 0)[i]? = some (some newIdx)) :
    remapIdx (buildRemapAux reach 0) i = newIdx := by
  unfold remapIdx
  rw [hRemap]

private theorem remapIdx_oob {reach : List Bool} {i : Nat}
    (hGe : reach.length ≤ i) :
    remapIdx (buildRemapAux reach 0) i = i := by
  unfold remapIdx
  have hNone : (buildRemapAux reach 0)[i]? = none := by
    apply List.getElem?_eq_none
    rw [buildRemapAux_length]
    exact hGe
  rw [hNone]

private theorem lookupSwitchTarget_remap (remap : List (Option Nat))
    (v : Nat) (cases : List (Nat × Nat)) (otherwise : Nat) :
    lookupSwitchTarget v (cases.map fun (val, tgt) => (val, remapIdx remap tgt)) (remapIdx remap otherwise) =
      remapIdx remap (lookupSwitchTarget v cases otherwise) := by
  induction cases with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [List.map, lookupSwitchTarget]
    cases (v == hd.1) with
    | true => rfl
    | false => exact ih

private theorem bodyCanUnwind_compact (cfg : CompileCfg) (b : Body) :
    bodyCanUnwind cfg (compactReachableBody b) = bodyCanUnwind cfg b := rfl

private theorem stepTerm_compact_bisim (cfg : CompileCfg) (mode : EvalMode) (b : Body)
    (remap : List (Option Nat))
    (stComp stOrig : EvalState) (bbData : BasicBlock) (ev : StepEvent)
    (hSame : stComp = { stOrig with bb := remapIdx remap stOrig.bb }) :
    (match stepTerm cfg mode (compactReachableBody b) stComp (remapTerm remap bbData.term) ev,
           stepTerm cfg mode b stOrig bbData.term ev with
     | .finished oC stC, .finished oO stO =>
       oC = oO ∧ stC.store = stO.store ∧ stC.trace = stO.trace ∧ stC.stmtIdx = stO.stmtIdx
     | .nextState stC, .nextState stO =>
       stC = { stO with bb := remapIdx remap stO.bb } ∧ stO.bb ∈ termSuccs bbData.term
     | _, _ => False) := by
  subst hSame
  cases bbData.term with
  | goto tgt =>
    exact ⟨rfl, List.Mem.head _⟩
  | falseEdge rt it =>
    unfold remapTerm stepTerm
    cases mode.forbidsAnalysis with
    | false =>
      constructor
      · rfl
      · dsimp only [termSuccs]; exact List.Mem.head _
    | true => exact ⟨rfl, rfl, rfl, rfl⟩
  | falseUnwind rt u =>
    unfold remapTerm stepTerm
    cases mode.forbidsAnalysis with
    | false =>
      constructor
      · rfl
      · dsimp only [termSuccs]; cases u <;> exact List.Mem.head _
    | true => exact ⟨rfl, rfl, rfl, rfl⟩
  | switchInt d cases oth =>
    unfold remapTerm stepTerm; dsimp only
    cases hRd : readDiscrFromPlace stOrig.store (.localSlot d) with
    | error k => exact ⟨rfl, rfl, rfl, rfl⟩
    | ok dv =>
      dsimp only
      rw [lookupSwitchTarget_remap]
      exact ⟨rfl, lookupSwitchTarget_mem dv cases oth⟩
  | call c dst tgt u =>
    unfold remapTerm stepTerm; dsimp only
    rw [bodyCanUnwind_compact]
    cases ev.unwind with
    | false =>
      refine ⟨rfl, ?_⟩
      cases u <;> exact List.Mem.head _
    | true =>
      dsimp only
      cases u with
      | cleanup pad => exact ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩
      | terminate r => exact ⟨rfl, rfl, rfl, rfl⟩
      | unreachable => exact ⟨rfl, rfl, rfl, rfl⟩
      | continue_ =>
        unfold takeUnwind
        cases bodyCanUnwind cfg b <;> dsimp only
        · cases mode.isRuntimeUnwind <;> exact ⟨rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl⟩
  | drop l tag tgt u =>
    unfold remapTerm stepTerm; dsimp only
    rw [bodyCanUnwind_compact]
    cases ev.unwind with
    | false =>
      refine ⟨rfl, ?_⟩
      cases u <;> exact List.Mem.head _
    | true =>
      dsimp only
      cases u with
      | cleanup pad => exact ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩
      | terminate r => exact ⟨rfl, rfl, rfl, rfl⟩
      | unreachable => exact ⟨rfl, rfl, rfl, rfl⟩
      | continue_ =>
        unfold takeUnwind
        cases bodyCanUnwind cfg b <;> dsimp only
        · cases mode.isRuntimeUnwind <;> exact ⟨rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl⟩
  | assert cond exp tgt u =>
    unfold remapTerm stepTerm; dsimp only
    rw [bodyCanUnwind_compact]
    cases readDiscrFromPlace stOrig.store (.localSlot cond) with
    | error _ => exact ⟨rfl, rfl, rfl, rfl⟩
    | ok dv =>
      dsimp only
      cases ((dv != 0) == exp) with
      | true =>
        refine ⟨rfl, ?_⟩
        cases u <;> exact List.Mem.head _
      | false =>
        dsimp only
        cases u with
        | cleanup pad => exact ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩
        | terminate _ => exact ⟨rfl, rfl, rfl, rfl⟩
        | unreachable => exact ⟨rfl, rfl, rfl, rfl⟩
        | continue_ =>
          unfold takeUnwind
          cases bodyCanUnwind cfg b <;> dsimp only
          · cases mode.isRuntimeUnwind <;> exact ⟨rfl, rfl, rfl, rfl⟩
          · exact ⟨rfl, rfl, rfl, rfl⟩
  | inlineAsm m tgt u =>
    unfold remapTerm stepTerm; dsimp only
    rw [bodyCanUnwind_compact]
    cases ev.unwind with
    | false =>
      refine ⟨rfl, ?_⟩
      cases u <;> exact List.Mem.head _
    | true =>
      dsimp only
      cases u with
      | cleanup pad => exact ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩
      | terminate _ => exact ⟨rfl, rfl, rfl, rfl⟩
      | unreachable => exact ⟨rfl, rfl, rfl, rfl⟩
      | continue_ =>
        unfold takeUnwind
        cases bodyCanUnwind cfg b <;> dsimp only
        · cases mode.isRuntimeUnwind <;> exact ⟨rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl⟩
  | return_ r =>
    unfold remapTerm stepTerm; dsimp only
    cases readValueFromPlace stOrig.store (.localSlot r) with
    | error _ => exact ⟨rfl, rfl, rfl, rfl⟩
    | ok v => cases v <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | unwindResume =>
    unfold remapTerm stepTerm; dsimp only
    rw [bodyCanUnwind_compact]
    cases bodyCanUnwind cfg b <;> dsimp only
    · cases mode.isRuntimeUnwind <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  | unwindTerminate _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | unreachable => exact ⟨rfl, rfl, rfl, rfl⟩

private theorem stepStmt_remap_bb_irrel (mode : EvalMode) (stOrig : EvalState) (bbNew : Nat) (s : Stmt) :
    match stepStmt mode { stOrig with bb := bbNew } s, stepStmt mode stOrig s with
    | .error k1, .error k2 => k1 = k2
    | .ok st1, .ok st2 => st1 = { st2 with bb := bbNew }
    | _, _ => False := by
  cases s with
  | nop | recordDrop _ | storageLive _ | storageDead _
  | assignConst _ _ | assignPtr _ _ | assignEnum _ _ _ => exact rfl
  | assignCopy _ src =>
    unfold stepStmt; dsimp only
    cases readValueFromPlace stOrig.store src <;> exact rfl
  | assignDiscr _ src =>
    unfold stepStmt; dsimp only
    cases readDiscrFromPlace stOrig.store src <;> exact rfl
  | assignPtrCoercion _ kind src =>
    unfold stepStmt; dsimp only
    cases mode.forbidsAnalysis && kind != .ptrToPtr with
    | false =>
      cases readValueFromPlace stOrig.store (.localSlot src) <;> exact rfl
    | true => exact rfl
  | placeMention p =>
    unfold stepStmt; dsimp only
    cases evalPlaceAddr stOrig.store p <;> exact rfl
  | coverageMarker rem _ =>
    unfold stepStmt; dsimp only
    cases mode.forbidsAnalysis && rem <;> exact rfl
  | ascribeUserType _ | dropHint _ =>
    unfold stepStmt; dsimp only
    cases mode.forbidsAnalysis <;> exact rfl
  | assignFakeBorrow _ _ src =>
    unfold stepStmt; dsimp only
    cases mode.forbidsAnalysis with
    | false =>
      cases mode with
      | analysisUnguarded => exact rfl
      | analysisGuarded => cases evalPlaceAddr stOrig.store src <;> exact rfl
      | analysisPostCleanup => cases evalPlaceAddr stOrig.store src <;> exact rfl
      | runtime => cases evalPlaceAddr stOrig.store src <;> exact rfl
    | true => exact rfl
  | fakeRead cause p =>
    unfold stepStmt; dsimp only
    cases mode.forbidsAnalysis with
    | false =>
      cases mode with
      | analysisUnguarded => exact rfl
      | analysisGuarded => cases checkFakeReadPlace stOrig.store stOrig.fakeBorrows cause p <;> exact rfl
      | analysisPostCleanup => cases checkFakeReadPlace stOrig.store stOrig.fakeBorrows cause p <;> exact rfl
      | runtime => cases checkFakeReadPlace stOrig.store stOrig.fakeBorrows cause p <;> exact rfl
    | true => exact rfl

private theorem compactReachableBody_bisim_aux (cfg : CompileCfg) (mode : EvalMode)
    (fuel : Nat) (b : Body) (stComp stOrig : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat)
    (hNonEmpty : 0 < b.blocks.length)
    (hInv : stOrig.bb < b.blocks.length → getNatBool (computeReachable b.blocks) stOrig.bb = true)
    (hMatch : stComp = { stOrig with bb := remapIdx (buildRemapAux (computeReachable b.blocks) 0) stOrig.bb }) :
    let rC := runEval cfg mode fuel (compactReachableBody b) stComp oracle stepIdx
    let rO := runEval cfg mode fuel b stOrig oracle stepIdx
    rC.2 = rO.2 ∧ rC.1.store = rO.1.store ∧ rC.1.trace = rO.1.trace := by
  induction fuel generalizing stComp stOrig stepIdx with
  | zero =>
    subst hMatch
    exact ⟨rfl, rfl, rfl⟩
  | succ f ih =>
    have hReach := computeReachable_closed b.blocks hNonEmpty
    rcases hReach with ⟨hCl, _, hLen⟩
    let reach := computeReachable b.blocks
    let remap := buildRemapAux reach 0
    have hCompBlks : (compactReachableBody b).blocks = filterCompactBlocks b.blocks reach remap := rfl
    rw [runEval_succ, runEval_succ]
    cases (Nat.lt_or_ge stOrig.bb b.blocks.length) with
    | inr hGe =>
      have hNoneO : b.blocks[stOrig.bb]? = none := List.getElem?_eq_none hGe
      have hRemapOob : remapIdx remap stOrig.bb = stOrig.bb := remapIdx_oob (by rw [hLen]; exact hGe)
      have hGeC : (filterCompactBlocks b.blocks reach remap).length ≤ stOrig.bb :=
        Nat.le_trans (filterCompactBlocks_length_le b.blocks reach remap) hGe
      have hNoneC : (compactReachableBody b).blocks[stComp.bb]? = none := by
        rw [hCompBlks, hMatch]
        dsimp only
        rw [hRemapOob]
        exact List.getElem?_eq_none hGeC
      rw [hNoneC, hNoneO]
      subst hMatch
      exact ⟨rfl, rfl, rfl⟩
    | inl hLt =>
      have hReachBb : getNatBool reach stOrig.bb = true := hInv hLt
      rcases getNatBool_true_implies_remap_some reach 0 stOrig.bb hReachBb with ⟨newIdx, hRemapEq, _⟩
      have hRemapVal : remapIdx remap stOrig.bb = newIdx := by
        unfold remapIdx; rw [hRemapEq]
      have hGetC := filterCompactBlocks_getElem_of_remap b.blocks reach remap 0 stOrig.bb newIdx hLen.symm hRemapEq
      rw [Nat.sub_zero] at hGetC
      cases hBb : b.blocks[stOrig.bb]? with
      | none =>
        have hGe := List.getElem?_eq_none_iff.mp hBb
        exact absurd hLt (Nat.not_lt_of_le hGe)
      | some bbData =>
        rw [hBb] at hGetC
        dsimp only [Option.map] at hGetC
        have hCompAt : (compactReachableBody b).blocks[stComp.bb]? =
            some { bbData with term := remapTerm remap bbData.term } := by
          rw [hCompBlks, hMatch, hRemapVal]; exact hGetC
        rw [hCompAt]
        dsimp only
        have hIdxEq : stComp.stmtIdx = stOrig.stmtIdx := by rw [hMatch]
        rw [hIdxEq]
        cases hst : bbData.stmts[stOrig.stmtIdx]? with
        | some s =>
          dsimp only
          have hStMatch := stepStmt_remap_bb_irrel mode stOrig (remapIdx remap stOrig.bb) s
          rw [hMatch]
          cases hSC : stepStmt mode { stOrig with bb := remapIdx remap stOrig.bb } s <;>
          cases hSO : stepStmt mode stOrig s <;>
          rw [hSC, hSO] at hStMatch
          · cases hStMatch; exact ⟨rfl, rfl, rfl⟩
          · exact False.elim hStMatch
          · exact False.elim hStMatch
          · dsimp only at hStMatch ⊢
            apply ih _ _ (stepIdx + 1)
            · rw [stepStmt_preserves_bb mode stOrig _ s hSO]; exact hInv
            · rw [hStMatch, stepStmt_preserves_bb mode stOrig _ s hSO]
        | none =>
          dsimp only
          have hTmBisim := stepTerm_compact_bisim cfg mode b remap stComp stOrig bbData (oracle stepIdx) hMatch
          cases hTC : stepTerm cfg mode (compactReachableBody b) stComp (remapTerm remap bbData.term) (oracle stepIdx) with
          | nextState stC =>
            cases hTO : stepTerm cfg mode b stOrig bbData.term (oracle stepIdx) with
            | nextState stO =>
              rw [hTC, hTO] at hTmBisim
              dsimp only at hTmBisim
              rcases hTmBisim with ⟨hNextEq, hSuccMem⟩
              apply ih _ _ (stepIdx + 1)
              · intro hSuccLt
                exact reachClosedBool_step_true hCl hReachBb hBb hSuccMem hSuccLt
              · exact hNextEq
            | finished oO stO =>
              rw [hTC, hTO] at hTmBisim
              exact False.elim hTmBisim
          | finished oC stC =>
            cases hTO : stepTerm cfg mode b stOrig bbData.term (oracle stepIdx) with
            | nextState stO =>
              rw [hTC, hTO] at hTmBisim
              exact False.elim hTmBisim
            | finished oO stO =>
              rw [hTC, hTO] at hTmBisim
              exact ⟨hTmBisim.1, hTmBisim.2.1, hTmBisim.2.2.1⟩

theorem compactReachableBody_bisim (cfg : CompileCfg) (mode : EvalMode)
    (fuel : Nat) (b : Body) (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0)
    (hBbZero : st.bb = 0) :
    let rC := runEval cfg mode fuel (compactReachableBody b) st oracle stepIdx
    let rO := runEval cfg mode fuel b st oracle stepIdx
    rC.2 = rO.2 ∧ rC.1.store = rO.1.store ∧ rC.1.trace = rO.1.trace := by
  cases hLen : b.blocks.length with
  | zero =>
    have hNil : b.blocks = [] := List.eq_nil_of_length_eq_zero hLen
    have hCompNil : compactReachableBody b = b := by
      cases b with
      | mk bBlks bAbi bFor bAnn =>
        dsimp only at hNil
        subst hNil
        rfl
    rw [hCompNil]
    exact ⟨rfl, rfl, rfl⟩
  | succ n =>
    have hPos : 0 < b.blocks.length := by rw [hLen]; exact Nat.succ_pos n
    have hReach := computeReachable_closed b.blocks hPos
    have hRemap0 : remapIdx (buildRemapAux (computeReachable b.blocks) 0) 0 = 0 := by
      cases hRm : computeReachable b.blocks with
      | nil => rw [hRm] at hReach; cases hReach.2.1
      | cons r0 rs =>
        rw [hRm] at hReach
        cases r0 with
        | false => cases hReach.2.1
        | true =>
          unfold remapIdx buildRemapAux
          rfl
    have hMatch0 : st = { st with bb := remapIdx (buildRemapAux (computeReachable b.blocks) 0) st.bb } := by
      cases st with
      | mk sBb sIdx sSt sFb sTr =>
        dsimp only at hBbZero ⊢
        rw [hBbZero, hRemap0]
    exact compactReachableBody_bisim_aux cfg mode fuel b st st oracle stepIdx hPos
      (fun _ => by rw [hBbZero]; exact hReach.2.1) hMatch0

/-- Proof that orphaned (`reach = false`) cleanup blocks are never mapped into `buildRemapAux`,
confirming dead cleanup blocks stripped by `AbortUnwindingCalls` (`remove_dead_blocks`) are unreachable
from `bb = 0`. -/
theorem unreachable_blocks_dropped_by_compaction (b : Body) (i : Nat)
    (hi : i < b.blocks.length)
    (hUnreach : getNatBool (computeReachable b.blocks) i = false) :
    (buildRemapAux (computeReachable b.blocks) 0)[i]? = some none := by
  have hLen : (computeReachable b.blocks).length = b.blocks.length := by
    unfold computeReachable
    rw [iterReach_length, setNatBool_length, List.length_replicate]
  exact getNatBool_false_implies_remap_none (computeReachable b.blocks) 0 i (by rw [hLen]; exact hi) hUnreach

/-! ## 9.4 Complete `AbortUnwindingCalls` Theorems (`abortUnwindingCalls = compactReachableBody ∘ abortRewriteOnly`) -/

theorem abortUnwindingCalls_exact_analysis_equiv (cfg : CompileCfg) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0)
    (hBbZero : st.bb = 0)
    (hWf : wfBodyForAbort b = true)
    (hEntry : match b.blocks[0]? with | some bb => cfg.targetSupportsUnwinding = false → bb.isCleanup = false | none => True)
    (hAbi : OracleRespectsAbi cfg b st oracle stepIdx fuel) :
    let rRt := runEval cfg .runtime fuel (abortUnwindingCalls cfg b) st oracle stepIdx
    let rAn := runEval cfg .analysisPostCleanup fuel b st oracle stepIdx
    rRt.2 = rAn.2 ∧ rRt.1.store = rAn.1.store ∧ rRt.1.trace = rAn.1.trace := by
  have hBisim := compactReachableBody_bisim cfg .runtime fuel (abortRewriteOnly cfg b) st oracle stepIdx hBbZero
  have hEntrySt : match b.blocks[st.bb]? with | some bb => cfg.targetSupportsUnwinding = false → bb.isCleanup = false | none => True := by
    rw [hBbZero]; exact hEntry
  have hRew := abortRewriteOnly_exact_analysis_equiv cfg fuel b st oracle stepIdx hWf hEntrySt hAbi
  unfold abortUnwindingCalls
  rw [hRew] at hBisim
  exact hBisim

theorem abortUnwindingCalls_nonpanicking_equiv (cfg cfg0 : CompileCfg) (fuel : Nat) (b : Body)
    (st : EvalState) (oracle : Nat → StepEvent) (stepIdx : Nat := 0)
    (hBbZero : st.bb = 0)
    (hWf : wfBodyForAbort b = true)
    (hInBounds : match b.blocks[0]? with | some bb => bb.isCleanup = false | none => True)
    (hNoPanic : NonPanickingRun b st oracle stepIdx fuel) :
    let rRt := runEval cfg .runtime fuel (abortUnwindingCalls cfg b) st oracle stepIdx
    let r0 := runEval cfg0 .runtime fuel b st oracle stepIdx
    rRt.2 = r0.2 ∧ rRt.1.store = r0.1.store ∧ rRt.1.trace = r0.1.trace := by
  have hBisim := compactReachableBody_bisim cfg .runtime fuel (abortRewriteOnly cfg b) st oracle stepIdx hBbZero
  have hInBoundsSt : match b.blocks[st.bb]? with | some bb => bb.isCleanup = false | none => True := by
    rw [hBbZero]; exact hInBounds
  have hRew := abortRewriteOnly_nonpanicking_equiv cfg cfg0 fuel b st oracle stepIdx hWf hInBoundsSt hNoPanic
  unfold abortUnwindingCalls
  rw [hRew] at hBisim
  exact hBisim

/-! ## 10. End-to-End Composition: Analysis-Guarded MIR -> Validated Runtime MIR -/

private theorem termWithUnwind_allowed_in_runtime (t : Term) (u : UnwindAction)
    (h : termAllowedInRuntime t = true) :
    termAllowedInRuntime (termWithUnwind t u) = true := by
  cases t <;> first | rfl | exact h

private theorem abortRewriteTerm_allowed_in_runtime (cfg : CompileCfg) (bCanUnwind isCleanup : Bool)
    (t : Term) (h : termAllowedInRuntime t = true) :
    termAllowedInRuntime (abortRewriteTerm cfg bCanUnwind isCleanup t) = true := by
  unfold abortRewriteTerm
  cases t with
  | falseEdge _ _ | falseUnwind _ _ => cases h
  | goto _ | switchInt _ _ _ | return_ _ | unreachable | unwindTerminate _ =>
    cases isCleanup <;> exact h
  | unwindResume =>
    cases isCleanup with
    | true =>
      cases !cfg.targetSupportsUnwinding with
      | true => rfl
      | false => cases !bCanUnwind <;> rfl
    | false =>
      cases hTsu : !cfg.targetSupportsUnwinding with
      | true => rfl
      | false => cases !bCanUnwind <;> rfl
  | call c _ _ u =>
    cases isCleanup with
    | true => rfl
    | false =>
      dsimp only [termCanUnwind, termUnwind]
      cases (!callCanUnwind cfg c || !cfg.targetSupportsUnwinding) with
      | true => rfl
      | false => cases (!bCanUnwind && (u == .continue_)) <;> rfl
  | drop _ _ _ u =>
    cases isCleanup with
    | true => rfl
    | false =>
      dsimp only [termCanUnwind, termUnwind]
      cases (!dropCanUnwind cfg || !cfg.targetSupportsUnwinding) with
      | true => rfl
      | false => cases (!bCanUnwind && (u == .continue_)) <;> rfl
  | assert _ _ _ u =>
    cases isCleanup with
    | true => rfl
    | false =>
      dsimp only [termCanUnwind, termUnwind]
      cases (!assertCanUnwind cfg || !cfg.targetSupportsUnwinding) with
      | true => rfl
      | false => cases (!bCanUnwind && (u == .continue_)) <;> rfl
  | inlineAsm mayUnw _ u =>
    cases isCleanup with
    | true => rfl
    | false =>
      dsimp only [termCanUnwind, termUnwind]
      cases (!mayUnw || !cfg.targetSupportsUnwinding) with
      | true => rfl
      | false => cases (!bCanUnwind && (u == .continue_)) <;> rfl

private theorem remapTerm_allowed_in_runtime (remap : List (Option Nat)) (t : Term)
    (h : termAllowedInRuntime t = true) :
    termAllowedInRuntime (remapTerm remap t) = true := by
  cases t <;> first | rfl | exact h

private theorem list_all_map_mem_true {α β : Type} (g : α → Bool) (f : β → Bool) (m : α → β)
    (xs : List α) (hAll : xs.all g = true) (hStep : ∀ x, g x = true → f (m x) = true) :
    (xs.map m).all f = true := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    have hHd := hStep hd (bool_and_left_true hAll)
    have hTl := ih (bool_and_right_true hAll)
    dsimp only [List.map, List.all]
    rw [hHd, hTl]
    rfl

private theorem abortUnwindingCalls_preserves_validRuntimeSyntax (cfg : CompileCfg) (b : Body)
    (h : validRuntimeSyntax b = true) :
    validRuntimeSyntax (abortUnwindingCalls cfg b) = true := by
  unfold validRuntimeSyntax at h ⊢
  have hAnn : (!b.hasUserTypeAnnots) = true := bool_and_left_true h
  have hBlks : b.blocks.all (fun bb => bb.stmts.all stmtAllowedInRuntime && termAllowedInRuntime bb.term) = true :=
    bool_and_right_true h
  have hRewBlks : (abortRewriteOnly cfg b).blocks.all
      (fun bb => bb.stmts.all stmtAllowedInRuntime && termAllowedInRuntime bb.term) = true := by
    apply list_all_map_mem_true _ _ _ b.blocks hBlks
    intro bb hBb
    unfold abortRewriteBlock
    dsimp only
    rw [bool_and_left_true hBb, abortRewriteTerm_allowed_in_runtime cfg (bodyCanUnwind cfg b) bb.isCleanup bb.term (bool_and_right_true hBb)]
    rfl
  have hFilt : ∀ (blocks : List BasicBlock) (reach : List Bool) (remap : List (Option Nat)),
      blocks.all (fun bb => bb.stmts.all stmtAllowedInRuntime && termAllowedInRuntime bb.term) = true →
      (filterCompactBlocks blocks reach remap).all (fun bb => bb.stmts.all stmtAllowedInRuntime && termAllowedInRuntime bb.term) = true := by
    intro blocks reach remap hAll
    induction blocks generalizing reach with
    | nil => cases reach <;> rfl
    | cons hd tl ih =>
      cases reach with
      | nil => rfl
      | cons r rs =>
        have hHd := bool_and_left_true hAll
        have hTl := bool_and_right_true hAll
        cases r <;> unfold filterCompactBlocks
        · exact ih rs hTl
        · rw [List.all_cons]
          dsimp only
          rw [bool_and_left_true hHd, remapTerm_allowed_in_runtime remap hd.term (bool_and_right_true hHd), Bool.true_and, Bool.true_and]
          exact ih rs hTl
  unfold abortUnwindingCalls compactReachableBody
  dsimp only [abortRewriteOnly] at hRewBlks ⊢
  rw [hAnn, Bool.true_and]
  exact hFilt (b.blocks.map (abortRewriteBlock cfg (bodyCanUnwind cfg b)))
    (computeReachable (b.blocks.map (abortRewriteBlock cfg (bodyCanUnwind cfg b))))
    (buildRemapAux (computeReachable (b.blocks.map (abortRewriteBlock cfg (bodyCanUnwind cfg b)))) 0)
    hRewBlks

theorem full_analysis_to_runtime_lowering_sound (isFake : Nat → Bool) (cfg : CompileCfg)
    (fuel : Nat) (b : Body) (stRt stAn : EvalState) (oracle : Nat → StepEvent)
    (hClean : bodyUsesFakeCleanly isFake b = true)
    (hCert : CertifiedForFakeRead cfg fuel b stAn oracle 0)
    (hWf : wfBodyForAbort (cleanupPostBorrowck b) = true)
    (hEntry : match (cleanupPostBorrowck b).blocks[0]? with
              | some bb => cfg.targetSupportsUnwinding = false → bb.isCleanup = false
              | none => True)
    (hAbi : OracleRespectsAbi cfg (cleanupPostBorrowck b) stRt oracle 0 fuel)
    (hBbZero : stRt.bb = 0)
    (hBbEq : stRt.bb = stAn.bb) (hIdx : stRt.stmtIdx = stAn.stmtIdx)
    (hTr : stRt.trace = stAn.trace) (hLen : stRt.store.length = stAn.store.length)
    (hAg : StoresAgreeNonFake isFake stRt.store stAn.store)
    (hPtrRt : PtrsNonFake isFake stRt.store) (hPtrAn : PtrsNonFake isFake stAn.store) :
    let lowered := abortUnwindingCalls cfg (cleanupPostBorrowck b)
    let rRt := runEval cfg .runtime fuel lowered stRt oracle 0
    let rAn := runEval cfg .analysisGuarded fuel b stAn oracle 0
    validRuntimeSyntax lowered = true ∧
    rRt.2 = rAn.2 ∧ rRt.1.trace = rAn.1.trace ∧
    StoresAgreeNonFake isFake rRt.1.store rAn.1.store := by
  have hSyn : validRuntimeSyntax (abortUnwindingCalls cfg (cleanupPostBorrowck b)) = true :=
    abortUnwindingCalls_preserves_validRuntimeSyntax cfg (cleanupPostBorrowck b) (cleanupPostBorrowck_syntax_valid b)
  have hStep2 := abortUnwindingCalls_exact_analysis_equiv cfg fuel (cleanupPostBorrowck b) stRt oracle 0 hBbZero hWf hEntry hAbi
  have hStep1 := cleanupPostBorrowck_certified_equiv isFake cfg fuel b stRt stAn oracle 0
    hClean hCert hBbEq hIdx hTr hLen hAg hPtrRt hPtrAn
  refine ⟨hSyn, ?_, ?_, ?_⟩
  · exact Eq.trans hStep2.1 hStep1.1
  · rw [hStep2.2.2]; exact hStep1.2.1
  · rw [hStep2.2.1]; exact hStep1.2.2

/-! ## 11. Concrete Sharpness Counterexamples (All Kernel-Checked by `rfl`) -/

private def emptyCfgUnwind : CompileCfg :=
  { panicAborts := false, targetSupportsUnwinding := true, panicInDropUnwinds := true }

private def emptyCfgAbort : CompileCfg :=
  { panicAborts := true, targetSupportsUnwinding := true, panicInDropUnwinds := true }

private def silentOracle : Nat → StepEvent :=
  fun _ => { unwind := false, retVal := 0 }

private def panicOracle : Nat → StepEvent :=
  fun _ => { unwind := true, retVal := 0 }

/-- CE1a: Uncertified `FakeRead(.forMatchedPlace, _)` erasure hides uninitialized match-scrutinee UB. -/
private def ce1aBody : Body :=
  { blocks :=
      [{ stmts := [.storageLive 0, .fakeRead .forMatchedPlace (.localSlot 0), .assignConst 1 42]
         term := .return_ 1
         isCleanup := false }]
    bodyAbi := .rust
    bodyIsForeign := false
    hasUserTypeAnnots := true }

private def ce1aInitState : EvalState :=
  { bb := 0, stmtIdx := 0, store := [.dead, .dead], fakeBorrows := [], trace := [] }

theorem ce1a_uncertified_fakeread_uninit_scrutinee :
    (runEval emptyCfgUnwind .analysisPostCleanup 10 (cleanupPostBorrowck ce1aBody) ce1aInitState silentOracle 0).2 = .returned 42 ∧
    (runEval emptyCfgUnwind .analysisGuarded 10 ce1aBody ce1aInitState silentOracle 0).2 = .fault .ubFakeReadViolation :=
  ⟨rfl, rfl⟩

/-- CE1b: Uncertified `FakeRead(.forMatchedPlace, _)` erasure hides invalid enum discriminant UB. -/
private def ce1bBody : Body :=
  { blocks :=
      [{ stmts := [.assignEnum 0 2 2, .fakeRead .forMatchedPlace (.localSlot 0), .assignConst 1 7]
         term := .return_ 1
         isCleanup := false }]
    bodyAbi := .rust
    bodyIsForeign := false
    hasUserTypeAnnots := true }

private def ce1bInitState : EvalState :=
  { bb := 0, stmtIdx := 0, store := [.dead, .dead], fakeBorrows := [], trace := [] }

theorem ce1b_uncertified_fakeread_invalid_discriminant :
    (runEval emptyCfgUnwind .analysisPostCleanup 10 (cleanupPostBorrowck ce1bBody) ce1bInitState silentOracle 0).2 = .returned 7 ∧
    (runEval emptyCfgUnwind .analysisGuarded 10 ce1bBody ce1bInitState silentOracle 0).2 = .fault .ubFakeReadViolation :=
  ⟨rfl, rfl⟩

/-- CE1c: Mutating the matched place between `BorrowKind::Fake` and `FakeRead(.forMatchGuard, _)`
triggers `.ubFakeReadViolation` under guarded Analysis MIR, whereas `CleanupPostBorrowck`
erases both and silently returns the mutated discriminant (`#102030` pattern). -/
private def ce1cBody : Body :=
  { blocks :=
      [{ stmts :=
           [ .assignEnum 0 0 2
           , .assignFakeBorrow 1 .deep (.localSlot 0)
           , .assignEnum 0 1 2
           , .fakeRead .forMatchGuard (.localSlot 0)
           , .assignDiscr 2 (.localSlot 0) ]
         term := .return_ 2
         isCleanup := false }]
    bodyAbi := .rust
    bodyIsForeign := false
    hasUserTypeAnnots := false }

private def ce1cInitState : EvalState :=
  { bb := 0, stmtIdx := 0, store := [.dead, .dead, .dead], fakeBorrows := [], trace := [] }

theorem ce1c_guard_mutation_bypasses_erased_fake_borrow :
    (runEval emptyCfgUnwind .analysisPostCleanup 12 (cleanupPostBorrowck ce1cBody) ce1cInitState silentOracle 0).2 = .returned 1 ∧
    (runEval emptyCfgUnwind .analysisGuarded 12 ce1cBody ce1cInitState silentOracle 0).2 = .fault .ubFakeReadViolation :=
  ⟨rfl, rfl⟩

/-- CE2: Mutant lowering rewriting `UnwindAction::Cleanup` to `UnwindAction::Continue` across a
non-unwinding C-ABI boundary (`bodyAbi := .cNounwind`) skips destructors and triggers
`.ubUnwindPastNounwindAbi`, whereas real `AbortUnwindingCalls` preserves `Cleanup` and rewrites
its `UnwindResume` terminator to `UnwindTerminate(Abi)`. -/
private def mutantCleanupToContinue (cfg : CompileCfg) (b : Body) : Body :=
  let bCan := bodyCanUnwind cfg b
  { b with blocks := b.blocks.map fun bb =>
      if bb.isCleanup then
        abortRewriteBlock cfg bCan bb
      else
        match termUnwind bb.term with
        | some (.cleanup _) =>
          { bb with term := termWithUnwind bb.term .continue_ }
        | _ => abortRewriteBlock cfg bCan bb }

private def ce2Body : Body :=
  { blocks :=
      [ { stmts := []
          term := .call { abi := .rust, isForeign := false, isFnPtr := false } 0 1 (.cleanup 2)
          isCleanup := false }
      , { stmts := [.assignConst 0 0]
          term := .return_ 0
          isCleanup := false }
      , { stmts := [.recordDrop 99]
          term := .unwindResume
          isCleanup := true } ]
    bodyAbi := .cNounwind
    bodyIsForeign := false
    hasUserTypeAnnots := false }

private def ce2InitState : EvalState :=
  { bb := 0, stmtIdx := 0, store := [.dead], fakeBorrows := [], trace := [] }

theorem ce2_mutant_cleanup_to_continue_causes_abi_ub :
    let rTrue := runEval emptyCfgUnwind .runtime 10 (abortUnwindingCalls emptyCfgUnwind ce2Body) ce2InitState panicOracle 0
    let rMutant := runEval emptyCfgUnwind .runtime 10 (mutantCleanupToContinue emptyCfgUnwind ce2Body) ce2InitState panicOracle 0
    rTrue.2 = .aborted .abi ∧ rTrue.1.trace = [99] ∧
    rMutant.2 = .fault .ubUnwindPastNounwindAbi ∧ rMutant.1.trace = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- CE3: Under `-C panic=abort`, Rust-defined `C-unwind` functions have `callCanUnwind = false`,
so `AbortUnwindingCalls` marks their unwind edges `Unreachable` and compacts away the orphaned
cleanup block (3 -> 2 blocks). A foreign `C-unwind` call (or indirect `C-unwind` fn pointer) retains
`callCanUnwind = true`, preserving its 3-block cleanup pad and aborting cleanly via `Terminate(Abi)`. -/
private def ce3LocalCUnwindBody : Body :=
  { blocks :=
      [ { stmts := []
          term := .call { abi := .cUnwind, isForeign := false, isFnPtr := false } 0 1 (.cleanup 2)
          isCleanup := false }
      , { stmts := [.assignConst 0 1]
          term := .return_ 0
          isCleanup := false }
      , { stmts := [.recordDrop 77]
          term := .unwindResume
          isCleanup := true } ]
    bodyAbi := .cNounwind
    bodyIsForeign := false
    hasUserTypeAnnots := false }

private def ce3ForeignCUnwindBody : Body :=
  { blocks :=
      [ { stmts := []
          term := .call { abi := .cUnwind, isForeign := true, isFnPtr := false } 0 1 (.cleanup 2)
          isCleanup := false }
      , { stmts := [.assignConst 0 1]
          term := .return_ 0
          isCleanup := false }
      , { stmts := [.recordDrop 77]
          term := .unwindResume
          isCleanup := true } ]
    bodyAbi := .cNounwind
    bodyIsForeign := false
    hasUserTypeAnnots := false }

theorem ce3_nounwind_violation_hits_unreachable_ub :
    let localLowered := abortUnwindingCalls emptyCfgAbort ce3LocalCUnwindBody
    let foreignLowered := abortUnwindingCalls emptyCfgAbort ce3ForeignCUnwindBody
    let rLocal := runEval emptyCfgAbort .runtime 10 localLowered ce2InitState panicOracle 0
    let rForeign := runEval emptyCfgAbort .runtime 10 foreignLowered ce2InitState panicOracle 0
    localLowered.blocks.length = 2 ∧
    rLocal.2 = .fault .ubUnreachableUnwind ∧ rLocal.1.trace = [] ∧
    foreignLowered.blocks.length = 3 ∧
    rForeign.2 = .aborted .abi ∧ rForeign.1.trace = [77] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end MirCleanupLowering
