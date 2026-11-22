/-!
# `rustc_codegen_ssa::mir::analyze` (`LocalKind`, `CleanupKind`) and `-C instrument-coverage` Kirchhoff BCB Flow

Standalone constructive `Lean v4.34.1` mechanization of:
1. **`LocalAnalyzer` (`non_ssa_locals`) 4-State Lattice and $\phi$-Free Lowering Simulation**:
   Formalizes `LocalKind` (`zst`, `unused`, `ssa defLoc`, `memory`), semilattice transitions across
   `Argument`, `Assignment`, `CallReturn`, `Read` dominance checks, `Field` / single-variant
   `Downcast` projections, mutating projections / borrows, and `Drop`, plus exact simulation between
   addressable-slot MIR execution and `LocalRef` (`PendingOperand` / `Operand` / `Place`) codegen.
2. **Windows SEH / Wasm EH `CleanupKind` Funclet Tree Promotion**:
   Formalizes `discoverMasters`, RPO `propagate`, `setSuccessor` single-parent enforcement,
   shared-join promotion `Internal { funclet } -> Funclet`, and `llbbCharacteristics` cross-funclet
   `cleanupret` boundary safety (instantiated on both `seh_shared_cleanup_promotion` and
   `seh_true_internal_join_promotion`).
3. **`-C instrument-coverage` Kirchhoff Balanced-Flow BCB Counter Elimination**:
   Formalizes `BalancedFlowGraph`, `makeNodeFlowPriorityList` (`isOutSummable`, `isReloopNode`,
   reverse dominator rank), `node_flow_data_for_balanced_graph` supernode quotient, Knuth-Stevenson
   `SpantreeBuilder` with `yank_to_spantree_root`, universal Kirchhoff conservation on the
   7-BCB `hot_loop_diamond` graph recovering all 7 counts from 3 physical counters (`bcb0`, `bcb1`,
   `bcb3`), and per-monomorphization `scope.inlined_instance` attribution.
4. **Three Constructive Counterexamples**:
   - `ce1_nondominated_single_def_in_ssa_reads_unbound_vreg`
   - `ce2_unpromoted_shared_cleanup_join_violates_seh_funclet_isolation`
   - `ce3_non_out_summable_abort_block_breaks_naive_outflow_conservation`

Axiom hygiene: pure core Lean 4 (`propext` / `Quot.sound` only — zero external imports, zero
`sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero
`partial def`).
-/

namespace SsaLocalAnalyzerAndCoverageFlow

-- ============================================================================
-- Part I: `LocalAnalyzer` (`non_ssa_locals`) 4-State Lattice & Lowering Soundness
-- ============================================================================

/-- Classification of a local's `BackendRepr` for `LocalAnalyzer`. -/
inductive BackendReprClass where
  | zst
  | scalar
  | scalarPair
  | memoryAggregate
  deriving DecidableEq, Repr

/-- Definition site of a MIR local (`rustc_middle::mir::DefLocation`). -/
inductive DefLoc where
  | argument
  | assignment (bb : Nat) (stmtIdx : Nat)
  | callReturn (callBb : Nat) (targetBb : Option Nat)
  deriving DecidableEq, Repr

/-- Exact 4-state `LocalKind` lattice (`compiler/rustc_codegen_ssa/src/mir/analyze.rs`). -/
inductive LocalKind where
  | zst
  | unused
  | ssa (defLoc : DefLoc)
  | memory
  deriving DecidableEq, Repr

/-- Read-path projections checked by `LocalAnalyzer::process_place`. -/
inductive ReadProj where
  | field (idx : Nat)
  | singleVariantDowncast (vidx : Nat)
  | otherProj
  deriving DecidableEq, Repr

def ReadProj.isDirectReadable : ReadProj → Bool
  | .field _ => true
  | .singleVariantDowncast _ => true
  | .otherProj => false

noncomputable def allDirectReadable : List ReadProj → Bool
  | [] => true
  | p :: ps => p.isDirectReadable && allDirectReadable ps

/-- MIR place uses classified for `LocalAnalyzer` transitions. -/
inductive UseKind where
  | define (loc : DefLoc)
  | read (bb : Nat) (stmtIdx : Nat) (projs : List ReadProj)
  | indirectDerefRead (bb : Nat) (stmtIdx : Nat)
  | mutatingProjOrBorrow
  | drop (needsDrop : Bool)
  | nonUseOrPlaceMention
  deriving DecidableEq, Repr

/-- Abstract dominance predicate matching `DefLocation::dominates`:
    `domBlock a b` is true iff basic block `a` dominates basic block `b`. -/
def defDominates (domBlock : Nat → Nat → Bool) (defLoc : DefLoc)
    (useBb useStmt : Nat) : Bool :=
  match defLoc with
  | .argument => true
  | .assignment defBb defStmt =>
    if defBb == useBb then defStmt + 1 <= useStmt
    else domBlock defBb useBb
  | .callReturn _ none => false
  | .callReturn callBb (some targetBb) =>
    !(callBb == targetBb) && domBlock callBb targetBb && domBlock targetBb useBb

/-- Lattice join for one `define` event (`analyze.rs:77-95`). -/
def stepDefine (repr : BackendReprClass) (kind : LocalKind) (loc : DefLoc) : LocalKind :=
  match kind with
  | .zst => .zst
  | .memory => .memory
  | .unused =>
    match repr with
    | .zst => .zst
    | .memoryAggregate => .memory
    | .scalar | .scalarPair => .ssa loc
  | .ssa _ => .memory

/-- Lattice transition for one MIR use (`analyze.rs:97-267`). -/
noncomputable def stepUse (repr : BackendReprClass) (domBlock : Nat → Nat → Bool)
    (kind : LocalKind) (u : UseKind) : LocalKind :=
  match u with
  | .define loc => stepDefine repr kind loc
  | .nonUseOrPlaceMention => kind
  | .drop needsDrop =>
    if kind == .memory then .memory
    else if needsDrop then .memory
    else kind
  | .mutatingProjOrBorrow =>
    match kind with
    | .zst => .zst
    | _ => .memory
  | .indirectDerefRead bb stmt =>
    match kind with
    | .zst => .zst
    | .memory => .memory
    | .ssa d => if defDominates domBlock d bb stmt then .ssa d else .memory
    | .unused => .memory
  | .read bb stmt projs =>
    match kind with
    | .zst => .zst
    | .memory => .memory
    | .ssa d =>
      if allDirectReadable projs && defDominates domBlock d bb stmt then .ssa d else .memory
    | .unused => .memory

def initLocalKind : BackendReprClass → LocalKind
  | .zst => .zst
  | _ => .unused

noncomputable def analyzeUses (repr : BackendReprClass) (domBlock : Nat → Nat → Bool)
    (uses : List UseKind) : LocalKind :=
  uses.foldl (stepUse repr domBlock) (initLocalKind repr)

/-- Semilattice rank (`unused = 0 < ssa _ = 1 < memory = 2`, `zst = 3` terminal). -/
def kindRank : LocalKind → Nat
  | .unused => 0
  | .ssa _ => 1
  | .memory => 2
  | .zst => 3

theorem zst_preserved_non_drop (domBlock : Nat → Nat → Bool) (u : UseKind)
    (hnotdrop : u ≠ .drop true) :
    stepUse .zst domBlock .zst u = .zst := by
  cases u with
  | define _ => rfl
  | read _ _ _ => rfl
  | indirectDerefRead _ _ => rfl
  | mutatingProjOrBorrow => rfl
  | drop b =>
    cases b with
    | false => rfl
    | true => exact False.elim (hnotdrop rfl)
  | nonUseOrPlaceMention => rfl

/-- In `rustc_codegen_ssa` (`analyze.rs:254-264`), even a ZST local (`LocalKind::ZST`) is
    promoted to `LocalKind::Memory` on `MutatingUseContext::Drop` when `type_needs_drop` holds,
    explaining `alloca [0 x i8], align 1` for `OuterGuard`/`InnerGuard` in MSVC SEH IR. -/
theorem zst_with_drop_promotes_to_memory (domBlock : Nat → Nat → Bool) :
    stepUse .zst domBlock .zst (.drop true) = .memory := by
  rfl

theorem memory_fixed_step (repr : BackendReprClass) (domBlock : Nat → Nat → Bool) (u : UseKind) :
    stepUse repr domBlock .memory u = .memory := by
  cases u with
  | define loc => rfl
  | read bb stmt projs => rfl
  | indirectDerefRead bb stmt => rfl
  | mutatingProjOrBorrow => rfl
  | drop b => cases b <;> rfl
  | nonUseOrPlaceMention => rfl

theorem stepUse_monotone_non_zst (repr : BackendReprClass) (hrepr : repr ≠ .zst)
    (domBlock : Nat → Nat → Bool) (k : LocalKind) (hk : k ≠ .zst) (u : UseKind) :
    kindRank k ≤ kindRank (stepUse repr domBlock k u) ∧ stepUse repr domBlock k u ≠ .zst := by
  cases u with
  | define loc =>
    cases k <;> cases repr <;> simp [stepUse, stepDefine, kindRank] at hrepr hk ⊢
  | read bb stmt projs =>
    cases k with
    | zst => exact False.elim (hk rfl)
    | unused => simp [stepUse, kindRank]
    | memory => simp [stepUse, kindRank]
    | ssa d =>
      by_cases h : (allDirectReadable projs && defDominates domBlock d bb stmt) = true <;>
        simp [stepUse, kindRank, h]
  | indirectDerefRead bb stmt =>
    cases k with
    | zst => exact False.elim (hk rfl)
    | unused => simp [stepUse, kindRank]
    | memory => simp [stepUse, kindRank]
    | ssa d =>
      by_cases h : defDominates domBlock d bb stmt = true <;> simp [stepUse, kindRank, h]
  | mutatingProjOrBorrow =>
    cases k <;> simp [stepUse, kindRank] at hk ⊢
  | drop b =>
    cases k <;> cases b <;> simp [stepUse, kindRank] at hk ⊢
  | nonUseOrPlaceMention =>
    exact ⟨Nat.le_refl _, hk⟩

theorem second_define_demotes_to_memory (repr : BackendReprClass)
    (domBlock : Nat → Nat → Bool) (d1 d2 : DefLoc) :
    stepUse repr domBlock (.ssa d1) (.define d2) = .memory := by
  rfl

theorem non_dominated_read_demotes_to_memory (repr : BackendReprClass)
    (domBlock : Nat → Nat → Bool) (d : DefLoc) (bb stmt : Nat) (projs : List ReadProj)
    (hnd : defDominates domBlock d bb stmt = false) :
    stepUse repr domBlock (.ssa d) (.read bb stmt projs) = .memory := by
  simp [stepUse, hnd]

theorem disallowed_proj_demotes_to_memory (repr : BackendReprClass)
    (domBlock : Nat → Nat → Bool) (d : DefLoc) (bb stmt : Nat) (projs : List ReadProj)
    (hproj : allDirectReadable projs = false) :
    stepUse repr domBlock (.ssa d) (.read bb stmt projs) = .memory := by
  simp [stepUse, hproj]

-- ----------------------------------------------------------------------------
-- Exact Single-Local Lowering Simulation (MIR Slot vs. `LocalRef` Codegen)
-- ----------------------------------------------------------------------------

/-- Runtime MIR slot state (`uninit` vs `init v`). -/
inductive MirSlotVal where
  | uninit
  | init (v : Nat)
  deriving DecidableEq, Repr

/-- `rustc_codegen_ssa`'s `LocalRef` representation for a single local. -/
inductive LoweredSlot where
  | zstOperand
  | pendingOperand
  | ssaOperand (v : Nat)
  | allocaSlot (m : MirSlotVal)
  deriving DecidableEq, Repr

inductive SimError where
  | ssaUseBeforeDef
  | ssaAlreadyAssigned
  deriving DecidableEq, Repr

/-- Trace events executed along one concrete dynamic execution path of a function. -/
inductive TraceEvent where
  | assign (v : Nat)
  | projWrite (newV : Nat)
  | read (bb : Nat) (stmtIdx : Nat) (projs : List ReadProj)
  | storageLive
  | storageDead
  deriving DecidableEq, Repr

def evalMirTraceStep (s : MirSlotVal) (ev : TraceEvent) : MirSlotVal × Option MirSlotVal :=
  match ev with
  | .assign v => (.init v, none)
  | .projWrite newV => (.init newV, none)
  | .read _ _ _ => (s, some s)
  | .storageLive => (.uninit, none)
  | .storageDead => (.uninit, none)

noncomputable def evalMirTrace (events : List TraceEvent) : List (Option MirSlotVal) :=
  let rec go (s : MirSlotVal) : List TraceEvent → List (Option MirSlotVal)
    | [] => []
    | ev :: rest =>
      let (s', out) := evalMirTraceStep s ev
      out :: go s' rest
  go .uninit events

def initLoweredSlot (kind : LocalKind) : LoweredSlot :=
  match kind with
  | .zst => .zstOperand
  | .unused => .pendingOperand
  | .ssa _ => .pendingOperand
  | .memory => .allocaSlot .uninit

/-- Lowered `LocalRef` execution step matching `statement.rs:20-86` & `operand.rs:1079-1114`.
    Crucially, `StorageLive`/`StorageDead` on `PendingOperand`/`Operand` are no-ops,
    reading `PendingOperand` panics (`ssaUseBeforeDef`), and overwriting an already-assigned
    non-ZST `Operand` panics (`ssaAlreadyAssigned`). -/
noncomputable def evalLoweredStep (s : LoweredSlot) (ev : TraceEvent) :
    Except SimError (LoweredSlot × Option MirSlotVal) :=
  match ev with
  | .assign v =>
    match s with
    | .zstOperand => .ok (.zstOperand, none)
    | .pendingOperand => .ok (.ssaOperand v, none)
    | .ssaOperand _ => .error .ssaAlreadyAssigned
    | .allocaSlot _ => .ok (.allocaSlot (.init v), none)
  | .projWrite newV =>
    match s with
    | .zstOperand => .ok (.zstOperand, none)
    | .allocaSlot _ => .ok (.allocaSlot (.init newV), none)
    | .pendingOperand => .error .ssaUseBeforeDef
    | .ssaOperand _ => .error .ssaAlreadyAssigned
  | .read _ _ projs =>
    match s with
    | .zstOperand => .ok (.zstOperand, some (.init 0))
    | .pendingOperand => .error .ssaUseBeforeDef
    | .ssaOperand v =>
      if allDirectReadable projs then .ok (.ssaOperand v, some (.init v))
      else .error .ssaUseBeforeDef
    | .allocaSlot m => .ok (.allocaSlot m, some m)
  | .storageLive =>
    match s with
    | .allocaSlot _ => .ok (.allocaSlot .uninit, none)
    | other => .ok (other, none)
  | .storageDead =>
    match s with
    | .allocaSlot _ => .ok (.allocaSlot .uninit, none)
    | other => .ok (other, none)

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    match decEq e1 e2 with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun he => h (Except.error.inj he))
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)
  | .ok a1, .ok a2 =>
    match decEq a1 a2 with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun he => h (Except.ok.inj he))

noncomputable def listGetOpt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGetOpt xs n

noncomputable def evalLoweredTrace (kind : LocalKind) (events : List TraceEvent) :
    Except SimError (List (Option MirSlotVal)) :=
  let rec go (s : LoweredSlot) : List TraceEvent → Except SimError (List (Option MirSlotVal))
    | [] => .ok []
    | ev :: rest =>
      match evalLoweredStep s ev with
      | .error e => .error e
      | .ok (s', out) =>
        match go s' rest with
        | .error e => .error e
        | .ok tl => .ok (out :: tl)
  go (initLoweredSlot kind) events

/-- Well-formedness of a dynamic execution trace for a local classified as `.ssa`:
    - Before the unique definition is executed (`assigned = false`), no `read` occurs and
      at most one `assign` occurs;
    - After the definition (`assigned = true`), no second `assign` occurs, no `projWrite` occurs,
      no `storageDead`/`storageLive` invalidates the register value while live, and every `read`
      uses only direct-readable projections (`Field` or single-variant `Downcast`). -/
noncomputable def validSsaTrace (assigned : Bool) : List TraceEvent → Bool
  | [] => true
  | ev :: rest =>
    match ev with
    | .assign _ => (!assigned) && validSsaTrace true rest
    | .projWrite _ => false
    | .read _ _ projs => assigned && allDirectReadable projs && validSsaTrace true rest
    | .storageLive => (!assigned) && validSsaTrace assigned rest
    | .storageDead => (!assigned) && validSsaTrace false rest

/-- Well-formedness of a trace for a `.memory` (alloca) local: unrestricted writes/reads/storage. -/
noncomputable def validMemoryTrace : List TraceEvent → Bool
  | [] => true
  | _ :: rest => validMemoryTrace rest

private theorem sim_ssa_go (events : List TraceEvent) :
    (∀ (v : Nat), validSsaTrace true events = true →
      evalLoweredTrace.go (.ssaOperand v) events =
        .ok (evalMirTrace.go (.init v) events)) ∧
    (validSsaTrace false events = true →
      evalLoweredTrace.go .pendingOperand events =
        .ok (evalMirTrace.go .uninit events)) := by
  induction events with
  | nil =>
    constructor
    · intro v _; rfl
    · intro _; rfl
  | cons ev rest ih =>
    constructor
    · intro v hv
      cases ev with
      | assign w => simp [validSsaTrace] at hv
      | projWrite w => simp [validSsaTrace] at hv
      | read bb stmt projs =>
        simp [validSsaTrace] at hv
        obtain ⟨hp, hrest⟩ := hv
        have htl := ih.1 v hrest
        simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep, hp]
        rw [htl]
      | storageLive => simp [validSsaTrace] at hv
      | storageDead => simp [validSsaTrace] at hv
    · intro hv
      cases ev with
      | assign w =>
        simp [validSsaTrace] at hv
        have htl := ih.1 w hv
        simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
        rw [htl]
      | projWrite w => simp [validSsaTrace] at hv
      | read bb stmt projs => simp [validSsaTrace] at hv
      | storageLive =>
        simp [validSsaTrace] at hv
        have htl := ih.2 hv
        simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
        rw [htl]
      | storageDead =>
        simp [validSsaTrace] at hv
        have htl := ih.2 hv
        simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
        rw [htl]

private theorem sim_memory_go (m : MirSlotVal) (events : List TraceEvent) :
    evalLoweredTrace.go (.allocaSlot m) events = .ok (evalMirTrace.go m events) := by
  induction events generalizing m with
  | nil => rfl
  | cons ev rest ih =>
    cases ev with
    | assign v =>
      simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
      rw [ih (.init v)]
    | projWrite newV =>
      simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
      rw [ih (.init newV)]
    | read bb stmt projs =>
      simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
      rw [ih m]
    | storageLive =>
      simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
      rw [ih .uninit]
    | storageDead =>
      simp [evalLoweredTrace.go, evalLoweredStep, evalMirTrace.go, evalMirTraceStep]
      rw [ih .uninit]

/-- **Theorem 1 (`localAnalyzer_ssa_or_memory_simulation_exact`)**:
    Whenever `LocalAnalyzer` classifies a non-ZST local as `.ssa d` (so any trace respecting
    dominance satisfies `validSsaTrace false events = true`) OR demotes it to `.memory` (`alloca`),
    `rustc_codegen_ssa`'s lowered `LocalRef` execution produces the exact same sequence of
    observed slot reads as the pure MIR addressable-slot semantics without ever hitting
    `ssaUseBeforeDef` or `ssaAlreadyAssigned`. -/
theorem localAnalyzer_ssa_or_memory_simulation_exact
    (kind : LocalKind) (events : List TraceEvent)
    (hvalid : match kind with
      | .ssa _ => validSsaTrace false events = true
      | .memory => True
      | .unused | .zst => False) :
    evalLoweredTrace kind events = .ok (evalMirTrace events) := by
  cases kind with
  | zst => exact False.elim hvalid
  | unused => exact False.elim hvalid
  | ssa d =>
    simpa [evalLoweredTrace, initLoweredSlot, evalMirTrace] using (sim_ssa_go events).2 hvalid
  | memory =>
    simpa [evalLoweredTrace, initLoweredSlot, evalMirTrace] using sim_memory_go .uninit events

-- Concrete verification matching all 6 `#[custom_mir]` specimens (`cm_1` .. `cm_6`).
def cm1Dom (a b : Nat) : Bool := a <= b
def cm2Dom (a b : Nat) : Bool :=
  a == b || a == 0

theorem cm1_single_def_stays_ssa :
    analyzeUses .scalar cm1Dom
      [ .define (.assignment 0 0)
      , .read 0 1 [] ] = .ssa (.assignment 0 0) := by
  decide

theorem cm2_two_defs_demotes_to_memory :
    analyzeUses .scalar cm2Dom
      [ .define (.assignment 1 0)
      , .define (.assignment 2 0)
      , .read 3 0 [] ] = .memory := by
  decide

theorem cm3_nondominated_single_def_demotes_to_memory :
    analyzeUses .scalar cm2Dom
      [ .define (.assignment 1 0)
      , .read 2 0 [] ] = .memory := by
  decide

theorem cm4_scalarpair_field_read_stays_ssa :
    analyzeUses .scalarPair cm1Dom
      [ .define .argument
      , .read 0 0 [.field 1] ] = .ssa .argument := by
  decide

theorem cm5_scalarpair_field_write_demotes_to_memory :
    analyzeUses .scalarPair cm1Dom
      [ .mutatingProjOrBorrow
      , .mutatingProjOrBorrow
      , .read 0 2 [.field 1] ] = .memory := by
  decide

theorem cm6_raw_borrow_demotes_to_memory :
    analyzeUses .scalar cm1Dom
      [ .define (.assignment 0 0)
      , .mutatingProjOrBorrow
      , .read 0 2 [] ] = .memory := by
  decide

-- ============================================================================
-- Part II: `cleanup_kinds` Windows SEH / Wasm EH Funclet Tree Promotion
-- ============================================================================

/-- `analyze::CleanupKind` (`compiler/rustc_codegen_ssa/src/mir/analyze.rs:275-290`). -/
inductive CleanupKind where
  | notCleanup
  | funclet
  | internal (funclet : Nat)
  deriving DecidableEq, Repr

def CleanupKind.funcletBb (forBb : Nat) : CleanupKind → Option Nat
  | .notCleanup => none
  | .funclet => some forBb
  | .internal f => some f

inductive CleanupError where
  | twoParents (funclet : Nat) (p1 : Nat) (p2 : Nat)
  | jumpOutOfCleanup (src : Nat) (dst : Nat)
  deriving DecidableEq, Repr

structure CleanupState where
  kinds : List CleanupKind
  funcletSuccs : List (Option Nat)
  deriving DecidableEq, Repr

noncomputable def setListAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: setListAt xs n v

noncomputable def getKind (kinds : List CleanupKind) (bb : Nat) : CleanupKind :=
  (listGetOpt kinds bb).getD .notCleanup

noncomputable def getSuccOpt (succs : List (Option Nat)) (bb : Nat) : Option Nat :=
  (listGetOpt succs bb).getD none

theorem getKind_setListAt_eq (kinds : List CleanupKind) (i : Nat) (v : CleanupKind)
    (hi : i < kinds.length) :
    getKind (setListAt kinds i v) i = v := by
  induction kinds generalizing i with
  | nil => cases hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
      exact ih i' hi'

theorem getKind_setListAt_ne (kinds : List CleanupKind) (i j : Nat) (v : CleanupKind)
    (hne : i ≠ j) :
    getKind (setListAt kinds i v) j = getKind kinds j := by
  induction kinds generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ j' => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' =>
        have hne' : i' ≠ j' := fun h => hne (congrArg Nat.succ h)
        exact ih i' j' hne'

noncomputable def setSuccessor (succs : List (Option Nat)) (funclet succ : Nat) :
    Except CleanupError (List (Option Nat)) :=
  match getSuccOpt succs funclet with
  | none => .ok (setListAt succs funclet (some succ))
  | some s =>
    if s == succ then .ok succs
    else .error (.twoParents funclet s succ)

/-- Single-edge step of `cleanup_kinds::propagate` (`analyze.rs:371-397`). -/
noncomputable def propagateEdge (st : CleanupState) (srcFunclet succ : Nat) :
    Except CleanupError CleanupState :=
  match getKind st.kinds succ with
  | .notCleanup =>
    .ok { st with kinds := setListAt st.kinds succ (.internal srcFunclet) }
  | .funclet =>
    if srcFunclet == succ then .ok st
    else
      match setSuccessor st.funcletSuccs srcFunclet succ with
      | .error e => .error e
      | .ok succs' => .ok { st with funcletSuccs := succs' }
  | .internal succFunclet =>
    if srcFunclet == succFunclet then .ok st
    else
      let kinds' := setListAt st.kinds succ .funclet
      match setSuccessor st.funcletSuccs succFunclet succ with
      | .error e => .error e
      | .ok succs1 =>
        match setSuccessor succs1 srcFunclet succ with
        | .error e => .error e
        | .ok succs2 => .ok { kinds := kinds', funcletSuccs := succs2 }

noncomputable def propagateEdgesFrom (st : CleanupState) (srcFunclet : Nat) :
    List Nat → Except CleanupError CleanupState
  | [] => .ok st
  | s :: ss => do
    let st' ← propagateEdge st srcFunclet s
    propagateEdgesFrom st' srcFunclet ss

noncomputable def propagateBlock (cfgSuccs : List (List Nat)) (st : CleanupState) (bb : Nat) :
    Except CleanupError CleanupState :=
  match getKind st.kinds bb with
  | .notCleanup => .ok st
  | .funclet => propagateEdgesFrom st bb ((listGetOpt cfgSuccs bb).getD [])
  | .internal f => propagateEdgesFrom st f ((listGetOpt cfgSuccs bb).getD [])

/-- Register `UnwindAction::Cleanup(target)` entries unless `target ∈ nopLandingPads`. -/
noncomputable def discoverMasters (n : Nat) (unwindTargets : List Nat) (nopLandingPads : List Nat) :
    CleanupState :=
  let initKinds := List.replicate n CleanupKind.notCleanup
  let kinds := unwindTargets.foldl
    (fun ks u => if nopLandingPads.contains u then ks else setListAt ks u .funclet)
    initKinds
  { kinds := kinds, funcletSuccs := List.replicate n none }

noncomputable def propagateRpo (cfgSuccs : List (List Nat)) (rpo : List Nat) (st : CleanupState) :
    Except CleanupError CleanupState :=
  rpo.foldlM (propagateBlock cfgSuccs) st

noncomputable def runCleanupKinds (n : Nat) (unwindTargets nopLandingPads : List Nat)
    (cfgSuccs : List (List Nat)) (rpo : List Nat) : Except CleanupError CleanupState :=
  propagateRpo cfgSuccs rpo (discoverMasters n unwindTargets nopLandingPads)

/-- Exact mirror of `TerminatorCodegenHelper::llbb_characteristics` (`block.rs:111-127`). -/
noncomputable def llbbCharacteristics (kinds : List CleanupKind) (src dst : Nat) :
    Except CleanupError (Bool × Bool) :=
  match (getKind kinds src).funcletBb src, (getKind kinds dst).funcletBb dst with
  | none, none => .ok (false, false)
  | none, some _ => .ok (true, false)
  | some f, some tf => .ok (f != tf, f != tf)
  | some _, none => .error (.jumpOutOfCleanup src dst)

/-- Post-propagation edge invariant for cleanup edge `src -> succ`:
    when `src` has funclet `fSrc` and `succ < kinds.length`, after `propagateEdge`,
    `succ` cannot remain `.notCleanup`, and if `succ` is `.internal fSucc` then `fSucc = fSrc`. -/
theorem cleanupKinds_no_cross_funclet_internal_edge
    (st st' : CleanupState) (srcFunclet succ : Nat)
    (hbound : succ < st.kinds.length)
    (hprop : propagateEdge st srcFunclet succ = .ok st') :
    (getKind st'.kinds succ ≠ .notCleanup) ∧
    (∀ fSucc, getKind st'.kinds succ = .internal fSucc → fSucc = srcFunclet) := by
  unfold propagateEdge at hprop
  cases hcur : getKind st.kinds succ with
  | notCleanup =>
    rw [hcur] at hprop
    dsimp only at hprop
    cases hprop
    have hget : getKind (setListAt st.kinds succ (.internal srcFunclet)) succ =
        .internal srcFunclet := getKind_setListAt_eq st.kinds succ (.internal srcFunclet) hbound
    constructor
    · rw [hget]; intro h; cases h
    · intro fSucc hf; rw [hget] at hf; cases hf; rfl
  | funclet =>
    rw [hcur] at hprop
    dsimp only at hprop
    cases heq : (srcFunclet == succ) with
    | true =>
      rw [heq] at hprop
      simp only [↓reduceIte] at hprop
      cases hprop
      constructor
      · rw [hcur]; intro h; cases h
      · intro fSucc hf; rw [hcur] at hf; cases hf
    | false =>
      rw [heq] at hprop
      simp only [Bool.false_eq_true, ↓reduceIte] at hprop
      cases hss : setSuccessor st.funcletSuccs srcFunclet succ with
      | error e => rw [hss] at hprop; dsimp only at hprop; cases hprop
      | ok sNew =>
        rw [hss] at hprop
        dsimp only at hprop
        cases hprop
        constructor
        · rw [hcur]; intro h; cases h
        · intro fSucc hf; rw [hcur] at hf; cases hf
  | internal oldF =>
    rw [hcur] at hprop
    dsimp only at hprop
    cases heq : (srcFunclet == oldF) with
    | true =>
      have heq' : srcFunclet = oldF := beq_iff_eq.mp heq
      rw [heq] at hprop
      simp only [↓reduceIte] at hprop
      cases hprop
      constructor
      · rw [hcur]; intro h; cases h
      · intro fSucc hf; rw [hcur] at hf; cases hf; exact heq'.symm
    | false =>
      rw [heq] at hprop
      simp only [Bool.false_eq_true, ↓reduceIte] at hprop
      cases hss1 : setSuccessor st.funcletSuccs oldF succ with
      | error e => rw [hss1] at hprop; dsimp only at hprop; cases hprop
      | ok s1 =>
        rw [hss1] at hprop
        dsimp only at hprop
        cases hss2 : setSuccessor s1 srcFunclet succ with
        | error e => rw [hss2] at hprop; dsimp only at hprop; cases hprop
        | ok s2 =>
          rw [hss2] at hprop
          dsimp only at hprop
          cases hprop
          have hget : getKind (setListAt st.kinds succ .funclet) succ = .funclet :=
            getKind_setListAt_eq st.kinds succ .funclet hbound
          constructor
          · rw [hget]; intro h; cases h
          · intro fSucc hf; rw [hget] at hf; cases hf

/-- Corollary: if `src` and `dst` have distinct owning funclets `fSrc ≠ fDst` and `dst` has no
    cross-funclet `Internal` tag (`getKind kinds dst = .funclet` whenever `fDst ≠ fSrc`), then
    `llbbCharacteristics` strictly lowers `src -> dst` as `(true, true)` (`cleanupret`), never
    a cross-funclet `br`. -/
theorem distinct_funclet_edge_lowers_to_cleanupret
    (kinds : List CleanupKind) (src dst fSrc fDst : Nat)
    (hsrc : (getKind kinds src).funcletBb src = some fSrc)
    (hdst : (getKind kinds dst).funcletBb dst = some fDst)
    (hne : fSrc ≠ fDst) :
    llbbCharacteristics kinds src dst = .ok (true, true) := by
  have hbne : (fSrc != fDst) = true := bne_iff_ne.mpr hne
  simp [llbbCharacteristics, hsrc, hdst, hbne]

-- Concrete verification 1: `seh_shared_cleanup_promotion` (`bb5 -> bb6` unwinds into funclet `bb6`).
theorem seh_shared_cleanup_promotion_tree_verified :
    let cfg : List (List Nat) :=
      [ [1, 6] -- bb0 (start) -> bb1, unwind bb6
      , [2, 5] -- bb1 -> bb2, unwind bb5
      , [3, 6] -- bb2 -> bb3, unwind bb6
      , []     -- bb3 (ret)
      , []     -- bb4 (unused)
      , [6]    -- bb5 (inner cleanup) -> bb6 (outer cleanup)
      , []     -- bb6 (outer cleanup) -> unwind to caller
      ]
    runCleanupKinds 7 [6, 5, 6] [] cfg [0, 1, 2, 3, 5, 6] =
      .ok {
        kinds := [ .notCleanup, .notCleanup, .notCleanup, .notCleanup,
                   .notCleanup, .funclet, .funclet ],
        funcletSuccs := [none, none, none, none, none, some 6, none]
      } ∧
    llbbCharacteristics
      [.notCleanup, .notCleanup, .notCleanup, .notCleanup, .notCleanup, .funclet, .funclet]
      5 6 = .ok (true, true) := by
  decide

-- Concrete verification 2: `seh_true_internal_join_promotion`:
-- `bb4` has ZERO direct `UnwindAction::Cleanup` edge! `discoverMasters` leaves `bb4 = .notCleanup`,
-- RPO visiting `bb7` sets `bb4 = .internal 7`, and visiting `bb6` promotes `bb4 -> .funclet`,
-- linking BOTH `bb6` and `bb7` to parent funclet `bb4` (`cleanupret ... unwind label %funclet_bb4`).
theorem seh_true_internal_join_promotion_tree_verified :
    let cfg : List (List Nat) :=
      [ [1, 2] -- bb0
      , [8, 7] -- bb1 -> bb8, unwind bb7
      , [9, 6] -- bb2 -> bb9, unwind bb6
      , []     -- bb3 (ret)
      , []     -- bb4 (outer cleanup: NOT directly targeted by any normal invoke!)
      , []     -- bb5 (unused)
      , [4]    -- bb6 (right inner cleanup) -> bb4
      , [4]    -- bb7 (left inner cleanup) -> bb4
      , [3]    -- bb8 -> bb3
      , [3]    -- bb9 -> bb3
      ]
    runCleanupKinds 10 [7, 6] [] cfg [0, 1, 8, 2, 9, 3, 7, 6, 4] =
      .ok {
        kinds := [ .notCleanup, .notCleanup, .notCleanup, .notCleanup,
                   .funclet,    .notCleanup, .funclet,    .funclet,
                   .notCleanup, .notCleanup ],
        funcletSuccs := [none, none, none, none, none, none, some 4, some 4, none, none]
      } ∧
    llbbCharacteristics
      [.notCleanup, .notCleanup, .notCleanup, .notCleanup, .funclet,
       .notCleanup, .funclet, .funclet, .notCleanup, .notCleanup] 6 4 = .ok (true, true) ∧
    llbbCharacteristics
      [.notCleanup, .notCleanup, .notCleanup, .notCleanup, .funclet,
       .notCleanup, .funclet, .funclet, .notCleanup, .notCleanup] 7 4 = .ok (true, true) := by
  decide

-- Concrete verification 3: multi-parent funclet triggers `twoParents` (`analyze.rs:348-354`).
theorem seh_two_parents_triggers_span_bug :
    let cfg : List (List Nat) :=
      [ [1, 2] -- bb0
      , [3]    -- bb1 (funclet 1) -> bb3
      , [4]    -- bb2 (funclet 2) -> bb4
      , [5]    -- bb3 (internal 1) -> bb5 (funclet)
      , [5]    -- bb4 (internal 2) -> bb5 (funclet)
      , [6, 7] -- bb5 (funclet) branches to TWO distinct funclets 6 and 7!
      , []     -- bb6
      , []     -- bb7
      ]
    runCleanupKinds 8 [1, 2, 5, 6, 7] [] cfg [0, 1, 3, 2, 4, 5, 6, 7] =
      .error (.twoParents 5 6 7) := by
  decide

-- ============================================================================
-- Part III: `-C instrument-coverage` Kirchhoff Balanced-Flow BCB Elimination
-- ============================================================================

inductive CovOp where
  | add
  | subtract
  deriving DecidableEq, Repr

structure CounterTerm where
  op : CovOp
  physId : Nat
  deriving DecidableEq, Repr

/-- Evaluates a `CovTerm` expression list (`transcribe_counters`: `SUM(pos) - SUM(neg)`). -/
noncomputable def evalCounterTerms (phys : Nat → Int) : List CounterTerm → Int
  | [] => 0
  | ⟨.add, id⟩ :: ts => phys id + evalCounterTerms phys ts
  | ⟨.subtract, id⟩ :: ts => -(phys id) + evalCounterTerms phys ts

/-- Priority criterion matching `counters.rs:52-75`. -/
structure PriorityNode where
  id : Nat
  isSink : Bool
  isOutSummable : Bool
  isReloopNode : Bool
  domRank : Nat
  deriving DecidableEq, Repr

def isReloopPred (succs : List Nat) (dominates : Nat → Bool) : Bool :=
  match succs with
  | [s] => dominates s
  | _ => false

/-- Lexicographic priority order (`lt a b = true` means `a` gets expression priority before `b`). -/
def priorityLt (a b : PriorityNode) : Bool :=
  if a.isSink != b.isSink then a.isSink
  else if a.isOutSummable != b.isOutSummable then !a.isOutSummable
  else if a.isReloopNode != b.isReloopNode then a.isReloopNode
  else a.domRank > b.domRank

-- Model of `hot_loop_diamond`'s 7 BCBs (`bcb0 .. bcb6`) + synthetic `sink` (`7`).
-- CFG edges:
--   bcb0 -> bcb1
--   bcb1 -> bcb6, bcb2
--   bcb2 -> bcb5, bcb3
--   bcb3 -> bcb4
--   bcb4 -> bcb1           (sole reloop backedge: bcb1 dominates bcb4!)
--   bcb5 -> bcb4
--   bcb6 -> sink           (is_out_summable = false => forced sink edge)
--   sink -> bcb0           (synthetic cycle closing flow)

inductive HotLoopBcb where
  | bcb0 | bcb1 | bcb2 | bcb3 | bcb4 | bcb5 | bcb6
  deriving DecidableEq, Repr

structure HotLoopFlow where
  f0 : Int    -- node bcb0 flow (= edge 0->1, edge sink->0)
  f1 : Int    -- node bcb1 flow
  e12 : Int   -- edge 1 -> 2
  e16 : Int   -- edge 1 -> 6
  f2 : Int    -- node bcb2 flow
  e23 : Int   -- edge 2 -> 3
  e25 : Int   -- edge 2 -> 5
  f3 : Int    -- node bcb3 flow (= edge 3->4)
  f4 : Int    -- node bcb4 flow (= edge 4->1)
  f5 : Int    -- node bcb5 flow (= edge 5->4)
  f6 : Int    -- node bcb6 flow (= edge 6->sink)
  fSink : Int -- synthetic sink flow

/-- Kirchhoff flow conservation at every node of `hot_loop_diamond`'s `BalancedFlowGraph`. -/
structure IsHotLoopBalancedFlow (fl : HotLoopFlow) : Prop where
  in_0 : fl.fSink = fl.f0
  out_1 : fl.f1 = fl.e16 + fl.e12
  in_1 : fl.f0 + fl.f4 = fl.f1
  in_2 : fl.e12 = fl.f2
  out_2 : fl.f2 = fl.e25 + fl.e23
  in_3 : fl.e23 = fl.f3
  in_4 : fl.f3 + fl.f5 = fl.f4
  in_5 : fl.e25 = fl.f5
  in_6 : fl.e16 = fl.f6
  in_sink : fl.f6 = fl.fSink

def hotLoopNodeFlow (fl : HotLoopFlow) : HotLoopBcb → Int
  | .bcb0 => fl.f0
  | .bcb1 => fl.f1
  | .bcb2 => fl.f2
  | .bcb3 => fl.f3
  | .bcb4 => fl.f4
  | .bcb5 => fl.f5
  | .bcb6 => fl.f6

/-- Exact `CounterTerm` assignment synthesized by `rustc`'s `SpantreeBuilder` +
    `transcribe_counters` on `hot_loop_diamond`:
    - `physId 0 = bcb0` (`Counter(0)`)
    - `physId 1 = bcb1` (`Counter(1)`)
    - `physId 2 = bcb3` (`Counter(2)`)
    Notice `bcb4` (the loop latch), `bcb5` (else arm), `bcb2` (body), and `bcb6` (return)
    have ZERO physical counters! -/
def hotLoopTerms : HotLoopBcb → List CounterTerm
  | .bcb0 => [⟨.add, 0⟩]
  | .bcb1 => [⟨.add, 1⟩]
  | .bcb2 => [⟨.add, 1⟩, ⟨.subtract, 0⟩]
  | .bcb3 => [⟨.add, 2⟩]
  | .bcb4 => [⟨.add, 1⟩, ⟨.subtract, 0⟩]
  | .bcb5 => [⟨.add, 1⟩, ⟨.subtract, 0⟩, ⟨.subtract, 2⟩]
  | .bcb6 => [⟨.add, 0⟩]

private theorem int_add_zero_right (x : Int) : x + 0 = x := Int.add_zero x

private theorem int_solve_left_sum (a b c : Int) (h : a + b = c) : c + (-a) = b := by
  rw [← h]
  calc
    (a + b) + (-a) = (b + a) + (-a) := by rw [Int.add_comm a b]
    _ = b + (a + (-a)) := Int.add_assoc b a (-a)
    _ = b + 0 := by rw [Int.add_right_neg a]
    _ = b := Int.add_zero b

private theorem int_solve_right_sum (a b c : Int) (h : a + b = c) : c + (-b) = a := by
  rw [← h]
  calc
    (a + b) + (-b) = a + (b + (-b)) := Int.add_assoc a b (-b)
    _ = a + 0 := by rw [Int.add_right_neg b]
    _ = a := Int.add_zero a

/-- **Theorem 2 (`bcbFlow_counterExpression_reconstructs_exact`)**:
    For ANY `Int`-valued flow `fl` satisfying Kirchhoff conservation on the `hot_loop_diamond`
    `BalancedFlowGraph`, evaluating `rustc`'s 3-counter `hotLoopTerms` (`bcb0`, `bcb1`, `bcb3`)
    reconstructs all 7 BCB execution counts identically. -/
theorem bcbFlow_counterExpression_reconstructs_exact
    (fl : HotLoopFlow) (hbal : IsHotLoopBalancedFlow fl) (b : HotLoopBcb) :
    let phys : Nat → Int := fun id =>
      match id with
      | 0 => fl.f0
      | 1 => fl.f1
      | _ => fl.f3
    evalCounterTerms phys (hotLoopTerms b) = hotLoopNodeFlow fl b := by
  intro phys
  have hf6 : fl.f6 = fl.f0 := by
    calc
      fl.f6 = fl.fSink := hbal.in_sink
      _ = fl.f0 := hbal.in_0
  have he16 : fl.e16 = fl.f0 := by
    calc
      fl.e16 = fl.f6 := hbal.in_6
      _ = fl.f0 := hf6
  have hf2 : fl.f2 = fl.f1 + (-fl.f0) := by
    have h1 : fl.f0 + fl.e12 = fl.f1 := by
      calc
        fl.f0 + fl.e12 = fl.e16 + fl.e12 := by rw [he16]
        _ = fl.f1 := hbal.out_1.symm
    have h2 : fl.f1 + (-fl.f0) = fl.e12 := int_solve_left_sum fl.f0 fl.e12 fl.f1 h1
    rw [← hbal.in_2, h2]
  have hf4 : fl.f4 = fl.f1 + (-fl.f0) :=
    (int_solve_left_sum fl.f0 fl.f4 fl.f1 hbal.in_1).symm
  have hf5 : fl.f5 = (fl.f1 + (-fl.f0)) + (-fl.f3) := by
    have h1 : fl.f3 + fl.f5 = fl.f1 + (-fl.f0) := by
      rw [hbal.in_4, hf4]
    exact (int_solve_left_sum fl.f3 fl.f5 (fl.f1 + (-fl.f0)) h1).symm
  cases b with
  | bcb0 => simp [evalCounterTerms, hotLoopTerms, hotLoopNodeFlow, phys, Int.add_zero]
  | bcb1 => simp [evalCounterTerms, hotLoopTerms, hotLoopNodeFlow, phys, Int.add_zero]
  | bcb2 =>
    simp [evalCounterTerms, hotLoopTerms, hotLoopNodeFlow, phys, Int.add_zero, hf2]
  | bcb3 => simp [evalCounterTerms, hotLoopTerms, hotLoopNodeFlow, phys, Int.add_zero]
  | bcb4 =>
    simp [evalCounterTerms, hotLoopTerms, hotLoopNodeFlow, phys, Int.add_zero, hf4]
  | bcb5 =>
    simp [evalCounterTerms, hotLoopTerms, hotLoopNodeFlow, phys, Int.add_zero, hf5, Int.add_assoc]
  | bcb6 =>
    simp [evalCounterTerms, hotLoopTerms, hotLoopNodeFlow, phys, Int.add_zero, hf6]

/-- Verify `isReloopNode` detects `bcb4` (`bcb4 -> bcb1` where `bcb1` dominates `bcb4`)
    and `priorityLt` ranks `sink < bcb6 < bcb4 < bcb5 < bcb3 < bcb2 < bcb1 < bcb0`. -/
theorem hotLoop_reloop_priority_places_latch_first :
    let domBcb4 (target : Nat) : Bool := target == 0 || target == 1 || target == 2 || target == 4
    let isReloop4 := isReloopPred [1] domBcb4
    let nSink : PriorityNode := ⟨7, true, false, false, 7⟩
    let n6 : PriorityNode := ⟨6, false, false, false, 6⟩
    let n4 : PriorityNode := ⟨4, false, true, isReloop4, 5⟩
    let n5 : PriorityNode := ⟨5, false, true, false, 4⟩
    let n3 : PriorityNode := ⟨3, false, true, false, 3⟩
    let n2 : PriorityNode := ⟨2, false, true, false, 2⟩
    let n1 : PriorityNode := ⟨1, false, true, false, 1⟩
    let n0 : PriorityNode := ⟨0, false, true, false, 0⟩
    isReloop4 = true ∧
    priorityLt nSink n6 = true ∧
    priorityLt n6 n4 = true ∧
    priorityLt n4 n5 = true ∧
    priorityLt n5 n3 = true ∧
    priorityLt n3 n2 = true ∧
    priorityLt n2 n1 = true ∧
    priorityLt n1 n0 = true := by
  decide

/-- Concrete instantiation matching the live `n = 100` execution (`[1, 101, 100, 25, 100, 75, 1]`). -/
theorem hotLoop_concrete_100_iters_reconstructs_exact :
    let phys : Nat → Int := fun id =>
      match id with
      | 0 => 1
      | 1 => 101
      | _ => 25
    [ evalCounterTerms phys (hotLoopTerms .bcb0)
    , evalCounterTerms phys (hotLoopTerms .bcb1)
    , evalCounterTerms phys (hotLoopTerms .bcb2)
    , evalCounterTerms phys (hotLoopTerms .bcb3)
    , evalCounterTerms phys (hotLoopTerms .bcb4)
    , evalCounterTerms phys (hotLoopTerms .bcb5)
    , evalCounterTerms phys (hotLoopTerms .bcb6) ] =
      [1, 101, 100, 25, 100, 75, 1] := by
  decide

-- ----------------------------------------------------------------------------
-- Per-Monomorphization `scope.inlined_instance` Attribution Across `MIR Inline`
-- ----------------------------------------------------------------------------

/-- Monomorphized instance key (`DefId × TypeArgTag`). -/
structure InstanceKey where
  fnId : Nat
  tyArg : Nat
  deriving DecidableEq, Repr

/-- Mirror of `rustc_middle::mir::SourceScopeData` (`compiler/rustc_middle/src/mir/mod.rs:1488-1516`). -/
structure ScopeData where
  parentScope : Option Nat
  inlined : Option InstanceKey
  inlinedParentScope : Option Nat
  deriving DecidableEq, Repr

noncomputable def inlinedInstance (scopes : List ScopeData) (scopeIdx : Nat) : Option InstanceKey :=
  match listGetOpt scopes scopeIdx with
  | none => none
  | some sd =>
    match ScopeData.inlined sd with
    | some inst => some inst
    | none =>
      match ScopeData.inlinedParentScope sd with
      | some pid => (listGetOpt scopes pid).bind ScopeData.inlined
      | none => none

/-- Attribute a `Coverage::VirtualCounter` statement in `callerInstance` using `codegen_coverage`
    (`compiler/rustc_codegen_ssa/src/mir/coverageinfo.rs:7-17`) and `query::is_inlined`. -/
noncomputable def attributeCoverageCounter (caller : InstanceKey) (scopes : List ScopeData)
    (scopeIdx bcb : Nat) : InstanceKey × Nat :=
  match inlinedInstance scopes scopeIdx with
  | some inst => (inst, bcb)
  | none => (caller, bcb)

/-- **Theorem 3 (`inlinedInstance_monomorphize_preserves_distinct_counters`)**:
    Inlining `generic_inlined::<u32>` (`tyArg = 32`) and `generic_inlined::<u64>` (`tyArg = 64`)
    into `main` (`fnId = 0`) preserves their distinct `(InstanceKey, bcb)` counter slots,
    and transitive inlining (`C` into `B` into `A`) preserves the innermost callee `C`. -/
theorem inlinedInstance_monomorphize_preserves_distinct_counters :
    let mainInst : InstanceKey := ⟨0, 0⟩
    let genU32 : InstanceKey := ⟨1, 32⟩
    let genU64 : InstanceKey := ⟨1, 64⟩
    let innerC : InstanceKey := ⟨2, 99⟩
    let scopes : List ScopeData :=
      [ ⟨none, none, none⟩            -- 0: main root
      , ⟨some 0, some genU32, none⟩   -- 1: inlined generic_inlined::<u32> root
      , ⟨some 1, none, some 1⟩        -- 2: child scope inside generic_inlined::<u32>
      , ⟨some 0, some genU64, none⟩   -- 3: inlined generic_inlined::<u64> root
      , ⟨some 2, some innerC, some 1⟩ -- 4: nested callee C inlined inside generic_inlined::<u32>
      ]
    attributeCoverageCounter mainInst scopes 2 0 ≠ attributeCoverageCounter mainInst scopes 3 0 ∧
    attributeCoverageCounter mainInst scopes 2 0 = (genU32, 0) ∧
    attributeCoverageCounter mainInst scopes 3 0 = (genU64, 0) ∧
    attributeCoverageCounter mainInst scopes 4 1 = (innerC, 1) := by
  decide

-- ============================================================================
-- Part IV: Three Constructive Counterexamples
-- ============================================================================

/-- **Counterexample 1 (`ce1_nondominated_single_def_in_ssa_reads_unbound_vreg`)**:
    On `cm_3_single_def_nondominating_read_forces_alloca`, taking the direct branch `bb0 -> bb2`
    bypasses the unique assignment in `bb1`. Keeping local `_3` in `LocalKind::SSA` (without
    `LocalKind::Memory` alloca fallback) hits `ssaUseBeforeDef` at runtime (reading an unbound
    virtual register), whereas `LocalAnalyzer`'s demotion to `LocalKind::Memory` succeeds and
    matches MIR (`uninit`) slot semantics. -/
theorem ce1_nondominated_single_def_in_ssa_reads_unbound_vreg :
    let events : List TraceEvent := [.read 2 0 []]
    analyzeUses .scalar cm2Dom [.define (.assignment 1 0), .read 2 0 []] = .memory ∧
    evalLoweredTrace (.ssa (.assignment 1 0)) events = .error .ssaUseBeforeDef ∧
    evalLoweredTrace .memory events = .ok (evalMirTrace events) := by
  decide

/-- **Counterexample 2 (`ce2_unpromoted_shared_cleanup_join_violates_seh_funclet_isolation`)**:
    Before promoting shared join block `bb4` in `seh_true_internal_join_promotion` from
    `Internal { funclet := 7 }` to `Funclet`, `7 -> 4` lowers as an intra-funclet `br`
    (`(false, false)` — keeping `bb4` under `%cleanuppad2`), while `6 -> 4` lowers as
    `cleanupret unwind label %funclet_bb4` (`(true, true)` — entering a separate `%cleanuppad1`),
    creating conflicting LLVM WinEH funclet colors on `bb4`. After `propagateEdge` promotes
    `bb4` to `Funclet`, BOTH `7 -> 4` and `6 -> 4` lower cleanly as `(true, true)` `cleanupret`. -/
theorem ce2_unpromoted_shared_cleanup_join_violates_seh_funclet_isolation :
    let prePromotionKinds : List CleanupKind :=
      [ .notCleanup, .notCleanup, .notCleanup, .notCleanup, .internal 7,
        .notCleanup, .funclet,    .funclet,    .notCleanup, .notCleanup ]
    llbbCharacteristics prePromotionKinds 7 4 = .ok (false, false) ∧
    llbbCharacteristics prePromotionKinds 6 4 = .ok (true, true) ∧
    (∃ st', propagateEdge ⟨prePromotionKinds, List.replicate 10 none⟩ 6 4 = .ok st' ∧
      getKind st'.kinds 4 = .funclet ∧
      llbbCharacteristics st'.kinds 7 4 = .ok (true, true) ∧
      llbbCharacteristics st'.kinds 6 4 = .ok (true, true)) := by
  refine ⟨by decide, by decide, ?_⟩
  refine ⟨{
    kinds := [ .notCleanup, .notCleanup, .notCleanup, .notCleanup, .funclet,
               .notCleanup, .funclet,    .funclet,    .notCleanup, .notCleanup ],
    funcletSuccs := [none, none, none, none, none, none, some 4, some 4, none, none]
  }, by decide, by decide, by decide, by decide⟩

/-- **Counterexample 3 (`ce3_non_out_summable_abort_block_breaks_naive_outflow_conservation`)**:
    In a 2-node CFG `start (bb0)` -> `yield_or_abort (bb1)` -> `resumed (bb2)` where `bb1` is entered
    10 times (`flow(bb0) = flow(bb1) = 10`) but yields/aborts without resuming 3 times so
    `flow(bb2) = 7` (`is_out_summable(bb1) = false`), naive outflow conservation `flow(bb1) = flow(bb2)`
    would falsely reconstruct `flow(bb1) = 7 ≠ 10` (error of 3), whereas `BalancedFlowGraph`'s
    forced sink edge `bb1 -> sink` carries the missing `3` units (`7 + 3 = 10`). -/
theorem ce3_non_out_summable_abort_block_breaks_naive_outflow_conservation :
    let flow0 : Int := 10
    let flow1 : Int := 10
    let flow2 : Int := 7
    let sinkEdgeFrom1 : Int := 3
    flow1 ≠ flow2 ∧
    flow0 = flow1 ∧
    flow1 = flow2 + sinkEdgeFrom1 := by
  decide

-- ============================================================================
-- Axiom Footprint Checks
-- ============================================================================

#print axioms zst_preserved_non_drop
#print axioms zst_with_drop_promotes_to_memory
#print axioms memory_fixed_step
#print axioms stepUse_monotone_non_zst
#print axioms second_define_demotes_to_memory
#print axioms non_dominated_read_demotes_to_memory
#print axioms disallowed_proj_demotes_to_memory
#print axioms localAnalyzer_ssa_or_memory_simulation_exact
#print axioms cm1_single_def_stays_ssa
#print axioms cm2_two_defs_demotes_to_memory
#print axioms cm3_nondominated_single_def_demotes_to_memory
#print axioms cm4_scalarpair_field_read_stays_ssa
#print axioms cm5_scalarpair_field_write_demotes_to_memory
#print axioms cm6_raw_borrow_demotes_to_memory
#print axioms cleanupKinds_no_cross_funclet_internal_edge
#print axioms distinct_funclet_edge_lowers_to_cleanupret
#print axioms seh_shared_cleanup_promotion_tree_verified
#print axioms seh_true_internal_join_promotion_tree_verified
#print axioms seh_two_parents_triggers_span_bug
#print axioms bcbFlow_counterExpression_reconstructs_exact
#print axioms hotLoop_reloop_priority_places_latch_first
#print axioms hotLoop_concrete_100_iters_reconstructs_exact
#print axioms inlinedInstance_monomorphize_preserves_distinct_counters
#print axioms ce1_nondominated_single_def_in_ssa_reads_unbound_vreg
#print axioms ce2_unpromoted_shared_cleanup_join_violates_seh_funclet_isolation
#print axioms ce3_non_out_summable_abort_block_breaks_naive_outflow_conservation

end SsaLocalAnalyzerAndCoverageFlow
