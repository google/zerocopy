/-!
# Soundness of `rustc` MIR `UnwindAction`, `AbortUnwindingCalls`, `extern "C-unwind"` ABI Boundaries, Double-Panic `InCleanup`, `-Cpanic=abort` Cleanup Erasure, and LLVM `nounwind` Lowering

This standalone, zero-import (`Init` only) Lean `v4.34.1` formalization establishes
kernel-checked soundness theorems corresponding to:
- `compiler/rustc_middle/src/mir/syntax.rs` (`UnwindAction`, `UnwindTerminateReason`)
- `compiler/rustc_middle/src/mir/terminator.rs` (`UnwindTerminateReason::lang_item`)
- `compiler/rustc_middle/src/ty/layout.rs` (`fn_can_unwind`)
- `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` (`AbortUnwindingCalls`)
- `compiler/rustc_mir_transform/src/validate.rs` (`CfgChecker::check_unwind_edge`)
- `compiler/rustc_codegen_ssa/src/mir/block.rs` (`do_call`, `terminate_block`)
- `compiler/rustc_codegen_llvm/src/abi.rs` (`apply_attrs_llfn`, `apply_attrs_callsite`)

## Purity Discipline
- Every term-level definition carries explicit `noncomputable def` (zero implicit recursive
  definitions, zero file-wide noncomputable sections, zero compiler-synthesized derived clauses,
  and zero unsafe-recursion helper constants).
- Pure constructive proofs strictly within `{propext, Quot.sound}`: zero stubbed holes, zero
  choice axioms, zero SMT/decider automation, zero native evaluation, and zero partial recursion.
-/

namespace MirUnwindSoundness

/-! ## Section 1: Pure Kernel-Reducible Collection & Boolean Primitives -/

/-- Structural Boolean equality on `Nat` using only primitive recursion. -/
noncomputable def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | n + 1, m + 1 => natEq n m
  | _, _ => false

/-- Strict less-than comparison on `Nat` using only primitive recursion. -/
noncomputable def natLt : Nat → Nat → Bool
  | _, 0 => false
  | 0, _ + 1 => true
  | n + 1, m + 1 => natLt n m

/-- Less-than-or-equal comparison on `Nat`. -/
noncomputable def natLe : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | n + 1, m + 1 => natLe n m

/-- Boolean negation. -/
noncomputable def bnot : Bool → Bool
  | true => false
  | false => true

/-- Boolean conjunction. -/
noncomputable def band : Bool → Bool → Bool
  | true, b => b
  | false, _ => false

/-- Boolean disjunction. -/
noncomputable def bor : Bool → Bool → Bool
  | true, _ => true
  | false, b => b

/-- Boolean equality. -/
noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Safe total list indexing by `Nat`. -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Safe functional update at index `Nat`. -/
noncomputable def listSet {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

/-- Pure list map. -/
noncomputable def listMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: listMap f xs

/-- Pure list fold-left. -/
noncomputable def listFoldl {α β : Type} (f : β → α → β) (init : β) : List α → β
  | [] => init
  | x :: xs => listFoldl f (f init x) xs

/-- Pure list universal predicate in `Prop`. -/
noncomputable def listForall {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ listForall P xs

/-- Pure indexed list universal predicate in `Prop`. -/
noncomputable def listForallIdxFrom {α : Type} (P : Nat → α → Prop) (k : Nat) : List α → Prop
  | [] => True
  | x :: xs => P k x ∧ listForallIdxFrom P (k + 1) xs

/-- Pure indexed list universal predicate starting at index `0`. -/
noncomputable def listForallIdx {α : Type} (P : Nat → α → Prop) (xs : List α) : Prop :=
  listForallIdxFrom P 0 xs

/-- Pure membership predicate for `Nat` lists. -/
noncomputable def natListMem (k : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => bor (natEq k x) (natListMem k xs)

/-- Length of a list without relying on typeclass projections. -/
noncomputable def listLen {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => listLen xs + 1

/-- Append a single optional trace event to a trace list. -/
noncomputable def appendOptEvent (tr : List Nat) : Option Nat → List Nat
  | none => tr
  | some ev => tr ++ [ev]

/-- Read a register slot from a local environment, defaulting to `0` if out of bounds
when `read` is total, or returning `Option` for strict well-formed lookup. -/
noncomputable def readLocal? (locals : List Nat) (r : Nat) : Option Nat :=
  listGet? locals r

/-- Write a register slot if in bounds, leaving lengths unchanged. -/
noncomputable def writeLocal (locals : List Nat) (r v : Nat) : List Nat :=
  listSet locals r v

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natEq_eq {n m : Nat} (h : natEq n m = true) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m' => contradiction
  | succ n' ih =>
    cases m with
    | zero => contradiction
    | succ m' =>
      have h' : n' = m' := ih h
      rw [h']

theorem natEq_true_iff (n m : Nat) : natEq n m = true ↔ n = m :=
  ⟨natEq_eq, fun h => by rw [h]; exact natEq_refl m⟩

theorem band_true_iff (a b : Bool) : band a b = true ↔ a = true ∧ b = true := by
  cases a
  · cases b
    · constructor <;> intro h
      · contradiction
      · exact (Bool.false_ne_true h.1).elim
    · constructor <;> intro h
      · contradiction
      · exact (Bool.false_ne_true h.1).elim
  · cases b
    · constructor <;> intro h
      · contradiction
      · exact (Bool.false_ne_true h.2).elim
    · constructor <;> intro _
      · exact ⟨rfl, rfl⟩
      · rfl

theorem bor_true_iff (a b : Bool) : bor a b = true ↔ a = true ∨ b = true := by
  cases a
  · cases b
    · constructor <;> intro h
      · contradiction
      · cases h <;> contradiction
    · constructor <;> intro _
      · exact Or.inr rfl
      · rfl
  · cases b
    · constructor <;> intro _
      · exact Or.inl rfl
      · rfl
    · constructor <;> intro _
      · exact Or.inl rfl
      · rfl

theorem listGet?_listMap {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    listGet? (listMap f xs) i = match listGet? xs i with | some x => some (f x) | none => none := by
  induction xs generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' => exact ih i'

theorem listGet?_listForallIdxFrom {α : Type} (P : Nat → α → Prop) (xs : List α) (k i : Nat) (x : α)
    (hall : listForallIdxFrom P k xs) (hget : listGet? xs i = some x) : P (k + i) x := by
  induction xs generalizing k i with
  | nil =>
    cases i <;> contradiction
  | cons y ys ih =>
    cases i with
    | zero =>
      cases hget
      have h0 : k + 0 = k := Nat.add_zero k
      rw [h0]
      exact hall.1
    | succ i' =>
      have hstep := ih (k + 1) i' hall.2 hget
      have hassoc : k + 1 + i' = k + (i' + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 i']
      rw [← hassoc]
      exact hstep

theorem listGet?_listForallIdx {α : Type} (P : Nat → α → Prop) (xs : List α) (i : Nat) (x : α)
    (hall : listForallIdx P xs) (hget : listGet? xs i = some x) : P i x := by
  have h := listGet?_listForallIdxFrom P xs 0 i x hall hget
  have hz : 0 + i = i := Nat.zero_add i
  rw [hz] at h
  exact h

theorem listForallIdxFrom_map {α β : Type} (f : α → β) (P : Nat → β → Prop) (xs : List α) (k : Nat)
    (h : listForallIdxFrom (fun idx a => P idx (f a)) k xs) :
    listForallIdxFrom P k (listMap f xs) := by
  induction xs generalizing k with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨h.1, ih (k + 1) h.2⟩

theorem listForallIdx_map {α β : Type} (f : α → β) (P : Nat → β → Prop) (xs : List α)
    (h : listForallIdx (fun idx a => P idx (f a)) xs) :
    listForallIdx P (listMap f xs) :=
  listForallIdxFrom_map f P xs 0 h

/-! ## Section 2: MIR Syntax, ABI Unwind Eligibility, and Program Representation -/

abbrev FnId := Nat
abbrev BlockId := Nat
abbrev LocalId := Nat
abbrev TraceEvent := Nat

/-- Target panic strategy (`rustc_target::spec::PanicStrategy`). -/
inductive PanicStrategy where
  | unwind
  | abort

/-- Function ABI classification (`rustc_abi::ExternAbi` subset relevant to unwinding). -/
inductive FnAbi where
  | rust
  | c (canUnwind : Bool)

/-- Termination reason on `UnwindAction::Terminate` and `TerminatorKind::UnwindTerminate`
(`compiler/rustc_middle/src/mir/syntax.rs`). -/
inductive UnwindTerminateReason where
  | abi
  | inCleanup

/-- Structural equality on `UnwindTerminateReason`. -/
noncomputable def unwindTerminateReasonEq : UnwindTerminateReason → UnwindTerminateReason → Bool
  | .abi, .abi => true
  | .inCleanup, .inCleanup => true
  | _, _ => false

/-- Action on unwind edge (`rustc_middle::mir::UnwindAction`). -/
inductive UnwindAction where
  | continue_
  | unreachable
  | terminate (reason : UnwindTerminateReason)
  | cleanup (bb : BlockId)

/-- Structural equality on `UnwindAction`. -/
noncomputable def unwindActionEq : UnwindAction → UnwindAction → Bool
  | .continue_, .continue_ => true
  | .unreachable, .unreachable => true
  | .terminate r1, .terminate r2 => unwindTerminateReasonEq r1 r2
  | .cleanup b1, .cleanup b2 => natEq b1 b2
  | _, _ => false

/-- Exact `rustc_middle::ty::layout::fn_can_unwind` predicate
(`compiler/rustc_middle/src/ty/layout.rs`).
- `#[rustc_nounwind]` (`neverUnwind = true`) unconditionally disables unwinding.
- Under `-C panic=abort`, every non-foreign function (`isForeign = false`) cannot unwind,
  even if declared `extern "C-unwind"`.
- Foreign declarations (`isForeign = true`, or indirect `extern "C-unwind"` fn pointers)
  obey the ABI flag (`C { unwind }`) even under `-C panic=abort`. -/
noncomputable def fnCanUnwind (strat : PanicStrategy) (isForeign : Bool)
    (neverUnwind : Bool) (abi : FnAbi) : Bool :=
  match neverUnwind with
  | true => false
  | false =>
    match strat, isForeign with
    | .abort, false => false
    | _, _ =>
      match abi with
      | .rust =>
        match strat with
        | .unwind => true
        | .abort => false
      | .c canUnwind => canUnwind

/-- MIR basic-block statements capturing local dataflow and observable trace events. -/
inductive Stmt where
  | assignConst (dst : LocalId) (val : Nat)
  | assignLocal (dst src : LocalId)
  | emit (ev : TraceEvent)
  | nop

/-- MIR basic-block terminators covering normal flow, calls, drops, panics, and unwinds. -/
inductive Terminator where
  | goto (target : BlockId)
  | branch (cond : LocalId) (zeroTarget nonzeroTarget : BlockId)
  | return_ (valReg : LocalId)
  | unreachable
  | unwindResume
  | unwindTerminate (reason : UnwindTerminateReason)
  | call (callee : FnId) (arg : LocalId) (dst : LocalId) (retTarget : BlockId) (unwind : UnwindAction)
  | drop (dropFn : FnId) (arg : LocalId) (retTarget : BlockId) (unwind : UnwindAction)
  | panicCall (unwind : UnwindAction)

/-- MIR basic block (`rustc_middle::mir::BasicBlockData`). -/
structure BasicBlock where
  stmts : List Stmt
  term : Terminator
  isCleanup : Bool

/-- Foreign FFI outcome returned by an external callee specification. -/
inductive ForeignOutcome where
  | ret (val : Nat) (ev : Option TraceEvent)
  | unwound (ev : Option TraceEvent)

/-- MIR function body (either a local Rust MIR definition or a foreign extern decl). -/
structure FnBody where
  abi : FnAbi
  isForeign : Bool
  neverUnwind : Bool
  localCount : Nat
  blocks : List BasicBlock

/-- Effective `fn_can_unwind` for a `FnBody` under `strat`. -/
noncomputable def bodyCanUnwind (strat : PanicStrategy) (fn : FnBody) : Bool :=
  fnCanUnwind strat fn.isForeign fn.neverUnwind fn.abi

/-- Complete MIR program unit. -/
structure Program where
  strategy : PanicStrategy
  targetSupportsUnwinding : Bool
  panicInDropUnwinds : Bool
  entryFn : FnId
  fns : List FnBody
  foreignSpecs : FnId → Nat → ForeignOutcome

/-- Lookup `fn_can_unwind` for a callee `FnId` (failing closed to `false` if missing). -/
noncomputable def calleeCanUnwind (prog : Program) (callee : FnId) : Bool :=
  match listGet? prog.fns callee with
  | none => false
  | some fn => bodyCanUnwind prog.strategy fn

/-- Lookup `fn_can_unwind` for a `Drop` terminator (`layout::fn_can_unwind` with
`ExternAbi::Rust` gated by `panic_in_drop` and `panic_strategy`). -/
noncomputable def dropCanUnwind (prog : Program) (dropFn : FnId) : Bool :=
  match listGet? prog.fns dropFn with
  | none => false
  | some fn =>
    band prog.panicInDropUnwinds
      (band (fnCanUnwind prog.strategy false fn.neverUnwind .rust)
            (bodyCanUnwind prog.strategy fn))

/-- Compute whether the call/drop/panic terminator itself may unwind at runtime under `prog`
(`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`). -/
noncomputable def termCallCanUnwind (prog : Program) : Terminator → Bool
  | .call callee _ _ _ _ => calleeCanUnwind prog callee
  | .drop dropFn _ _ _ => dropCanUnwind prog dropFn
  | .panicCall _ => fnCanUnwind prog.strategy false false .rust
  | _ => false

/-- Foreign contract: any foreign declaration whose `bodyCanUnwind = false` never returns
an `.unwound` foreign outcome (a precondition of FFI ABI soundness). -/
noncomputable def ForeignContractOK (prog : Program) : Prop :=
  ∀ fid arg,
    match listGet? prog.fns fid with
    | some fn =>
      fn.isForeign = true →
      bodyCanUnwind prog.strategy fn = false →
      ∀ ev, prog.foreignSpecs fid arg ≠ .unwound ev
    | none => True

/-! ## Section 3: MIR Well-Formedness (`validate.rs` Pre-Pass and Post-Pass Invariants) -/

/-- Normal (non-unwind) successors of a MIR terminator. -/
noncomputable def normalSuccs : Terminator → List BlockId
  | .goto t => [t]
  | .branch _ z nz => [z, nz]
  | .call _ _ _ rt _ => [rt]
  | .drop _ _ rt _ => [rt]
  | .return_ _ | .unreachable | .unwindResume | .unwindTerminate _ | .panicCall _ => []

/-- Unwind action carried by a terminator, if any. -/
noncomputable def termUnwind? : Terminator → Option UnwindAction
  | .call _ _ _ _ u => some u
  | .drop _ _ _ u => some u
  | .panicCall u => some u
  | _ => none

/-- Pre-`AbortUnwindingCalls` unwind edge validity:
- `Cleanup(target)` is only valid in non-cleanup blocks (`bbCleanup = false`) and targets
  a valid cleanup block (`targetBlk.isCleanup = true`).
- `Continue` is only valid in non-cleanup blocks (`bbCleanup = false`).
- `Terminate(.inCleanup)` is only valid in cleanup blocks (`bbCleanup = true`).
- Inside cleanup blocks, unwinding edges may only be `Terminate(.inCleanup)` or `Unreachable`. -/
noncomputable def PrePassUnwindEdgeWF (blocks : List BasicBlock) (bbCleanup : Bool)
    (u : UnwindAction) : Prop :=
  match u with
  | .cleanup target =>
    bbCleanup = false ∧
    ∃ blk, listGet? blocks target = some blk ∧ blk.isCleanup = true
  | .continue_ =>
    bbCleanup = false
  | .terminate .inCleanup =>
    bbCleanup = true
  | .terminate .abi =>
    bbCleanup = false
  | .unreachable =>
    True

/-- Post-`AbortUnwindingCalls` unwind edge validity (matching `CfgChecker::check_unwind_edge`
in `compiler/rustc_mir_transform/src/validate.rs`):
- All `PrePassUnwindEdgeWF` constraints hold.
- If `targetSupportsUnwinding = false` or `callCanUnwind = false`, non-cleanup unwind edge is `.unreachable`.
- If `bodyCanUnwind = false` (or `targetSupportsUnwinding = false`), `UnwindAction.continue_` is forbidden. -/
noncomputable def PostPassUnwindEdgeWF (targetSupportsUnwinding : Bool) (bodyUnw : Bool)
    (callUnw : Bool) (blocks : List BasicBlock) (bbCleanup : Bool) (u : UnwindAction) : Prop :=
  PrePassUnwindEdgeWF blocks bbCleanup u ∧
  (bbCleanup = false → (targetSupportsUnwinding = false ∨ callUnw = false) → u = .unreachable) ∧
  ((targetSupportsUnwinding = false ∨ bodyUnw = false) → u ≠ .continue_)

/-- Check local register validity for a statement. -/
noncomputable def StmtWF (locCount : Nat) : Stmt → Prop
  | .assignConst dst _ => natLt dst locCount = true
  | .assignLocal dst src => natLt dst locCount = true ∧ natLt src locCount = true
  | .emit _ | .nop => True

/-- Pre-pass terminator well-formedness for a basic block in `fn`. -/
noncomputable def PrePassTermWF (prog : Program) (fn : FnBody) (bbCleanup : Bool)
    (t : Terminator) : Prop :=
  match t with
  | .goto target =>
    ∃ blk, listGet? fn.blocks target = some blk ∧ blk.isCleanup = bbCleanup
  | .branch cond z nz =>
    natLt cond fn.localCount = true ∧
    (∃ b1, listGet? fn.blocks z = some b1 ∧ b1.isCleanup = bbCleanup) ∧
    (∃ b2, listGet? fn.blocks nz = some b2 ∧ b2.isCleanup = bbCleanup)
  | .return_ valReg =>
    bbCleanup = false ∧ natLt valReg fn.localCount = true
  | .unreachable =>
    True
  | .unwindResume =>
    bbCleanup = true
  | .unwindTerminate _ =>
    bbCleanup = true
  | .call callee arg dst rt u =>
    natLt arg fn.localCount = true ∧
    natLt dst fn.localCount = true ∧
    (∃ cfn, listGet? prog.fns callee = some cfn) ∧
    (∃ rblk, listGet? fn.blocks rt = some rblk ∧ rblk.isCleanup = bbCleanup) ∧
    PrePassUnwindEdgeWF fn.blocks bbCleanup u ∧
    (bbCleanup = true → u = .terminate .inCleanup)
  | .drop dropFn arg rt u =>
    natLt arg fn.localCount = true ∧
    (∃ dfn, listGet? prog.fns dropFn = some dfn ∧
      dfn.isForeign = false ∧ dfn.abi = .rust ∧
      (prog.panicInDropUnwinds = false → dfn.neverUnwind = true)) ∧
    (∃ rblk, listGet? fn.blocks rt = some rblk ∧ rblk.isCleanup = bbCleanup) ∧
    PrePassUnwindEdgeWF fn.blocks bbCleanup u ∧
    (bbCleanup = true → u = .terminate .inCleanup)
  | .panicCall u =>
    PrePassUnwindEdgeWF fn.blocks bbCleanup u ∧
    (bbCleanup = true → u = .terminate .inCleanup)

/-- Post-pass terminator well-formedness enforcing `AbortUnwindingCalls` guarantees:
- If `targetSupportsUnwinding = false`, `UnwindResume` is forbidden.
- If `bodyCanUnwind = false`, `UnwindResume` is forbidden (replaced by `UnwindTerminate .abi`).
- Every unwind edge satisfies `PostPassUnwindEdgeWF`. -/
noncomputable def PostPassTermWF (prog : Program) (fn : FnBody) (bbCleanup : Bool)
    (t : Terminator) : Prop :=
  PrePassTermWF prog fn bbCleanup t ∧
  (t = .unwindResume → prog.targetSupportsUnwinding = true ∧ bodyCanUnwind prog.strategy fn = true) ∧
  match termUnwind? t with
  | none => True
  | some u =>
    PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn)
      (termCallCanUnwind prog t) fn.blocks bbCleanup u

/-- Well-formedness of one basic block (pre-pass). -/
noncomputable def PrePassBlockWF (prog : Program) (fn : FnBody) (blk : BasicBlock) : Prop :=
  listForall (StmtWF fn.localCount) blk.stmts ∧
  PrePassTermWF prog fn blk.isCleanup blk.term

/-- Well-formedness of one basic block (post-pass). -/
noncomputable def PostPassBlockWF (prog : Program) (fn : FnBody) (blk : BasicBlock) : Prop :=
  listForall (StmtWF fn.localCount) blk.stmts ∧
  PostPassTermWF prog fn blk.isCleanup blk.term

/-- Function-level well-formedness (pre-pass): entry block `0` exists and is non-cleanup,
non-foreign functions have non-empty blocks and `localCount ≥ 2`, and foreign functions
have empty blocks (never directly executed in MIR). -/
noncomputable def PrePassFnWF (prog : Program) (fn : FnBody) : Prop :=
  match fn.isForeign with
  | true => fn.blocks = []
  | false =>
    natLe 2 fn.localCount = true ∧
    (∃ b0, listGet? fn.blocks 0 = some b0 ∧ b0.isCleanup = false) ∧
    listForall (PrePassBlockWF prog fn) fn.blocks

/-- Function-level well-formedness (post-pass). -/
noncomputable def PostPassFnWF (prog : Program) (fn : FnBody) : Prop :=
  match fn.isForeign with
  | true => fn.blocks = []
  | false =>
    natLe 2 fn.localCount = true ∧
    (∃ b0, listGet? fn.blocks 0 = some b0 ∧ b0.isCleanup = false) ∧
    listForall (PostPassBlockWF prog fn) fn.blocks

/-- Program-level well-formedness (pre-pass). -/
noncomputable def MirPrePassWF (prog : Program) : Prop :=
  (prog.targetSupportsUnwinding = false → prog.strategy = .abort) ∧
  (∃ entry, listGet? prog.fns prog.entryFn = some entry ∧ entry.isForeign = false) ∧
  listForall (PrePassFnWF prog) prog.fns

/-- Program-level well-formedness (post-pass). -/
noncomputable def MirPostPassWF (prog : Program) : Prop :=
  (prog.targetSupportsUnwinding = false → prog.strategy = .abort) ∧
  (∃ entry, listGet? prog.fns prog.entryFn = some entry ∧ entry.isForeign = false) ∧
  listForall (PostPassFnWF prog) prog.fns

/-! ## Section 4: Multi-Frame MIR Operational Semantics with Cleanup Depth -/

/-- Caller continuation frame saved when pushing a callee frame. -/
structure CallerCont where
  fnId : FnId
  locals : List Nat
  inCleanup : Bool
  retDst : LocalId
  retTarget : BlockId
  unwindOnCall : UnwindAction

/-- Active execution frame. -/
structure ActiveFrame where
  fnId : FnId
  bb : BlockId
  stmtIdx : Nat
  locals : List Nat
  inCleanup : Bool

/-- Full multi-frame MIR runtime state. -/
structure MirState where
  cur : ActiveFrame
  stack : List CallerCont
  cleanupDepth : Nat
  trace : List TraceEvent

/-- Terminal or out-of-fuel execution outcomes. -/
inductive MirExecResult where
  | returned (val : Nat) (trace : List TraceEvent)
  | unwound (trace : List TraceEvent)
  | terminated (reason : UnwindTerminateReason) (trace : List TraceEvent)
  | aborted (trace : List TraceEvent)
  | ub (trace : List TraceEvent)
  | invalid (trace : List TraceEvent)
  | outOfFuel (st : MirState)

/-- Single-step transition output. -/
inductive MirStep where
  | running (st : MirState)
  | halted (res : MirExecResult)

/-- Build initial local register vector of length `count`, placing `arg` at slot `1`. -/
noncomputable def initLocalsAux : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n + 1, idx, arg =>
    let v := match idx with | 1 => arg | _ => 0
    v :: initLocalsAux n (idx + 1) arg

noncomputable def initLocals (count arg : Nat) : List Nat :=
  initLocalsAux count 0 arg

/-- Initial MIR machine state for `prog` with entry argument `arg`. -/
noncomputable def initMirState (prog : Program) (arg : Nat) : Option MirState :=
  match listGet? prog.fns prog.entryFn with
  | none => none
  | some fn =>
    some {
      cur := { fnId := prog.entryFn, bb := 0, stmtIdx := 0, locals := initLocals fn.localCount arg, inCleanup := false }
      stack := []
      cleanupDepth := 0
      trace := []
    }

/-- Execute a single MIR statement inside `cur`. -/
noncomputable def execStmt (st : MirState) : Stmt → MirStep
  | .nop =>
    .running { st with cur := { st.cur with stmtIdx := st.cur.stmtIdx + 1 } }
  | .emit ev =>
    .running {
      st with
      cur := { st.cur with stmtIdx := st.cur.stmtIdx + 1 }
      trace := st.trace ++ [ev]
    }
  | .assignConst dst val =>
    .running {
      st with
      cur := {
        st.cur with
        stmtIdx := st.cur.stmtIdx + 1
        locals := writeLocal st.cur.locals dst val
      }
    }
  | .assignLocal dst src =>
    match readLocal? st.cur.locals src with
    | none => .halted (.invalid st.trace)
    | some v =>
      .running {
        st with
        cur := {
          st.cur with
          stmtIdx := st.cur.stmtIdx + 1
          locals := writeLocal st.cur.locals dst v
        }
      }

/-- Propagate an unwind through `cur`'s `u`, structurally descending `stack` on `.continue_`.
- `.cleanup pad`: enters cleanup block `pad` in `cur` (`inCleanup := true`, `depth + 1`).
- `.terminate r`: deterministically halts with `.terminated r` (zero UB).
- `.unreachable`: immediate `.ub`.
- `.continue_`: pops `cur`; if `stack` is empty, halts with `.unwound`; otherwise dispatches
  caller's `c.unwindOnCall` in caller context `c` (preserving `depth` across non-cleanup frames). -/
noncomputable def dispatchUnwind (fns : List FnBody) (cur : ActiveFrame)
    (stack : List CallerCont) (u : UnwindAction) (depth : Nat)
    (trace : List Nat) : MirStep :=
  match u with
  | .terminate reason => .halted (.terminated reason trace)
  | .unreachable => .halted (.ub trace)
  | .cleanup padBB =>
    match listGet? fns cur.fnId with
    | none => .halted (.invalid trace)
    | some fn =>
      match listGet? fn.blocks padBB with
      | none => .halted (.invalid trace)
      | some blk =>
        match blk.isCleanup with
        | false => .halted (.invalid trace)
        | true =>
          .running {
            cur := { cur with bb := padBB, stmtIdx := 0, inCleanup := true }
            stack := stack
            cleanupDepth := depth + 1
            trace := trace
          }
  | .continue_ =>
    match stack with
    | [] => .halted (.unwound trace)
    | c :: rest =>
      let callerFrame : ActiveFrame := {
        fnId := c.fnId
        bb := c.retTarget
        stmtIdx := 0
        locals := c.locals
        inCleanup := c.inCleanup
      }
      dispatchUnwind fns callerFrame rest c.unwindOnCall depth trace

/-- Helper for completing a MIR call (pushing a local frame or invoking a foreign spec). -/
noncomputable def enterCall (prog : Program) (st : MirState) (callee : FnId)
    (argVal : Nat) (dst : LocalId) (rt : BlockId) (u : UnwindAction) : MirStep :=
  match listGet? prog.fns callee with
  | none => .halted (.invalid st.trace)
  | some cfn =>
    match cfn.isForeign with
    | true =>
      match prog.foreignSpecs callee argVal with
      | .ret v evOpt =>
        let tr' := appendOptEvent st.trace evOpt
        .running {
          st with
          cur := { st.cur with bb := rt, stmtIdx := 0, locals := writeLocal st.cur.locals dst v }
          trace := tr'
        }
      | .unwound evOpt =>
        let tr' := appendOptEvent st.trace evOpt
        dispatchUnwind prog.fns st.cur st.stack u st.cleanupDepth tr'
    | false =>
      let cont : CallerCont := {
        fnId := st.cur.fnId
        locals := st.cur.locals
        inCleanup := st.cur.inCleanup
        retDst := dst
        retTarget := rt
        unwindOnCall := u
      }
      let nextFrame : ActiveFrame := {
        fnId := callee
        bb := 0
        stmtIdx := 0
        locals := initLocals cfn.localCount argVal
        inCleanup := false
      }
      .running {
        cur := nextFrame
        stack := cont :: st.stack
        cleanupDepth := st.cleanupDepth
        trace := st.trace
      }

/-- Execute a MIR terminator inside `st`. -/
noncomputable def execTerm (prog : Program) (st : MirState) : Terminator → MirStep
  | .goto target =>
    .running { st with cur := { st.cur with bb := target, stmtIdx := 0 } }
  | .branch cond z nz =>
    match readLocal? st.cur.locals cond with
    | none => .halted (.invalid st.trace)
    | some v =>
      let target := match v with | 0 => z | _ => nz
      .running { st with cur := { st.cur with bb := target, stmtIdx := 0 } }
  | .return_ valReg =>
    match st.cur.inCleanup with
    | true => .halted (.invalid st.trace)
    | false =>
      match readLocal? st.cur.locals valReg with
      | none => .halted (.invalid st.trace)
      | some v =>
        match st.stack with
        | [] => .halted (.returned v st.trace)
        | c :: rest =>
          .running {
            cur := {
              fnId := c.fnId
              bb := c.retTarget
              stmtIdx := 0
              locals := writeLocal c.locals c.retDst v
              inCleanup := c.inCleanup
            }
            stack := rest
            cleanupDepth := st.cleanupDepth
            trace := st.trace
          }
  | .unreachable =>
    .halted (.ub st.trace)
  | .unwindTerminate reason =>
    .halted (.terminated reason st.trace)
  | .unwindResume =>
    match st.cur.inCleanup with
    | false => .halted (.invalid st.trace)
    | true =>
      let depth' := match st.cleanupDepth with | 0 => 0 | d + 1 => d
      match st.stack with
      | [] => .halted (.unwound st.trace)
      | c :: rest =>
        let callerFrame : ActiveFrame := {
          fnId := c.fnId
          bb := c.retTarget
          stmtIdx := 0
          locals := c.locals
          inCleanup := c.inCleanup
        }
        dispatchUnwind prog.fns callerFrame rest c.unwindOnCall depth' st.trace
  | .call callee argReg dst rt u =>
    match readLocal? st.cur.locals argReg with
    | none => .halted (.invalid st.trace)
    | some argVal => enterCall prog st callee argVal dst rt u
  | .drop dropFn argReg rt u =>
    match readLocal? st.cur.locals argReg with
    | none => .halted (.invalid st.trace)
    | some argVal => enterCall prog st dropFn argVal 0 rt u
  | .panicCall u =>
    match prog.strategy, prog.targetSupportsUnwinding with
    | .unwind, true => dispatchUnwind prog.fns st.cur st.stack u st.cleanupDepth st.trace
    | _, _ => .halted (.aborted st.trace)

/-- Single small-step MIR transition. -/
noncomputable def stepMir (prog : Program) (st : MirState) : MirStep :=
  match listGet? prog.fns st.cur.fnId with
  | none => .halted (.invalid st.trace)
  | some fn =>
    match fn.isForeign with
    | true => .halted (.invalid st.trace)
    | false =>
      match listGet? fn.blocks st.cur.bb with
      | none => .halted (.invalid st.trace)
      | some blk =>
        match boolEq st.cur.inCleanup blk.isCleanup with
        | false => .halted (.invalid st.trace)
        | true =>
          match listGet? blk.stmts st.cur.stmtIdx with
          | some stmt => execStmt st stmt
          | none =>
            match natEq st.cur.stmtIdx (listLen blk.stmts) with
            | true => execTerm prog st blk.term
            | false => .halted (.invalid st.trace)

/-- Fuel-bounded MIR execution. -/
noncomputable def runMir (prog : Program) : Nat → MirState → MirExecResult
  | 0, st => .outOfFuel st
  | n + 1, st =>
    match stepMir prog st with
    | .running st' => runMir prog n st'
    | .halted res => res

/-- Run a `Program` from its entry point with argument `arg` for `fuel` steps. -/
noncomputable def evalMirProg (prog : Program) (fuel arg : Nat) : MirExecResult :=
  match initMirState prog arg with
  | none => .invalid []
  | some st => runMir prog fuel st

/-! ## Section 5: `AbortUnwindingCalls` MIR Pass and Dead Cleanup Erasure -/

/-- Exact terminator transformation in `AbortUnwindingCalls::run_pass`
(`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:78-135`):
- `UnwindResume` -> `Unreachable` if `!targetSupportsUnwinding`, else `UnwindTerminate .abi` if `!bodyUnw`.
- For non-cleanup blocks (`bbCleanup = false`) with unwind-bearing terminators (`call`, `drop`, `panicCall`):
  - if `!callUnw || !targetSupportsUnwinding`, set `unwind := .unreachable`
  - else if `!bodyUnw` and `unwind == .continue_`, set `unwind := .terminate .abi`
  - else preserve `unwind` (e.g. `Cleanup(bb)` still runs cleanup, then `bb`'s `UnwindResume` hits `UnwindTerminate .abi`). -/
noncomputable def abortUnwindingUnwindAction (prog : Program) (bodyUnw callUnw : Bool)
    (u : UnwindAction) : UnwindAction :=
  match bor (bnot callUnw) (bnot prog.targetSupportsUnwinding) with
  | true => .unreachable
  | false =>
    match bnot bodyUnw, u with
    | true, .continue_ => .terminate .abi
    | _, _ => u

noncomputable def abortUnwindingTerm (prog : Program) (bodyUnw bbCleanup : Bool)
    (t : Terminator) : Terminator :=
  match t with
  | .unwindResume =>
    match bnot prog.targetSupportsUnwinding with
    | true => .unreachable
    | false =>
      match bnot bodyUnw with
      | true => .unwindTerminate .abi
      | false => .unwindResume
  | .call callee arg dst rt u =>
    match bbCleanup with
    | true => .call callee arg dst rt u
    | false =>
      let cu := calleeCanUnwind prog callee
      .call callee arg dst rt (abortUnwindingUnwindAction prog bodyUnw cu u)
  | .drop dropFn arg rt u =>
    match bbCleanup with
    | true => .drop dropFn arg rt u
    | false =>
      let du := dropCanUnwind prog dropFn
      .drop dropFn arg rt (abortUnwindingUnwindAction prog bodyUnw du u)
  | .panicCall u =>
    match bbCleanup with
    | true => .panicCall u
    | false =>
      let pu := fnCanUnwind prog.strategy false false .rust
      .panicCall (abortUnwindingUnwindAction prog bodyUnw pu u)
  | other => other

/-- Apply `AbortUnwindingCalls` to a single basic block. -/
noncomputable def abortUnwindingBlock (prog : Program) (bodyUnw : Bool)
    (blk : BasicBlock) : BasicBlock :=
  { blk with term := abortUnwindingTerm prog bodyUnw blk.isCleanup blk.term }

/-- Apply `AbortUnwindingCalls` to a single function body (leaving foreign items unchanged). -/
noncomputable def abortUnwindingFn (prog : Program) (fn : FnBody) : FnBody :=
  match fn.isForeign with
  | true => fn
  | false =>
    let bu := bodyCanUnwind prog.strategy fn
    { fn with blocks := listMap (abortUnwindingBlock prog bu) fn.blocks }

/-- Apply `AbortUnwindingCalls` to all functions in `prog`. -/
noncomputable def abortUnwindingCallsProg (prog : Program) : Program :=
  { prog with fns := listMap (abortUnwindingFn prog) prog.fns }

/-- Direct CFG edge relation in a MIR function body (combining normal successors and `Cleanup(bb)` unwind targets). -/
inductive CfgEdge (blocks : List BasicBlock) : BlockId → BlockId → Prop where
  | normal {src dst : BlockId} {blk : BasicBlock} :
      listGet? blocks src = some blk →
      natListMem dst (normalSuccs blk.term) = true →
      CfgEdge blocks src dst
  | unwindCleanup {src dst : BlockId} {blk : BasicBlock} {u : UnwindAction} :
      listGet? blocks src = some blk →
      termUnwind? blk.term = some u →
      u = .cleanup dst →
      CfgEdge blocks src dst

/-- Inductive CFG reachability from block `0` (`START_BLOCK`). -/
inductive ReachableBB (blocks : List BasicBlock) : BlockId → Prop where
  | entry : ReachableBB blocks 0
  | step {u v : BlockId} : ReachableBB blocks u → CfgEdge blocks u v → ReachableBB blocks v

/-- Predicate expressing that no block in `fn` calls an unwinding foreign item
or an unwinding local item when `strat = .abort`. -/
noncomputable def NoUnwindingForeignCallsInFn (prog : Program) (fn : FnBody) : Prop :=
  listForall (fun blk =>
    match blk.term with
    | .call callee _ _ _ _ => calleeCanUnwind prog callee = false
    | .drop dropFn _ _ _ => dropCanUnwind prog dropFn = false
    | .panicCall _ => fnCanUnwind prog.strategy false false .rust = false
    | _ => True) fn.blocks

/-- Program-wide absence of calls that can unwind under `prog.strategy` (e.g. `-Cpanic=abort`
without foreign `extern "C-unwind"` callees). -/
noncomputable def NoUnwindingCalls (prog : Program) : Prop :=
  listForall (NoUnwindingForeignCallsInFn prog) prog.fns

/-- Replace unreachable cleanup blocks by `{ stmts := [], term := .unreachable, isCleanup := true }`
or erase cleanup blocks from a non-unwinding `-Cpanic=abort` CFG. Here we model exact
dead cleanup block removal (`eraseDeadCleanupBlocks`) where unreachable cleanup blocks are
stripped and non-cleanup block indices remain compactly preserved if cleanup blocks were placed
after normal blocks, OR more generally we remap every normal block id via `remapId`. -/
noncomputable def countNonCleanupBefore : List BasicBlock → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | blk :: rest, n + 1 =>
    let cur := match blk.isCleanup with | false => 1 | true => 0
    cur + countNonCleanupBefore rest n

noncomputable def remapNormalTerm (blocks : List BasicBlock) : Terminator → Terminator
  | .goto t => .goto (countNonCleanupBefore blocks t)
  | .branch c z nz =>
    .branch c (countNonCleanupBefore blocks z) (countNonCleanupBefore blocks nz)
  | .call callee arg dst rt _ =>
    .call callee arg dst (countNonCleanupBefore blocks rt) .unreachable
  | .drop df arg rt _ =>
    .drop df arg (countNonCleanupBefore blocks rt) .unreachable
  | .panicCall _ => .panicCall .unreachable
  | .return_ r => .return_ r
  | .unreachable => .unreachable
  | .unwindResume => .unreachable
  | .unwindTerminate _ => .unreachable

noncomputable def filterAndRemapNormalBlocks (allBlocks : List BasicBlock) :
    List BasicBlock → List BasicBlock
  | [] => []
  | blk :: rest =>
    match blk.isCleanup with
    | true => filterAndRemapNormalBlocks allBlocks rest
    | false =>
      { blk with term := remapNormalTerm allBlocks blk.term } ::
        filterAndRemapNormalBlocks allBlocks rest

/-- Dead cleanup block erasure (`simplify::remove_dead_blocks` specialized to removing
unreachable `isCleanup = true` blocks under `-Cpanic=abort`). -/
noncomputable def eraseDeadCleanupFn (fn : FnBody) : FnBody :=
  match fn.isForeign with
  | true => fn
  | false => { fn with blocks := filterAndRemapNormalBlocks fn.blocks fn.blocks }

noncomputable def eraseDeadCleanupProg (prog : Program) : Program :=
  { prog with fns := listMap eraseDeadCleanupFn prog.fns }

/-! ## Section 6: LLVM `call` vs `invoke`, `nounwind`, and `terminate` Lowering -/

/-- LLVM landingpad clause kind emitted by `rustc_codegen_ssa` (`mir/block.rs`). -/
inductive LlvmPad where
  | cleanupPad (mirBB : BlockId)
  | filterTerminatePad (reason : UnwindTerminateReason)

/-- LLVM lowered block terminator (`call` vs `invoke`, `landingpad`, `resume`). -/
inductive LlvmTerm where
  | br (target : BlockId)
  | condBr (cond : LocalId) (z nz : BlockId)
  | ret (valReg : LocalId)
  | unreachable
  | resume
  | terminateDirect (reason : UnwindTerminateReason)
  | callPlain (callee : FnId) (isDrop : Bool) (arg dst : LocalId) (retTarget : BlockId) (ubOnUnwind : Bool)
  | invoke (callee : FnId) (isDrop : Bool) (arg dst : LocalId) (retTarget : BlockId) (pad : LlvmPad)
  | panicPlain (ubOnUnwind : Bool)
  | panicInvoke (pad : LlvmPad)
  | panicAbort

/-- Lowered LLVM basic block. -/
structure LlvmBlock where
  stmts : List Stmt
  term : LlvmTerm
  isCleanup : Bool

/-- Lowered LLVM function carrying `AttributeKind::NoUnwind` (`nounwind`). -/
structure LlvmFn where
  hasNoUnwind : Bool
  isForeign : Bool
  localCount : Nat
  blocks : List LlvmBlock

/-- Lowered LLVM module. -/
structure LlvmProg where
  strategy : PanicStrategy
  entryFn : FnId
  fns : List LlvmFn
  foreignSpecs : FnId → Nat → ForeignOutcome

/-- Lower a MIR call/drop terminator to LLVM `call` vs `invoke` (`block.rs:221-250`). -/
noncomputable def llvmLowerCallTerm (callUnw : Bool) (callee : FnId) (isDrop : Bool)
    (arg dst : LocalId) (rt : BlockId) (u : UnwindAction) : LlvmTerm :=
  let uEff : UnwindAction := match callUnw with | false => .unreachable | true => u
  match uEff with
  | .cleanup c => .invoke callee isDrop arg dst rt (.cleanupPad c)
  | .terminate r => .invoke callee isDrop arg dst rt (.filterTerminatePad r)
  | .continue_ => .callPlain callee isDrop arg dst rt false
  | .unreachable => .callPlain callee isDrop arg dst rt true

/-- Lower a MIR panic terminator to LLVM `call` vs `invoke` vs `panic_abort`. -/
noncomputable def llvmLowerPanicTerm (panicUnw : Bool) (u : UnwindAction) : LlvmTerm :=
  match panicUnw with
  | false => .panicAbort
  | true =>
    match u with
    | .cleanup c => .panicInvoke (.cleanupPad c)
    | .terminate r => .panicInvoke (.filterTerminatePad r)
    | .continue_ => .panicPlain false
    | .unreachable => .panicPlain true

/-- Lower any MIR terminator to LLVM IR. -/
noncomputable def llvmLowerTerm (prog : Program) : Terminator → LlvmTerm
  | .goto t => .br t
  | .branch c z nz => .condBr c z nz
  | .return_ r => .ret r
  | .unreachable => .unreachable
  | .unwindResume => .resume
  | .unwindTerminate r => .terminateDirect r
  | .call callee arg dst rt u =>
    llvmLowerCallTerm (calleeCanUnwind prog callee) callee false arg dst rt u
  | .drop df arg rt u =>
    llvmLowerCallTerm (dropCanUnwind prog df) df true arg 0 rt u
  | .panicCall u =>
    llvmLowerPanicTerm (band (fnCanUnwind prog.strategy false false .rust) prog.targetSupportsUnwinding) u

noncomputable def llvmLowerBlock (prog : Program) (blk : BasicBlock) : LlvmBlock :=
  { stmts := blk.stmts, term := llvmLowerTerm prog blk.term, isCleanup := blk.isCleanup }

/-- Lower a MIR `FnBody` to an `LlvmFn`, attaching `NoUnwind := !bodyCanUnwind`
(`compiler/rustc_codegen_llvm/src/abi.rs:apply_attrs_llfn`). -/
noncomputable def llvmLowerFn (prog : Program) (fn : FnBody) : LlvmFn :=
  {
    hasNoUnwind := bnot (bodyCanUnwind prog.strategy fn)
    isForeign := fn.isForeign
    localCount := fn.localCount
    blocks := listMap (llvmLowerBlock prog) fn.blocks
  }

noncomputable def llvmLowerProg (prog : Program) : LlvmProg :=
  {
    strategy := prog.strategy
    entryFn := prog.entryFn
    fns := listMap (llvmLowerFn prog) prog.fns
    foreignSpecs := prog.foreignSpecs
  }

/-- LLVM execution stack continuation tracking both caller's `hasNoUnwind` and `callPlain`/`invoke` handler. -/
inductive LlvmUnwindHandler where
  | pad (p : LlvmPad)
  | propagate (ubOnUnwind : Bool)

structure LlvmCallerCont where
  fnId : FnId
  hasNoUnwind : Bool
  locals : List Nat
  inCleanup : Bool
  retDst : LocalId
  retTarget : BlockId
  handler : LlvmUnwindHandler

structure LlvmActiveFrame where
  fnId : FnId
  hasNoUnwind : Bool
  bb : BlockId
  stmtIdx : Nat
  locals : List Nat
  inCleanup : Bool

structure LlvmState where
  cur : LlvmActiveFrame
  stack : List LlvmCallerCont
  cleanupDepth : Nat
  trace : List TraceEvent

inductive LlvmExecResult where
  | returned (val : Nat) (trace : List TraceEvent)
  | unwound (trace : List TraceEvent)
  | terminated (reason : UnwindTerminateReason) (trace : List TraceEvent)
  | aborted (trace : List TraceEvent)
  | ub (trace : List TraceEvent)
  | invalid (trace : List TraceEvent)
  | outOfFuel (st : LlvmState)

inductive LlvmStep where
  | running (st : LlvmState)
  | halted (res : LlvmExecResult)

noncomputable def initLlvmState (lprog : LlvmProg) (arg : Nat) : Option LlvmState :=
  match listGet? lprog.fns lprog.entryFn with
  | none => none
  | some fn =>
    some {
      cur := {
        fnId := lprog.entryFn
        hasNoUnwind := fn.hasNoUnwind
        bb := 0
        stmtIdx := 0
        locals := initLocals fn.localCount arg
        inCleanup := false
      }
      stack := []
      cleanupDepth := 0
      trace := []
    }

noncomputable def execLlvmStmt (st : LlvmState) : Stmt → LlvmStep
  | .nop =>
    .running { st with cur := { st.cur with stmtIdx := st.cur.stmtIdx + 1 } }
  | .emit ev =>
    .running {
      st with
      cur := { st.cur with stmtIdx := st.cur.stmtIdx + 1 }
      trace := st.trace ++ [ev]
    }
  | .assignConst dst val =>
    .running {
      st with
      cur := {
        st.cur with
        stmtIdx := st.cur.stmtIdx + 1
        locals := writeLocal st.cur.locals dst val
      }
    }
  | .assignLocal dst src =>
    match readLocal? st.cur.locals src with
    | none => .halted (.invalid st.trace)
    | some v =>
      .running {
        st with
        cur := {
          st.cur with
          stmtIdx := st.cur.stmtIdx + 1
          locals := writeLocal st.cur.locals dst v
        }
      }

/-- Dispatch an exception through an LLVM `invoke` landingpad or `call` unwind edge.
Crucially enforces LLVM LangRef `nounwind` UB:
- Any unwind attempting to exit a function with `hasNoUnwind = true` (`nounwind`) triggers `.ub`!
- Any unwind hitting a `call` with `ubOnUnwind = true` (`UnwindAction::Unreachable`) triggers `.ub`!
- An `invoke` to `.filterTerminatePad r` enters the filter landingpad and calls `panic_cannot_unwind`/`panic_in_cleanup`, deterministically yielding `.terminated r`. -/
noncomputable def enterLlvmPad (fns : List LlvmFn) (cur : LlvmActiveFrame)
    (stack : List LlvmCallerCont) (pad : LlvmPad) (depth : Nat)
    (trace : List TraceEvent) : LlvmStep :=
  match pad with
  | .filterTerminatePad reason => .halted (.terminated reason trace)
  | .cleanupPad c =>
    match listGet? fns cur.fnId with
    | none => .halted (.invalid trace)
    | some fn =>
      match listGet? fn.blocks c with
      | none => .halted (.invalid trace)
      | some blk =>
        match blk.isCleanup with
        | false => .halted (.invalid trace)
        | true =>
          .running {
            cur := { cur with bb := c, stmtIdx := 0, inCleanup := true }
            stack := stack
            cleanupDepth := depth + 1
            trace := trace
          }

noncomputable def propagateLlvmUnwind (fns : List LlvmFn) (curNoUnwind : Bool)
    (stack : List LlvmCallerCont) (depth : Nat) (trace : List TraceEvent) : LlvmStep :=
  match curNoUnwind with
  | true => .halted (.ub trace)
  | false =>
    match stack with
    | [] => .halted (.unwound trace)
    | c :: rest =>
      let callerFrame : LlvmActiveFrame := {
        fnId := c.fnId
        hasNoUnwind := c.hasNoUnwind
        bb := c.retTarget
        stmtIdx := 0
        locals := c.locals
        inCleanup := c.inCleanup
      }
      match c.handler with
      | .pad p => enterLlvmPad fns callerFrame rest p depth trace
      | .propagate true => .halted (.ub trace)
      | .propagate false => propagateLlvmUnwind fns c.hasNoUnwind rest depth trace

noncomputable def enterLlvmCall (lprog : LlvmProg) (st : LlvmState) (callee : FnId)
    (argVal : Nat) (dst : LocalId) (rt : BlockId) (h : LlvmUnwindHandler) : LlvmStep :=
  match listGet? lprog.fns callee with
  | none => .halted (.invalid st.trace)
  | some cfn =>
    match cfn.isForeign with
    | true =>
      match lprog.foreignSpecs callee argVal with
      | .ret v evOpt =>
        let tr' := appendOptEvent st.trace evOpt
        .running {
          st with
          cur := { st.cur with bb := rt, stmtIdx := 0, locals := writeLocal st.cur.locals dst v }
          trace := tr'
        }
      | .unwound evOpt =>
        let tr' := appendOptEvent st.trace evOpt
        match cfn.hasNoUnwind with
        | true => .halted (.ub tr')
        | false =>
          match h with
          | .pad p => enterLlvmPad lprog.fns st.cur st.stack p st.cleanupDepth tr'
          | .propagate true => .halted (.ub tr')
          | .propagate false => propagateLlvmUnwind lprog.fns st.cur.hasNoUnwind st.stack st.cleanupDepth tr'
    | false =>
      let cont : LlvmCallerCont := {
        fnId := st.cur.fnId
        hasNoUnwind := st.cur.hasNoUnwind
        locals := st.cur.locals
        inCleanup := st.cur.inCleanup
        retDst := dst
        retTarget := rt
        handler := h
      }
      let nextFrame : LlvmActiveFrame := {
        fnId := callee
        hasNoUnwind := cfn.hasNoUnwind
        bb := 0
        stmtIdx := 0
        locals := initLocals cfn.localCount argVal
        inCleanup := false
      }
      .running {
        cur := nextFrame
        stack := cont :: st.stack
        cleanupDepth := st.cleanupDepth
        trace := st.trace
      }

noncomputable def execLlvmTerm (lprog : LlvmProg) (st : LlvmState) : LlvmTerm → LlvmStep
  | .br t =>
    .running { st with cur := { st.cur with bb := t, stmtIdx := 0 } }
  | .condBr cond z nz =>
    match readLocal? st.cur.locals cond with
    | none => .halted (.invalid st.trace)
    | some v =>
      let target := match v with | 0 => z | _ => nz
      .running { st with cur := { st.cur with bb := target, stmtIdx := 0 } }
  | .ret valReg =>
    match st.cur.inCleanup with
    | true => .halted (.invalid st.trace)
    | false =>
      match readLocal? st.cur.locals valReg with
      | none => .halted (.invalid st.trace)
      | some v =>
        match st.stack with
        | [] => .halted (.returned v st.trace)
        | c :: rest =>
          .running {
            cur := {
              fnId := c.fnId
              hasNoUnwind := c.hasNoUnwind
              bb := c.retTarget
              stmtIdx := 0
              locals := writeLocal c.locals c.retDst v
              inCleanup := c.inCleanup
            }
            stack := rest
            cleanupDepth := st.cleanupDepth
            trace := st.trace
          }
  | .unreachable =>
    .halted (.ub st.trace)
  | .terminateDirect reason =>
    .halted (.terminated reason st.trace)
  | .resume =>
    match st.cur.inCleanup with
    | false => .halted (.invalid st.trace)
    | true =>
      let depth' := match st.cleanupDepth with | 0 => 0 | d + 1 => d
      propagateLlvmUnwind lprog.fns st.cur.hasNoUnwind st.stack depth' st.trace
  | .callPlain callee isDrop argReg dst rt ubFlag =>
    match readLocal? st.cur.locals argReg with
    | none => .halted (.invalid st.trace)
    | some argVal =>
      let dst' := match isDrop with | true => 0 | false => dst
      enterLlvmCall lprog st callee argVal dst' rt (.propagate ubFlag)
  | .invoke callee isDrop argReg dst rt pad =>
    match readLocal? st.cur.locals argReg with
    | none => .halted (.invalid st.trace)
    | some argVal =>
      let dst' := match isDrop with | true => 0 | false => dst
      enterLlvmCall lprog st callee argVal dst' rt (.pad pad)
  | .panicPlain ubFlag =>
    match ubFlag with
    | true => .halted (.ub st.trace)
    | false => propagateLlvmUnwind lprog.fns st.cur.hasNoUnwind st.stack st.cleanupDepth st.trace
  | .panicInvoke pad =>
    enterLlvmPad lprog.fns st.cur st.stack pad st.cleanupDepth st.trace
  | .panicAbort =>
    .halted (.aborted st.trace)

noncomputable def stepLlvm (lprog : LlvmProg) (st : LlvmState) : LlvmStep :=
  match listGet? lprog.fns st.cur.fnId with
  | none => .halted (.invalid st.trace)
  | some fn =>
    match fn.isForeign with
    | true => .halted (.invalid st.trace)
    | false =>
      match listGet? fn.blocks st.cur.bb with
      | none => .halted (.invalid st.trace)
      | some blk =>
        match boolEq st.cur.inCleanup blk.isCleanup with
        | false => .halted (.invalid st.trace)
        | true =>
          match listGet? blk.stmts st.cur.stmtIdx with
          | some stmt => execLlvmStmt st stmt
          | none =>
            match natEq st.cur.stmtIdx (listLen blk.stmts) with
            | true => execLlvmTerm lprog st blk.term
            | false => .halted (.invalid st.trace)

noncomputable def runLlvm (lprog : LlvmProg) : Nat → LlvmState → LlvmExecResult
  | 0, st => .outOfFuel st
  | n + 1, st =>
    match stepLlvm lprog st with
    | .running st' => runLlvm lprog n st'
    | .halted res => res

noncomputable def evalLlvmProg (lprog : LlvmProg) (fuel arg : Nat) : LlvmExecResult :=
  match initLlvmState lprog arg with
  | none => .invalid []
  | some st => runLlvm lprog fuel st

/-! ## Section 7: Runtime State Invariants & Soundness Lemmas -/

/-- Well-formedness of an active MIR frame relative to `prog`. -/
noncomputable def ActiveFrameWF (prog : Program) (f : ActiveFrame) : Prop :=
  ∃ fn blk,
    listGet? prog.fns f.fnId = some fn ∧
    fn.isForeign = false ∧
    listGet? fn.blocks f.bb = some blk ∧
    f.inCleanup = blk.isCleanup ∧
    natLe f.stmtIdx (listLen blk.stmts) = true ∧
    listLen f.locals = fn.localCount

/-- Well-formedness of a saved caller continuation frame. -/
noncomputable def CallerContWF (prog : Program) (c : CallerCont) : Prop :=
  ∃ fn rblk,
    listGet? prog.fns c.fnId = some fn ∧
    fn.isForeign = false ∧
    listGet? fn.blocks c.retTarget = some rblk ∧
    c.inCleanup = rblk.isCleanup ∧
    natLt c.retDst fn.localCount = true ∧
    listLen c.locals = fn.localCount ∧
    PrePassUnwindEdgeWF fn.blocks c.inCleanup c.unwindOnCall

/-- Strong post-pass invariant on caller continuations linking callee's `bodyCanUnwind`
to `c.unwindOnCall`:
whenever `CallerContPostWF prog calleeBodyUnw c` holds:
- if `calleeBodyUnw = false` (non-unwinding callee!), `c.unwindOnCall = .unreachable`
  (because `AbortUnwindingCalls` proved the callee cannot unwind!).
- if `bodyCanUnwind prog.strategy callerFn = false`, `c.unwindOnCall ≠ .continue_`.
- if `c.inCleanup = true`, `c.unwindOnCall = .terminate .inCleanup ∨ c.unwindOnCall = .unreachable`. -/
noncomputable def CallerContPostWF (prog : Program) (calleeUnw : Bool) (c : CallerCont) : Prop :=
  ∃ fn rblk,
    listGet? prog.fns c.fnId = some fn ∧
    fn.isForeign = false ∧
    listGet? fn.blocks c.retTarget = some rblk ∧
    c.inCleanup = rblk.isCleanup ∧
    natLt c.retDst fn.localCount = true ∧
    listLen c.locals = fn.localCount ∧
    PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn) calleeUnw
      fn.blocks c.inCleanup c.unwindOnCall ∧
    (c.inCleanup = true → c.unwindOnCall = .terminate .inCleanup)

/-- Well-formedness of an entire caller continuation stack where each frame tracks
whether its immediate callee could unwind. -/
noncomputable def StackPostWF (prog : Program) : Bool → List CallerCont → Prop
  | _, [] => True
  | calleeUnw, c :: rest =>
    ∃ fn,
      listGet? prog.fns c.fnId = some fn ∧
      CallerContPostWF prog calleeUnw c ∧
      StackPostWF prog (bodyCanUnwind prog.strategy fn) rest

/-- Full runtime invariant on `MirState` for a post-`AbortUnwindingCalls` program. -/
noncomputable def MirStatePostWF (prog : Program) (st : MirState) : Prop :=
  ∃ fn,
    listGet? prog.fns st.cur.fnId = some fn ∧
    ActiveFrameWF prog st.cur ∧
    StackPostWF prog (bodyCanUnwind prog.strategy fn) st.stack ∧
    (st.cur.inCleanup = true → st.cleanupDepth ≥ 1)

/-- Predicates classifying bad outcomes ruled out by our theorems. -/
noncomputable def mirIsBad : MirExecResult → Prop
  | .ub _ => True
  | .invalid _ => True
  | _ => False

noncomputable def llvmIsBad : LlvmExecResult → Prop
  | .ub _ => True
  | .invalid _ => True
  | _ => False

theorem natLt_succ_le (a b : Nat) (h : natLt a b = true) : natLe a b = true := by
  induction a generalizing b with
  | zero => rfl
  | succ a' ih =>
    cases b with
    | zero => contradiction
    | succ b' => exact ih b' h

theorem natLe_refl (n : Nat) : natLe n n = true := by
  induction n with
  | zero => rfl
  | succ n' ih => exact ih

theorem natLe_succ_of_lt (a b : Nat) (h : natLt a b = true) : natLe (a + 1) b = true := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => contradiction
    | succ b' => rfl
  | succ a' ih =>
    cases b with
    | zero => contradiction
    | succ b' => exact ih b' h

theorem natLe_eq_false_lt (a b : Nat) (hle : natLe a b = true) (hne : natEq a b = false) :
    natLt a b = true := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => contradiction
    | succ b' => rfl
  | succ a' ih =>
    cases b with
    | zero => contradiction
    | succ b' => exact ih b' hle hne

theorem listLen_listSet {α : Type} (xs : List α) (i : Nat) (v : α) :
    listLen (listSet xs i v) = listLen xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      show listLen (x :: listSet xs i' v) = listLen (x :: xs)
      show listLen (listSet xs i' v) + 1 = listLen xs + 1
      rw [ih i']

theorem listLen_initLocalsAux (n k arg : Nat) : listLen (initLocalsAux n k arg) = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n' ih =>
    show listLen (_ :: initLocalsAux n' (k + 1) arg) = n' + 1
    show listLen (initLocalsAux n' (k + 1) arg) + 1 = n' + 1
    rw [ih (k + 1)]

theorem listLen_initLocals (n arg : Nat) : listLen (initLocals n arg) = n :=
  listLen_initLocalsAux n 0 arg

theorem listGet?_lt_len {α : Type} (xs : List α) (i : Nat) (h : natLt i (listLen xs) = true) :
    ∃ x, listGet? xs i = some x := by
  induction xs generalizing i with
  | nil =>
    cases i <;> contradiction
  | cons x xs ih =>
    cases i with
    | zero => exact ⟨x, rfl⟩
    | succ i' =>
      have h' : natLt i' (listLen xs) = true := h
      exact ih i' h'

theorem listGet?_ge_len_none {α : Type} (xs : List α) (i : Nat) (h : natLe (listLen xs) i = true) :
    listGet? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      change natLe (listLen xs + 1) 0 = true at h
      contradiction
    | succ i' => exact ih i' h

theorem listLen_listMap {α β : Type} (f : α → β) (xs : List α) :
    listLen (listMap f xs) = listLen xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show listLen (f x :: listMap f xs) = listLen (x :: xs)
    show listLen (listMap f xs) + 1 = listLen xs + 1
    rw [ih]

theorem natEq_false_of_lt {a b : Nat} (h : natLt a b = true) : natEq a b = false := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => contradiction
    | succ _ => rfl
  | succ a' ih =>
    cases b with
    | zero => contradiction
    | succ b' => exact ih h

theorem listGet?_eq_none_implies_ge {α : Type} (xs : List α) (i : Nat)
    (hnone : listGet? xs i = none) (hle : natLe i (listLen xs) = true) : i = listLen xs := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ i' => contradiction
  | cons x xs ih =>
    cases i with
    | zero => contradiction
    | succ i' =>
      have h' := ih i' hnone hle
      exact congrArg Nat.succ h'

theorem abortUnwindingCalls_preserves_bodyCanUnwind (prog : Program) (fn : FnBody) :
    bodyCanUnwind prog.strategy (abortUnwindingFn prog fn) = bodyCanUnwind prog.strategy fn := by
  unfold abortUnwindingFn
  cases hf : fn.isForeign
  · simp only [bodyCanUnwind, fnCanUnwind, hf]
  · rfl

theorem calleeCanUnwind_abortUnwindingProg (prog : Program) (callee : FnId) :
    calleeCanUnwind (abortUnwindingCallsProg prog) callee = calleeCanUnwind prog callee := by
  unfold calleeCanUnwind abortUnwindingCallsProg
  rw [listGet?_listMap]
  cases hget : listGet? prog.fns callee with
  | none => rfl
  | some fn =>
    exact abortUnwindingCalls_preserves_bodyCanUnwind prog fn

theorem dropCanUnwind_abortUnwindingProg (prog : Program) (dropFn : FnId) :
    dropCanUnwind (abortUnwindingCallsProg prog) dropFn = dropCanUnwind prog dropFn := by
  unfold dropCanUnwind abortUnwindingCallsProg
  rw [listGet?_listMap]
  cases hget : listGet? prog.fns dropFn with
  | none => rfl
  | some fn =>
    unfold abortUnwindingFn
    cases hf : fn.isForeign
    · simp only [bodyCanUnwind, fnCanUnwind, hf]
    · simp only [bodyCanUnwind, fnCanUnwind, hf]

theorem abortUnwindingFn_blocks_nonForeign (prog : Program) (fn : FnBody) (hnonF : fn.isForeign = false) :
    (abortUnwindingFn prog fn).blocks =
      listMap (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn)) fn.blocks := by
  unfold abortUnwindingFn
  rw [hnonF]

theorem prePassUnwindEdgeWF_cleanup_map (prog : Program) (fn : FnBody) (hnonF : fn.isForeign = false)
    (target : BlockId) (hpre : PrePassUnwindEdgeWF fn.blocks false (.cleanup target)) :
    PrePassUnwindEdgeWF (abortUnwindingFn prog fn).blocks false (.cleanup target) := by
  obtain ⟨_, blk, hget, hblkC⟩ := hpre
  refine ⟨rfl, abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) blk, ?_, ?_⟩
  · rw [abortUnwindingFn_blocks_nonForeign prog fn hnonF, listGet?_listMap, hget]
  · exact hblkC

/-! ## Section 8: `AbortUnwindingCalls` Preserves Well-Formedness (`MirPostPassWF`) -/

theorem bor_true_right (b : Bool) : bor b true = true := by
  cases b <;> rfl

theorem abortUnwindingUnwindAction_wf_nonCleanup (prog : Program) (fn : FnBody)
    (hnonF : fn.isForeign = false) (callUnw : Bool) (u : UnwindAction)
    (hpre : PrePassUnwindEdgeWF fn.blocks false u) :
    PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn) callUnw
      (abortUnwindingFn prog fn).blocks false
      (abortUnwindingUnwindAction prog (bodyCanUnwind prog.strategy fn) callUnw u) := by
  unfold PostPassUnwindEdgeWF abortUnwindingUnwindAction
  cases hts : prog.targetSupportsUnwinding
  · simp only [bnot, bor_true_right]
    refine ⟨trivial, (fun _ _ => trivial), (fun _ hc => by cases hc)⟩
  · cases hcu : callUnw
    · simp only [bnot, bor]
      refine ⟨trivial, (fun _ _ => trivial), (fun _ hc => by cases hc)⟩
    · simp only [bnot, bor]
      cases hbu : bodyCanUnwind prog.strategy fn
      · cases u with
        | continue_ =>
          refine ⟨rfl, (fun _ hbad => by cases hbad <;> contradiction), (fun _ hc => by cases hc)⟩
        | unreachable =>
          refine ⟨trivial, (fun _ hbad => by cases hbad <;> contradiction), (fun _ hc => by cases hc)⟩
        | terminate r =>
          cases r with
          | abi =>
            refine ⟨rfl, (fun _ hbad => by cases hbad <;> contradiction), (fun _ hc => by cases hc)⟩
          | inCleanup => contradiction
        | cleanup target =>
          refine ⟨prePassUnwindEdgeWF_cleanup_map prog fn hnonF target hpre,
            (fun _ hbad => by cases hbad <;> contradiction), (fun _ hc => by cases hc)⟩
      · cases u with
        | continue_ =>
          refine ⟨rfl, (fun _ hbad => by cases hbad <;> contradiction),
            (fun hbad _ => by cases hbad <;> contradiction)⟩
        | unreachable =>
          refine ⟨trivial, (fun _ hbad => by cases hbad <;> contradiction), (fun _ hc => by cases hc)⟩
        | terminate r =>
          cases r with
          | abi =>
            refine ⟨rfl, (fun _ hbad => by cases hbad <;> contradiction), (fun _ hc => by cases hc)⟩
          | inCleanup => contradiction
        | cleanup target =>
          refine ⟨prePassUnwindEdgeWF_cleanup_map prog fn hnonF target hpre,
            (fun _ hbad => by cases hbad <;> contradiction), (fun _ hc => by cases hc)⟩

theorem abortUnwindingUnwindAction_wf_cleanup (prog : Program) (fn : FnBody)
    (callUnw : Bool) (u : UnwindAction)
    (hclean : u = .terminate .inCleanup) :
    PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn) callUnw
      (abortUnwindingFn prog fn).blocks true u := by
  rw [hclean]
  refine ⟨rfl, (fun hbad _ => by contradiction), (fun _ hc => by cases hc)⟩

theorem abortUnwindingFn_preserves_metadata (prog : Program) (fn : FnBody) :
    (abortUnwindingFn prog fn).isForeign = fn.isForeign ∧
    (abortUnwindingFn prog fn).localCount = fn.localCount ∧
    (abortUnwindingFn prog fn).neverUnwind = fn.neverUnwind ∧
    (abortUnwindingFn prog fn).abi = fn.abi := by
  unfold abortUnwindingFn
  cases hf : fn.isForeign
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨hf, rfl, rfl, rfl⟩

theorem abortUnwindingTerm_postWF (prog : Program) (fn : FnBody) (hnonF : fn.isForeign = false)
    (bbCleanup : Bool) (t : Terminator) (hpre : PrePassTermWF prog fn bbCleanup t) :
    PostPassTermWF (abortUnwindingCallsProg prog) (abortUnwindingFn prog fn) bbCleanup
      (abortUnwindingTerm prog (bodyCanUnwind prog.strategy fn) bbCleanup t) := by
  have hblocks := abortUnwindingFn_blocks_nonForeign prog fn hnonF
  have hmeta := abortUnwindingFn_preserves_metadata prog fn
  have hloc : (abortUnwindingFn prog fn).localCount = fn.localCount := hmeta.2.1
  have hbu : bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog fn) =
      bodyCanUnwind prog.strategy fn := abortUnwindingCalls_preserves_bodyCanUnwind prog fn
  cases t with
  | goto target =>
    obtain ⟨blk, hget, hblkC⟩ := hpre
    unfold PostPassTermWF abortUnwindingTerm
    dsimp only
    refine ⟨?_, (fun h => by contradiction), trivial⟩
    refine ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) blk, ?_, hblkC⟩
    rw [hblocks, listGet?_listMap, hget]
  | branch cond z nz =>
    obtain ⟨hcond, ⟨b1, hget1, h1C⟩, ⟨b2, hget2, h2C⟩⟩ := hpre
    unfold PostPassTermWF abortUnwindingTerm
    dsimp only
    refine ⟨?_, (fun h => by contradiction), trivial⟩
    refine ⟨?_, ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) b1, ?_, h1C⟩,
      ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) b2, ?_, h2C⟩⟩
    · rw [hloc]; exact hcond
    · rw [hblocks, listGet?_listMap, hget1]
    · rw [hblocks, listGet?_listMap, hget2]
  | return_ valReg =>
    obtain ⟨hnc, hval⟩ := hpre
    unfold PostPassTermWF abortUnwindingTerm
    dsimp only
    refine ⟨⟨hnc, ?_⟩, (fun h => by contradiction), trivial⟩
    rw [hloc]; exact hval
  | unreachable =>
    unfold PostPassTermWF abortUnwindingTerm
    dsimp only
    exact ⟨trivial, (fun h => by contradiction), trivial⟩
  | unwindTerminate reason =>
    unfold PostPassTermWF abortUnwindingTerm
    dsimp only
    exact ⟨hpre, (fun h => by contradiction), trivial⟩
  | unwindResume =>
    unfold PostPassTermWF abortUnwindingTerm
    dsimp only
    cases hts : prog.targetSupportsUnwinding
    · dsimp only [bnot]
      exact ⟨trivial, (fun h => by contradiction), trivial⟩
    · cases hbody : bodyCanUnwind prog.strategy fn
      · dsimp only [bnot]
        exact ⟨hpre, (fun h => by contradiction), trivial⟩
      · dsimp only [bnot]
        refine ⟨hpre, (fun _ => ⟨hts, ?_⟩), trivial⟩
        rw [hbu, hbody]
  | call callee arg dst rt u =>
    obtain ⟨harg, hdst, ⟨cfn, hcfn⟩, ⟨rblk, hrblk, hrblkC⟩, hu, hclean⟩ := hpre
    unfold PostPassTermWF abortUnwindingTerm
    cases hcbb : bbCleanup
    · rw [hcbb] at hu hrblkC
      dsimp only
      refine ⟨?_, (fun h => by contradiction), ?_⟩
      · refine ⟨?_, ?_, ⟨abortUnwindingFn prog cfn, ?_⟩,
          ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) rblk, ?_, hrblkC⟩, ?_, ?_⟩
        · rw [hloc]; exact harg
        · rw [hloc]; exact hdst
        · unfold abortUnwindingCallsProg; rw [listGet?_listMap, hcfn]
        · rw [hblocks, listGet?_listMap, hrblk]
        · have hw := abortUnwindingUnwindAction_wf_nonCleanup prog fn hnonF (calleeCanUnwind prog callee) u hu
          exact hw.1
        · intro hbad; contradiction
      · show PostPassUnwindEdgeWF (abortUnwindingCallsProg prog).targetSupportsUnwinding
          (bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog fn))
          (calleeCanUnwind (abortUnwindingCallsProg prog) callee)
          (abortUnwindingFn prog fn).blocks false
          (abortUnwindingUnwindAction prog (bodyCanUnwind prog.strategy fn) (calleeCanUnwind prog callee) u)
        rw [hbu, calleeCanUnwind_abortUnwindingProg]
        exact abortUnwindingUnwindAction_wf_nonCleanup prog fn hnonF (calleeCanUnwind prog callee) u hu
    · rw [hcbb] at hrblkC hclean
      dsimp only
      have huc : u = .terminate .inCleanup := hclean rfl
      refine ⟨?_, (fun h => by contradiction), ?_⟩
      · refine ⟨?_, ?_, ⟨abortUnwindingFn prog cfn, ?_⟩,
          ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) rblk, ?_, hrblkC⟩, ?_, (fun _ => huc)⟩
        · rw [hloc]; exact harg
        · rw [hloc]; exact hdst
        · unfold abortUnwindingCallsProg; rw [listGet?_listMap, hcfn]
        · rw [hblocks, listGet?_listMap, hrblk]
        · rw [huc]; exact rfl
      · show PostPassUnwindEdgeWF (abortUnwindingCallsProg prog).targetSupportsUnwinding
          (bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog fn))
          (calleeCanUnwind (abortUnwindingCallsProg prog) callee)
          (abortUnwindingFn prog fn).blocks true u
        rw [hbu, calleeCanUnwind_abortUnwindingProg]
        exact abortUnwindingUnwindAction_wf_cleanup prog fn (calleeCanUnwind prog callee) u huc
  | drop df arg rt u =>
    obtain ⟨harg, ⟨dfn, hdfn, hdfNonF, hdfAbi, hdfPinD⟩, ⟨rblk, hrblk, hrblkC⟩, hu, hclean⟩ := hpre
    have hdfMeta := abortUnwindingFn_preserves_metadata prog dfn
    unfold PostPassTermWF abortUnwindingTerm
    cases hcbb : bbCleanup
    · rw [hcbb] at hu hrblkC
      dsimp only
      refine ⟨?_, (fun h => by contradiction), ?_⟩
      · refine ⟨?_, ⟨abortUnwindingFn prog dfn, ?_, ?_, ?_, ?_⟩,
          ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) rblk, ?_, hrblkC⟩, ?_, ?_⟩
        · rw [hloc]; exact harg
        · unfold abortUnwindingCallsProg; rw [listGet?_listMap, hdfn]
        · rw [hdfMeta.1]; exact hdfNonF
        · rw [hdfMeta.2.2.2]; exact hdfAbi
        · intro hp; rw [hdfMeta.2.2.1]; exact hdfPinD hp
        · rw [hblocks, listGet?_listMap, hrblk]
        · have hw := abortUnwindingUnwindAction_wf_nonCleanup prog fn hnonF (dropCanUnwind prog df) u hu
          exact hw.1
        · intro hbad; contradiction
      · show PostPassUnwindEdgeWF (abortUnwindingCallsProg prog).targetSupportsUnwinding
          (bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog fn))
          (dropCanUnwind (abortUnwindingCallsProg prog) df)
          (abortUnwindingFn prog fn).blocks false
          (abortUnwindingUnwindAction prog (bodyCanUnwind prog.strategy fn) (dropCanUnwind prog df) u)
        rw [hbu, dropCanUnwind_abortUnwindingProg]
        exact abortUnwindingUnwindAction_wf_nonCleanup prog fn hnonF (dropCanUnwind prog df) u hu
    · rw [hcbb] at hrblkC hclean
      dsimp only
      have huc : u = .terminate .inCleanup := hclean rfl
      refine ⟨?_, (fun h => by contradiction), ?_⟩
      · refine ⟨?_, ⟨abortUnwindingFn prog dfn, ?_, ?_, ?_, ?_⟩,
          ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) rblk, ?_, hrblkC⟩, ?_, (fun _ => huc)⟩
        · rw [hloc]; exact harg
        · unfold abortUnwindingCallsProg; rw [listGet?_listMap, hdfn]
        · rw [hdfMeta.1]; exact hdfNonF
        · rw [hdfMeta.2.2.2]; exact hdfAbi
        · intro hp; rw [hdfMeta.2.2.1]; exact hdfPinD hp
        · rw [hblocks, listGet?_listMap, hrblk]
        · rw [huc]; exact rfl
      · show PostPassUnwindEdgeWF (abortUnwindingCallsProg prog).targetSupportsUnwinding
          (bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog fn))
          (dropCanUnwind (abortUnwindingCallsProg prog) df)
          (abortUnwindingFn prog fn).blocks true u
        rw [hbu, dropCanUnwind_abortUnwindingProg]
        exact abortUnwindingUnwindAction_wf_cleanup prog fn (dropCanUnwind prog df) u huc
  | panicCall u =>
    obtain ⟨hu, hclean⟩ := hpre
    unfold PostPassTermWF abortUnwindingTerm
    cases hcbb : bbCleanup
    · rw [hcbb] at hu
      dsimp only
      refine ⟨?_, (fun h => by contradiction), ?_⟩
      · refine ⟨?_, ?_⟩
        · have hw := abortUnwindingUnwindAction_wf_nonCleanup prog fn hnonF
            (fnCanUnwind prog.strategy false false .rust) u hu
          exact hw.1
        · intro hbad; contradiction
      · show PostPassUnwindEdgeWF (abortUnwindingCallsProg prog).targetSupportsUnwinding
          (bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog fn))
          (fnCanUnwind (abortUnwindingCallsProg prog).strategy false false .rust)
          (abortUnwindingFn prog fn).blocks false
          (abortUnwindingUnwindAction prog (bodyCanUnwind prog.strategy fn)
            (fnCanUnwind prog.strategy false false .rust) u)
        rw [hbu]
        exact abortUnwindingUnwindAction_wf_nonCleanup prog fn hnonF
          (fnCanUnwind prog.strategy false false .rust) u hu
    · rw [hcbb] at hclean
      dsimp only
      have huc : u = .terminate .inCleanup := hclean rfl
      refine ⟨?_, (fun h => by contradiction), ?_⟩
      · refine ⟨?_, (fun _ => huc)⟩
        rw [huc]; exact rfl
      · show PostPassUnwindEdgeWF (abortUnwindingCallsProg prog).targetSupportsUnwinding
          (bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog fn))
          (fnCanUnwind (abortUnwindingCallsProg prog).strategy false false .rust)
          (abortUnwindingFn prog fn).blocks true u
        rw [hbu]
        exact abortUnwindingUnwindAction_wf_cleanup prog fn
          (fnCanUnwind prog.strategy false false .rust) u huc

theorem listForall_map_preserved {α β : Type} (f : α → β) (P : α → Prop) (Q : β → Prop)
    (xs : List α) (himpl : ∀ x, P x → Q (f x)) (hall : listForall P xs) :
    listForall Q (listMap f xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨himpl x hall.1, ih hall.2⟩

theorem abortUnwindingCallsProg_postWF (prog : Program) (hpre : MirPrePassWF prog) :
    MirPostPassWF (abortUnwindingCallsProg prog) := by
  obtain ⟨htarg, ⟨entry, hentry, henonF⟩, hfns⟩ := hpre
  refine ⟨htarg, ⟨abortUnwindingFn prog entry, ?_, ?_⟩, ?_⟩
  · unfold abortUnwindingCallsProg; rw [listGet?_listMap, hentry]
  · exact (abortUnwindingFn_preserves_metadata prog entry).1.trans henonF
  · apply listForall_map_preserved (abortUnwindingFn prog) (PrePassFnWF prog)
      (PostPassFnWF (abortUnwindingCallsProg prog)) prog.fns
    · intro fn hfn
      unfold PrePassFnWF at hfn
      unfold PostPassFnWF
      cases hf : fn.isForeign
      · rw [hf] at hfn
        obtain ⟨hle, ⟨b0, hb0, hb0C⟩, hblks⟩ := hfn
        have hm := abortUnwindingFn_preserves_metadata prog fn
        have hblocks := abortUnwindingFn_blocks_nonForeign prog fn hf
        rw [hm.1, hf]
        refine ⟨?_, ⟨abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) b0, ?_, hb0C⟩, ?_⟩
        · rw [hm.2.1]; exact hle
        · rw [hblocks, listGet?_listMap, hb0]
        · rw [hblocks]
          apply listForall_map_preserved (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn))
            (PrePassBlockWF prog fn) (PostPassBlockWF (abortUnwindingCallsProg prog) (abortUnwindingFn prog fn))
            fn.blocks
          · intro blk hblk
            refine ⟨?_, ?_⟩
            · have hloc : (abortUnwindingFn prog fn).localCount = fn.localCount := hm.2.1
              show listForall (StmtWF (abortUnwindingFn prog fn).localCount) blk.stmts
              rw [hloc]
              exact hblk.1
            · exact abortUnwindingTerm_postWF prog fn hf blk.isCleanup blk.term hblk.2
          · exact hblks
      · rw [hf] at hfn
        have hm := abortUnwindingFn_preserves_metadata prog fn
        rw [hm.1, hf]
        unfold abortUnwindingFn; rw [hf]
        exact hfn
    · exact hfns

/-! ## Section 9: Main Theorem 1 — `AbortUnwindingCalls` Exact Soundness -/

theorem listGet?_listForall {α : Type} (P : α → Prop) (xs : List α) (i : Nat) (x : α)
    (hall : listForall P xs) (hget : listGet? xs i = some x) : P x := by
  induction xs generalizing i with
  | nil => cases i <;> contradiction
  | cons y ys ih =>
    cases i with
    | zero =>
      cases hget
      exact hall.1
    | succ i' => exact ih i' hall.2 hget

theorem listForall_conj {α : Type} (P Q : α → Prop) (xs : List α)
    (hp : listForall P xs) (hq : listForall Q xs) : listForall (fun x => P x ∧ Q x) xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨⟨hp.1, hq.1⟩, ih hp.2 hq.2⟩

theorem boolEq_refl (b : Bool) : boolEq b b = true := by
  cases b <;> rfl

theorem natLt_zero_of_le2 (n : Nat) (h : natLe 2 n = true) : natLt 0 n = true := by
  cases n with
  | zero => contradiction
  | succ _ => rfl

theorem stepMir_stmt_eq {prog : Program} {st : MirState} {fn : FnBody} {blk : BasicBlock}
    {stmt : Stmt}
    (hfn : listGet? prog.fns st.cur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hblk : listGet? fn.blocks st.cur.bb = some blk) (hceq : st.cur.inCleanup = blk.isCleanup)
    (hstmt : listGet? blk.stmts st.cur.stmtIdx = some stmt) :
    stepMir prog st = execStmt st stmt := by
  unfold stepMir
  rw [hfn]; dsimp only
  rw [hnonF]; dsimp only
  rw [hblk]; dsimp only
  rw [← hceq, boolEq_refl]; dsimp only
  rw [hstmt]

theorem stepMir_term_eq {prog : Program} {st : MirState} {fn : FnBody} {blk : BasicBlock}
    (hfn : listGet? prog.fns st.cur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hblk : listGet? fn.blocks st.cur.bb = some blk) (hceq : st.cur.inCleanup = blk.isCleanup)
    (hnone : listGet? blk.stmts st.cur.stmtIdx = none) (hlen : st.cur.stmtIdx = listLen blk.stmts) :
    stepMir prog st = execTerm prog st blk.term := by
  unfold stepMir
  rw [hfn]; dsimp only
  rw [hnonF]; dsimp only
  rw [hblk]; dsimp only
  rw [← hceq, boolEq_refl]; dsimp only
  rw [hnone]; dsimp only
  rw [hlen, natEq_refl]

theorem dispatchUnwind_cleanup_eq {fns : List FnBody} {cur : ActiveFrame}
    {stk : List CallerCont} {padBB depth : Nat} {tr : List TraceEvent}
    {fn : FnBody} {pb : BasicBlock}
    (hfn : listGet? fns cur.fnId = some fn) (hpb : listGet? fn.blocks padBB = some pb)
    (hpbc : pb.isCleanup = true) :
    dispatchUnwind fns cur stk (.cleanup padBB) depth tr =
      .running { cur := { cur with bb := padBB, stmtIdx := 0, inCleanup := true },
                 stack := stk, cleanupDepth := depth + 1, trace := tr } := by
  unfold dispatchUnwind
  rw [hfn]; dsimp only
  rw [hpb]; dsimp only
  rw [hpbc]

theorem dispatchUnwind_terminate_eq {fns : List FnBody} {cur : ActiveFrame}
    {stk : List CallerCont} {r : UnwindTerminateReason} {depth : Nat} {tr : List TraceEvent} :
    dispatchUnwind fns cur stk (.terminate r) depth tr = .halted (.terminated r tr) := by
  unfold dispatchUnwind
  rfl

theorem abortUnwindingCalls_preserves_foreignContract (prog : Program)
    (hfok : ForeignContractOK prog) : ForeignContractOK (abortUnwindingCallsProg prog) := by
  intro fid arg
  unfold abortUnwindingCallsProg
  dsimp only
  rw [listGet?_listMap]
  cases hget : listGet? prog.fns fid with
  | none => trivial
  | some fn =>
    dsimp only
    have hf := hfok fid arg
    rw [hget] at hf
    dsimp only at hf
    have hm := abortUnwindingFn_preserves_metadata prog fn
    intro hfor hbu ev
    rw [hm.1] at hfor
    rw [abortUnwindingCalls_preserves_bodyCanUnwind] at hbu
    exact hf hfor hbu ev

/-- Pre-pass premise: MIR does not invent spurious `.unreachable` terminators or spurious
`.unreachable` unwind edges on live unwinding calls/panics, and foreign callees respect
targets that lack runtime unwinding tables (`!targetSupportsUnwinding`). -/
noncomputable def PrePassNoBogusUnreachable (prog : Program) : Prop :=
  (prog.targetSupportsUnwinding = false → ∀ fid arg ev, prog.foreignSpecs fid arg ≠ .unwound ev) ∧
  listForall (fun fn =>
    fn.isForeign = false →
    listForall (fun blk =>
      blk.term ≠ .unreachable ∧
      (termUnwind? blk.term = some .unreachable →
        prog.targetSupportsUnwinding = false ∨ termCallCanUnwind prog blk.term = false))
      fn.blocks)
    prog.fns

/-- Post-pass version of `PrePassNoBogusUnreachable`:
note that if `targetSupportsUnwinding = false`, `AbortUnwindingCalls` converts dead
cleanup `UnwindResume` terminators into `.unreachable`, which remain dead because
non-cleanup blocks never unwind into cleanup blocks when `targetSupportsUnwinding = false`. -/
noncomputable def PostPassNoBogusUnreachable (prog : Program) : Prop :=
  (prog.targetSupportsUnwinding = false → ∀ fid arg ev, prog.foreignSpecs fid arg ≠ .unwound ev) ∧
  listForall (fun fn =>
    fn.isForeign = false →
    listForall (fun blk =>
      (blk.isCleanup = false → blk.term ≠ .unreachable) ∧
      (prog.targetSupportsUnwinding = true → blk.term ≠ .unreachable) ∧
      (termUnwind? blk.term = some .unreachable →
        prog.targetSupportsUnwinding = false ∨ termCallCanUnwind prog blk.term = false))
      fn.blocks)
    prog.fns

theorem abortUnwindingCallsProg_postNoBogus (prog : Program)
    (hpre : MirPrePassWF prog) (hnob : PrePassNoBogusUnreachable prog) :
    PostPassNoBogusUnreachable (abortUnwindingCallsProg prog) := by
  obtain ⟨hfor, hfns⟩ := hnob
  refine ⟨hfor, ?_⟩
  apply listForall_map_preserved (abortUnwindingFn prog)
    (fun fn => PrePassFnWF prog fn ∧ (fn.isForeign = false →
      listForall (fun blk =>
        blk.term ≠ .unreachable ∧
        (termUnwind? blk.term = some .unreachable →
          prog.targetSupportsUnwinding = false ∨ termCallCanUnwind prog blk.term = false))
        fn.blocks))
    _ prog.fns
  · intro fn ⟨hfnWF, hfnNB⟩ hf'
    have hm := abortUnwindingFn_preserves_metadata prog fn
    have hf : fn.isForeign = false := by rw [← hm.1]; exact hf'
    have hblocks := abortUnwindingFn_blocks_nonForeign prog fn hf
    unfold PrePassFnWF at hfnWF
    rw [hf] at hfnWF
    dsimp only at hfnWF
    rw [hblocks]
    apply listForall_map_preserved (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn))
      (fun blk => PrePassBlockWF prog fn blk ∧
        (blk.term ≠ .unreachable ∧
          (termUnwind? blk.term = some .unreachable →
            prog.targetSupportsUnwinding = false ∨ termCallCanUnwind prog blk.term = false)))
      _ fn.blocks
    · intro blk ⟨hblkWF, hblkNoUnreach, hblkEdge⟩
      refine ⟨?_, ?_, ?_⟩
      · intro hnc hbad
        unfold abortUnwindingBlock at hnc hbad
        dsimp only at hnc hbad
        cases ht : blk.term with
        | goto _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | branch _ _ _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | return_ _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | unreachable => exact hblkNoUnreach ht
        | unwindResume =>
          have hpt := hblkWF.2
          rw [ht, hnc] at hpt
          cases hpt
        | unwindTerminate _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | call _ _ _ _ _ =>
          rw [ht] at hbad; unfold abortUnwindingTerm at hbad; rw [hnc] at hbad; cases hbad
        | drop _ _ _ _ =>
          rw [ht] at hbad; unfold abortUnwindingTerm at hbad; rw [hnc] at hbad; cases hbad
        | panicCall _ =>
          rw [ht] at hbad; unfold abortUnwindingTerm at hbad; rw [hnc] at hbad; cases hbad
      · intro hts hbad
        unfold abortUnwindingBlock at hbad
        dsimp only at hbad
        cases ht : blk.term with
        | goto _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | branch _ _ _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | return_ _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | unreachable => exact hblkNoUnreach ht
        | unwindResume =>
          rw [ht] at hbad; unfold abortUnwindingTerm at hbad
          dsimp only [abortUnwindingCallsProg] at hts
          rw [hts] at hbad; dsimp only [bnot] at hbad
          cases hb2 : bodyCanUnwind prog.strategy fn <;> rw [hb2] at hbad <;> cases hbad
        | unwindTerminate _ => rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hbad
        | call _ _ _ _ _ =>
          rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hc2 : blk.isCleanup <;> rw [hc2] at hbad <;> cases hbad
        | drop _ _ _ _ =>
          rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hc2 : blk.isCleanup <;> rw [hc2] at hbad <;> cases hbad
        | panicCall _ =>
          rw [ht] at hbad; unfold abortUnwindingTerm at hbad; cases hc2 : blk.isCleanup <;> rw [hc2] at hbad <;> cases hbad
      · intro hu
        have hpostTerm := abortUnwindingTerm_postWF prog fn hf blk.isCleanup blk.term hblkWF.2
        unfold abortUnwindingBlock at hu
        dsimp only at hu
        cases hcbb : blk.isCleanup with
        | false =>
          have hpreU : termUnwind? blk.term = some .unreachable →
              prog.targetSupportsUnwinding = false ∨ termCallCanUnwind prog blk.term = false := hblkEdge
          cases ht : blk.term with
          | goto _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | branch _ _ _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | return_ _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | unreachable => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | unwindResume =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu
            cases hts : prog.targetSupportsUnwinding with
            | false => exact Or.inl hts
            | true =>
              rw [hts] at hu; dsimp only [bnot] at hu
              cases hb2 : bodyCanUnwind prog.strategy fn <;> rw [hb2] at hu <;> cases hu
          | unwindTerminate _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | call callee arg dst rt u =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu
            rw [hcbb] at hu; dsimp only [termUnwind?] at hu
            injection hu with h0
            cases hts : prog.targetSupportsUnwinding with
            | false => exact Or.inl hts
            | true =>
              cases hcu : calleeCanUnwind prog callee with
              | false =>
                refine Or.inr ?_
                unfold termCallCanUnwind abortUnwindingCallsProg abortUnwindingBlock abortUnwindingTerm calleeCanUnwind
                rw [ht, hcbb]; dsimp only; rw [listGet?_listMap]
                unfold calleeCanUnwind at hcu
                cases hcg : listGet? prog.fns callee with
                | none => rfl
                | some cfn =>
                  dsimp only
                  rw [abortUnwindingCalls_preserves_bodyCanUnwind]
                  rw [hcg] at hcu; exact hcu
              | true =>
                unfold abortUnwindingUnwindAction at h0
                rw [hts, hcu] at h0; dsimp only [bnot, bor] at h0
                cases hb : bodyCanUnwind prog.strategy fn <;> rw [hb] at h0 <;> dsimp only [bnot] at h0
                · cases u with
                  | continue_ => cases h0
                  | terminate _ => cases h0
                  | cleanup _ => cases h0
                  | unreachable =>
                    rw [ht] at hpreU
                    cases hpreU rfl with
                    | inl hf2 => rw [hts] at hf2; cases hf2
                    | inr hc2 => dsimp only [termCallCanUnwind] at hc2; rw [hc2] at hcu; cases hcu
                · cases u with
                  | continue_ => cases h0
                  | terminate _ => cases h0
                  | cleanup _ => cases h0
                  | unreachable =>
                    rw [ht] at hpreU
                    cases hpreU rfl with
                    | inl hf2 => rw [hts] at hf2; cases hf2
                    | inr hc2 => dsimp only [termCallCanUnwind] at hc2; rw [hc2] at hcu; cases hcu
          | drop df arg rt u =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu
            rw [hcbb] at hu; dsimp only [termUnwind?] at hu
            injection hu with h0
            cases hts : prog.targetSupportsUnwinding with
            | false => exact Or.inl hts
            | true =>
              cases hdu : dropCanUnwind prog df with
              | false =>
                refine Or.inr ?_
                unfold termCallCanUnwind abortUnwindingCallsProg abortUnwindingBlock abortUnwindingTerm dropCanUnwind
                rw [ht, hcbb]; dsimp only; rw [listGet?_listMap]
                unfold dropCanUnwind at hdu
                cases hdg : listGet? prog.fns df with
                | none => rfl
                | some dfn =>
                  dsimp only
                  have hm2 := abortUnwindingFn_preserves_metadata prog dfn
                  rw [hm2.2.2.1, abortUnwindingCalls_preserves_bodyCanUnwind]
                  rw [hdg] at hdu; exact hdu
              | true =>
                unfold abortUnwindingUnwindAction at h0
                rw [hts, hdu] at h0; dsimp only [bnot, bor] at h0
                cases hb : bodyCanUnwind prog.strategy fn <;> rw [hb] at h0 <;> dsimp only [bnot] at h0
                · cases u with
                  | continue_ => cases h0
                  | terminate _ => cases h0
                  | cleanup _ => cases h0
                  | unreachable =>
                    rw [ht] at hpreU
                    cases hpreU rfl with
                    | inl hf2 => rw [hts] at hf2; cases hf2
                    | inr hc2 => dsimp only [termCallCanUnwind] at hc2; rw [hc2] at hdu; cases hdu
                · cases u with
                  | continue_ => cases h0
                  | terminate _ => cases h0
                  | cleanup _ => cases h0
                  | unreachable =>
                    rw [ht] at hpreU
                    cases hpreU rfl with
                    | inl hf2 => rw [hts] at hf2; cases hf2
                    | inr hc2 => dsimp only [termCallCanUnwind] at hc2; rw [hc2] at hdu; cases hdu
          | panicCall u =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu
            rw [hcbb] at hu; dsimp only [termUnwind?] at hu
            injection hu with h0
            cases hts : prog.targetSupportsUnwinding with
            | false => exact Or.inl hts
            | true =>
              cases hpu : fnCanUnwind prog.strategy false false FnAbi.rust with
              | false =>
                refine Or.inr ?_
                unfold termCallCanUnwind abortUnwindingCallsProg abortUnwindingBlock abortUnwindingTerm
                rw [ht, hcbb]; exact hpu
              | true =>
                unfold abortUnwindingUnwindAction at h0
                rw [hts, hpu] at h0; dsimp only [bnot, bor] at h0
                cases hb : bodyCanUnwind prog.strategy fn <;> rw [hb] at h0 <;> dsimp only [bnot] at h0
                · cases u with
                  | continue_ => cases h0
                  | terminate _ => cases h0
                  | cleanup _ => cases h0
                  | unreachable =>
                    rw [ht] at hpreU
                    cases hpreU rfl with
                    | inl hf2 => rw [hts] at hf2; cases hf2
                    | inr hc2 => dsimp only [termCallCanUnwind] at hc2; rw [hc2] at hpu; cases hpu
                · cases u with
                  | continue_ => cases h0
                  | terminate _ => cases h0
                  | cleanup _ => cases h0
                  | unreachable =>
                    rw [ht] at hpreU
                    cases hpreU rfl with
                    | inl hf2 => rw [hts] at hf2; cases hf2
                    | inr hc2 => dsimp only [termCallCanUnwind] at hc2; rw [hc2] at hpu; cases hpu
        | true =>
          have hpreT := hblkWF.2
          cases ht : blk.term with
          | goto _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | branch _ _ _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | return_ _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | unreachable => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | unwindResume =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu
            cases hts : prog.targetSupportsUnwinding with
            | false => exact Or.inl hts
            | true =>
              rw [hts] at hu; dsimp only [bnot] at hu
              cases hb2 : bodyCanUnwind prog.strategy fn <;> rw [hb2] at hu <;> cases hu
          | unwindTerminate _ => rw [ht] at hu; unfold abortUnwindingTerm at hu; cases hu
          | call _ _ _ _ u =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu; rw [hcbb] at hu
            dsimp only [termUnwind?] at hu; injection hu with h0
            rw [ht, hcbb] at hpreT
            have huc := hpreT.2.2.2.2.2 rfl
            rw [huc] at h0; cases h0
          | drop _ _ _ u =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu; rw [hcbb] at hu
            dsimp only [termUnwind?] at hu; injection hu with h0
            rw [ht, hcbb] at hpreT
            have huc := hpreT.2.2.2.2 rfl
            rw [huc] at h0; cases h0
          | panicCall u =>
            rw [ht] at hu; unfold abortUnwindingTerm at hu; rw [hcbb] at hu
            dsimp only [termUnwind?] at hu; injection hu with h0
            rw [ht, hcbb] at hpreT
            have huc := hpreT.2 rfl
            rw [huc] at h0; cases h0
    · exact listForall_conj _ _ _ hfnWF.2.2 (hfnNB hf)
  · exact listForall_conj _ _ _ hpre.2.2 hfns

/-- Unwind edges along a valid post-pass `CallerCont` can only be `.unreachable` if
`targetSupportsUnwinding = false ∨ calleeUnw = false`. -/
noncomputable def StackContNoBogus (prog : Program) : Bool → List CallerCont → Prop
  | _, [] => True
  | calleeUnw, c :: rest =>
    (c.unwindOnCall = .unreachable →
      prog.targetSupportsUnwinding = false ∨ calleeUnw = false) ∧
    (∃ fn, listGet? prog.fns c.fnId = some fn ∧
      StackContNoBogus prog (bodyCanUnwind prog.strategy fn) rest)

/-- Predicate stating that every saved caller continuation is outside a cleanup frame. -/
noncomputable def StackAllNonCleanup : List CallerCont → Prop
  | [] => True
  | c :: rest => c.inCleanup = false ∧ StackAllNonCleanup rest

/-- Exact count of cleanup frames currently open on the continuation stack
(putting the accumulator on the left so `+ 0` and `+ 1` reduce by `rfl`). -/
noncomputable def countCleanupStack : List CallerCont → Nat
  | [] => 0
  | c :: rest =>
    countCleanupStack rest + (match c.inCleanup with | true => 1 | false => 0)

/-- Exact count of active + stacked cleanup frames (`= st.cleanupDepth` invariant). -/
noncomputable def countCleanupActive (inC : Bool) (stk : List CallerCont) : Nat :=
  countCleanupStack stk + (match inC with | true => 1 | false => 0)

/-- True iff at least one frame on the stack has `inCleanup = true`. -/
noncomputable def StackAnyCleanup : List CallerCont → Prop
  | [] => False
  | c :: rest => c.inCleanup = true ∨ StackAnyCleanup rest

theorem countCleanupActive_true_ge_one (stk : List CallerCont) :
    countCleanupActive true stk ≥ 1 := by
  unfold countCleanupActive
  exact Nat.le_add_left 1 (countCleanupStack stk)

/-- Full runtime invariant pairing `MirStatePostWF` with `StackContNoBogus`, exact cleanup depth,
and cleanup-disallowed-when-no-unwind. -/
noncomputable def MirRuntimeSafe (prog : Program) (st : MirState) : Prop :=
  ∃ fn,
    listGet? prog.fns st.cur.fnId = some fn ∧
    ActiveFrameWF prog st.cur ∧
    StackPostWF prog (bodyCanUnwind prog.strategy fn) st.stack ∧
    StackContNoBogus prog (bodyCanUnwind prog.strategy fn) st.stack ∧
    st.cleanupDepth = countCleanupActive st.cur.inCleanup st.stack ∧
    (prog.targetSupportsUnwinding = false → st.cur.inCleanup = false) ∧
    (prog.targetSupportsUnwinding = false → StackAllNonCleanup st.stack)

theorem MirRuntimeSafe_to_PostWF (prog : Program) (st : MirState)
    (hs : MirRuntimeSafe prog st) : MirStatePostWF prog st := by
  obtain ⟨fn, hfn, hact, hst, _, hd, _⟩ := hs
  refine ⟨fn, hfn, hact, hst, ?_⟩
  intro hc
  rw [hd, hc]
  exact countCleanupActive_true_ge_one st.stack

theorem initMirState_runtimeSafe (prog : Program) (arg : Nat)
    (hpost : MirPostPassWF prog) :
    ∃ st, initMirState prog arg = some st ∧ MirRuntimeSafe prog st := by
  obtain ⟨_, ⟨entry, hentry, henonF⟩, hfns⟩ := hpost
  have hfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns prog.entryFn entry hfns hentry
  unfold PostPassFnWF at hfnWF
  rw [henonF] at hfnWF
  obtain ⟨_, ⟨b0, hb0, hb0C⟩, _⟩ := hfnWF
  let st0 : MirState := {
    cur := {
      fnId := prog.entryFn,
      bb := 0,
      stmtIdx := 0,
      locals := initLocals entry.localCount arg,
      inCleanup := false
    },
    stack := [],
    cleanupDepth := 0,
    trace := []
  }
  refine ⟨st0, ?_, ?_⟩
  · unfold initMirState; rw [hentry]
  · refine ⟨entry, hentry, ⟨entry, b0, hentry, henonF, hb0, hb0C.symm, rfl,
      listLen_initLocals entry.localCount arg⟩, trivial, trivial, rfl,
      (fun _ => rfl), (fun _ => trivial)⟩

theorem band_self_eq_false {b : Bool} (h : band b b = false) : b = false := by
  cases b
  · rfl
  · contradiction

theorem drop_true_bodyUnw_implies_dropCanUnwind (prog : Program) (df : FnId) (dfn : FnBody)
    (hget : listGet? prog.fns df = some dfn)
    (hnonF : dfn.isForeign = false) (habi : dfn.abi = .rust)
    (hpinD : prog.panicInDropUnwinds = false → dfn.neverUnwind = true)
    (hd : dropCanUnwind prog df = false) :
    bodyCanUnwind prog.strategy dfn = false := by
  cases hp : prog.panicInDropUnwinds with
  | false =>
    have hnu := hpinD hp
    unfold bodyCanUnwind fnCanUnwind
    rw [hnu]
  | true =>
    unfold dropCanUnwind at hd
    rw [hget, hp] at hd
    dsimp only [band] at hd
    have heq : fnCanUnwind prog.strategy false dfn.neverUnwind .rust =
        bodyCanUnwind prog.strategy dfn := by
      unfold bodyCanUnwind
      rw [hnonF, habi]
    rw [heq] at hd
    exact band_self_eq_false hd

theorem dropCanUnwind_eq_bodyCanUnwind (prog : Program) (df : FnId) (dfn : FnBody)
    (hget : listGet? prog.fns df = some dfn)
    (hnonF : dfn.isForeign = false) (habi : dfn.abi = .rust)
    (hpinD : prog.panicInDropUnwinds = false → dfn.neverUnwind = true) :
    dropCanUnwind prog df = bodyCanUnwind prog.strategy dfn := by
  cases hd : dropCanUnwind prog df
  · exact (drop_true_bodyUnw_implies_dropCanUnwind prog df dfn hget hnonF habi hpinD hd).symm
  · unfold dropCanUnwind at hd
    rw [hget] at hd
    have h1 := (band_true_iff _ _).1 hd
    have h2 := (band_true_iff _ _).1 h1.2
    exact h2.2.symm

theorem countCleanupStack_cons (c : CallerCont) (rest : List CallerCont) :
    countCleanupStack (c :: rest) =
      countCleanupStack rest + (match c.inCleanup with | true => 1 | false => 0) := rfl

/-- `dispatchUnwind` on a valid post-pass unwind edge preserves `MirRuntimeSafe` and
never returns `.ub` or `.invalid` when `targetSupportsUnwinding = true` and `callUnw = true`
and `u ≠ .unreachable`. -/
theorem dispatchUnwind_preserves_safe (prog : Program)
    (_hpost : MirPostPassWF prog)
    (hts : prog.targetSupportsUnwinding = true)
    (cur : ActiveFrame) (stack : List CallerCont) (u : UnwindAction)
    (depth : Nat) (trace : List TraceEvent)
    (fn : FnBody) (hfn : listGet? prog.fns cur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hcurLoc : listLen cur.locals = fn.localCount)
    (callUnw : Bool) (hcu : callUnw = true)
    (huWF : PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn)
      callUnw fn.blocks cur.inCleanup u)
    (huNE : u ≠ .unreachable)
    (hdepth : depth = countCleanupActive cur.inCleanup stack)
    (hstack : StackPostWF prog (bodyCanUnwind prog.strategy fn) stack)
    (hstackNB : StackContNoBogus prog (bodyCanUnwind prog.strategy fn) stack) :
    match dispatchUnwind prog.fns cur stack u depth trace with
    | .running st' => MirRuntimeSafe prog st'
    | .halted res => ¬ mirIsBad res := by
  induction stack generalizing cur fn u depth with
  | nil =>
    cases u with
    | terminate reason =>
      rw [dispatchUnwind_terminate_eq]
      intro h; cases h
    | unreachable =>
      exact absurd rfl huNE
    | cleanup padBB =>
      obtain ⟨hnc, padBlk, hpadGet, hpadC⟩ := huWF.1
      rw [dispatchUnwind_cleanup_eq hfn hpadGet hpadC]
      refine ⟨fn, hfn, ⟨fn, padBlk, hfn, hnonF, hpadGet, hpadC.symm, rfl, hcurLoc⟩,
        hstack, hstackNB, ?_, (fun hf => by rw [hts] at hf; cases hf),
        (fun hf => by rw [hts] at hf; cases hf)⟩
      unfold countCleanupActive
      rw [hdepth, hnc]
      rfl
    | continue_ =>
      unfold dispatchUnwind
      intro h; cases h
  | cons c rest ih =>
    cases u with
    | terminate reason =>
      rw [dispatchUnwind_terminate_eq]
      intro h; cases h
    | unreachable =>
      exact absurd rfl huNE
    | cleanup padBB =>
      obtain ⟨hnc, padBlk, hpadGet, hpadC⟩ := huWF.1
      rw [dispatchUnwind_cleanup_eq hfn hpadGet hpadC]
      refine ⟨fn, hfn, ⟨fn, padBlk, hfn, hnonF, hpadGet, hpadC.symm, rfl, hcurLoc⟩,
        hstack, hstackNB, ?_, (fun hf => by rw [hts] at hf; cases hf),
        (fun hf => by rw [hts] at hf; cases hf)⟩
      unfold countCleanupActive
      rw [hdepth, hnc]
      rfl
    | continue_ =>
      have hncCur : cur.inCleanup = false := huWF.1
      have hbu : bodyCanUnwind prog.strategy fn = true := by
        cases hb : bodyCanUnwind prog.strategy fn
        · exact absurd rfl (huWF.2.2 (Or.inr hb))
        · rfl
      obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstack
      obtain ⟨hcNB, cfn2, hcfn2, hrestNB⟩ := hstackNB
      have hcfnEq : cfn2 = cfn := by
        rw [hcfn] at hcfn2; cases hcfn2; rfl
      rw [hcfnEq] at hrestNB
      obtain ⟨cfn', rblk, hcfn', hcfnNonF, hrblk, hcClean, hdst, hcloc, hcEdge, hcCleanTerm⟩ := hcWF
      have hcfnEq2 : cfn' = cfn := by
        rw [hcfn] at hcfn'; cases hcfn'; rfl
      rw [hcfnEq2] at hcfnNonF hdst hcloc hcEdge
      unfold dispatchUnwind
      dsimp only
      cases hcc : c.inCleanup
      · have hcu' : bodyCanUnwind prog.strategy fn = true := hbu
        have hcNE : c.unwindOnCall ≠ .unreachable := by
          intro hbad
          cases hcNB hbad with
          | inl htsF => rw [hts] at htsF; cases htsF
          | inr hbuF => rw [hbu] at hbuF; cases hbuF
        have hdepth' : depth = countCleanupActive c.inCleanup rest := by
          unfold countCleanupActive at hdepth ⊢
          rw [countCleanupStack_cons] at hdepth
          rw [hncCur, hcc] at hdepth
          rw [hcc]
          exact hdepth
        rw [hbu, ← hcu] at hcEdge
        rw [hcc] at hcEdge hdepth'
        exact ih { fnId := c.fnId, bb := c.retTarget, stmtIdx := 0, locals := c.locals, inCleanup := false }
          c.unwindOnCall depth cfn hcfn hcfnNonF hcloc hcEdge hcNE hdepth' hrestWF hrestNB
      · have hterm := hcCleanTerm hcc
        rw [hterm, dispatchUnwind_terminate_eq]
        intro h; cases h

theorem stepMir_preserves_safe (prog : Program)
    (hpost : MirPostPassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PostPassNoBogusUnreachable prog) (st : MirState)
    (hsafe : MirRuntimeSafe prog st) :
    match stepMir prog st with
    | .running st' => MirRuntimeSafe prog st'
    | .halted res => ¬ mirIsBad res := by
  obtain ⟨fn, hfn, hact, hstack, hstackNB, hdepth, htsc, htss⟩ := hsafe
  obtain ⟨fn', blk, hfn', hnonF, hblk, hcleanEq, hstmtLe, hlocals⟩ := hact
  have hfnEq : fn' = fn := by rw [hfn] at hfn'; cases hfn'; rfl
  rw [hfnEq] at hnonF hblk hlocals
  have hfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns st.cur.fnId fn hpost.2.2 hfn
  unfold PostPassFnWF at hfnWF
  rw [hnonF] at hfnWF
  have hblkWF := listGet?_listForall (PostPassBlockWF prog fn) fn.blocks st.cur.bb blk hfnWF.2.2 hblk
  have hfnNB := listGet?_listForall _ prog.fns st.cur.fnId fn hnob.2 hfn hnonF
  have hblkNB := listGet?_listForall _ fn.blocks st.cur.bb blk hfnNB hblk
  cases hstGet : listGet? blk.stmts st.cur.stmtIdx with
  | some stmt =>
    rw [stepMir_stmt_eq hfn hnonF hblk hcleanEq hstGet]
    have hltStmt : natLt st.cur.stmtIdx (listLen blk.stmts) = true := by
      apply natLe_eq_false_lt st.cur.stmtIdx (listLen blk.stmts) hstmtLe
      cases heq : natEq st.cur.stmtIdx (listLen blk.stmts)
      · rfl
      · have heq' := natEq_eq heq
        rw [heq', listGet?_ge_len_none _ _ (natLe_refl _)] at hstGet
        cases hstGet
    have hstmtLe' : natLe (st.cur.stmtIdx + 1) (listLen blk.stmts) = true :=
      natLe_succ_of_lt st.cur.stmtIdx (listLen blk.stmts) hltStmt
    have hstmtWF := listGet?_listForall (StmtWF fn.localCount) blk.stmts st.cur.stmtIdx stmt hblkWF.1 hstGet
    cases stmt with
    | nop =>
      unfold execStmt; dsimp only
      exact ⟨fn, hfn, ⟨fn, blk, hfn, hnonF, hblk, hcleanEq, hstmtLe', hlocals⟩,
        hstack, hstackNB, hdepth, htsc, htss⟩
    | emit ev =>
      unfold execStmt; dsimp only
      exact ⟨fn, hfn, ⟨fn, blk, hfn, hnonF, hblk, hcleanEq, hstmtLe', hlocals⟩,
        hstack, hstackNB, hdepth, htsc, htss⟩
    | assignConst dst val =>
      unfold execStmt; dsimp only
      exact ⟨fn, hfn, ⟨fn, blk, hfn, hnonF, hblk, hcleanEq, hstmtLe', by
          unfold writeLocal; rw [listLen_listSet, hlocals]⟩,
        hstack, hstackNB, hdepth, htsc, htss⟩
    | assignLocal dst src =>
      unfold execStmt readLocal?; dsimp only
      have hsrcLt : natLt src fn.localCount = true := hstmtWF.2
      rw [← hlocals] at hsrcLt
      obtain ⟨v, hv⟩ := listGet?_lt_len st.cur.locals src hsrcLt
      rw [hv]; dsimp only
      exact ⟨fn, hfn, ⟨fn, blk, hfn, hnonF, hblk, hcleanEq, hstmtLe', by
          unfold writeLocal; rw [listLen_listSet, hlocals]⟩,
        hstack, hstackNB, hdepth, htsc, htss⟩
  | none =>
    have heqLen : st.cur.stmtIdx = listLen blk.stmts :=
      listGet?_eq_none_implies_ge blk.stmts st.cur.stmtIdx hstGet hstmtLe
    rw [stepMir_term_eq hfn hnonF hblk hcleanEq hstGet heqLen]
    have htermWF := hblkWF.2
    cases ht : blk.term with
    | goto target =>
      unfold execTerm; dsimp only
      have hpt := htermWF.1
      rw [ht] at hpt
      obtain ⟨tblk, htblk, htclean⟩ := hpt
      have hcleanNew : st.cur.inCleanup = tblk.isCleanup := by rw [hcleanEq, htclean]
      refine ⟨fn, hfn, ⟨fn, tblk, hfn, hnonF, htblk, hcleanNew, rfl, hlocals⟩,
        hstack, hstackNB, hdepth, htsc, htss⟩
    | branch cond z nz =>
      unfold execTerm readLocal?; dsimp only
      have hpt := htermWF.1
      rw [ht] at hpt
      obtain ⟨hcondLt, ⟨b1, hb1, hb1C⟩, ⟨b2, hb2, hb2C⟩⟩ := hpt
      rw [← hlocals] at hcondLt
      obtain ⟨v, hv⟩ := listGet?_lt_len st.cur.locals cond hcondLt
      rw [hv]; dsimp only
      cases v with
      | zero =>
        refine ⟨fn, hfn, ⟨fn, b1, hfn, hnonF, hb1, ?_, rfl, hlocals⟩,
          hstack, hstackNB, hdepth, htsc, htss⟩
        rw [hcleanEq, hb1C]
      | succ _ =>
        refine ⟨fn, hfn, ⟨fn, b2, hfn, hnonF, hb2, ?_, rfl, hlocals⟩,
          hstack, hstackNB, hdepth, htsc, htss⟩
        rw [hcleanEq, hb2C]
    | return_ valReg =>
      unfold execTerm readLocal?; dsimp only
      have hpt := htermWF.1
      rw [ht] at hpt
      obtain ⟨hnc, hvalLt⟩ := hpt
      have hcurNC : st.cur.inCleanup = false := by rw [hcleanEq, hnc]
      rw [hcurNC]; dsimp only
      rw [← hlocals] at hvalLt
      obtain ⟨v, hv⟩ := listGet?_lt_len st.cur.locals valReg hvalLt
      rw [hv]; dsimp only
      cases hstStk : st.stack with
      | nil =>
        intro hbad; cases hbad
      | cons c rest =>
        rw [hstStk] at hstack hstackNB htss hdepth
        obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstack
        obtain ⟨_, cfn2, hcfn2, hrestNB⟩ := hstackNB
        have hcfnEq : cfn2 = cfn := by rw [hcfn] at hcfn2; cases hcfn2; rfl
        rw [hcfnEq] at hrestNB
        obtain ⟨cfn', rblk, hcfn', hcfnNonF, hrblk, hcClean, hdstLt, hcloc, _, _⟩ := hcWF
        have hcfnEq2 : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
        rw [hcfnEq2] at hcfnNonF hrblk hdstLt hcloc
        refine ⟨cfn, hcfn, ⟨cfn, rblk, hcfn, hcfnNonF, hrblk, hcClean, rfl, ?_⟩,
          hrestWF, hrestNB, ?_, (fun hf => (htss hf).1), (fun hf => (htss hf).2)⟩
        · unfold writeLocal; rw [listLen_listSet, hcloc]
        · unfold countCleanupActive at hdepth ⊢
          rw [countCleanupStack_cons] at hdepth
          rw [hcurNC] at hdepth
          exact hdepth
    | unreachable =>
      have hts := hblkNB.2.1
      have hnc := hblkNB.1
      cases hcu : st.cur.inCleanup
      · rw [← hcleanEq, hcu] at hnc
        exact absurd ht (hnc rfl)
      · cases htsB : prog.targetSupportsUnwinding
        · rw [htsc htsB] at hcu; cases hcu
        · exact absurd ht (hts htsB)
    | unwindTerminate reason =>
      unfold execTerm; dsimp only
      intro hbad; cases hbad
    | unwindResume =>
      have htsBody := htermWF.2.1 ht
      obtain ⟨hts, hbu⟩ := htsBody
      have hpt := htermWF.1
      rw [ht] at hpt
      have hcurC : st.cur.inCleanup = true := by rw [hcleanEq, hpt]
      unfold execTerm; dsimp only
      rw [hcurC]; dsimp only
      cases hstStk : st.stack with
      | nil =>
        intro hbad; cases hbad
      | cons c rest =>
        rw [hstStk] at hstack hstackNB hdepth
        obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstack
        obtain ⟨hcNB, cfn2, hcfn2, hrestNB⟩ := hstackNB
        have hcfnEq : cfn2 = cfn := by rw [hcfn] at hcfn2; cases hcfn2; rfl
        rw [hcfnEq] at hrestNB
        obtain ⟨cfn', rblk, hcfn', hcfnNonF, hrblk, hcClean, hdstLt, hcloc, hcEdge, hcCleanTerm⟩ := hcWF
        have hcfnEq2 : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
        rw [hcfnEq2] at hcfnNonF hdstLt hcloc hcEdge
        dsimp only
        cases hcc : c.inCleanup
        · have hcNE : c.unwindOnCall ≠ .unreachable := by
            intro hbad
            cases hcNB hbad with
            | inl htsF => rw [hts] at htsF; cases htsF
            | inr hbuF => rw [hbu] at hbuF; cases hbuF
          have hdepth' : (match st.cleanupDepth with | 0 => 0 | d + 1 => d) =
              countCleanupActive false rest := by
            unfold countCleanupActive at hdepth ⊢
            rw [countCleanupStack_cons] at hdepth
            rw [hcurC, hcc] at hdepth
            rw [hdepth]
          rw [hcc] at hcEdge
          exact dispatchUnwind_preserves_safe prog hpost hts
            { fnId := c.fnId, bb := c.retTarget, stmtIdx := 0, locals := c.locals, inCleanup := false }
            rest c.unwindOnCall (match st.cleanupDepth with | 0 => 0 | d + 1 => d) st.trace
            cfn hcfn hcfnNonF hcloc (bodyCanUnwind prog.strategy fn) hbu hcEdge hcNE hdepth'
            hrestWF hrestNB
        · rw [hcCleanTerm hcc, dispatchUnwind_terminate_eq]
          intro hbad; cases hbad
    | call callee argReg dst rt u =>
      unfold execTerm readLocal?; dsimp only
      have hpt := htermWF.1
      have hpe := htermWF.2.2
      rw [ht] at hpt hpe
      dsimp only [termUnwind?, termCallCanUnwind] at hpe
      obtain ⟨hargLt, hdstLt, ⟨cfn, hcfn⟩, ⟨rblk, hrblk, hrblkC⟩, huPre, huClean⟩ := hpt
      rw [← hlocals] at hargLt
      obtain ⟨argVal, hargVal⟩ := listGet?_lt_len st.cur.locals argReg hargLt
      rw [hargVal]; dsimp only
      unfold enterCall; dsimp only
      rw [hcfn]; dsimp only
      cases hcfnF : cfn.isForeign with
      | false =>
        dsimp only
        have hcfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns callee cfn hpost.2.2 hcfn
        unfold PostPassFnWF at hcfnWF
        rw [hcfnF] at hcfnWF
        obtain ⟨_, ⟨cb0, hcb0, hcb0C⟩, _⟩ := hcfnWF
        refine ⟨cfn, hcfn, ⟨cfn, cb0, hcfn, hcfnF, hcb0, hcb0C.symm, rfl,
            listLen_initLocals cfn.localCount argVal⟩, ?_, ?_, ?_, (fun _ => rfl), ?_⟩
        · refine ⟨fn, hfn, ⟨fn, rblk, hfn, hnonF, hrblk, ?_, hdstLt, hlocals, ?_, ?_⟩, hstack⟩
          · rw [hcleanEq, hrblkC]
          · dsimp only; rw [hcleanEq]
            have hccEq : calleeCanUnwind prog callee = bodyCanUnwind prog.strategy cfn := by
              unfold calleeCanUnwind; rw [hcfn]
            rw [← hccEq]; exact hpe
          · intro hcC; dsimp only at hcC; rw [hcleanEq] at hcC; exact huClean hcC
        · refine ⟨?_, fn, hfn, hstackNB⟩
          intro hbad
          dsimp only at hbad
          have hnb := hblkNB.2.2
          rw [ht] at hnb
          dsimp only [termUnwind?, termCallCanUnwind] at hnb
          cases hnb (by rw [hbad]) with
          | inl htsF => exact Or.inl htsF
          | inr hcuF =>
            unfold calleeCanUnwind at hcuF
            rw [hcfn] at hcuF
            exact Or.inr hcuF
        · unfold countCleanupActive countCleanupStack
          rw [hdepth]
          unfold countCleanupActive
          rfl
        · intro htsF
          exact ⟨htsc htsF, htss htsF⟩
      | true =>
        dsimp only
        cases hfo : prog.foreignSpecs callee argVal with
        | ret v evOpt =>
          dsimp only
          refine ⟨fn, hfn, ⟨fn, rblk, hfn, hnonF, hrblk, ?_, rfl, by
              unfold writeLocal; rw [listLen_listSet, hlocals]⟩,
            hstack, hstackNB, ?_, htsc, htss⟩
          · rw [hcleanEq, hrblkC]
          · rw [hdepth, hcleanEq]
        | unwound evOpt =>
          dsimp only
          have hts : prog.targetSupportsUnwinding = true := by
            cases hts0 : prog.targetSupportsUnwinding
            · exact absurd hfo (hnob.1 hts0 callee argVal evOpt)
            · rfl
          have hcbU : bodyCanUnwind prog.strategy cfn = true := by
            cases hcb0 : bodyCanUnwind prog.strategy cfn
            · have hfbad := hfok callee argVal
              rw [hcfn] at hfbad
              exact absurd hfo (hfbad hcfnF hcb0 evOpt)
            · rfl
          have hccU : calleeCanUnwind prog callee = true := by
            unfold calleeCanUnwind; rw [hcfn]; dsimp only; rw [hcbU]
          have huNE : u ≠ .unreachable := by
            intro hbad
            have hnb := hblkNB.2.2
            rw [ht] at hnb
            dsimp only [termUnwind?, termCallCanUnwind] at hnb
            cases hnb (by rw [hbad]) with
            | inl htsF => rw [hts] at htsF; cases htsF
            | inr hcuF => rw [hccU] at hcuF; cases hcuF
          rw [← hcleanEq] at hpe
          exact dispatchUnwind_preserves_safe prog hpost hts st.cur st.stack u st.cleanupDepth
            (appendOptEvent st.trace evOpt) fn hfn hnonF hlocals (calleeCanUnwind prog callee)
            hccU hpe huNE hdepth hstack hstackNB
    | drop df argReg rt u =>
      unfold execTerm readLocal?; dsimp only
      have hpt := htermWF.1
      have hpe := htermWF.2.2
      rw [ht] at hpt hpe
      dsimp only [termUnwind?, termCallCanUnwind] at hpe
      obtain ⟨hargLt, ⟨dfn, hdfn, hdfNonF, hdfAbi, hdfPinD⟩, ⟨rblk, hrblk, hrblkC⟩, huPre, huClean⟩ := hpt
      rw [← hlocals] at hargLt
      obtain ⟨argVal, hargVal⟩ := listGet?_lt_len st.cur.locals argReg hargLt
      rw [hargVal]; dsimp only
      unfold enterCall; dsimp only
      rw [hdfn]; dsimp only
      rw [hdfNonF]; dsimp only
      have hdfWF := listGet?_listForall (PostPassFnWF prog) prog.fns df dfn hpost.2.2 hdfn
      unfold PostPassFnWF at hdfWF
      rw [hdfNonF] at hdfWF
      obtain ⟨_, ⟨db0, hdb0, hdb0C⟩, _⟩ := hdfWF
      have hdEq := dropCanUnwind_eq_bodyCanUnwind prog df dfn hdfn hdfNonF hdfAbi hdfPinD
      refine ⟨dfn, hdfn, ⟨dfn, db0, hdfn, hdfNonF, hdb0, hdb0C.symm, rfl,
          listLen_initLocals dfn.localCount argVal⟩, ?_, ?_, ?_, (fun _ => rfl), ?_⟩
      · refine ⟨fn, hfn, ⟨fn, rblk, hfn, hnonF, hrblk, ?_, natLt_zero_of_le2 fn.localCount hfnWF.1,
            hlocals, ?_, ?_⟩, hstack⟩
        · rw [hcleanEq, hrblkC]
        · dsimp only; rw [hcleanEq, ← hdEq]; exact hpe
        · intro hcC; dsimp only at hcC; rw [hcleanEq] at hcC; exact huClean hcC
      · refine ⟨?_, fn, hfn, hstackNB⟩
        intro hbad
        dsimp only at hbad
        have hnb := hblkNB.2.2
        rw [ht] at hnb
        dsimp only [termUnwind?, termCallCanUnwind] at hnb
        cases hnb (by rw [hbad]) with
        | inl htsF => exact Or.inl htsF
        | inr hduF => rw [hdEq] at hduF; exact Or.inr hduF
      · unfold countCleanupActive countCleanupStack
        rw [hdepth]
        unfold countCleanupActive
        rfl
      · intro htsF
        exact ⟨htsc htsF, htss htsF⟩
    | panicCall u =>
      unfold execTerm; dsimp only
      cases hstrat : prog.strategy with
      | abort =>
        dsimp only
        intro hbad; cases hbad
      | unwind =>
        cases hts0 : prog.targetSupportsUnwinding with
        | false =>
          dsimp only
          intro hbad; cases hbad
        | true =>
          dsimp only
          have hpt := htermWF.1
          have hpe := htermWF.2.2
          rw [ht] at hpt hpe
          dsimp only [termUnwind?, termCallCanUnwind] at hpe
          have hpu : fnCanUnwind prog.strategy false false .rust = true := by
            rw [hstrat]; rfl
          have huNE : u ≠ .unreachable := by
            intro hbad
            have hnb := hblkNB.2.2
            rw [ht] at hnb
            dsimp only [termUnwind?, termCallCanUnwind] at hnb
            cases hnb (by rw [hbad]) with
            | inl htsF => rw [hts0] at htsF; cases htsF
            | inr hpuF => rw [hpu] at hpuF; cases hpuF
          rw [← hcleanEq] at hpe
          exact dispatchUnwind_preserves_safe prog hpost hts0 st.cur st.stack u st.cleanupDepth
            st.trace fn hfn hnonF hlocals (fnCanUnwind prog.strategy false false .rust)
            hpu hpe huNE hdepth hstack hstackNB

theorem runMir_safe (prog : Program)
    (hpost : MirPostPassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PostPassNoBogusUnreachable prog) (fuel : Nat) (st : MirState)
    (hsafe : MirRuntimeSafe prog st) :
    ¬ mirIsBad (runMir prog fuel st) := by
  induction fuel generalizing st with
  | zero =>
    unfold runMir mirIsBad
    intro h; cases h
  | succ k ih =>
    unfold runMir
    have hs := stepMir_preserves_safe prog hpost hfok hnob st hsafe
    cases hst : stepMir prog st with
    | running st' =>
      rw [hst] at hs
      exact ih st' hs
    | halted res =>
      rw [hst] at hs
      exact hs

theorem evalMirProg_safe (prog : Program)
    (hpost : MirPostPassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PostPassNoBogusUnreachable prog) (fuel arg : Nat) :
    ¬ mirIsBad (evalMirProg prog fuel arg) := by
  obtain ⟨st, hinit, hsafe⟩ := initMirState_runtimeSafe prog arg hpost
  unfold evalMirProg
  rw [hinit]
  exact runMir_safe prog hpost hfok hnob fuel st hsafe

/-- Bottom-most function ID on the MIR call stack (the original entry point). -/
noncomputable def stackBottomFn : List CallerCont → FnId → FnId
  | [], fallback => fallback
  | c :: rest, _ => stackBottomFn rest c.fnId

theorem stackBottomFn_eq_entry_dispatch (prog : Program)
    (cur : ActiveFrame) (stack : List CallerCont) (u : UnwindAction)
    (depth : Nat) (trace : List TraceEvent)
    (fn entry : FnBody)
    (hfn : listGet? prog.fns cur.fnId = some fn)
    (huWF : PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn)
      true fn.blocks cur.inCleanup u)
    (hstack : StackPostWF prog (bodyCanUnwind prog.strategy fn) stack)
    (hbot : stackBottomFn stack cur.fnId = prog.entryFn)
    (hentry : listGet? prog.fns prog.entryFn = some entry)
    (hbotNoUnw : bodyCanUnwind prog.strategy entry = false) :
    match dispatchUnwind prog.fns cur stack u depth trace with
    | .running st' => stackBottomFn st'.stack st'.cur.fnId = prog.entryFn
    | .halted res => ∀ tr, res ≠ .unwound tr := by
  induction stack generalizing cur fn u depth with
  | nil =>
    cases u with
    | terminate reason =>
      rw [dispatchUnwind_terminate_eq]; intro tr h; cases h
    | unreachable =>
      unfold dispatchUnwind; intro tr h; cases h
    | cleanup padBB =>
      obtain ⟨_, padBlk, hpadGet, hpadC⟩ := huWF.1
      rw [dispatchUnwind_cleanup_eq hfn hpadGet hpadC]
      exact hbot
    | continue_ =>
      have hcurEq : cur.fnId = prog.entryFn := hbot
      rw [hcurEq, hentry] at hfn
      cases hfn
      have hbad := huWF.2.2 (Or.inr hbotNoUnw)
      exact absurd rfl hbad
  | cons c rest ih =>
    cases u with
    | terminate reason =>
      rw [dispatchUnwind_terminate_eq]; intro tr h; cases h
    | unreachable =>
      unfold dispatchUnwind; intro tr h; cases h
    | cleanup padBB =>
      obtain ⟨_, padBlk, hpadGet, hpadC⟩ := huWF.1
      rw [dispatchUnwind_cleanup_eq hfn hpadGet hpadC]
      exact hbot
    | continue_ =>
      obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstack
      obtain ⟨cfn', _, hcfn', _, _, _, _, _, hcEdge, _⟩ := hcWF
      have hcfnEq : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
      rw [hcfnEq] at hcEdge
      unfold dispatchUnwind
      dsimp only
      have hbu : bodyCanUnwind prog.strategy fn = true := by
        cases hb : bodyCanUnwind prog.strategy fn
        · exact absurd rfl (huWF.2.2 (Or.inr hb))
        · rfl
      rw [hbu] at hcEdge
      have hbot' : stackBottomFn rest c.fnId = prog.entryFn := by
        unfold stackBottomFn at hbot; exact hbot
      exact ih _ c.unwindOnCall depth cfn hcfn hcEdge hrestWF hbot'

theorem entry_nonUnwinding_never_unwound_run (prog : Program)
    (hpost : MirPostPassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PostPassNoBogusUnreachable prog) (entry : FnBody)
    (hentry : listGet? prog.fns prog.entryFn = some entry)
    (hbotNoUnw : bodyCanUnwind prog.strategy entry = false)
    (fuel : Nat) (st : MirState) (hsafe : MirRuntimeSafe prog st)
    (hbot : stackBottomFn st.stack st.cur.fnId = prog.entryFn) :
    ∀ tr, runMir prog fuel st ≠ .unwound tr := by
  induction fuel generalizing st with
  | zero =>
    unfold runMir; intro tr h; cases h
  | succ k ih =>
    unfold runMir
    have hsafeCopy := hsafe
    obtain ⟨fn, hfn, hact, hstack, hstackNB, hdepth, htsc, htss⟩ := hsafe
    obtain ⟨fn', blk, hfn', hnonF, hblk, hcleanEq, hstmtLe, hlocals⟩ := hact
    have hfnEq : fn' = fn := by rw [hfn] at hfn'; cases hfn'; rfl
    rw [hfnEq] at hnonF hblk hlocals
    have hfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns st.cur.fnId fn hpost.2.2 hfn
    unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
    have hblkWF := listGet?_listForall (PostPassBlockWF prog fn) fn.blocks st.cur.bb blk hfnWF.2.2 hblk
    have hs := stepMir_preserves_safe prog hpost hfok hnob st hsafeCopy
    cases hstGet : listGet? blk.stmts st.cur.stmtIdx with
    | some stmt =>
      have hsteq := stepMir_stmt_eq hfn hnonF hblk hcleanEq hstGet
      rw [hsteq] at hs ⊢
      cases stmt with
      | nop =>
        unfold execStmt at hs ⊢; dsimp only at hs ⊢; exact ih _ hs hbot
      | emit ev =>
        unfold execStmt at hs ⊢; dsimp only at hs ⊢; exact ih _ hs hbot
      | assignConst dst val =>
        unfold execStmt at hs ⊢; dsimp only at hs ⊢; exact ih _ hs hbot
      | assignLocal dst src =>
        unfold execStmt readLocal? at hs ⊢; dsimp only at hs ⊢
        cases hr : listGet? st.cur.locals src with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some v => rw [hr] at hs; dsimp only at hs ⊢; exact ih _ hs hbot
    | none =>
      have heqLen : st.cur.stmtIdx = listLen blk.stmts :=
        listGet?_eq_none_implies_ge blk.stmts st.cur.stmtIdx hstGet hstmtLe
      rw [stepMir_term_eq hfn hnonF hblk hcleanEq hstGet heqLen] at hs ⊢
      have htermWF := hblkWF.2
      cases ht : blk.term with
      | goto target =>
        rw [ht] at hs; unfold execTerm at hs ⊢; dsimp only at hs ⊢; exact ih _ hs hbot
      | branch cond z nz =>
        rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
        cases hr : listGet? st.cur.locals cond with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some v =>
          rw [hr] at hs; dsimp only at hs ⊢
          cases v with
          | zero => exact ih _ hs hbot
          | succ _ => exact ih _ hs hbot
      | return_ valReg =>
        rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
        cases hinc : st.cur.inCleanup with
        | true => rw [hinc] at hs; dsimp only at hs; exact absurd trivial hs
        | false =>
          rw [hinc] at hs; dsimp only at hs ⊢
          cases hr : listGet? st.cur.locals valReg with
          | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
          | some v =>
            rw [hr] at hs; dsimp only at hs ⊢
            cases hstk : st.stack with
            | nil => intro tr hbad; cases hbad
            | cons c rest =>
              rw [hstk] at hs hbot; dsimp only at hs ⊢
              exact ih _ hs hbot
      | unreachable =>
        rw [ht] at hs; unfold execTerm at hs; dsimp only at hs; exact absurd trivial hs
      | unwindTerminate reason =>
        unfold execTerm; intro tr h; cases h
      | unwindResume =>
        have htsBody := htermWF.2.1 ht
        obtain ⟨hts, hbu⟩ := htsBody
        have hpt := htermWF.1; rw [ht] at hpt
        have hcurC : st.cur.inCleanup = true := by rw [hcleanEq, hpt]
        rw [ht] at hs; unfold execTerm at hs ⊢; rw [hcurC] at hs ⊢; dsimp only at hs ⊢
        cases hstk : st.stack with
        | nil =>
          exfalso
          have hcurEq : st.cur.fnId = prog.entryFn := by
            rw [hstk] at hbot; exact hbot
          rw [hcurEq, hentry] at hfn; cases hfn
          rw [hbotNoUnw] at hbu; cases hbu
        | cons c rest =>
          rw [hstk] at hs hstack hbot; dsimp only at hs ⊢
          obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstack
          obtain ⟨cfn', _, hcfn', _, _, _, _, _, hcEdge, _⟩ := hcWF
          have hcfnEq : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
          rw [hcfnEq] at hcEdge
          rw [hbu] at hcEdge
          have hbot' : stackBottomFn rest c.fnId = prog.entryFn := hbot
          let cFrame : ActiveFrame := {
            fnId := c.fnId,
            bb := c.retTarget,
            stmtIdx := 0,
            locals := c.locals,
            inCleanup := c.inCleanup
          }
          have hdisp := stackBottomFn_eq_entry_dispatch prog cFrame rest c.unwindOnCall
            (match st.cleanupDepth with | 0 => 0 | d + 1 => d) st.trace cfn entry hcfn hcEdge hrestWF hbot' hentry hbotNoUnw
          cases hd : dispatchUnwind prog.fns cFrame rest c.unwindOnCall
              (match st.cleanupDepth with | 0 => 0 | d + 1 => d) st.trace with
          | running st' =>
            rw [hd] at hs hdisp
            exact ih st' hs hdisp
          | halted res =>
            rw [hd] at hdisp
            exact hdisp
      | call callee argReg dst rt u =>
        rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
        cases hr : listGet? st.cur.locals argReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some argVal =>
          rw [hr] at hs; dsimp only at hs ⊢
          unfold enterCall at hs ⊢; dsimp only at hs ⊢
          cases hgetC : listGet? prog.fns callee with
          | none => rw [hgetC] at hs; dsimp only at hs; exact absurd trivial hs
          | some cfn =>
            rw [hgetC] at hs; dsimp only at hs ⊢
            cases hcf : cfn.isForeign with
            | false =>
              rw [hcf] at hs; dsimp only at hs ⊢
              let cont : CallerCont := {
                fnId := st.cur.fnId,
                locals := st.cur.locals,
                inCleanup := st.cur.inCleanup,
                retDst := dst,
                retTarget := rt,
                unwindOnCall := u
              }
              have hbot' : stackBottomFn (cont :: st.stack) callee = prog.entryFn := hbot
              exact ih _ hs hbot'
            | true =>
              rw [hcf] at hs; dsimp only at hs ⊢
              cases hfo : prog.foreignSpecs callee argVal with
              | ret v evOpt =>
                rw [hfo] at hs; dsimp only at hs ⊢
                exact ih _ hs hbot
              | unwound evOpt =>
                rw [hfo] at hs; dsimp only at hs ⊢
                have hpe := htermWF.2.2; rw [ht] at hpe
                dsimp only [termUnwind?, termCallCanUnwind] at hpe
                have hcbU : bodyCanUnwind prog.strategy cfn = true := by
                  cases hcb0 : bodyCanUnwind prog.strategy cfn
                  · have hfbad := hfok callee argVal; rw [hgetC] at hfbad
                    exact absurd hfo (hfbad hcf hcb0 evOpt)
                  · rfl
                have hccU : calleeCanUnwind prog callee = true := by
                  unfold calleeCanUnwind; rw [hgetC]; dsimp only; rw [hcbU]
                rw [hccU, ← hcleanEq] at hpe
                have hdisp := stackBottomFn_eq_entry_dispatch prog st.cur st.stack u
                  st.cleanupDepth (appendOptEvent st.trace evOpt) fn entry hfn hpe hstack hbot hentry hbotNoUnw
                cases hd : dispatchUnwind prog.fns st.cur st.stack u st.cleanupDepth
                    (appendOptEvent st.trace evOpt) with
                | running st' =>
                  rw [hd] at hs hdisp
                  exact ih st' hs hdisp
                | halted res =>
                  rw [hd] at hdisp
                  exact hdisp
      | drop df argReg rt u =>
        rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
        cases hr : listGet? st.cur.locals argReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some argVal =>
          rw [hr] at hs; dsimp only at hs ⊢
          unfold enterCall at hs ⊢; dsimp only at hs ⊢
          cases hgetD : listGet? prog.fns df with
          | none => rw [hgetD] at hs; dsimp only at hs; exact absurd trivial hs
          | some dfn =>
            rw [hgetD] at hs; dsimp only at hs ⊢
            cases hdfF : dfn.isForeign with
            | false =>
              rw [hdfF] at hs; dsimp only at hs ⊢
              let cont : CallerCont := {
                fnId := st.cur.fnId,
                locals := st.cur.locals,
                inCleanup := st.cur.inCleanup,
                retDst := 0,
                retTarget := rt,
                unwindOnCall := u
              }
              have hbot' : stackBottomFn (cont :: st.stack) df = prog.entryFn := hbot
              exact ih _ hs hbot'
            | true =>
              rw [hdfF] at hs
              have hpt := htermWF.1; rw [ht] at hpt
              obtain ⟨_, ⟨dfn', hdfn', hdfNonF, _, _⟩, _⟩ := hpt
              rw [hdfn'] at hgetD; cases hgetD; rw [hdfNonF] at hdfF; cases hdfF
      | panicCall u =>
        rw [ht] at hs; unfold execTerm at hs ⊢; dsimp only at hs ⊢
        cases hstrat : prog.strategy with
        | abort => rw [hstrat] at hs; dsimp only at hs ⊢; intro tr hbad; cases hbad
        | unwind =>
          cases hts0 : prog.targetSupportsUnwinding with
          | false => rw [hstrat, hts0] at hs; dsimp only at hs ⊢; intro tr hbad; cases hbad
          | true =>
            rw [hstrat, hts0] at hs; dsimp only at hs ⊢
            have hpe := htermWF.2.2; rw [ht] at hpe
            dsimp only [termUnwind?, termCallCanUnwind] at hpe
            have hpu : fnCanUnwind prog.strategy false false .rust = true := by
              rw [hstrat]; rfl
            rw [hpu, ← hcleanEq] at hpe
            have hdisp := stackBottomFn_eq_entry_dispatch prog st.cur st.stack u
              st.cleanupDepth st.trace fn entry hfn hpe hstack hbot hentry hbotNoUnw
            cases hd : dispatchUnwind prog.fns st.cur st.stack u st.cleanupDepth st.trace with
            | running st' =>
              rw [hd] at hs hdisp
              exact ih st' hs hdisp
            | halted res =>
              rw [hd] at hdisp
              exact hdisp

/-- Direct boundary determinism theorem (`extern "C"` / non-unwinding boundary):
Whenever a non-unwinding function (`bodyCanUnwind prog.strategy fn = false`) in a
post-`AbortUnwindingCalls` program hits an unwinding terminator in a non-cleanup block
with `u ≠ .cleanup _`, `dispatchUnwind` deterministically halts with `.terminated .abi _`
(zero UB, zero unwind escape). -/
theorem boundary_nonUnwinding_terminates_abi (prog : Program)
    (fn : FnBody) (cur : ActiveFrame) (stack : List CallerCont)
    (u : UnwindAction) (depth : Nat) (trace : List TraceEvent)
    (callUnw : Bool)
    (hnonUnw : bodyCanUnwind prog.strategy fn = false)
    (hnc : cur.inCleanup = false)
    (huWF : PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn)
      callUnw fn.blocks cur.inCleanup u)
    (huNE : u ≠ .unreachable)
    (huNoClean : ∀ pad, u ≠ .cleanup pad) :
    dispatchUnwind prog.fns cur stack u depth trace = .halted (.terminated .abi trace) := by
  cases u with
  | continue_ => exact absurd rfl (huWF.2.2 (Or.inr hnonUnw))
  | unreachable => exact absurd rfl huNE
  | cleanup pad => exact absurd rfl (huNoClean pad)
  | terminate r =>
    cases r with
    | abi => exact dispatchUnwind_terminate_eq
    | inCleanup =>
      have hpre := huWF.1
      unfold PrePassUnwindEdgeWF at hpre
      rw [hnc] at hpre
      cases hpre

theorem dispatchUnwind_never_returns_using_ih (prog : Program) (k : Nat)
    (ih : ∀ st', st'.cur.inCleanup = true → ∀ v trOut, runMir prog k st' ≠ .returned v trOut)
    (cur : ActiveFrame) (stk : List CallerCont) (u : UnwindAction)
    (depth : Nat) (tr : List TraceEvent) :
    ∀ v trOut,
      (match dispatchUnwind prog.fns cur stk u depth tr with
        | .running st' => runMir prog k st'
        | .halted res => res) ≠ .returned v trOut := by
  induction stk generalizing cur u with
  | nil =>
    cases u with
    | terminate _ => unfold dispatchUnwind; intro v trO h; cases h
    | unreachable => unfold dispatchUnwind; intro v trO h; cases h
    | continue_ => unfold dispatchUnwind; intro v trO h; cases h
    | cleanup padBB =>
      unfold dispatchUnwind
      cases h1 : listGet? prog.fns cur.fnId with
      | none => intro v trO h; cases h
      | some fn =>
        dsimp only
        cases h2 : listGet? fn.blocks padBB with
        | none => intro v trO h; cases h
        | some pb =>
          dsimp only
          cases h3 : pb.isCleanup with
          | false => intro v trO h; cases h
          | true => exact ih _ rfl
  | cons c rest ihStk =>
    cases u with
    | terminate _ => unfold dispatchUnwind; intro v trO h; cases h
    | unreachable => unfold dispatchUnwind; intro v trO h; cases h
    | continue_ => exact ihStk _ c.unwindOnCall
    | cleanup padBB =>
      unfold dispatchUnwind
      cases h1 : listGet? prog.fns cur.fnId with
      | none => intro v trO h; cases h
      | some fn =>
        dsimp only
        cases h2 : listGet? fn.blocks padBB with
        | none => intro v trO h; cases h
        | some pb =>
          dsimp only
          cases h3 : pb.isCleanup with
          | false => intro v trO h; cases h
          | true => exact ih _ rfl

/-- Cleanup frames never reach `.returned`: under `MirPrePassWF`, any state currently inside
or containing a cleanup block (`cur.inCleanup = true ∨ StackAnyCleanup stack`) can never halt
with `.returned v tr` in any number of steps. -/
theorem cleanup_never_returns_normally (prog : Program) (hpre : MirPrePassWF prog)
    (fuel : Nat) (st : MirState)
    (hclean : st.cur.inCleanup = true ∨ StackAnyCleanup st.stack) :
    ∀ v tr, runMir prog fuel st ≠ .returned v tr := by
  induction fuel generalizing st with
  | zero => unfold runMir; intro v tr h; cases h
  | succ k ih =>
    have ihC : ∀ st', st'.cur.inCleanup = true → ∀ v trOut, runMir prog k st' ≠ .returned v trOut :=
      fun st' hc => ih st' (Or.inl hc)
    unfold runMir
    cases hfn : listGet? prog.fns st.cur.fnId with
    | none =>
      unfold stepMir; rw [hfn]; intro v tr h; cases h
    | some fn =>
      cases hf : fn.isForeign with
      | true =>
        unfold stepMir; rw [hfn]; dsimp only; rw [hf]; intro v tr h; cases h
      | false =>
        have hfnWF := listGet?_listForall (PrePassFnWF prog) prog.fns st.cur.fnId fn hpre.2.2 hfn
        unfold PrePassFnWF at hfnWF; rw [hf] at hfnWF
        cases hblk : listGet? fn.blocks st.cur.bb with
        | none =>
          unfold stepMir; rw [hfn]; dsimp only; rw [hf]; dsimp only; rw [hblk]; intro v tr h; cases h
        | some blk =>
          have hblkWF := listGet?_listForall (PrePassBlockWF prog fn) fn.blocks st.cur.bb blk hfnWF.2.2 hblk
          cases hceq : boolEq st.cur.inCleanup blk.isCleanup with
          | false =>
            unfold stepMir; rw [hfn]; dsimp only; rw [hf]; dsimp only; rw [hblk]; dsimp only
            rw [hceq]; intro v tr h; cases h
          | true =>
            have hcleanEq : st.cur.inCleanup = blk.isCleanup := by
              cases h1 : st.cur.inCleanup <;> cases h2 : blk.isCleanup <;>
                rw [h1, h2] at hceq <;> cases hceq <;> rfl
            cases hs : listGet? blk.stmts st.cur.stmtIdx with
            | some stmt =>
              rw [stepMir_stmt_eq hfn hf hblk hcleanEq hs]
              cases stmt with
              | nop => unfold execStmt; dsimp only; exact ih _ hclean
              | emit _ => unfold execStmt; dsimp only; exact ih _ hclean
              | assignConst _ _ => unfold execStmt; dsimp only; exact ih _ hclean
              | assignLocal _ src =>
                unfold execStmt readLocal?; dsimp only
                cases hr : listGet? st.cur.locals src with
                | none => intro v tr h; cases h
                | some _ => dsimp only; exact ih _ hclean
            | none =>
              unfold stepMir; rw [hfn]; dsimp only; rw [hf]; dsimp only; rw [hblk]; dsimp only
              rw [hceq]; dsimp only; rw [hs]; dsimp only
              cases heq : natEq st.cur.stmtIdx (listLen blk.stmts) with
              | false => intro v tr h; cases h
              | true =>
                dsimp only
                have hterm := hblkWF.2
                cases ht : blk.term with
                | goto target =>
                  rw [ht] at hterm
                  obtain ⟨tblk, htblk, htclean⟩ := hterm
                  unfold execTerm; dsimp only
                  cases hclean with
                  | inl hcurC => exact ih _ (Or.inl hcurC)
                  | inr hstkC => exact ih _ (Or.inr hstkC)
                | branch cond z nz =>
                  rw [ht] at hterm
                  obtain ⟨_, ⟨b1, _, h1C⟩, ⟨b2, _, h2C⟩⟩ := hterm
                  unfold execTerm readLocal?; dsimp only
                  cases hr : listGet? st.cur.locals cond with
                  | none => intro v tr h; cases h
                  | some val =>
                    dsimp only
                    cases val with
                    | zero =>
                      cases hclean with
                      | inl hcurC => exact ih _ (Or.inl hcurC)
                      | inr hstkC => exact ih _ (Or.inr hstkC)
                    | succ _ =>
                      cases hclean with
                      | inl hcurC => exact ih _ (Or.inl hcurC)
                      | inr hstkC => exact ih _ (Or.inr hstkC)
                | return_ valReg =>
                  rw [ht] at hterm
                  have hcurNC : st.cur.inCleanup = false := by rw [hcleanEq, hterm.1]
                  unfold execTerm readLocal?; dsimp only
                  rw [hcurNC]; dsimp only
                  cases hr : listGet? st.cur.locals valReg with
                  | none => intro v tr h; cases h
                  | some val =>
                    dsimp only
                    cases hstk : st.stack with
                    | nil =>
                      exfalso
                      rw [hcurNC, hstk] at hclean
                      cases hclean with
                      | inl h1 => cases h1
                      | inr h2 => exact h2
                    | cons c rest =>
                      have hstkC : StackAnyCleanup (c :: rest) := by
                        rw [hcurNC, hstk] at hclean
                        cases hclean with
                        | inl h1 => cases h1
                        | inr h2 => exact h2
                      exact ih _ hstkC
                | unreachable => unfold execTerm; dsimp only; intro v tr h; cases h
                | unwindTerminate _ => unfold execTerm; dsimp only; intro v tr h; cases h
                | unwindResume =>
                  unfold execTerm; dsimp only
                  cases hcu : st.cur.inCleanup with
                  | false => intro v tr h; cases h
                  | true =>
                    dsimp only
                    cases hstk : st.stack with
                    | nil => intro v tr h; cases h
                    | cons c rest =>
                      exact dispatchUnwind_never_returns_using_ih prog k ihC _ rest c.unwindOnCall _ st.trace
                | call callee argReg dst rt u =>
                  unfold execTerm readLocal?; dsimp only
                  cases hr : listGet? st.cur.locals argReg with
                  | none => intro v tr h; cases h
                  | some argVal =>
                    dsimp only
                    unfold enterCall; dsimp only
                    cases hcget : listGet? prog.fns callee with
                    | none => intro v tr h; cases h
                    | some cfn =>
                      dsimp only
                      cases hcf : cfn.isForeign with
                      | false =>
                        dsimp only
                        exact ih _ (Or.inr hclean)
                      | true =>
                        dsimp only
                        cases hfo : prog.foreignSpecs callee argVal with
                        | ret _ _ =>
                          dsimp only
                          rw [ht] at hterm
                          obtain ⟨_, _, _, ⟨rblk, hrblk, hrC⟩, _⟩ := hterm
                          cases hclean with
                          | inl hcurC => exact ih _ (Or.inl hcurC)
                          | inr hstkC => exact ih _ (Or.inr hstkC)
                        | unwound _ =>
                          dsimp only
                          exact dispatchUnwind_never_returns_using_ih prog k ihC st.cur st.stack u _ _
                | drop df argReg rt u =>
                  unfold execTerm readLocal?; dsimp only
                  cases hr : listGet? st.cur.locals argReg with
                  | none => intro v tr h; cases h
                  | some argVal =>
                    dsimp only
                    unfold enterCall; dsimp only
                    cases hdget : listGet? prog.fns df with
                    | none => intro v tr h; cases h
                    | some dfn =>
                      dsimp only
                      cases hdf : dfn.isForeign with
                      | false =>
                        dsimp only
                        exact ih _ (Or.inr hclean)
                      | true =>
                        dsimp only
                        cases hfo : prog.foreignSpecs df argVal with
                        | ret _ _ =>
                          dsimp only
                          rw [ht] at hterm
                          obtain ⟨_, _, ⟨rblk, hrblk, hrC⟩, _⟩ := hterm
                          cases hclean with
                          | inl hcurC => exact ih _ (Or.inl hcurC)
                          | inr hstkC => exact ih _ (Or.inr hstkC)
                        | unwound _ =>
                          dsimp only
                          exact dispatchUnwind_never_returns_using_ih prog k ihC st.cur st.stack u _ _
                | panicCall u =>
                  unfold execTerm; dsimp only
                  cases hst0 : prog.strategy with
                  | abort => intro v tr h; cases h
                  | unwind =>
                    cases hts0 : prog.targetSupportsUnwinding with
                    | false => intro v tr h; cases h
                    | true =>
                      dsimp only
                      exact dispatchUnwind_never_returns_using_ih prog k ihC st.cur st.stack u _ st.trace

/-- Stack relation equating pre-pass and post-pass stacks on non-cleanup normal execution
(all frame data identical except `unwindOnCall` edges on saved continuations). -/
noncomputable def NormalStackRel (prog : Program) : List CallerCont → List CallerCont → Prop
  | [], [] => True
  | c1 :: s1, c2 :: s2 =>
    c1.fnId = c2.fnId ∧
    c1.locals = c2.locals ∧
    c1.inCleanup = c2.inCleanup ∧
    c1.inCleanup = false ∧
    c1.retDst = c2.retDst ∧
    c1.retTarget = c2.retTarget ∧
    (∃ fn, listGet? prog.fns c1.fnId = some fn ∧ fn.isForeign = false) ∧
    NormalStackRel prog s1 s2
  | _, _ => False

/-- State relation equating pre-pass and post-pass runtime states during non-cleanup
normal execution. -/
noncomputable def NormalStateRel (prog : Program) (st1 st2 : MirState) : Prop :=
  st1.cur = st2.cur ∧
  st1.cur.inCleanup = false ∧
  st1.cleanupDepth = st2.cleanupDepth ∧
  st1.trace = st2.trace ∧
  NormalStackRel prog st1.stack st2.stack

theorem abortUnwindingCalls_preserves_returned_run (prog : Program) (hpre : MirPrePassWF prog)
    (fuel : Nat) (st1 st2 : MirState) (hrel : NormalStateRel prog st1 st2)
    (v : Nat) (tr : List TraceEvent) (hret : runMir prog fuel st1 = .returned v tr) :
    runMir (abortUnwindingCallsProg prog) fuel st2 = .returned v tr := by
  induction fuel generalizing st1 st2 with
  | zero => unfold runMir at hret; cases hret
  | succ k ih =>
    have ihC : ∀ st', st'.cur.inCleanup = true → ∀ v' trOut, runMir prog k st' ≠ .returned v' trOut :=
      fun st' hc => cleanup_never_returns_normally prog hpre k st' (Or.inl hc)
    obtain ⟨hcur, hnc1, hdep, htr, hstk⟩ := hrel
    unfold runMir at hret ⊢
    cases hfn1 : listGet? prog.fns st1.cur.fnId with
    | none =>
      unfold stepMir at hret; rw [hfn1] at hret; cases hret
    | some fn =>
      have hfnWF := listGet?_listForall (PrePassFnWF prog) prog.fns st1.cur.fnId fn hpre.2.2 hfn1
      cases hf : fn.isForeign with
      | true =>
        unfold stepMir at hret; rw [hfn1] at hret; dsimp only at hret; rw [hf] at hret; cases hret
      | false =>
        unfold PrePassFnWF at hfnWF; rw [hf] at hfnWF
        have hfn2 : listGet? (abortUnwindingCallsProg prog).fns st2.cur.fnId =
            some (abortUnwindingFn prog fn) := by
          unfold abortUnwindingCallsProg; dsimp only; rw [← hcur, listGet?_listMap, hfn1]
        have hm := abortUnwindingFn_preserves_metadata prog fn
        have hblocks := abortUnwindingFn_blocks_nonForeign prog fn hf
        cases hblk1 : listGet? fn.blocks st1.cur.bb with
        | none =>
          unfold stepMir at hret; rw [hfn1] at hret; dsimp only at hret
          rw [hf] at hret; dsimp only at hret; rw [hblk1] at hret; cases hret
        | some blk =>
          have hblkWF := listGet?_listForall (PrePassBlockWF prog fn) fn.blocks st1.cur.bb blk hfnWF.2.2 hblk1
          have hblk2 : listGet? (abortUnwindingFn prog fn).blocks st2.cur.bb =
              some (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) blk) := by
            rw [hblocks, ← hcur, listGet?_listMap, hblk1]
          cases hceq : boolEq st1.cur.inCleanup blk.isCleanup with
          | false =>
            unfold stepMir at hret
            rw [hfn1] at hret; dsimp only at hret
            rw [hf] at hret; dsimp only at hret
            rw [hblk1] at hret; dsimp only at hret
            rw [hceq] at hret; cases hret
          | true =>
            have hcleanEq : st1.cur.inCleanup = blk.isCleanup := by
              cases h1 : st1.cur.inCleanup <;> cases h2 : blk.isCleanup <;>
                rw [h1, h2] at hceq <;> cases hceq <;> rfl
            have hcleanEq2 : st2.cur.inCleanup =
                (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) blk).isCleanup := by
              rw [← hcur]; exact hcleanEq
            cases hs1 : listGet? blk.stmts st1.cur.stmtIdx with
            | some stmt =>
              have hs2 : listGet? (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) blk).stmts
                  st2.cur.stmtIdx = some stmt := by
                rw [← hcur]; exact hs1
              rw [stepMir_stmt_eq hfn1 hf hblk1 hcleanEq hs1] at hret
              rw [stepMir_stmt_eq hfn2 (hm.1.trans hf) hblk2 hcleanEq2 hs2]
              cases stmt with
              | nop =>
                unfold execStmt at hret ⊢; dsimp only at hret ⊢
                refine ih _ _ ?_ hret
                exact ⟨by rw [hcur], hnc1, hdep, htr, hstk⟩
              | emit ev =>
                unfold execStmt at hret ⊢; dsimp only at hret ⊢
                refine ih _ _ ?_ hret
                exact ⟨by rw [hcur], hnc1, hdep, by rw [htr], hstk⟩
              | assignConst dst val =>
                unfold execStmt at hret ⊢; dsimp only at hret ⊢
                refine ih _ _ ?_ hret
                exact ⟨by rw [hcur], hnc1, hdep, htr, hstk⟩
              | assignLocal dst src =>
                unfold execStmt readLocal? at hret ⊢; dsimp only at hret ⊢
                cases hr1 : listGet? st1.cur.locals src with
                | none => rw [hr1] at hret; cases hret
                | some val =>
                  have hr2 : listGet? st2.cur.locals src = some val := by rw [← hcur]; exact hr1
                  rw [hr1] at hret
                  rw [hr2]; dsimp only at hret ⊢
                  refine ih _ _ ?_ hret
                  exact ⟨by rw [hcur], hnc1, hdep, htr, hstk⟩
            | none =>
              have hs2 : listGet? (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) blk).stmts
                  st2.cur.stmtIdx = none := by
                rw [← hcur]; exact hs1
              cases hnat : natEq st1.cur.stmtIdx (listLen blk.stmts) with
              | false =>
                unfold stepMir at hret
                rw [hfn1] at hret; dsimp only at hret
                rw [hf] at hret; dsimp only at hret
                rw [hblk1] at hret; dsimp only at hret
                rw [hceq] at hret; dsimp only at hret
                rw [hs1] at hret; dsimp only at hret
                rw [hnat] at hret; cases hret
              | true =>
                have heqLen : st1.cur.stmtIdx = listLen blk.stmts := natEq_eq hnat
                have heqLen2 : st2.cur.stmtIdx =
                    listLen (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn) blk).stmts := by
                  rw [← hcur]; exact heqLen
                rw [stepMir_term_eq hfn1 hf hblk1 hcleanEq hs1 heqLen] at hret
                rw [stepMir_term_eq hfn2 (hm.1.trans hf) hblk2 hcleanEq2 hs2 heqLen2]
                have hblkC : blk.isCleanup = false := by
                  cases hbc : blk.isCleanup with
                  | false => rfl
                  | true => rw [hnc1, hbc] at hceq; cases hceq
                have hpt := hblkWF.2
                cases ht : blk.term with
                | goto target =>
                  rw [ht] at hret
                  unfold abortUnwindingBlock abortUnwindingTerm; rw [ht]
                  unfold execTerm at hret ⊢
                  dsimp only at hret ⊢
                  refine ih _ _ ?_ hret
                  exact ⟨by rw [hcur], hnc1, hdep, htr, hstk⟩
                | branch cond z nz =>
                  rw [ht] at hret
                  unfold abortUnwindingBlock abortUnwindingTerm; rw [ht]
                  unfold execTerm readLocal? at hret ⊢
                  dsimp only at hret ⊢
                  cases hr1 : listGet? st1.cur.locals cond with
                  | none => rw [hr1] at hret; cases hret
                  | some val =>
                    have hr2 : listGet? st2.cur.locals cond = some val := by rw [← hcur]; exact hr1
                    rw [hr1] at hret
                    rw [hr2]; dsimp only at hret ⊢
                    cases val with
                    | zero =>
                      refine ih _ _ ?_ hret
                      exact ⟨by rw [hcur], hnc1, hdep, htr, hstk⟩
                    | succ _ =>
                      refine ih _ _ ?_ hret
                      exact ⟨by rw [hcur], hnc1, hdep, htr, hstk⟩
                | return_ valReg =>
                  rw [ht] at hret
                  unfold abortUnwindingBlock abortUnwindingTerm; rw [ht]
                  unfold execTerm readLocal? at hret ⊢
                  dsimp only at hret ⊢
                  rw [hnc1] at hret
                  rw [← hcur, hnc1]; dsimp only at hret ⊢
                  cases hr1 : listGet? st1.cur.locals valReg with
                  | none => rw [hr1] at hret; cases hret
                  | some val =>
                    rw [hr1] at hret
                    dsimp only at hret ⊢
                    cases hstk1 : st1.stack with
                    | nil =>
                      rw [hstk1] at hstk hret
                      cases hstk2 : st2.stack with
                      | nil => rw [htr] at hret; exact hret
                      | cons _ _ => rw [hstk2] at hstk; cases hstk
                    | cons c1 rest1 =>
                      rw [hstk1] at hstk hret
                      cases hstk2 : st2.stack with
                      | nil => rw [hstk2] at hstk; cases hstk
                      | cons c2 rest2 =>
                        rw [hstk2] at hstk
                        obtain ⟨hcFn, hcLoc, hcInc, hcIncF, hcDst, hcRet, _, hrest⟩ := hstk
                        refine ih _ _ ?_ hret
                        exact ⟨by rw [hcFn, hcRet, hcDst, hcLoc, hcInc], hcIncF, hdep, htr, hrest⟩
                | unreachable => rw [ht] at hret; unfold execTerm at hret; dsimp only at hret; cases hret
                | unwindTerminate _ => rw [ht] at hret; unfold execTerm at hret; dsimp only at hret; cases hret
                | unwindResume =>
                  rw [ht] at hpt
                  rw [hblkC] at hpt; cases hpt
                | call callee argReg dst rt u =>
                  rw [ht] at hret
                  unfold abortUnwindingBlock abortUnwindingTerm; rw [ht]
                  unfold execTerm readLocal? at hret ⊢
                  dsimp only at hret ⊢
                  rw [hblkC]; dsimp only at hret ⊢
                  cases hr1 : listGet? st1.cur.locals argReg with
                  | none => rw [hr1] at hret; cases hret
                  | some argVal =>
                    have hr2 : listGet? st2.cur.locals argReg = some argVal := by rw [← hcur]; exact hr1
                    rw [hr1] at hret
                    rw [hr2]; dsimp only at hret ⊢
                    unfold enterCall at hret ⊢
                    dsimp only at hret ⊢
                    cases hcget : listGet? prog.fns callee with
                    | none => rw [hcget] at hret; cases hret
                    | some cfn =>
                      have hcget2 : listGet? (abortUnwindingCallsProg prog).fns callee =
                          some (abortUnwindingFn prog cfn) := by
                        unfold abortUnwindingCallsProg; dsimp only; rw [listGet?_listMap, hcget]
                      have hcm := abortUnwindingFn_preserves_metadata prog cfn
                      rw [hcget] at hret
                      rw [hcget2]; dsimp only at hret ⊢
                      rw [hcm.1, hcm.2.1]
                      cases hcf : cfn.isForeign with
                      | false =>
                        rw [hcf] at hret
                        dsimp only at hret ⊢
                        refine ih _ _ ?_ hret
                        refine ⟨rfl, rfl, hdep, htr, ?_⟩
                        exact ⟨by rw [hcur], by rw [hcur], by rw [hcur], hnc1, rfl, rfl,
                          ⟨fn, hfn1, hf⟩, hstk⟩
                      | true =>
                        rw [hcf] at hret
                        dsimp only [abortUnwindingCallsProg] at hret ⊢
                        cases hfo : prog.foreignSpecs callee argVal with
                        | ret retV evOpt =>
                          rw [hfo] at hret
                          dsimp only at hret ⊢
                          refine ih _ _ ?_ hret
                          exact ⟨by rw [hcur], hnc1, hdep, by rw [htr], hstk⟩
                        | unwound evOpt =>
                          rw [hfo] at hret
                          dsimp only at hret
                          exfalso
                          exact dispatchUnwind_never_returns_using_ih prog k ihC st1.cur st1.stack u
                            st1.cleanupDepth (appendOptEvent st1.trace evOpt) v tr hret
                | drop df argReg rt u =>
                  rw [ht] at hret
                  unfold abortUnwindingBlock abortUnwindingTerm; rw [ht]
                  unfold execTerm readLocal? at hret ⊢
                  dsimp only at hret ⊢
                  rw [hblkC]; dsimp only at hret ⊢
                  cases hr1 : listGet? st1.cur.locals argReg with
                  | none => rw [hr1] at hret; cases hret
                  | some argVal =>
                    have hr2 : listGet? st2.cur.locals argReg = some argVal := by rw [← hcur]; exact hr1
                    rw [hr1] at hret
                    rw [hr2]; dsimp only at hret ⊢
                    unfold enterCall at hret ⊢
                    dsimp only at hret ⊢
                    cases hdget : listGet? prog.fns df with
                    | none => rw [hdget] at hret; cases hret
                    | some dfn =>
                      have hdget2 : listGet? (abortUnwindingCallsProg prog).fns df =
                          some (abortUnwindingFn prog dfn) := by
                        unfold abortUnwindingCallsProg; dsimp only; rw [listGet?_listMap, hdget]
                      have hdm := abortUnwindingFn_preserves_metadata prog dfn
                      rw [hdget] at hret
                      rw [hdget2]; dsimp only at hret ⊢
                      rw [hdm.1, hdm.2.1]
                      cases hdf : dfn.isForeign with
                      | false =>
                        rw [hdf] at hret
                        dsimp only at hret ⊢
                        refine ih _ _ ?_ hret
                        refine ⟨rfl, rfl, hdep, htr, ?_⟩
                        exact ⟨by rw [hcur], by rw [hcur], by rw [hcur], hnc1, rfl, rfl,
                          ⟨fn, hfn1, hf⟩, hstk⟩
                      | true =>
                        rw [hdf] at hret
                        dsimp only [abortUnwindingCallsProg] at hret ⊢
                        cases hfo : prog.foreignSpecs df argVal with
                        | ret retV evOpt =>
                          rw [hfo] at hret
                          dsimp only at hret ⊢
                          refine ih _ _ ?_ hret
                          exact ⟨by rw [hcur], hnc1, hdep, by rw [htr], hstk⟩
                        | unwound evOpt =>
                          rw [hfo] at hret
                          dsimp only at hret
                          exfalso
                          exact dispatchUnwind_never_returns_using_ih prog k ihC st1.cur st1.stack u
                            st1.cleanupDepth (appendOptEvent st1.trace evOpt) v tr hret
                | panicCall u =>
                  rw [ht] at hret
                  unfold execTerm at hret; dsimp only at hret
                  cases hstrat : prog.strategy with
                  | unwind =>
                    cases hts0 : prog.targetSupportsUnwinding with
                    | false => rw [hstrat, hts0] at hret; dsimp only at hret; cases hret
                    | true =>
                      rw [hstrat, hts0] at hret; dsimp only at hret
                      exfalso
                      exact dispatchUnwind_never_returns_using_ih prog k ihC st1.cur st1.stack u
                        st1.cleanupDepth st1.trace v tr hret
                  | abort => rw [hstrat] at hret; dsimp only at hret; cases hret

theorem abortUnwindingCalls_preserves_returned (prog : Program) (hpre : MirPrePassWF prog)
    (fuel arg v : Nat) (tr : List TraceEvent)
    (hret : evalMirProg prog fuel arg = .returned v tr) :
    evalMirProg (abortUnwindingCallsProg prog) fuel arg = .returned v tr := by
  unfold evalMirProg initMirState at hret ⊢
  unfold abortUnwindingCallsProg; dsimp only
  rw [listGet?_listMap]
  cases he1 : listGet? prog.fns prog.entryFn with
  | none => rw [he1] at hret; cases hret
  | some entry =>
    rw [he1] at hret
    have hm := abortUnwindingFn_preserves_metadata prog entry
    dsimp only at hret ⊢
    rw [hm.2.1]
    refine abortUnwindingCalls_preserves_returned_run prog hpre fuel _ _ ?_ v tr hret
    exact ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- **MAIN THEOREM 1 — `AbortUnwindingCalls` Exact Soundness**:
For any pre-pass well-formed MIR program `prog` obeying `ForeignContractOK` and
`PrePassNoBogusUnreachable`, `prog' := abortUnwindingCallsProg prog`:
1. Satisfies `MirPostPassWF prog'`, `ForeignContractOK prog'`, and `PostPassNoBogusUnreachable prog'`.
2. Never exhibits `.ub` or `.invalid` (`¬ mirIsBad`) for any fuel or argument.
3. If its entry function cannot unwind (`bodyCanUnwind prog.strategy entry = false`,
   e.g. `extern "C"` or `#[rustc_nounwind]`), no unwinding frame can ever escape the entry
   boundary (`evalMirProg prog' fuel arg ≠ .unwound tr`).
4. Preserves all normal-return behaviors and traces identically (`evalMirProg_returned`). -/
theorem abortUnwindingCalls_exact_soundness (prog : Program)
    (hpre : MirPrePassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PrePassNoBogusUnreachable prog) :
    let prog' := abortUnwindingCallsProg prog
    MirPostPassWF prog' ∧
    ForeignContractOK prog' ∧
    PostPassNoBogusUnreachable prog' ∧
    (∀ fuel arg, ¬ mirIsBad (evalMirProg prog' fuel arg)) ∧
    (∀ entry, listGet? prog.fns prog.entryFn = some entry →
      bodyCanUnwind prog.strategy entry = false →
      ∀ fuel arg tr, evalMirProg prog' fuel arg ≠ .unwound tr) ∧
    (∀ fuel arg v tr, evalMirProg prog fuel arg = .returned v tr →
      evalMirProg prog' fuel arg = .returned v tr) := by
  intro prog'
  have hpost := abortUnwindingCallsProg_postWF prog hpre
  have hfok' := abortUnwindingCalls_preserves_foreignContract prog hfok
  have hpostNB := abortUnwindingCallsProg_postNoBogus prog hpre hnob
  refine ⟨hpost, hfok', hpostNB, ?_, ?_, ?_⟩
  · intro fuel arg
    exact evalMirProg_safe prog' hpost hfok' hpostNB fuel arg
  · intro entry hentry hnoUnw fuel arg tr
    obtain ⟨st, hinit, hsafe⟩ := initMirState_runtimeSafe prog' arg hpost
    unfold evalMirProg; rw [hinit]
    have hbot : stackBottomFn st.stack st.cur.fnId = prog'.entryFn := by
      unfold initMirState at hinit
      cases hget : listGet? prog'.fns prog'.entryFn with
      | none => rw [hget] at hinit; cases hinit
      | some _ =>
        rw [hget] at hinit; cases hinit
        unfold stackBottomFn; rfl
    have hentry' : listGet? prog'.fns prog'.entryFn = some (abortUnwindingFn prog entry) := by
      unfold prog' abortUnwindingCallsProg; dsimp only; rw [listGet?_listMap, hentry]
    have hnoUnw' : bodyCanUnwind prog'.strategy (abortUnwindingFn prog entry) = false := by
      unfold prog'; dsimp only [abortUnwindingCallsProg]
      rw [abortUnwindingCalls_preserves_bodyCanUnwind]
      exact hnoUnw
    exact entry_nonUnwinding_never_unwound_run prog' hpost hfok' hpostNB (abortUnwindingFn prog entry)
      hentry' hnoUnw' fuel st hsafe hbot tr
  · intro fuel arg v tr hret
    exact abortUnwindingCalls_preserves_returned prog hpre fuel arg v tr hret

/-! ## Section 10: Main Theorem 2 — Double-Panic `InCleanup` Termination Invariant -/

/-- Predicate asserting that some caller frame on `stack` is actively guarding a cleanup block
(`c.unwindOnCall = .terminate .inCleanup`). Every `.drop` / `.call` emitted inside an
`isCleanup = true` block establishes this guard on the stack (`PrePassTermWF` + `PostPassTermWF`). -/
noncomputable def StackHasCleanupGuard : List CallerCont → Prop
  | [] => False
  | c :: rest => c.unwindOnCall = .terminate .inCleanup ∨ StackHasCleanupGuard rest

/-- Direct immediate double-panic theorem inside any cleanup block (`st.cur.inCleanup = true`):
When execution in a cleanup block hits a `panicCall` under `-C panic=unwind` with
`targetSupportsUnwinding = true`, `stepMir` deterministically halts immediately with
`.halted (.terminated .inCleanup _)`. -/
theorem double_panic_direct_inCleanup (prog : Program)
    (hpost : MirPostPassWF prog) (st : MirState)
    (fn : FnBody) (blk : BasicBlock)
    (hfn : listGet? prog.fns st.cur.fnId = some fn)
    (hnonF : fn.isForeign = false)
    (hblk : listGet? fn.blocks st.cur.bb = some blk)
    (hclean : st.cur.inCleanup = true)
    (hblkC : blk.isCleanup = true)
    (hidx : st.cur.stmtIdx = listLen blk.stmts)
    (hstrat : prog.strategy = .unwind) (hts : prog.targetSupportsUnwinding = true)
    (u : UnwindAction) (ht : blk.term = .panicCall u) :
    stepMir prog st = .halted (.terminated .inCleanup st.trace) := by
  have hfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns st.cur.fnId fn hpost.2.2 hfn
  unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
  have hblkWF := listGet?_listForall (PostPassBlockWF prog fn) fn.blocks st.cur.bb blk hfnWF.2.2 hblk
  have hpt := hblkWF.2.1; rw [ht, hblkC] at hpt
  have huInC : u = .terminate .inCleanup := hpt.2 rfl
  have hceq : st.cur.inCleanup = blk.isCleanup := by rw [hclean, hblkC]
  have hnone : listGet? blk.stmts st.cur.stmtIdx = none := by
    rw [hidx]; exact listGet?_ge_len_none _ _ (natLe_refl _)
  rw [stepMir_term_eq hfn hnonF hblk hceq hnone hidx, ht]
  unfold execTerm
  rw [hstrat, hts, huInC]
  exact dispatchUnwind_terminate_eq

/-- Direct foreign-drop / foreign-call double-panic inside a cleanup block (`st.cur.inCleanup = true`):
When a `.call` inside cleanup yields an `.unwound evOpt` outcome from a foreign item,
`stepMir` immediately halts with `.halted (.terminated .inCleanup (appendOptEvent st.trace evOpt))`. -/
theorem double_panic_foreign_inCleanup (prog : Program)
    (hpost : MirPostPassWF prog) (st : MirState)
    (fn : FnBody) (blk : BasicBlock)
    (hfn : listGet? prog.fns st.cur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hblk : listGet? fn.blocks st.cur.bb = some blk)
    (hclean : st.cur.inCleanup = true) (hblkC : blk.isCleanup = true)
    (hidx : st.cur.stmtIdx = listLen blk.stmts)
    (callee : FnId) (argReg dst rt : LocalId) (u : UnwindAction)
    (ht : blk.term = .call callee argReg dst rt u)
    (argVal : Nat) (harg : readLocal? st.cur.locals argReg = some argVal)
    (cfn : FnBody) (hcfn : listGet? prog.fns callee = some cfn) (hcf : cfn.isForeign = true)
    (evOpt : Option TraceEvent) (hfo : prog.foreignSpecs callee argVal = .unwound evOpt) :
    stepMir prog st = .halted (.terminated .inCleanup (appendOptEvent st.trace evOpt)) := by
  have hfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns st.cur.fnId fn hpost.2.2 hfn
  unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
  have hblkWF := listGet?_listForall (PostPassBlockWF prog fn) fn.blocks st.cur.bb blk hfnWF.2.2 hblk
  have hpt := hblkWF.2.1; rw [ht, hblkC] at hpt
  have huInC : u = .terminate .inCleanup := hpt.2.2.2.2.2 rfl
  have hceq : st.cur.inCleanup = blk.isCleanup := by rw [hclean, hblkC]
  have hnone : listGet? blk.stmts st.cur.stmtIdx = none := by
    rw [hidx]; exact listGet?_ge_len_none _ _ (natLe_refl _)
  rw [stepMir_term_eq hfn hnonF hblk hceq hnone hidx, ht]
  unfold execTerm; dsimp only
  rw [harg]; dsimp only
  unfold enterCall; dsimp only
  rw [hcfn]; dsimp only
  rw [hcf]; dsimp only
  rw [hfo, huInC]; dsimp only
  exact dispatchUnwind_terminate_eq

/-- Unwinding past a `StackHasCleanupGuard` continuation can never reach `.unwound`:
every unwinding pop across a cleanup-guarded stack hits either `.cleanup` (staying inside an
inner cleanup) or `.terminated .inCleanup` (or an earlier `.terminated`) before ever exiting. -/
theorem dispatchUnwind_cleanupGuard_never_unwound (prog : Program)
    (cur : ActiveFrame) (stack : List CallerCont) (u : UnwindAction)
    (depth : Nat) (trace : List TraceEvent)
    (fn : FnBody) (hfn : listGet? prog.fns cur.fnId = some fn)
    (huWF : PostPassUnwindEdgeWF prog.targetSupportsUnwinding (bodyCanUnwind prog.strategy fn)
      true fn.blocks cur.inCleanup u)
    (hstack : StackPostWF prog (bodyCanUnwind prog.strategy fn) stack)
    (hguard : cur.inCleanup = true ∨ StackHasCleanupGuard stack) :
    match dispatchUnwind prog.fns cur stack u depth trace with
    | .running st' => st'.cur.inCleanup = true ∨ StackHasCleanupGuard st'.stack
    | .halted res => (∀ tr, res ≠ .unwound tr) ∧ (u = .terminate .inCleanup → res = .terminated .inCleanup trace) := by
  induction stack generalizing cur fn u depth with
  | nil =>
    have hcurC : cur.inCleanup = true := by
      cases hguard with
      | inl hc => exact hc
      | inr hs => exact hs.elim
    cases u with
    | terminate r =>
      rw [dispatchUnwind_terminate_eq]
      refine ⟨(fun tr h => by cases h), (fun heq => by cases heq; rfl)⟩
    | unreachable =>
      unfold dispatchUnwind
      refine ⟨(fun tr h => by cases h), (fun heq => by cases heq)⟩
    | continue_ =>
      have hbad := huWF.1; unfold PrePassUnwindEdgeWF at hbad
      rw [hcurC] at hbad; cases hbad
    | cleanup padBB =>
      have hbad := huWF.1; unfold PrePassUnwindEdgeWF at hbad
      rw [hcurC] at hbad; cases hbad.1
  | cons c rest ih =>
    cases u with
    | terminate r =>
      rw [dispatchUnwind_terminate_eq]
      refine ⟨(fun tr h => by cases h), (fun heq => by cases heq; rfl)⟩
    | unreachable =>
      unfold dispatchUnwind
      refine ⟨(fun tr h => by cases h), (fun heq => by cases heq)⟩
    | cleanup padBB =>
      obtain ⟨_, padBlk, hpadGet, hpadC⟩ := huWF.1
      rw [dispatchUnwind_cleanup_eq hfn hpadGet hpadC]
      exact Or.inl rfl
    | continue_ =>
      have hncCur : cur.inCleanup = false := huWF.1
      have hguardStk : StackHasCleanupGuard (c :: rest) := by
        cases hguard with
        | inl hc => rw [hncCur] at hc; cases hc
        | inr hs => exact hs
      have hbu : bodyCanUnwind prog.strategy fn = true := by
        cases hb : bodyCanUnwind prog.strategy fn
        · exact absurd rfl (huWF.2.2 (Or.inr hb))
        · rfl
      obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstack
      obtain ⟨cfn', _, hcfn', _, _, _, _, _, hcEdge, _⟩ := hcWF
      have hcfnEq : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
      rw [hcfnEq] at hcEdge
      rw [hbu] at hcEdge
      unfold dispatchUnwind; dsimp only
      cases hguardStk with
      | inl hcTerm =>
        rw [hcTerm, dispatchUnwind_terminate_eq]
        exact ⟨(fun tr h => by cases h), (fun heq => by cases heq)⟩
      | inr hrestG =>
        have hih := ih { fnId := c.fnId, bb := c.retTarget, stmtIdx := 0, locals := c.locals, inCleanup := c.inCleanup }
          c.unwindOnCall depth cfn hcfn hcEdge hrestWF (Or.inr hrestG)
        cases hdisp : dispatchUnwind prog.fns
            { fnId := c.fnId, bb := c.retTarget, stmtIdx := 0, locals := c.locals, inCleanup := c.inCleanup }
            rest c.unwindOnCall depth trace with
        | running st' => rw [hdisp] at hih; exact hih
        | halted res => rw [hdisp] at hih; exact ⟨hih.1, (fun hbad => by cases hbad)⟩

/-- Executing a `.drop` inside a cleanup block (`st.cur.inCleanup = true`, local drop glue `dfn`)
establishes `StackHasCleanupGuard st'.stack` with the top saved frame carrying `unwindOnCall = .terminate .inCleanup`. -/
theorem cleanup_drop_establishes_guard (prog : Program)
    (hpost : MirPostPassWF prog) (st : MirState) (hsafe : MirRuntimeSafe prog st)
    (fn : FnBody) (blk : BasicBlock)
    (hfn : listGet? prog.fns st.cur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hblk : listGet? fn.blocks st.cur.bb = some blk)
    (hclean : st.cur.inCleanup = true) (hblkC : blk.isCleanup = true)
    (hidx : st.cur.stmtIdx = listLen blk.stmts)
    (df : FnId) (argReg rt : LocalId) (u : UnwindAction)
    (ht : blk.term = .drop df argReg rt u)
    (dfn : FnBody) (hdfn : listGet? prog.fns df = some dfn) (hdfNonF : dfn.isForeign = false) :
    ∃ argVal st',
      readLocal? st.cur.locals argReg = some argVal ∧
      stepMir prog st = .running st' ∧
      StackHasCleanupGuard st'.stack := by
  obtain ⟨fn', hfn', hact, _⟩ := hsafe
  obtain ⟨fn'', blk', hfn'', _, hblk', _, _, hlocals⟩ := hact
  have hfnEq2 : fn'' = fn := by rw [hfn] at hfn''; cases hfn''; rfl
  rw [hfnEq2] at hlocals
  have hfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns st.cur.fnId fn hpost.2.2 hfn
  unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
  have hblkWF := listGet?_listForall (PostPassBlockWF prog fn) fn.blocks st.cur.bb blk hfnWF.2.2 hblk
  have hpt := hblkWF.2.1; rw [ht, hblkC] at hpt
  obtain ⟨hargLt, _, _, _, huClean⟩ := hpt
  have huInC : u = .terminate .inCleanup := huClean rfl
  rw [← hlocals] at hargLt
  obtain ⟨argVal, harg⟩ := listGet?_lt_len st.cur.locals argReg hargLt
  let cont : CallerCont := {
    fnId := st.cur.fnId,
    locals := st.cur.locals,
    inCleanup := st.cur.inCleanup,
    retDst := 0,
    retTarget := rt,
    unwindOnCall := u
  }
  let nextFrame : ActiveFrame := {
    fnId := df,
    bb := 0,
    stmtIdx := 0,
    locals := initLocals dfn.localCount argVal,
    inCleanup := false
  }
  let st' : MirState := {
    cur := nextFrame,
    stack := cont :: st.stack,
    cleanupDepth := st.cleanupDepth,
    trace := st.trace
  }
  refine ⟨argVal, st', harg, ?_, ?_⟩
  · have hceq : st.cur.inCleanup = blk.isCleanup := by rw [hclean, hblkC]
    have hnone : listGet? blk.stmts st.cur.stmtIdx = none := by
      rw [hidx]; exact listGet?_ge_len_none _ _ (natLe_refl _)
    rw [stepMir_term_eq hfn hnonF hblk hceq hnone hidx, ht]
    unfold execTerm readLocal?; dsimp only
    rw [harg]; dsimp only
    unfold enterCall; dsimp only
    rw [hdfn]; dsimp only
    rw [hdfNonF]
  · exact Or.inl huInC

/-- Step-level invariance theorem for `StackHasCleanupGuard`: from ANY safe state `st` carrying
`StackHasCleanupGuard st.stack`, `stepMir prog st` can NEVER produce `.halted (.unwound _)`,
NEVER produces `.halted (.returned _ _)`, NEVER produces `.halted (.ub _)` / `.halted (.invalid _)`,
and every `.running st'` preserves `(st'.cur.inCleanup = true ∨ StackHasCleanupGuard st'.stack)`. -/
theorem cleanupGuard_step_preserves_and_blocks_escape (prog : Program)
    (hpost : MirPostPassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PostPassNoBogusUnreachable prog) (st : MirState)
    (hsafe : MirRuntimeSafe prog st)
    (hguard : StackHasCleanupGuard st.stack) :
    match stepMir prog st with
    | .running st' => MirRuntimeSafe prog st' ∧ (st'.cur.inCleanup = true ∨ StackHasCleanupGuard st'.stack)
    | .halted res => ¬ mirIsBad res ∧ (∀ tr, res ≠ .unwound tr) ∧ (∀ v tr, res ≠ .returned v tr) := by
  have hsafeCopy := hsafe
  have hs := stepMir_preserves_safe prog hpost hfok hnob st hsafeCopy
  obtain ⟨fn, hfn, hact, hstack, hstackNB, hdepth, htsc, htss⟩ := hsafe
  obtain ⟨fn', blk, hfn', hnonF, hblk, hcleanEq, hstmtLe, hlocals⟩ := hact
  have hfnEq : fn' = fn := by rw [hfn] at hfn'; cases hfn'; rfl
  rw [hfnEq] at hnonF hblk hlocals
  have hfnWF := listGet?_listForall (PostPassFnWF prog) prog.fns st.cur.fnId fn hpost.2.2 hfn
  unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
  have hblkWF := listGet?_listForall (PostPassBlockWF prog fn) fn.blocks st.cur.bb blk hfnWF.2.2 hblk
  cases hstGet : listGet? blk.stmts st.cur.stmtIdx with
  | some stmt =>
    rw [stepMir_stmt_eq hfn hnonF hblk hcleanEq hstGet] at hs ⊢
    cases stmt with
    | nop => unfold execStmt at hs ⊢; dsimp only at hs ⊢; exact ⟨hs, Or.inr hguard⟩
    | emit _ => unfold execStmt at hs ⊢; dsimp only at hs ⊢; exact ⟨hs, Or.inr hguard⟩
    | assignConst _ _ => unfold execStmt at hs ⊢; dsimp only at hs ⊢; exact ⟨hs, Or.inr hguard⟩
    | assignLocal _ src =>
      unfold execStmt readLocal? at hs ⊢; dsimp only at hs ⊢
      cases hr : listGet? st.cur.locals src with
      | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
      | some _ => rw [hr] at hs; dsimp only at hs ⊢; exact ⟨hs, Or.inr hguard⟩
  | none =>
    have heqLen : st.cur.stmtIdx = listLen blk.stmts :=
      listGet?_eq_none_implies_ge blk.stmts st.cur.stmtIdx hstGet hstmtLe
    rw [stepMir_term_eq hfn hnonF hblk hcleanEq hstGet heqLen] at hs ⊢
    have htermWF := hblkWF.2
    cases ht : blk.term with
    | goto _ => rw [ht] at hs; unfold execTerm at hs ⊢; dsimp only at hs ⊢; exact ⟨hs, Or.inr hguard⟩
    | branch cond _ _ =>
      rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
      cases hr : listGet? st.cur.locals cond with
      | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
      | some v => rw [hr] at hs; dsimp only at hs ⊢; cases v <;> exact ⟨hs, Or.inr hguard⟩
    | return_ valReg =>
      rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
      cases hinc : st.cur.inCleanup with
      | true => rw [hinc] at hs; dsimp only at hs; exact absurd trivial hs
      | false =>
        rw [hinc] at hs; dsimp only at hs ⊢
        cases hr : listGet? st.cur.locals valReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some v =>
          rw [hr] at hs; dsimp only at hs ⊢
          cases hstk : st.stack with
          | nil => rw [hstk] at hguard; exact absurd hguard (fun h => h)
          | cons c rest =>
            rw [hstk] at hs hguard hstack; dsimp only at hs ⊢
            obtain ⟨cfn, hcfn, hcWF, _⟩ := hstack
            obtain ⟨_, _, _, _, _, _, _, _, hcEdge, _⟩ := hcWF
            cases hguard with
            | inl hcTerm =>
              have hcC : c.inCleanup = true := by
                have hpe := hcEdge.1
                rw [hcTerm] at hpe
                exact hpe
              exact ⟨hs, Or.inl hcC⟩
            | inr hrestG =>
              exact ⟨hs, Or.inr hrestG⟩
    | unreachable => rw [ht] at hs; unfold execTerm at hs; dsimp only at hs; exact absurd trivial hs
    | unwindTerminate _ =>
      unfold execTerm; dsimp only
      exact ⟨(fun h => h), (fun tr h => by cases h), (fun v tr h => by cases h)⟩
    | unwindResume =>
      have htsBody := htermWF.2.1 ht
      obtain ⟨hts, hbu⟩ := htsBody
      have hpt := htermWF.1; rw [ht] at hpt
      have hcurC : st.cur.inCleanup = true := by rw [hcleanEq, hpt]
      rw [ht] at hs; unfold execTerm at hs ⊢; rw [hcurC] at hs ⊢; dsimp only at hs ⊢
      cases hstk : st.stack with
      | nil => rw [hstk] at hguard; exact absurd hguard (fun h => h)
      | cons c rest =>
        rw [hstk] at hs hstack hguard; dsimp only at hs ⊢
        obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstack
        obtain ⟨cfn', _, hcfn', _, _, _, _, _, hcEdge, _⟩ := hcWF
        have hcfnEq : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
        rw [hcfnEq] at hcEdge
        rw [hbu] at hcEdge
        cases hguard with
        | inl hcTerm =>
          rw [hcTerm] at hs ⊢
          rw [dispatchUnwind_terminate_eq]
          exact ⟨(fun h => h), (fun tr h => by cases h), (fun v tr h => by cases h)⟩
        | inr hrestG =>
          let cFrame : ActiveFrame := {
            fnId := c.fnId,
            bb := c.retTarget,
            stmtIdx := 0,
            locals := c.locals,
            inCleanup := c.inCleanup
          }
          have hdisp := dispatchUnwind_cleanupGuard_never_unwound prog cFrame rest
            c.unwindOnCall (match st.cleanupDepth with | 0 => 0 | d + 1 => d) st.trace cfn hcfn hcEdge hrestWF (Or.inr hrestG)
          cases hd : dispatchUnwind prog.fns cFrame rest c.unwindOnCall
              (match st.cleanupDepth with | 0 => 0 | d + 1 => d) st.trace with
          | running st' =>
            rw [hd] at hs hdisp
            exact ⟨hs, hdisp⟩
          | halted res =>
            rw [hd] at hs hdisp
            refine ⟨hs, hdisp.1, ?_⟩
            intro v tr hret
            have hn := dispatchUnwind_never_returns_using_ih prog 0
              (fun _ _ _ _ h => by cases h) cFrame rest c.unwindOnCall
              (match st.cleanupDepth with | 0 => 0 | d + 1 => d) st.trace v tr
            rw [hd] at hn
            exact hn hret
    | call callee argReg dst rt u =>
      rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
      cases hr : listGet? st.cur.locals argReg with
      | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
      | some argVal =>
        rw [hr] at hs; dsimp only at hs ⊢
        unfold enterCall at hs ⊢; dsimp only at hs ⊢
        cases hcget : listGet? prog.fns callee with
        | none => rw [hcget] at hs; dsimp only at hs; exact absurd trivial hs
        | some cfn =>
          rw [hcget] at hs; dsimp only at hs ⊢
          cases hcf : cfn.isForeign with
          | false =>
            rw [hcf] at hs; dsimp only at hs ⊢
            exact ⟨hs, Or.inr (Or.inr hguard)⟩
          | true =>
            rw [hcf] at hs; dsimp only at hs ⊢
            cases hfo : prog.foreignSpecs callee argVal with
            | ret v evOpt =>
              rw [hfo] at hs; dsimp only at hs ⊢
              exact ⟨hs, Or.inr hguard⟩
            | unwound evOpt =>
              rw [hfo] at hs; dsimp only at hs ⊢
              have hpe := htermWF.2.2; rw [ht] at hpe
              dsimp only [termUnwind?, termCallCanUnwind] at hpe
              have hcbU : bodyCanUnwind prog.strategy cfn = true := by
                cases hcb0 : bodyCanUnwind prog.strategy cfn
                · have hfbad := hfok callee argVal; rw [hcget] at hfbad
                  exact absurd hfo (hfbad hcf hcb0 evOpt)
                · rfl
              have hccU : calleeCanUnwind prog callee = true := by
                unfold calleeCanUnwind; rw [hcget]; dsimp only; rw [hcbU]
              rw [hccU, ← hcleanEq] at hpe
              have hdisp := dispatchUnwind_cleanupGuard_never_unwound prog st.cur st.stack u
                st.cleanupDepth (appendOptEvent st.trace evOpt) fn hfn hpe hstack (Or.inr hguard)
              cases hd : dispatchUnwind prog.fns st.cur st.stack u st.cleanupDepth
                  (appendOptEvent st.trace evOpt) with
              | running st' =>
                rw [hd] at hs hdisp
                exact ⟨hs, hdisp⟩
              | halted res =>
                rw [hd] at hs hdisp
                refine ⟨hs, hdisp.1, ?_⟩
                intro v tr hret
                have hn := dispatchUnwind_never_returns_using_ih prog 0
                  (fun _ _ _ _ h => by cases h) st.cur st.stack u st.cleanupDepth
                  (appendOptEvent st.trace evOpt) v tr
                rw [hd] at hn
                exact hn hret
    | drop df argReg rt u =>
      rw [ht] at hs; unfold execTerm readLocal? at hs ⊢; dsimp only at hs ⊢
      cases hr : listGet? st.cur.locals argReg with
      | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
      | some argVal =>
        rw [hr] at hs; dsimp only at hs ⊢
        unfold enterCall at hs ⊢; dsimp only at hs ⊢
        cases hdget : listGet? prog.fns df with
        | none => rw [hdget] at hs; dsimp only at hs; exact absurd trivial hs
        | some dfn =>
          rw [hdget] at hs; dsimp only at hs ⊢
          cases hdf : dfn.isForeign with
          | false =>
            rw [hdf] at hs; dsimp only at hs ⊢
            exact ⟨hs, Or.inr (Or.inr hguard)⟩
          | true =>
            rw [hdf] at hs
            have hpt := htermWF.1; rw [ht] at hpt
            obtain ⟨_, ⟨dfn', hdfn', hdfNonF, _, _⟩, _⟩ := hpt
            rw [hdfn'] at hdget; cases hdget; rw [hdfNonF] at hdf; cases hdf
    | panicCall u =>
      rw [ht] at hs; unfold execTerm at hs ⊢; dsimp only at hs ⊢
      cases hstrat : prog.strategy with
      | abort => rw [hstrat] at hs; dsimp only at hs ⊢; exact ⟨(fun h => h), (fun tr h => by cases h), (fun v tr h => by cases h)⟩
      | unwind =>
        cases hts0 : prog.targetSupportsUnwinding with
        | false => rw [hstrat, hts0] at hs; dsimp only at hs ⊢; exact ⟨(fun h => h), (fun tr h => by cases h), (fun v tr h => by cases h)⟩
        | true =>
          rw [hstrat, hts0] at hs; dsimp only at hs ⊢
          have hpe := htermWF.2.2; rw [ht] at hpe
          dsimp only [termUnwind?, termCallCanUnwind] at hpe
          have hpu : fnCanUnwind prog.strategy false false .rust = true := by rw [hstrat]; rfl
          rw [hpu, ← hcleanEq] at hpe
          have hdisp := dispatchUnwind_cleanupGuard_never_unwound prog st.cur st.stack u
            st.cleanupDepth st.trace fn hfn hpe hstack (Or.inr hguard)
          cases hd : dispatchUnwind prog.fns st.cur st.stack u st.cleanupDepth st.trace with
          | running st' =>
            rw [hd] at hs hdisp
            exact ⟨hs, hdisp⟩
          | halted res =>
            rw [hd] at hs hdisp
            refine ⟨hs, hdisp.1, ?_⟩
            intro v tr hret
            have hn := dispatchUnwind_never_returns_using_ih prog 0
              (fun _ _ _ _ h => by cases h) st.cur st.stack u st.cleanupDepth st.trace v tr
            rw [hd] at hn
            exact hn hret

/-- **MAIN THEOREM 2 — Double-Panic `InCleanup` Termination Invariant**:
For any post-`AbortUnwindingCalls` state `st` satisfying `MirRuntimeSafe prog st`:
1. Whenever execution is inside a cleanup block (`st.cur.inCleanup = true`), `st.cleanupDepth ≥ 1`.
2. Direct `panicCall` inside cleanup under `.unwind` deterministically halts immediately
   with `.terminated .inCleanup _` (`panic_in_cleanup`).
3. Foreign call unwinding inside cleanup deterministically halts immediately with `.terminated .inCleanup _`.
4. Entering a local `.drop` from cleanup preserves runtime safety (`st.stack` acquires
   `StackHasCleanupGuard`), while any unwind out of a `StackHasCleanupGuard` continuation can
   NEVER escape to `.unwound`, NEVER returns normally out of the frame with `.returned`, and
   never exhibits `.ub` / `.invalid`. -/
theorem double_panic_inCleanup_termination (prog : Program)
    (hpost : MirPostPassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PostPassNoBogusUnreachable prog) (st : MirState)
    (hsafe : MirRuntimeSafe prog st) :
    (st.cur.inCleanup = true → st.cleanupDepth ≥ 1) ∧
    (∀ fn blk u,
      listGet? prog.fns st.cur.fnId = some fn → fn.isForeign = false →
      listGet? fn.blocks st.cur.bb = some blk → st.cur.inCleanup = true → blk.isCleanup = true →
      st.cur.stmtIdx = listLen blk.stmts → prog.strategy = .unwind → prog.targetSupportsUnwinding = true →
      blk.term = .panicCall u →
      stepMir prog st = .halted (.terminated .inCleanup st.trace)) ∧
    (StackHasCleanupGuard st.stack →
      match stepMir prog st with
      | .running st' => MirRuntimeSafe prog st' ∧ (st'.cur.inCleanup = true ∨ StackHasCleanupGuard st'.stack)
      | .halted res => ¬ mirIsBad res ∧ (∀ tr, res ≠ .unwound tr) ∧ (∀ v tr, res ≠ .returned v tr)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨_, _, _, _, hdp⟩ := MirRuntimeSafe_to_PostWF prog st hsafe
    exact hdp
  · intro fn blk u hfn hnonF hblk hclean hblkC hidx hstrat hts ht
    exact double_panic_direct_inCleanup prog hpost st fn blk hfn hnonF hblk hclean hblkC hidx hstrat hts u ht
  · intro hguard
    exact cleanupGuard_step_preserves_and_blocks_escape prog hpost hfok hnob st hsafe hguard

/-! ## Section 11: Main Theorem 3 — `-C panic=abort` Cleanup-Block Reachability & Erasure Soundness -/

theorem listForall_mono {α : Type} (P Q : α → Prop) (xs : List α)
    (h : listForall P xs) (hpq : ∀ x, P x → Q x) : listForall Q xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨hpq x h.1, ih h.2⟩

theorem listForall_all {α : Type} (P : α → Prop) (xs : List α)
    (h : ∀ x, P x) : listForall P xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨h x, ih⟩

theorem listForall_map {α β : Type} (f : α → β) (P : β → Prop) (xs : List α)
    (h : ∀ x, P (f x)) : listForall P (listMap f xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨h x, ih⟩

theorem natListMem_singleton {x a : Nat} (h : natListMem x [a] = true) : x = a := by
  dsimp only [natListMem] at h
  cases hx : natEq x a with
  | false => rw [hx] at h; cases h
  | true => exact natEq_eq hx

theorem natListMem_pair {x a b : Nat} (h : natListMem x [a, b] = true) : x = a ∨ x = b := by
  dsimp only [natListMem] at h
  cases hx : natEq x a with
  | true => exact Or.inl (natEq_eq hx)
  | false =>
    rw [hx] at h; dsimp only [bor] at h
    cases hy : natEq x b with
    | false => rw [hy] at h; cases h
    | true => exact Or.inr (natEq_eq hy)

theorem countNonCleanupBefore_zero (blocks : List BasicBlock) :
    countNonCleanupBefore blocks 0 = 0 := by
  cases blocks <;> rfl

theorem listGet?_filterAndRemapNormalBlocks (allBlocks xs : List BasicBlock) (b : Nat)
    (blk : BasicBlock) (hget : listGet? xs b = some blk) (hnc : blk.isCleanup = false) :
    listGet? (filterAndRemapNormalBlocks allBlocks xs) (countNonCleanupBefore xs b) =
      some { blk with term := remapNormalTerm allBlocks blk.term } := by
  induction xs generalizing b with
  | nil => cases b <;> cases hget
  | cons y ys ih =>
    unfold filterAndRemapNormalBlocks
    cases hcy : y.isCleanup with
    | false =>
      dsimp only
      cases b with
      | zero =>
        dsimp only [listGet?] at hget
        cases hget
        rw [countNonCleanupBefore_zero, hnc]
        rfl
      | succ b' =>
        dsimp only [listGet?] at hget
        unfold countNonCleanupBefore
        rw [hcy]; dsimp only
        have hcomm : 1 + countNonCleanupBefore ys b' = countNonCleanupBefore ys b' + 1 :=
          Nat.add_comm 1 _
        rw [hcomm]
        dsimp only [listGet?]
        exact ih b' hget
    | true =>
      dsimp only
      cases b with
      | zero =>
        dsimp only [listGet?] at hget
        cases hget
        rw [hcy] at hnc; cases hnc
      | succ b' =>
        dsimp only [listGet?] at hget
        unfold countNonCleanupBefore
        rw [hcy]; dsimp only
        rw [Nat.zero_add]
        exact ih b' hget

theorem listForall_filterAndRemapNormalBlocks (allBlocks xs : List BasicBlock)
    (P : BasicBlock → Prop)
    (hxs : listForall (fun blk =>
      blk.isCleanup = false → P { blk with term := remapNormalTerm allBlocks blk.term }) xs) :
    listForall P (filterAndRemapNormalBlocks allBlocks xs) := by
  induction xs with
  | nil => trivial
  | cons y ys ih =>
    unfold filterAndRemapNormalBlocks
    cases hcy : y.isCleanup with
    | false =>
      dsimp only
      have h1 := hxs.1 hcy
      rw [hcy] at h1
      exact ⟨h1, ih hxs.2⟩
    | true =>
      dsimp only
      exact ih hxs.2

theorem eraseDeadCleanupFn_preserves_metadata (fn : FnBody) :
    (eraseDeadCleanupFn fn).isForeign = fn.isForeign ∧
    (eraseDeadCleanupFn fn).abi = fn.abi ∧
    (eraseDeadCleanupFn fn).neverUnwind = fn.neverUnwind ∧
    (eraseDeadCleanupFn fn).localCount = fn.localCount := by
  unfold eraseDeadCleanupFn
  cases h : fn.isForeign <;> dsimp only
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨h, rfl, rfl, rfl⟩

theorem eraseDeadCleanupProg_preserves_bodyCanUnwind (prog : Program) (fn : FnBody) :
    bodyCanUnwind (eraseDeadCleanupProg prog).strategy (eraseDeadCleanupFn fn) =
      bodyCanUnwind prog.strategy fn := by
  have hm := eraseDeadCleanupFn_preserves_metadata fn
  unfold bodyCanUnwind eraseDeadCleanupProg
  dsimp only
  rw [hm.1, hm.2.1, hm.2.2.1]

theorem eraseDeadCleanupProg_preserves_calleeCanUnwind (prog : Program) (c : FnId) :
    calleeCanUnwind (eraseDeadCleanupProg prog) c = calleeCanUnwind prog c := by
  unfold calleeCanUnwind eraseDeadCleanupProg
  dsimp only
  rw [listGet?_listMap]
  cases listGet? prog.fns c with
  | none => rfl
  | some fn =>
    dsimp only
    exact eraseDeadCleanupProg_preserves_bodyCanUnwind prog fn

theorem eraseDeadCleanupProg_preserves_dropCanUnwind (prog : Program) (d : FnId) :
    dropCanUnwind (eraseDeadCleanupProg prog) d = dropCanUnwind prog d := by
  unfold dropCanUnwind
  have h1 : (eraseDeadCleanupProg prog).fns = listMap eraseDeadCleanupFn prog.fns := rfl
  rw [h1, listGet?_listMap]
  cases listGet? prog.fns d with
  | none => rfl
  | some dfn =>
    have hm := eraseDeadCleanupFn_preserves_metadata dfn
    dsimp only
    rw [hm.2.2.1]
    rw [← eraseDeadCleanupProg_preserves_bodyCanUnwind prog dfn]
    rfl

theorem eraseDeadCleanupProg_preserves_foreignContract (prog : Program)
    (hfok : ForeignContractOK prog) : ForeignContractOK (eraseDeadCleanupProg prog) := by
  intro fid arg
  unfold eraseDeadCleanupProg; dsimp only
  rw [listGet?_listMap]
  cases hget : listGet? prog.fns fid with
  | none => trivial
  | some fn =>
    dsimp only
    have hf := hfok fid arg
    rw [hget] at hf; dsimp only at hf
    have hm := eraseDeadCleanupFn_preserves_metadata fn
    intro hfor hbu ev
    rw [hm.1] at hfor
    have hbu0 := eraseDeadCleanupProg_preserves_bodyCanUnwind prog fn
    change bodyCanUnwind (eraseDeadCleanupProg prog).strategy (eraseDeadCleanupFn fn) = false at hbu
    rw [hbu0] at hbu
    exact hf hfor hbu ev

theorem abortUnwindingCalls_preserves_NoUnwindingCalls (prog : Program)
    (hpre : MirPrePassWF prog) (hnoUnw : NoUnwindingCalls prog) :
    NoUnwindingCalls (abortUnwindingCallsProg prog) := by
  apply listForall_map_preserved (abortUnwindingFn prog)
    (fun fn => PrePassFnWF prog fn ∧ NoUnwindingForeignCallsInFn prog fn) _ prog.fns
  · intro fn ⟨hfnWF, hfnNU⟩
    unfold NoUnwindingForeignCallsInFn
    cases hnonF : fn.isForeign with
    | true =>
      unfold PrePassFnWF at hfnWF
      rw [hnonF] at hfnWF; dsimp only at hfnWF
      have hblocks : (abortUnwindingFn prog fn).blocks = [] := by
        unfold abortUnwindingFn; rw [hnonF]; exact hfnWF
      rw [hblocks]; trivial
    | false =>
      have hblocks := abortUnwindingFn_blocks_nonForeign prog fn hnonF
      rw [hblocks]
      unfold PrePassFnWF at hfnWF; rw [hnonF] at hfnWF
      apply listForall_map_preserved (abortUnwindingBlock prog (bodyCanUnwind prog.strategy fn))
        (fun blk => PrePassBlockWF prog fn blk ∧
          match blk.term with
          | .call callee _ _ _ _ => calleeCanUnwind prog callee = false
          | .drop dropFn _ _ _ => dropCanUnwind prog dropFn = false
          | .panicCall _ => fnCanUnwind prog.strategy false false .rust = false
          | _ => True) _ fn.blocks
      · intro blk ⟨_hblkWF, hblkNU⟩
        unfold abortUnwindingBlock; dsimp only
        cases ht : blk.term with
        | goto _ => trivial
        | branch _ _ _ => trivial
        | return_ _ => trivial
        | unreachable => trivial
        | unwindTerminate _ => trivial
        | unwindResume =>
          unfold abortUnwindingTerm
          cases hts : prog.targetSupportsUnwinding with
          | true =>
            dsimp only [bnot]
            cases hb : bodyCanUnwind prog.strategy fn <;> dsimp only <;> trivial
          | false => dsimp only [bnot]
        | call callee arg dst rt u =>
          rw [ht] at hblkNU
          unfold abortUnwindingTerm
          cases blk.isCleanup <;> dsimp only
          · rw [calleeCanUnwind_abortUnwindingProg]; exact hblkNU
          · rw [calleeCanUnwind_abortUnwindingProg]; exact hblkNU
        | drop df arg rt u =>
          rw [ht] at hblkNU
          unfold abortUnwindingTerm
          cases blk.isCleanup <;> dsimp only
          · rw [dropCanUnwind_abortUnwindingProg]; exact hblkNU
          · rw [dropCanUnwind_abortUnwindingProg]; exact hblkNU
        | panicCall u =>
          rw [ht] at hblkNU
          unfold abortUnwindingTerm
          cases blk.isCleanup <;> dsimp only <;> exact hblkNU
      · exact listForall_conj _ _ _ hfnWF.2.2 hfnNU
  · exact listForall_conj _ _ _ hpre.2.2 hnoUnw

theorem eraseDeadCleanupProg_preserves_NoUnwindingCalls (prog : Program)
    (hnoUnw : NoUnwindingCalls prog) :
    NoUnwindingCalls (eraseDeadCleanupProg prog) := by
  apply listForall_map_preserved eraseDeadCleanupFn (NoUnwindingForeignCallsInFn prog) _ prog.fns
  · intro fn hfnNU
    unfold NoUnwindingForeignCallsInFn
    cases hnonF : fn.isForeign with
    | true =>
      have hblocks : (eraseDeadCleanupFn fn).blocks = fn.blocks := by
        unfold eraseDeadCleanupFn; rw [hnonF]
      rw [hblocks]
      apply listForall_mono _ _ _ hfnNU
      intro blk hblkNU
      cases ht : blk.term with
      | goto _ | branch _ _ _ | return_ _ | unreachable | unwindResume | unwindTerminate _ =>
        trivial
      | call callee _ _ _ _ =>
        rw [ht] at hblkNU; dsimp only
        rw [eraseDeadCleanupProg_preserves_calleeCanUnwind prog callee]
        exact hblkNU
      | drop df _ _ _ =>
        rw [ht] at hblkNU; dsimp only
        rw [eraseDeadCleanupProg_preserves_dropCanUnwind prog df]
        exact hblkNU
      | panicCall _ =>
        rw [ht] at hblkNU; dsimp only
        exact hblkNU
    | false =>
      have hblocks : (eraseDeadCleanupFn fn).blocks = filterAndRemapNormalBlocks fn.blocks fn.blocks := by
        unfold eraseDeadCleanupFn; rw [hnonF]
      rw [hblocks]
      apply listForall_filterAndRemapNormalBlocks
      apply listForall_mono _ _ _ hfnNU
      intro blk hblkNU _hnc
      cases ht : blk.term with
      | goto _ => trivial
      | branch _ _ _ => trivial
      | return_ _ => trivial
      | unreachable => trivial
      | unwindResume => trivial
      | unwindTerminate _ => trivial
      | call callee _ _ _ _ =>
        rw [ht] at hblkNU
        dsimp only [remapNormalTerm]
        rw [eraseDeadCleanupProg_preserves_calleeCanUnwind prog callee]
        exact hblkNU
      | drop df _ _ _ =>
        rw [ht] at hblkNU
        dsimp only [remapNormalTerm]
        rw [eraseDeadCleanupProg_preserves_dropCanUnwind prog df]
        exact hblkNU
      | panicCall _ =>
        rw [ht] at hblkNU
        exact hblkNU
  · exact hnoUnw

/-- Under `-C panic=abort` and `NoUnwindingCalls`, every non-cleanup block in `prog'`
has zero `.cleanup _` unwind edges (`termUnwind? blk.term ≠ some (.cleanup _)`). -/
theorem abortUnwindingCalls_abort_no_cleanup_edges (prog' : Program)
    (hpost : MirPostPassWF prog') (hnoUnw : NoUnwindingCalls prog')
    (fid : FnId) (fn' : FnBody) (hfnGet : listGet? prog'.fns fid = some fn')
    (hnonF : fn'.isForeign = false)
    (bid : BlockId) (blk' : BasicBlock) (hblkGet : listGet? fn'.blocks bid = some blk')
    (hnc : blk'.isCleanup = false) :
    ∀ u, termUnwind? blk'.term = some u → u = .unreachable := by
  have hfnWF := listGet?_listForall (PostPassFnWF prog') prog'.fns fid fn' hpost.2.2 hfnGet
  unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
  have hblkWF := listGet?_listForall (PostPassBlockWF prog' fn') fn'.blocks bid blk' hfnWF.2.2 hblkGet
  have hfnNU := listGet?_listForall (NoUnwindingForeignCallsInFn prog') prog'.fns fid fn' hnoUnw hfnGet
  have hblkNU := listGet?_listForall _ fn'.blocks bid blk' hfnNU hblkGet
  intro u hu
  have hpostTerm := hblkWF.2
  have hpe := hpostTerm.2.2
  rw [hu] at hpe
  dsimp only at hpe
  apply hpe.2.1 hnc
  cases ht : blk'.term with
  | goto _ | branch _ _ _ | return_ _ | unreachable | unwindResume | unwindTerminate _ =>
    rw [ht] at hu; cases hu
  | call callee _ _ _ _ =>
    rw [ht] at hblkNU
    exact Or.inr hblkNU
  | drop df _ _ _ =>
    rw [ht] at hblkNU
    exact Or.inr hblkNU
  | panicCall _ =>
    rw [ht] at hblkNU
    exact Or.inr hblkNU

/-- **Reachability Theorem**: In any post-`AbortUnwindingCalls` program with `NoUnwindingCalls`
(in particular `-C panic=abort` with no unwinding foreign calls), NO cleanup block (`isCleanup = true`)
is statically reachable from `bb 0` in the CFG! -/
theorem panicAbort_cleanup_unreachable (prog' : Program)
    (hpost : MirPostPassWF prog') (hnoUnw : NoUnwindingCalls prog')
    (fid : FnId) (fn' : FnBody) (hfn : listGet? prog'.fns fid = some fn')
    (hnonF : fn'.isForeign = false) (b : BlockId)
    (hreach : ReachableBB fn'.blocks b) :
    ∀ blk', listGet? fn'.blocks b = some blk' → blk'.isCleanup = false := by
  induction hreach with
  | entry =>
    have hfnWF := listGet?_listForall (PostPassFnWF prog') prog'.fns fid fn' hpost.2.2 hfn
    unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
    obtain ⟨b0, hb0, hb0C⟩ := hfnWF.2.1
    intro blk' hget
    rw [hb0] at hget; cases hget
    exact hb0C
  | step _ hedge ih =>
    intro vblk hvget
    cases hedge with
    | normal husrc hmem =>
      rename_i ublk
      have huNC := ih ublk husrc
      have hfnWF := listGet?_listForall (PostPassFnWF prog') prog'.fns fid fn' hpost.2.2 hfn
      unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
      have hblkWF := listGet?_listForall (PostPassBlockWF prog' fn') fn'.blocks _ _ hfnWF.2.2 husrc
      have hpt := hblkWF.2.1
      cases ht : ublk.term with
      | return_ _ | unreachable | unwindResume | unwindTerminate _ | panicCall _ =>
        rw [ht] at hmem; cases hmem
      | goto t =>
        rw [ht] at hmem hpt
        have hv := natListMem_singleton hmem
        subst hv
        obtain ⟨tblk, htblk, htC⟩ := hpt
        rw [htblk] at hvget; cases hvget
        rw [htC, huNC]
      | branch c z nz =>
        rw [ht] at hmem hpt
        obtain ⟨_, ⟨bz, hbz, hbzC⟩, ⟨bnz, hbnz, hbnzC⟩⟩ := hpt
        cases natListMem_pair hmem with
        | inl hv =>
          subst hv
          rw [hbz] at hvget; cases hvget; rw [hbzC, huNC]
        | inr hv =>
          subst hv
          rw [hbnz] at hvget; cases hvget; rw [hbnzC, huNC]
      | call callee arg dst rt cu =>
        rw [ht] at hmem hpt
        have hv := natListMem_singleton hmem
        subst hv
        obtain ⟨_, _, _, ⟨rblk, hrblk, hrC⟩, _⟩ := hpt
        rw [hrblk] at hvget; cases hvget; rw [hrC, huNC]
      | drop df arg rt du =>
        rw [ht] at hmem hpt
        have hv := natListMem_singleton hmem
        subst hv
        obtain ⟨_, _, ⟨rblk, hrblk, hrC⟩, _⟩ := hpt
        rw [hrblk] at hvget; cases hvget; rw [hrC, huNC]
    | unwindCleanup husrc huTerm huEq =>
      rename_i ublk uw
      have huNC := ih ublk husrc
      have hfnWF := listGet?_listForall (PostPassFnWF prog') prog'.fns fid fn' hpost.2.2 hfn
      unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
      have hblkWF := listGet?_listForall (PostPassBlockWF prog' fn') fn'.blocks _ _ hfnWF.2.2 husrc
      have hfnNU := listGet?_listForall (NoUnwindingForeignCallsInFn prog') prog'.fns fid fn' hnoUnw hfn
      have hblkNU := listGet?_listForall _ fn'.blocks _ _ hfnNU husrc
      have hpe := hblkWF.2.2.2; rw [huTerm] at hpe; dsimp only at hpe
      have huUnreach : uw = UnwindAction.unreachable := by
        apply hpe.2.1 huNC
        cases ht : ublk.term with
        | goto _ | branch _ _ _ | return_ _ | unreachable | unwindResume | unwindTerminate _ =>
          rw [ht] at huTerm; cases huTerm
        | call callee _ _ _ _ => rw [ht] at hblkNU; exact Or.inr hblkNU
        | drop df _ _ _ => rw [ht] at hblkNU; exact Or.inr hblkNU
        | panicCall _ => rw [ht] at hblkNU; exact Or.inr hblkNU
      rw [huUnreach] at huEq; cases huEq

/-- After `eraseDeadCleanupProg`, ZERO basic blocks anywhere in any non-foreign function
have `isCleanup = true`. -/
theorem eraseDeadCleanup_zero_cleanup_blocks (prog' : Program) :
    listForall (fun fn =>
      fn.isForeign = false →
      listForall (fun blk => blk.isCleanup = false) fn.blocks)
      (eraseDeadCleanupProg prog').fns := by
  unfold eraseDeadCleanupProg; dsimp only
  apply listForall_map
  intro fn hnonF
  have hm := eraseDeadCleanupFn_preserves_metadata fn
  rw [hm.1] at hnonF
  have hblocks : (eraseDeadCleanupFn fn).blocks = filterAndRemapNormalBlocks fn.blocks fn.blocks := by
    unfold eraseDeadCleanupFn; rw [hnonF]
  rw [hblocks]
  apply listForall_filterAndRemapNormalBlocks
  apply listForall_all
  intro blk hnc
  exact hnc

theorem eraseDeadCleanup_preserves_postWF (prog' : Program)
    (hpost : MirPostPassWF prog') (hnoUnw : NoUnwindingCalls prog') :
    MirPostPassWF (eraseDeadCleanupProg prog') := by
  refine ⟨hpost.1, ?_, ?_⟩
  · obtain ⟨entry, hentry, henonF⟩ := hpost.2.1
    refine ⟨eraseDeadCleanupFn entry, ?_, ?_⟩
    · unfold eraseDeadCleanupProg; dsimp only; rw [listGet?_listMap, hentry]
    · exact (eraseDeadCleanupFn_preserves_metadata entry).1.trans henonF
  · apply listForall_map_preserved eraseDeadCleanupFn
      (fun fn => PostPassFnWF prog' fn ∧ NoUnwindingForeignCallsInFn prog' fn) _ prog'.fns
    · intro fn ⟨hfnWF, hfnNU⟩
      unfold PostPassFnWF
      cases hf : fn.isForeign with
      | true =>
        have hm := eraseDeadCleanupFn_preserves_metadata fn
        unfold PostPassFnWF at hfnWF
        rw [hf] at hfnWF; dsimp only at hfnWF
        have hblocks : (eraseDeadCleanupFn fn).blocks = [] := by
          unfold eraseDeadCleanupFn; rw [hf]; exact hfnWF
        rw [hm.1, hf, hblocks]
      | false =>
        have hm := eraseDeadCleanupFn_preserves_metadata fn
        have hblocks : (eraseDeadCleanupFn fn).blocks = filterAndRemapNormalBlocks fn.blocks fn.blocks := by
          unfold eraseDeadCleanupFn; rw [hf]
        rw [hm.1, hf]; dsimp only
        unfold PostPassFnWF at hfnWF; rw [hf] at hfnWF
        obtain ⟨hloc, ⟨b0, hb0, hb0C⟩, hblksWF⟩ := hfnWF
        refine ⟨by rw [hm.2.2.2]; exact hloc, ?_, ?_⟩
        · refine ⟨{ b0 with term := remapNormalTerm fn.blocks b0.term }, ?_, hb0C⟩
          rw [hblocks]
          have h0 := listGet?_filterAndRemapNormalBlocks fn.blocks fn.blocks 0 b0 hb0 hb0C
          rw [countNonCleanupBefore_zero] at h0
          exact h0
        · rw [hblocks]
          apply listForall_filterAndRemapNormalBlocks
          have hblksBoth := listForall_conj _ _ _ hblksWF hfnNU
          apply listForall_mono _ _ _ hblksBoth
          intro blk ⟨hblkWF, hblkNU⟩ hnc
          have hstmtsWF := listForall_mono (StmtWF fn.localCount)
            (StmtWF (eraseDeadCleanupFn fn).localCount) blk.stmts hblkWF.1 (fun s hs => by
            rw [hm.2.2.2]; exact hs)
          refine ⟨hstmtsWF, ?_⟩
          have hpreT := hblkWF.2.1
          cases ht : blk.term with
          | goto t =>
            rw [ht] at hpreT
            dsimp only [remapNormalTerm]
            refine ⟨?_, (fun h => by cases h), trivial⟩
            obtain ⟨tblk, htblk, htC⟩ := hpreT
            have htbNC : tblk.isCleanup = false := htC.trans hnc
            refine ⟨{ tblk with term := remapNormalTerm fn.blocks tblk.term }, ?_, htC⟩
            rw [hblocks]
            exact listGet?_filterAndRemapNormalBlocks fn.blocks fn.blocks t tblk htblk htbNC
          | branch c z nz =>
            rw [ht] at hpreT
            dsimp only [remapNormalTerm]
            refine ⟨?_, (fun h => by cases h), trivial⟩
            obtain ⟨hc, ⟨bz, hbz, hbzC⟩, ⟨bnz, hbnz, hbnzC⟩⟩ := hpreT
            refine ⟨by rw [hm.2.2.2]; exact hc, ?_, ?_⟩
            · refine ⟨{ bz with term := remapNormalTerm fn.blocks bz.term }, ?_, hbzC⟩
              rw [hblocks]
              exact listGet?_filterAndRemapNormalBlocks fn.blocks fn.blocks z bz hbz (hbzC.trans hnc)
            · refine ⟨{ bnz with term := remapNormalTerm fn.blocks bnz.term }, ?_, hbnzC⟩
              rw [hblocks]
              exact listGet?_filterAndRemapNormalBlocks fn.blocks fn.blocks nz bnz hbnz (hbnzC.trans hnc)
          | return_ r =>
            rw [ht] at hpreT
            dsimp only [remapNormalTerm]
            refine ⟨⟨hnc, by rw [hm.2.2.2]; exact hpreT.2⟩, (fun h => by cases h), trivial⟩
          | unreachable =>
            refine ⟨trivial, (fun h => by cases h), trivial⟩
          | unwindResume =>
            rw [ht] at hpreT; rw [hnc] at hpreT; cases hpreT
          | unwindTerminate _ =>
            rw [ht] at hpreT; rw [hnc] at hpreT; cases hpreT
          | call callee arg dst rt u =>
            rw [ht] at hpreT hblkNU
            dsimp only [remapNormalTerm]
            obtain ⟨harg, hdst, ⟨cfn, hcfn⟩, ⟨rblk, hrblk, hrC⟩, _⟩ := hpreT
            refine ⟨⟨by rw [hm.2.2.2]; exact harg, by rw [hm.2.2.2]; exact hdst,
              ⟨eraseDeadCleanupFn cfn, by unfold eraseDeadCleanupProg; dsimp only; rw [listGet?_listMap, hcfn]⟩,
              ⟨{ rblk with term := remapNormalTerm fn.blocks rblk.term },
                by rw [hblocks]; exact listGet?_filterAndRemapNormalBlocks fn.blocks fn.blocks rt rblk hrblk (hrC.trans hnc),
                hrC⟩,
              trivial, (fun h => by rw [hnc] at h; cases h)⟩, (fun h => by cases h), ?_⟩
            dsimp only [termUnwind?]
            refine ⟨trivial, (fun _ _ => rfl), (fun _ h => by cases h)⟩
          | drop df arg rt u =>
            rw [ht] at hpreT hblkNU
            dsimp only [remapNormalTerm]
            obtain ⟨harg, ⟨dfn, hdfn, hdfNonF, hdfAbi, hdfPinD⟩, ⟨rblk, hrblk, hrC⟩, _⟩ := hpreT
            have hdm := eraseDeadCleanupFn_preserves_metadata dfn
            refine ⟨⟨by rw [hm.2.2.2]; exact harg,
              ⟨eraseDeadCleanupFn dfn,
                by unfold eraseDeadCleanupProg; dsimp only; rw [listGet?_listMap, hdfn],
                by rw [hdm.1]; exact hdfNonF, by rw [hdm.2.1]; exact hdfAbi,
                fun hp => by rw [hdm.2.2.1]; exact hdfPinD hp⟩,
              ⟨{ rblk with term := remapNormalTerm fn.blocks rblk.term },
                by rw [hblocks]; exact listGet?_filterAndRemapNormalBlocks fn.blocks fn.blocks rt rblk hrblk (hrC.trans hnc),
                hrC⟩,
              trivial, (fun h => by rw [hnc] at h; cases h)⟩, (fun h => by cases h), ?_⟩
            dsimp only [termUnwind?]
            refine ⟨trivial, (fun _ _ => rfl), (fun _ h => by cases h)⟩
          | panicCall u =>
            rw [ht] at hblkNU
            dsimp only [remapNormalTerm]
            refine ⟨⟨trivial, (fun h => by rw [hnc] at h; cases h)⟩, (fun h => by cases h), ?_⟩
            dsimp only [termUnwind?, termCallCanUnwind]
            refine ⟨trivial, (fun _ _ => rfl), (fun _ h => by cases h)⟩
    · exact listForall_conj _ _ _ hpost.2.2 hnoUnw

theorem eraseDeadCleanup_preserves_postNoBogus (prog' : Program)
    (hpost : MirPostPassWF prog') (hnob : PostPassNoBogusUnreachable prog')
    (hnoUnw : NoUnwindingCalls prog') :
    PostPassNoBogusUnreachable (eraseDeadCleanupProg prog') := by
  refine ⟨hnob.1, ?_⟩
  apply listForall_map_preserved eraseDeadCleanupFn
    (fun fn => PostPassFnWF prog' fn ∧ NoUnwindingForeignCallsInFn prog' fn ∧
      (fn.isForeign = false →
        listForall (fun blk =>
          (blk.isCleanup = false → blk.term ≠ .unreachable) ∧
          (prog'.targetSupportsUnwinding = true → blk.term ≠ .unreachable) ∧
          (termUnwind? blk.term = some .unreachable →
            prog'.targetSupportsUnwinding = false ∨ termCallCanUnwind prog' blk.term = false))
          fn.blocks))
    _ prog'.fns
  · intro fn ⟨hfnWF, hfnNU, hfnNB⟩ hfE
    have hm := eraseDeadCleanupFn_preserves_metadata fn
    have hf : fn.isForeign = false := by rw [← hm.1]; exact hfE
    have hblocks : (eraseDeadCleanupFn fn).blocks = filterAndRemapNormalBlocks fn.blocks fn.blocks := by
      unfold eraseDeadCleanupFn; rw [hf]
    rw [hblocks]
    unfold PostPassFnWF at hfnWF; rw [hf] at hfnWF
    apply listForall_filterAndRemapNormalBlocks
    have h1 := listForall_conj _ _ _ hfnWF.2.2 hfnNU
    have h2 := listForall_conj _ _ _ h1 (hfnNB hf)
    apply listForall_mono _ _ _ h2
    intro blk ⟨⟨hblkWF, hblkNU⟩, hblkNB⟩ hnc
    refine ⟨?_, ?_, ?_⟩
    · intro _ hbad
      cases ht : blk.term with
      | goto _ | branch _ _ _ | return_ _ | call _ _ _ _ _ | drop _ _ _ _ | panicCall _ =>
        rw [ht] at hbad; dsimp only [remapNormalTerm] at hbad; cases hbad
      | unreachable => exact hblkNB.1 hnc ht
      | unwindResume => have hpt := hblkWF.2.1; rw [ht, hnc] at hpt; cases hpt
      | unwindTerminate _ => have hpt := hblkWF.2.1; rw [ht, hnc] at hpt; cases hpt
    · intro _ hbad
      cases ht : blk.term with
      | goto _ | branch _ _ _ | return_ _ | call _ _ _ _ _ | drop _ _ _ _ | panicCall _ =>
        rw [ht] at hbad; dsimp only [remapNormalTerm] at hbad; cases hbad
      | unreachable => exact hblkNB.1 hnc ht
      | unwindResume => have hpt := hblkWF.2.1; rw [ht, hnc] at hpt; cases hpt
      | unwindTerminate _ => have hpt := hblkWF.2.1; rw [ht, hnc] at hpt; cases hpt
    · intro hu
      cases ht : blk.term with
      | goto _ | branch _ _ _ | return_ _ | unreachable | unwindResume | unwindTerminate _ =>
        rw [ht] at hu; dsimp only [remapNormalTerm, termUnwind?] at hu; cases hu
      | call callee _ _ _ _ =>
        rw [ht] at hblkNU
        refine Or.inr ?_
        dsimp only [remapNormalTerm, termCallCanUnwind]
        rw [eraseDeadCleanupProg_preserves_calleeCanUnwind prog' callee]
        exact hblkNU
      | drop df _ _ _ =>
        rw [ht] at hblkNU
        refine Or.inr ?_
        dsimp only [remapNormalTerm, termCallCanUnwind]
        rw [eraseDeadCleanupProg_preserves_dropCanUnwind prog' df]
        exact hblkNU
      | panicCall _ =>
        rw [ht] at hblkNU
        exact Or.inr hblkNU
  · have hB := listForall_conj _ _ _ hnoUnw hnob.2
    exact listForall_conj _ _ _ hpost.2.2 hB

/-- Exact outcome equivalence between pre-erasure `-C panic=abort` MIR execution
and post-erasure cleanup-free MIR execution (identifying `.outOfFuel` after identical
step counts without comparing raw dead-block-indexed `BlockId`s). -/
noncomputable def MirCleanupEraseResultEq : MirExecResult → MirExecResult → Prop
  | .returned v1 tr1, .returned v2 tr2 => v1 = v2 ∧ tr1 = tr2
  | .unwound tr1, .unwound tr2 => tr1 = tr2
  | .terminated r1 tr1, .terminated r2 tr2 => r1 = r2 ∧ tr1 = tr2
  | .aborted tr1, .aborted tr2 => tr1 = tr2
  | .outOfFuel _, .outOfFuel _ => True
  | _, _ => False

noncomputable def CleanupEraseStackRel (prog' : Program) :
    List CallerCont → List CallerCont → Prop
  | [], [] => True
  | c1 :: r1, c2 :: r2 =>
    ∃ cfn,
      listGet? prog'.fns c1.fnId = some cfn ∧
      cfn.isForeign = false ∧
      c2.fnId = c1.fnId ∧
      c2.locals = c1.locals ∧
      c1.inCleanup = false ∧
      c2.inCleanup = false ∧
      c2.retDst = c1.retDst ∧
      c2.retTarget = countNonCleanupBefore cfn.blocks c1.retTarget ∧
      c2.unwindOnCall = .unreachable ∧
      CleanupEraseStackRel prog' r1 r2
  | _, _ => False

noncomputable def CleanupEraseStateRel (prog' : Program) (st1 st2 : MirState) : Prop :=
  ∃ fn,
    listGet? prog'.fns st1.cur.fnId = some fn ∧
    fn.isForeign = false ∧
    st2.cur.fnId = st1.cur.fnId ∧
    st2.cur.bb = countNonCleanupBefore fn.blocks st1.cur.bb ∧
    st2.cur.stmtIdx = st1.cur.stmtIdx ∧
    st2.cur.locals = st1.cur.locals ∧
    st1.cur.inCleanup = false ∧
    st2.cur.inCleanup = false ∧
    st2.cleanupDepth = st1.cleanupDepth ∧
    st2.trace = st1.trace ∧
    CleanupEraseStackRel prog' st1.stack st2.stack

theorem eraseDeadCleanup_run_sim (prog' : Program)
    (hpost : MirPostPassWF prog') (hfok : ForeignContractOK prog')
    (hnob : PostPassNoBogusUnreachable prog') (hnoUnw : NoUnwindingCalls prog')
    (hstrat : prog'.strategy = .abort)
    (fuel : Nat) (st1 st2 : MirState)
    (hsafe1 : MirRuntimeSafe prog' st1) (hrel : CleanupEraseStateRel prog' st1 st2) :
    MirCleanupEraseResultEq (runMir prog' fuel st1) (runMir (eraseDeadCleanupProg prog') fuel st2) ∧
    (∀ tr, runMir prog' fuel st1 ≠ .unwound tr) ∧
    (∀ tr, runMir (eraseDeadCleanupProg prog') fuel st2 ≠ .unwound tr) := by
  induction fuel generalizing st1 st2 with
  | zero =>
    unfold runMir MirCleanupEraseResultEq
    exact ⟨trivial, (fun tr h => by cases h), (fun tr h => by cases h)⟩
  | succ k ih =>
    obtain ⟨fn, hfn, hnonF, hfid2, hbb2, hidx2, hloc2, hinc1, hinc2, hdep2, htr2, hstk⟩ := hrel
    have hsafe1Copy := hsafe1
    have hs1 := stepMir_preserves_safe prog' hpost hfok hnob st1 hsafe1Copy
    obtain ⟨_, _, hact1, _, _, _, _, _⟩ := hsafe1
    obtain ⟨fn1', blk, hfn1', _, hblk, hcleanEq, hstmtLe, _⟩ := hact1
    have hfnEq : fn1' = fn := by rw [hfn] at hfn1'; cases hfn1'; rfl
    rw [hfnEq] at hblk
    have hblkNC : blk.isCleanup = false := by rw [← hcleanEq, hinc1]
    have hfnE : listGet? (eraseDeadCleanupProg prog').fns st2.cur.fnId = some (eraseDeadCleanupFn fn) := by
      unfold eraseDeadCleanupProg; dsimp only; rw [listGet?_listMap, hfid2, hfn]
    have hm := eraseDeadCleanupFn_preserves_metadata fn
    have hnonFE : (eraseDeadCleanupFn fn).isForeign = false := by rw [hm.1]; exact hnonF
    have hblkEGet : listGet? (eraseDeadCleanupFn fn).blocks st2.cur.bb =
        some { blk with term := remapNormalTerm fn.blocks blk.term } := by
      have hblocks : (eraseDeadCleanupFn fn).blocks = filterAndRemapNormalBlocks fn.blocks fn.blocks := by
        unfold eraseDeadCleanupFn; rw [hnonF]
      rw [hblocks, hbb2]
      exact listGet?_filterAndRemapNormalBlocks fn.blocks fn.blocks st1.cur.bb blk hblk hblkNC
    have hcleanEqE : st2.cur.inCleanup = ({ blk with term := remapNormalTerm fn.blocks blk.term } : BasicBlock).isCleanup := by
      rw [hinc2, hblkNC]
    have hfnWF := listGet?_listForall (PostPassFnWF prog') prog'.fns st1.cur.fnId fn hpost.2.2 hfn
    unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
    have hblkWF := listGet?_listForall (PostPassBlockWF prog' fn) fn.blocks st1.cur.bb blk hfnWF.2.2 hblk
    have hfnNU := listGet?_listForall (NoUnwindingForeignCallsInFn prog') prog'.fns st1.cur.fnId fn hnoUnw hfn
    have hblkNU := listGet?_listForall _ fn.blocks st1.cur.bb blk hfnNU hblk
    have hfnNB := listGet?_listForall _ prog'.fns st1.cur.fnId fn hnob.2 hfn hnonF
    have hblkNB := listGet?_listForall _ fn.blocks st1.cur.bb blk hfnNB hblk
    unfold runMir
    cases hsGet : listGet? blk.stmts st1.cur.stmtIdx with
    | some stmt =>
      have hsGetE : listGet? ({ blk with term := remapNormalTerm fn.blocks blk.term } : BasicBlock).stmts
          st2.cur.stmtIdx = some stmt := by
        rw [hidx2]; exact hsGet
      rw [stepMir_stmt_eq hfn hnonF hblk hcleanEq hsGet] at hs1 ⊢
      rw [stepMir_stmt_eq hfnE hnonFE hblkEGet hcleanEqE hsGetE]
      cases stmt with
      | nop =>
        unfold execStmt at hs1 ⊢; dsimp only at hs1 ⊢
        refine ih _ _ hs1 ?_
        exact ⟨fn, hfn, hnonF, hfid2, hbb2, by rw [hidx2], hloc2, hinc1, hinc2, hdep2, htr2, hstk⟩
      | emit ev =>
        unfold execStmt at hs1 ⊢; dsimp only at hs1 ⊢
        refine ih _ _ hs1 ?_
        exact ⟨fn, hfn, hnonF, hfid2, hbb2, by rw [hidx2], hloc2, hinc1, hinc2, hdep2, by rw [htr2], hstk⟩
      | assignConst dst val =>
        unfold execStmt at hs1 ⊢; dsimp only at hs1 ⊢
        refine ih _ _ hs1 ?_
        exact ⟨fn, hfn, hnonF, hfid2, hbb2, by rw [hidx2], by rw [hloc2], hinc1, hinc2, hdep2, htr2, hstk⟩
      | assignLocal dst src =>
        unfold execStmt readLocal? at hs1 ⊢; dsimp only at hs1 ⊢
        cases hr : listGet? st1.cur.locals src with
        | none => rw [hr] at hs1; dsimp only at hs1; exact absurd trivial hs1
        | some v =>
          have hrE : listGet? st2.cur.locals src = some v := by rw [hloc2]; exact hr
          rw [hr] at hs1; rw [hrE]; dsimp only at hs1 ⊢
          refine ih _ _ hs1 ?_
          exact ⟨fn, hfn, hnonF, hfid2, hbb2, by rw [hidx2], by rw [hloc2], hinc1, hinc2, hdep2, htr2, hstk⟩
    | none =>
      have heqLen : st1.cur.stmtIdx = listLen blk.stmts :=
        listGet?_eq_none_implies_ge blk.stmts st1.cur.stmtIdx hsGet hstmtLe
      have hsGetE : listGet? ({ blk with term := remapNormalTerm fn.blocks blk.term } : BasicBlock).stmts
          st2.cur.stmtIdx = none := by
        rw [hidx2]; exact hsGet
      have heqLenE : st2.cur.stmtIdx =
          listLen ({ blk with term := remapNormalTerm fn.blocks blk.term } : BasicBlock).stmts := by
        rw [hidx2]; exact heqLen
      rw [stepMir_term_eq hfn hnonF hblk hcleanEq hsGet heqLen] at hs1 ⊢
      rw [stepMir_term_eq hfnE hnonFE hblkEGet hcleanEqE hsGetE heqLenE]
      dsimp only
      have hpt := hblkWF.2.1
      cases ht : blk.term with
      | goto target =>
        rw [ht] at hs1 hpt
        dsimp only [remapNormalTerm]
        unfold execTerm at hs1 ⊢; dsimp only at hs1 ⊢
        refine ih _ _ hs1 ?_
        exact ⟨fn, hfn, hnonF, hfid2, rfl, rfl, hloc2, hinc1, hinc2, hdep2, htr2, hstk⟩
      | branch cond z nz =>
        rw [ht] at hs1 hpt
        dsimp only [remapNormalTerm]
        unfold execTerm readLocal? at hs1 ⊢; dsimp only at hs1 ⊢
        cases hr : listGet? st1.cur.locals cond with
        | none => rw [hr] at hs1; dsimp only at hs1; exact absurd trivial hs1
        | some v =>
          have hrE : listGet? st2.cur.locals cond = some v := by rw [hloc2]; exact hr
          rw [hr] at hs1; rw [hrE]; dsimp only at hs1 ⊢
          cases v with
          | zero =>
            refine ih _ _ hs1 ?_
            exact ⟨fn, hfn, hnonF, hfid2, rfl, rfl, hloc2, hinc1, hinc2, hdep2, htr2, hstk⟩
          | succ _ =>
            refine ih _ _ hs1 ?_
            exact ⟨fn, hfn, hnonF, hfid2, rfl, rfl, hloc2, hinc1, hinc2, hdep2, htr2, hstk⟩
      | return_ valReg =>
        rw [ht] at hs1 hpt
        dsimp only [remapNormalTerm]
        unfold execTerm readLocal? at hs1 ⊢; dsimp only at hs1 ⊢
        rw [hinc1] at hs1 ⊢; rw [hinc2]; dsimp only at hs1 ⊢
        cases hr : listGet? st1.cur.locals valReg with
        | none => rw [hr] at hs1; dsimp only at hs1; exact absurd trivial hs1
        | some v =>
          have hrE : listGet? st2.cur.locals valReg = some v := by rw [hloc2]; exact hr
          rw [hr] at hs1; rw [hrE]; dsimp only at hs1 ⊢
          cases hstk1 : st1.stack with
          | nil =>
            rw [hstk1] at hstk
            cases hstk2 : st2.stack with
            | cons _ _ => rw [hstk2] at hstk; cases hstk
            | nil =>
              unfold MirCleanupEraseResultEq
              refine ⟨⟨rfl, htr2.symm⟩, (fun tr h => by cases h), (fun tr h => by cases h)⟩
          | cons c1 r1 =>
            rw [hstk1] at hstk hs1
            cases hstk2 : st2.stack with
            | nil => rw [hstk2] at hstk; cases hstk
            | cons c2 r2 =>
              rw [hstk2] at hstk
              obtain ⟨cfn, hcfn, hcfNonF, hcfid, hcloc, hcinc1, hcinc2, hcdst, hcret, _, hrest⟩ := hstk
              dsimp only at hs1 ⊢
              refine ih _ _ hs1 ?_
              exact ⟨cfn, hcfn, hcfNonF, hcfid, hcret, rfl, by rw [hcloc, hcdst], hcinc1, hcinc2, hdep2, htr2, hrest⟩
      | unreachable => exact absurd ht (hblkNB.1 hblkNC)
      | unwindResume => rw [ht, hblkNC] at hpt; cases hpt
      | unwindTerminate _ => rw [ht, hblkNC] at hpt; cases hpt
      | panicCall u =>
        rw [ht] at hs1 hblkNU
        dsimp only [remapNormalTerm]
        unfold execTerm at hs1 ⊢
        rw [hstrat]
        have hstratE : (eraseDeadCleanupProg prog').strategy = .abort := hstrat
        rw [hstratE]; dsimp only
        unfold MirCleanupEraseResultEq
        exact ⟨htr2.symm, (fun tr h => by cases h), (fun tr h => by cases h)⟩
      | call callee argReg dst rt u =>
        rw [ht] at hs1 hpt hblkNU
        dsimp only [remapNormalTerm]
        unfold execTerm readLocal? at hs1 ⊢; dsimp only at hs1 ⊢
        cases hr : listGet? st1.cur.locals argReg with
        | none => rw [hr] at hs1; dsimp only at hs1; exact absurd trivial hs1
        | some argVal =>
          have hrE : listGet? st2.cur.locals argReg = some argVal := by rw [hloc2]; exact hr
          rw [hr] at hs1; rw [hrE]; dsimp only at hs1 ⊢
          unfold enterCall at hs1 ⊢; dsimp only at hs1 ⊢
          cases hcget : listGet? prog'.fns callee with
          | none => rw [hcget] at hs1; dsimp only at hs1; exact absurd trivial hs1
          | some cfn =>
            have hcgetE : listGet? (eraseDeadCleanupProg prog').fns callee =
                some (eraseDeadCleanupFn cfn) := by
              unfold eraseDeadCleanupProg; dsimp only; rw [listGet?_listMap, hcget]
            have hcm := eraseDeadCleanupFn_preserves_metadata cfn
            rw [hcget] at hs1
            rw [hcgetE]; dsimp only at hs1 ⊢
            rw [hcm.1]
            cases hcf : cfn.isForeign with
            | false =>
              rw [hcf] at hs1; dsimp only at hs1 ⊢
              rw [hcm.2.2.2]
              refine ih _ _ hs1 ?_
              refine ⟨cfn, hcget, hcf, rfl, ?_, rfl, rfl, rfl, rfl, hdep2, htr2, ?_⟩
              · rw [countNonCleanupBefore_zero]
              · exact ⟨fn, hfn, hnonF, hfid2, hloc2, hinc1, hinc2, rfl, rfl, rfl, hstk⟩
            | true =>
              rw [hcf] at hs1; dsimp only at hs1 ⊢
              have hspecs : (eraseDeadCleanupProg prog').foreignSpecs = prog'.foreignSpecs := rfl
              rw [hspecs]
              cases hfo : prog'.foreignSpecs callee argVal with
              | ret retV evOpt =>
                rw [hfo] at hs1; dsimp only at hs1 ⊢
                refine ih _ _ hs1 ?_
                exact ⟨fn, hfn, hnonF, hfid2, rfl, rfl, by rw [hloc2], hinc1, hinc2, hdep2, by rw [htr2], hstk⟩
              | unwound evOpt =>
                have hcuFalse : bodyCanUnwind prog'.strategy cfn = false := by
                  dsimp only [calleeCanUnwind] at hblkNU
                  rw [hcget] at hblkNU
                  exact hblkNU
                exact absurd hfo (hfok callee argVal |> fun h => by rw [hcget] at h; exact h hcf hcuFalse evOpt)
      | drop df argReg rt u =>
        rw [ht] at hs1 hpt hblkNU
        dsimp only [remapNormalTerm]
        unfold execTerm readLocal? at hs1 ⊢; dsimp only at hs1 ⊢
        cases hr : listGet? st1.cur.locals argReg with
        | none => rw [hr] at hs1; dsimp only at hs1; exact absurd trivial hs1
        | some argVal =>
          have hrE : listGet? st2.cur.locals argReg = some argVal := by rw [hloc2]; exact hr
          rw [hr] at hs1; rw [hrE]; dsimp only at hs1 ⊢
          unfold enterCall at hs1 ⊢; dsimp only at hs1 ⊢
          cases hdget : listGet? prog'.fns df with
          | none => rw [hdget] at hs1; dsimp only at hs1; exact absurd trivial hs1
          | some dfn =>
            have hdgetE : listGet? (eraseDeadCleanupProg prog').fns df =
                some (eraseDeadCleanupFn dfn) := by
              unfold eraseDeadCleanupProg; dsimp only; rw [listGet?_listMap, hdget]
            have hdm := eraseDeadCleanupFn_preserves_metadata dfn
            rw [hdget] at hs1
            rw [hdgetE]; dsimp only at hs1 ⊢
            obtain ⟨_, ⟨dfn', hdfn', hdfNonF, _, _⟩, _⟩ := hpt
            rw [hdfn'] at hdget; cases hdget
            rw [hdfNonF] at hs1
            rw [hdm.1, hdfNonF]
            dsimp only at hs1 ⊢
            rw [hdm.2.2.2]
            refine ih _ _ hs1 ?_
            refine ⟨dfn, hdfn', hdfNonF, rfl, ?_, rfl, rfl, rfl, rfl, hdep2, htr2, ?_⟩
            · rw [countNonCleanupBefore_zero]
            · exact ⟨fn, hfn, hnonF, hfid2, hloc2, hinc1, hinc2, rfl, rfl, rfl, hstk⟩

/-- **MAIN THEOREM 3 — `-C panic=abort` Cleanup-Block Reachability & Erasure Soundness**:
For any pre-pass well-formed `prog` satisfying `ForeignContractOK prog`, `PrePassNoBogusUnreachable prog`,
`prog.strategy = .abort`, and `NoUnwindingCalls prog` (no unwinding foreign items called in `-C panic=abort`),
letting `prog' := abortUnwindingCallsProg prog` and `progE := eraseDeadCleanupProg prog'`:
1. Every reachable basic block in `prog'` has `isCleanup = false` (`panicAbort_cleanup_unreachable`).
2. `progE` contains ZERO cleanup blocks anywhere (`eraseDeadCleanup_zero_cleanup_blocks`).
3. `progE` preserves `MirPostPassWF`, `ForeignContractOK`, `PostPassNoBogusUnreachable`, and `∀ fuel arg, ¬ mirIsBad (evalMirProg progE fuel arg)`.
4. Pre-erasure `prog'` and post-erasure `progE` execute in exact lockstep (`MirCleanupEraseResultEq`), never unwind (`≠ .unwound tr`), and agree identically on every returned value, abort, and trace. -/
theorem eraseDeadCleanup_preserves_WF_and_exec (prog : Program)
    (hpre : MirPrePassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PrePassNoBogusUnreachable prog) (hnoUnw : NoUnwindingCalls prog)
    (hstrat : prog.strategy = .abort) :
    let prog' := abortUnwindingCallsProg prog
    let progE := eraseDeadCleanupProg prog'
    MirPostPassWF progE ∧
    ForeignContractOK progE ∧
    PostPassNoBogusUnreachable progE ∧
    (listForall (fun fn => fn.isForeign = false → listForall (fun blk => blk.isCleanup = false) fn.blocks) progE.fns) ∧
    (∀ fid fn' b blk', listGet? prog'.fns fid = some fn' → fn'.isForeign = false →
      ReachableBB fn'.blocks b → listGet? fn'.blocks b = some blk' → blk'.isCleanup = false) ∧
    (∀ fuel arg, ¬ mirIsBad (evalMirProg progE fuel arg) ∧
      MirCleanupEraseResultEq (evalMirProg prog' fuel arg) (evalMirProg progE fuel arg) ∧
      (∀ tr, evalMirProg prog' fuel arg ≠ .unwound tr) ∧
      (∀ tr, evalMirProg progE fuel arg ≠ .unwound tr)) := by
  intro prog' progE
  have hpost' := abortUnwindingCallsProg_postWF prog hpre
  have hfok' := abortUnwindingCalls_preserves_foreignContract prog hfok
  have hnob' := abortUnwindingCallsProg_postNoBogus prog hpre hnob
  have hnu' := abortUnwindingCalls_preserves_NoUnwindingCalls prog hpre hnoUnw
  have hpostE := eraseDeadCleanup_preserves_postWF prog' hpost' hnu'
  have hfokE := eraseDeadCleanupProg_preserves_foreignContract prog' hfok'
  have hnobE := eraseDeadCleanup_preserves_postNoBogus prog' hpost' hnob' hnu'
  refine ⟨hpostE, hfokE, hnobE, eraseDeadCleanup_zero_cleanup_blocks prog', ?_, ?_⟩
  · intro fid fn' b blk' hfn hnonF hreach hblk
    exact panicAbort_cleanup_unreachable prog' hpost' hnu' fid fn' hfn hnonF b hreach blk' hblk
  · intro fuel arg
    refine ⟨evalMirProg_safe progE hpostE hfokE hnobE fuel arg, ?_⟩
    obtain ⟨st1, hinit1, hsafe1⟩ := initMirState_runtimeSafe prog' arg hpost'
    obtain ⟨entry, hentry, henonF⟩ := hpost'.2.1
    unfold evalMirProg
    rw [hinit1]
    unfold initMirState at hinit1
    rw [hentry] at hinit1
    cases hinit1
    have hentryE : listGet? progE.fns progE.entryFn = some (eraseDeadCleanupFn entry) := by
      unfold progE eraseDeadCleanupProg; dsimp only; rw [listGet?_listMap, hentry]
    have hm := eraseDeadCleanupFn_preserves_metadata entry
    unfold initMirState
    rw [hentryE]; dsimp only
    rw [hm.2.2.2]
    refine eraseDeadCleanup_run_sim prog' hpost' hfok' hnob' hnu' hstrat fuel _ _ hsafe1 ?_
    exact ⟨entry, hentry, henonF, rfl, by rw [countNonCleanupBefore_zero], rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-! ## Section 12: Main Theorem 4 — LLVM `call`/`invoke` & `nounwind` Attribute Soundness -/

/-- Exact outcome equivalence between post-pass MIR execution and lowered LLVM IR execution. -/
noncomputable def MirLlvmResultEq : MirExecResult → LlvmExecResult → Prop
  | .returned v1 tr1, .returned v2 tr2 => v1 = v2 ∧ tr1 = tr2
  | .unwound tr1, .unwound tr2 => tr1 = tr2
  | .terminated r1 tr1, .terminated r2 tr2 => r1 = r2 ∧ tr1 = tr2
  | .aborted tr1, .aborted tr2 => tr1 = tr2
  | .outOfFuel _, .outOfFuel _ => True
  | _, _ => False

theorem mirLlvmResultEq_not_bad {mres : MirExecResult} {lres : LlvmExecResult}
    (heq : MirLlvmResultEq mres lres) (hm : ¬ mirIsBad mres) : ¬ llvmIsBad lres := by
  cases mres <;> cases lres <;> dsimp only [MirLlvmResultEq, mirIsBad, llvmIsBad] at * <;>
    first | exact (fun h => h) | exact absurd trivial hm | exact False.elim heq

theorem mirLlvmResultEq_unwound {mres : MirExecResult} {lres : LlvmExecResult}
    {tr : List TraceEvent} (heq : MirLlvmResultEq mres lres) (hl : lres = .unwound tr) :
    mres = .unwound tr := by
  rw [hl] at heq
  cases mres with
  | unwound tr1 =>
    dsimp only [MirLlvmResultEq] at heq
    rw [heq]
  | returned _ _ | terminated _ _ | aborted _ | ub _ | invalid _ | outOfFuel _ =>
    exact False.elim heq

/-- Relation linking MIR call-site unwind action and lowered LLVM `callPlain`/`invoke` handler. -/
noncomputable def MirLlvmContHandlerRel (calleeUnw : Bool) (u : UnwindAction)
    (h : LlvmUnwindHandler) : Prop :=
  match calleeUnw with
  | false => h = .propagate true
  | true =>
    match u with
    | .cleanup c => h = .pad (.cleanupPad c)
    | .terminate r => h = .pad (.filterTerminatePad r)
    | .continue_ => h = .propagate false
    | .unreachable => h = .propagate true

theorem llvmLowerCallTerm_handlerRel (callUnw : Bool) (callee : FnId) (isDrop : Bool)
    (arg dst : LocalId) (rt : BlockId) (u : UnwindAction) :
    match llvmLowerCallTerm callUnw callee isDrop arg dst rt u with
    | .callPlain _ _ _ _ _ ub => MirLlvmContHandlerRel callUnw u (.propagate ub)
    | .invoke _ _ _ _ _ pad => MirLlvmContHandlerRel callUnw u (.pad pad)
    | _ => False := by
  unfold llvmLowerCallTerm MirLlvmContHandlerRel
  cases callUnw <;> cases u <;> rfl

/-- Relation between active MIR frame `mf` and lowered LLVM frame `lf`. -/
noncomputable def MirLlvmFrameEq (prog' : Program) (fn : FnBody)
    (mf : ActiveFrame) (lf : LlvmActiveFrame) : Prop :=
  lf.fnId = mf.fnId ∧
  lf.hasNoUnwind = bnot (bodyCanUnwind prog'.strategy fn) ∧
  lf.bb = mf.bb ∧
  lf.stmtIdx = mf.stmtIdx ∧
  lf.locals = mf.locals ∧
  lf.inCleanup = mf.inCleanup

/-- Relation between saved MIR continuation `mc` and lowered LLVM continuation `lc`. -/
noncomputable def MirLlvmContRel (prog' : Program) (calleeUnw : Bool)
    (cfn : FnBody) (mc : CallerCont) (lc : LlvmCallerCont) : Prop :=
  lc.fnId = mc.fnId ∧
  lc.hasNoUnwind = bnot (bodyCanUnwind prog'.strategy cfn) ∧
  lc.locals = mc.locals ∧
  lc.inCleanup = mc.inCleanup ∧
  lc.retDst = mc.retDst ∧
  lc.retTarget = mc.retTarget ∧
  MirLlvmContHandlerRel calleeUnw mc.unwindOnCall lc.handler

/-- Inductive stack correspondence indexed by the current callee's `bodyCanUnwind` flag. -/
noncomputable def MirLlvmStackRel (prog' : Program) :
    Bool → List CallerCont → List LlvmCallerCont → Prop
  | _, [], [] => True
  | calleeUnw, mc :: mrest, lc :: lrest =>
    ∃ cfn,
      listGet? prog'.fns mc.fnId = some cfn ∧
      cfn.isForeign = false ∧
      MirLlvmContRel prog' calleeUnw cfn mc lc ∧
      MirLlvmStackRel prog' (bodyCanUnwind prog'.strategy cfn) mrest lrest
  | _, _, _ => False

/-- Full machine-state correspondence between post-pass MIR state and lowered LLVM IR state. -/
noncomputable def MirLlvmStateRel (prog' : Program) (mst : MirState) (lst : LlvmState) : Prop :=
  ∃ fn,
    listGet? prog'.fns mst.cur.fnId = some fn ∧
    fn.isForeign = false ∧
    MirLlvmFrameEq prog' fn mst.cur lst.cur ∧
    lst.cleanupDepth = mst.cleanupDepth ∧
    lst.trace = mst.trace ∧
    MirLlvmStackRel prog' (bodyCanUnwind prog'.strategy fn) mst.stack lst.stack

/-- Combined step relation enforcing lockstep progression AND runtime safety. -/
noncomputable def MirLlvmStepRel (prog' : Program) : MirStep → LlvmStep → Prop
  | .running mst', .running lst' => MirLlvmStateRel prog' mst' lst' ∧ MirRuntimeSafe prog' mst'
  | .halted mres, .halted lres => MirLlvmResultEq mres lres
  | _, _ => False

theorem stepLlvm_stmt_eq {lprog : LlvmProg} {st : LlvmState} {fn : LlvmFn} {blk : LlvmBlock}
    {stmt : Stmt}
    (hfn : listGet? lprog.fns st.cur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hblk : listGet? fn.blocks st.cur.bb = some blk) (hceq : st.cur.inCleanup = blk.isCleanup)
    (hstmt : listGet? blk.stmts st.cur.stmtIdx = some stmt) :
    stepLlvm lprog st = execLlvmStmt st stmt := by
  unfold stepLlvm
  rw [hfn]; dsimp only
  rw [hnonF]; dsimp only
  rw [hblk]; dsimp only
  rw [← hceq, boolEq_refl]; dsimp only
  rw [hstmt]

theorem stepLlvm_term_eq {lprog : LlvmProg} {st : LlvmState} {fn : LlvmFn} {blk : LlvmBlock}
    (hfn : listGet? lprog.fns st.cur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hblk : listGet? fn.blocks st.cur.bb = some blk) (hceq : st.cur.inCleanup = blk.isCleanup)
    (hnone : listGet? blk.stmts st.cur.stmtIdx = none) (hlen : st.cur.stmtIdx = listLen blk.stmts) :
    stepLlvm lprog st = execLlvmTerm lprog st blk.term := by
  unfold stepLlvm
  rw [hfn]; dsimp only
  rw [hnonF]; dsimp only
  rw [hblk]; dsimp only
  rw [← hceq, boolEq_refl]; dsimp only
  rw [hnone]; dsimp only
  rw [hlen, natEq_refl]

theorem enterLlvmPad_terminate_eq {fns : List LlvmFn} {cur : LlvmActiveFrame}
    {stk : List LlvmCallerCont} {r : UnwindTerminateReason} {depth : Nat} {tr : List TraceEvent} :
    enterLlvmPad fns cur stk (.filterTerminatePad r) depth tr = .halted (.terminated r tr) := rfl

theorem enterLlvmPad_cleanup_eq {fns : List LlvmFn} {cur : LlvmActiveFrame}
    {stk : List LlvmCallerCont} {c depth : Nat} {tr : List TraceEvent}
    {fn : LlvmFn} {pb : LlvmBlock}
    (hfn : listGet? fns cur.fnId = some fn) (hpb : listGet? fn.blocks c = some pb)
    (hpbc : pb.isCleanup = true) :
    enterLlvmPad fns cur stk (.cleanupPad c) depth tr =
      .running { cur := { cur with bb := c, stmtIdx := 0, inCleanup := true },
                 stack := stk, cleanupDepth := depth + 1, trace := tr } := by
  unfold enterLlvmPad
  rw [hfn]; dsimp only
  rw [hpb]; dsimp only
  rw [hpbc]

/-- Unified LLVM unwind dispatch matching MIR `UnwindAction` whenever `callUnw = true`
(lowered via `invoke` + cleanup/terminate landingpad or `call` unwind continuation). -/
noncomputable def llvmDispatchUnwind (lprog : LlvmProg) (lcur : LlvmActiveFrame)
    (lstack : List LlvmCallerCont) (u : UnwindAction) (depth : Nat)
    (trace : List TraceEvent) : LlvmStep :=
  match u with
  | .cleanup c => enterLlvmPad lprog.fns lcur lstack (.cleanupPad c) depth trace
  | .terminate r => enterLlvmPad lprog.fns lcur lstack (.filterTerminatePad r) depth trace
  | .continue_ => propagateLlvmUnwind lprog.fns lcur.hasNoUnwind lstack depth trace
  | .unreachable => .halted (.ub trace)

theorem dispatchUnwind_llvm_sim (prog' : Program)
    (_hpost : MirPostPassWF prog') (hts : prog'.targetSupportsUnwinding = true)
    (mcur : ActiveFrame) (lcur : LlvmActiveFrame)
    (mstack : List CallerCont) (lstack : List LlvmCallerCont)
    (u : UnwindAction) (depth : Nat) (trace : List TraceEvent)
    (fn : FnBody) (hfn : listGet? prog'.fns mcur.fnId = some fn) (hnonF : fn.isForeign = false)
    (hmcurLoc : listLen mcur.locals = fn.localCount)
    (hfEq : MirLlvmFrameEq prog' fn mcur lcur)
    (huWF : PostPassUnwindEdgeWF prog'.targetSupportsUnwinding (bodyCanUnwind prog'.strategy fn)
      true fn.blocks mcur.inCleanup u)
    (huNE : u ≠ .unreachable)
    (hdepth : depth = countCleanupActive mcur.inCleanup mstack)
    (hstackWF : StackPostWF prog' (bodyCanUnwind prog'.strategy fn) mstack)
    (hstackNB : StackContNoBogus prog' (bodyCanUnwind prog'.strategy fn) mstack)
    (hstkRel : MirLlvmStackRel prog' (bodyCanUnwind prog'.strategy fn) mstack lstack) :
    MirLlvmStepRel prog'
      (dispatchUnwind prog'.fns mcur mstack u depth trace)
      (llvmDispatchUnwind (llvmLowerProg prog') lcur lstack u depth trace) := by
  induction mstack generalizing mcur lcur lstack u fn depth with
  | nil =>
    cases lstack with
    | cons _ _ => exact False.elim hstkRel
    | nil =>
      cases u with
      | unreachable => exact absurd rfl huNE
      | terminate r =>
        rw [dispatchUnwind_terminate_eq]
        unfold llvmDispatchUnwind; dsimp only
        rw [enterLlvmPad_terminate_eq]
        exact ⟨rfl, rfl⟩
      | cleanup padBB =>
        obtain ⟨hnc, padBlk, hpadGet, hpadC⟩ := huWF.1
        rw [dispatchUnwind_cleanup_eq hfn hpadGet hpadC]
        have hlfn : listGet? (llvmLowerProg prog').fns lcur.fnId = some (llvmLowerFn prog' fn) := by
          unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hfEq.1, hfn]
        have hlpb : listGet? (llvmLowerFn prog' fn).blocks padBB = some (llvmLowerBlock prog' padBlk) := by
          unfold llvmLowerFn; dsimp only; rw [listGet?_listMap, hpadGet]
        have hlpbc : (llvmLowerBlock prog' padBlk).isCleanup = true := hpadC
        unfold llvmDispatchUnwind; dsimp only
        rw [enterLlvmPad_cleanup_eq hlfn hlpb hlpbc]
        refine ⟨⟨fn, hfn, hnonF, ⟨hfEq.1, hfEq.2.1, rfl, rfl, hfEq.2.2.2.2.1, rfl⟩, rfl, rfl, trivial⟩, ?_⟩
        refine ⟨fn, hfn, ⟨fn, padBlk, hfn, hnonF, hpadGet, hpadC.symm, rfl, hmcurLoc⟩,
          trivial, trivial, by unfold countCleanupActive; rw [hdepth, hnc]; rfl,
          (fun hf => by rw [hts] at hf; cases hf), (fun hf => by rw [hts] at hf; cases hf)⟩
      | continue_ =>
        have hbu : bodyCanUnwind prog'.strategy fn = true := by
          cases hb : bodyCanUnwind prog'.strategy fn
          · exact absurd rfl (huWF.2.2 (Or.inr hb))
          · rfl
        have hlnoU : lcur.hasNoUnwind = false := by rw [hfEq.2.1, hbu]; rfl
        unfold dispatchUnwind llvmDispatchUnwind propagateLlvmUnwind
        rw [hlnoU]; dsimp only
        rfl
  | cons mc mrest ih =>
    cases lstack with
    | nil => exact False.elim hstkRel
    | cons lc lrest =>
      cases u with
      | unreachable => exact absurd rfl huNE
      | terminate r =>
        rw [dispatchUnwind_terminate_eq]
        unfold llvmDispatchUnwind; dsimp only
        rw [enterLlvmPad_terminate_eq]
        exact ⟨rfl, rfl⟩
      | cleanup padBB =>
        obtain ⟨hnc, padBlk, hpadGet, hpadC⟩ := huWF.1
        rw [dispatchUnwind_cleanup_eq hfn hpadGet hpadC]
        have hlfn : listGet? (llvmLowerProg prog').fns lcur.fnId = some (llvmLowerFn prog' fn) := by
          unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hfEq.1, hfn]
        have hlpb : listGet? (llvmLowerFn prog' fn).blocks padBB = some (llvmLowerBlock prog' padBlk) := by
          unfold llvmLowerFn; dsimp only; rw [listGet?_listMap, hpadGet]
        have hlpbc : (llvmLowerBlock prog' padBlk).isCleanup = true := hpadC
        unfold llvmDispatchUnwind; dsimp only
        rw [enterLlvmPad_cleanup_eq hlfn hlpb hlpbc]
        refine ⟨⟨fn, hfn, hnonF, ⟨hfEq.1, hfEq.2.1, rfl, rfl, hfEq.2.2.2.2.1, rfl⟩, rfl, rfl, hstkRel⟩, ?_⟩
        refine ⟨fn, hfn, ⟨fn, padBlk, hfn, hnonF, hpadGet, hpadC.symm, rfl, hmcurLoc⟩,
          hstackWF, hstackNB, by unfold countCleanupActive; rw [hdepth, hnc]; rfl,
          (fun hf => by rw [hts] at hf; cases hf), (fun hf => by rw [hts] at hf; cases hf)⟩
      | continue_ =>
        have hncCur : mcur.inCleanup = false := huWF.1
        have hbu : bodyCanUnwind prog'.strategy fn = true := by
          cases hb : bodyCanUnwind prog'.strategy fn
          · exact absurd rfl (huWF.2.2 (Or.inr hb))
          · rfl
        have hlnoU : lcur.hasNoUnwind = false := by rw [hfEq.2.1, hbu]; rfl
        rw [hbu] at hstackWF hstackNB hstkRel
        obtain ⟨cfn, hcfn, hcWF, hrestWF⟩ := hstackWF
        obtain ⟨hcNB, cfn2, hcfn2, hrestNB⟩ := hstackNB
        have hcfnEq : cfn2 = cfn := by rw [hcfn] at hcfn2; cases hcfn2; rfl
        rw [hcfnEq] at hrestNB
        obtain ⟨cfn3, hcfn3, _, hcRel, hrestRel⟩ := hstkRel
        have hcfnEq3 : cfn3 = cfn := by rw [hcfn] at hcfn3; cases hcfn3; rfl
        rw [hcfnEq3] at hcRel hrestRel
        obtain ⟨cfn', _, hcfn', hcfNonF, _, _, _, hcloc, hcEdge, _⟩ := hcWF
        have hcfnEq2 : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
        rw [hcfnEq2] at hcfNonF hcloc hcEdge
        have hcNE : mc.unwindOnCall ≠ .unreachable := by
          intro hbad
          cases hcNB hbad with
          | inl htsF => rw [hts] at htsF; cases htsF
          | inr hf => cases hf
        have hdepth' : depth = countCleanupActive mc.inCleanup mrest := by
          unfold countCleanupActive at hdepth ⊢
          rw [countCleanupStack_cons] at hdepth
          rw [hncCur] at hdepth
          cases hcc : mc.inCleanup
          · rw [hcc] at hdepth; exact hdepth
          · rw [hcc] at hdepth; exact hdepth
        unfold dispatchUnwind llvmDispatchUnwind propagateLlvmUnwind
        rw [hlnoU]; dsimp only
        let nextM : ActiveFrame := {
          fnId := mc.fnId, bb := mc.retTarget, stmtIdx := 0,
          locals := mc.locals, inCleanup := mc.inCleanup
        }
        let nextL : LlvmActiveFrame := {
          fnId := lc.fnId, hasNoUnwind := lc.hasNoUnwind, bb := lc.retTarget,
          stmtIdx := 0, locals := lc.locals, inCleanup := lc.inCleanup
        }
        have hnextFEq : MirLlvmFrameEq prog' cfn nextM nextL :=
          ⟨hcRel.1, hcRel.2.1, hcRel.2.2.2.2.2.1, rfl, hcRel.2.2.1, hcRel.2.2.2.1⟩
        have hcHandler := hcRel.2.2.2.2.2.2
        dsimp only [MirLlvmContHandlerRel] at hcHandler
        cases hmcu : mc.unwindOnCall with
        | unreachable => exact absurd hmcu hcNE
        | terminate r =>
          rw [hmcu] at hcHandler
          rw [hcHandler]; dsimp only
          rw [dispatchUnwind_terminate_eq, enterLlvmPad_terminate_eq]
          exact ⟨rfl, rfl⟩
        | cleanup padBB =>
          rw [hmcu] at hcHandler hcEdge
          rw [hcHandler]; dsimp only
          obtain ⟨hncMC, padBlk, hpadGet, hpadC⟩ := hcEdge.1
          rw [dispatchUnwind_cleanup_eq hcfn hpadGet hpadC]
          have hlcfn : listGet? (llvmLowerProg prog').fns nextL.fnId = some (llvmLowerFn prog' cfn) := by
            unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hnextFEq.1, hcfn]
          have hlpb : listGet? (llvmLowerFn prog' cfn).blocks padBB = some (llvmLowerBlock prog' padBlk) := by
            unfold llvmLowerFn; dsimp only; rw [listGet?_listMap, hpadGet]
          have hlpbc : (llvmLowerBlock prog' padBlk).isCleanup = true := hpadC
          rw [enterLlvmPad_cleanup_eq hlcfn hlpb hlpbc]
          refine ⟨⟨cfn, hcfn, hcfNonF, ⟨hcRel.1, hcRel.2.1, rfl, rfl, hcRel.2.2.1, rfl⟩, rfl, rfl, hrestRel⟩, ?_⟩
          refine ⟨cfn, hcfn, ⟨cfn, padBlk, hcfn, hcfNonF, hpadGet, hpadC.symm, rfl, hcloc⟩,
            hrestWF, hrestNB, by unfold countCleanupActive; rw [hdepth', hncMC]; rfl,
            (fun hf => by rw [hts] at hf; cases hf), (fun hf => by rw [hts] at hf; cases hf)⟩
        | continue_ =>
          rw [hmcu] at hcHandler hcEdge
          rw [hcHandler]; dsimp only
          have hih := ih nextM nextL lrest .continue_ depth cfn hcfn hcfNonF hcloc
            hnextFEq hcEdge (fun h => by cases h) hdepth' hrestWF hrestNB hrestRel
          exact hih

theorem llvmLowerCallTerm_dispatch_eq (lprog : LlvmProg) (lst : LlvmState)
    (callee : FnId) (isDrop : Bool) (argReg dst : LocalId) (rt : BlockId) (u : UnwindAction)
    (argVal : Nat) (evOpt : Option TraceEvent)
    (hspec : lprog.foreignSpecs callee argVal = .unwound evOpt)
    (hfor : (match listGet? lprog.fns callee with
      | some cfn => cfn.isForeign = true ∧ cfn.hasNoUnwind = false
      | none => False)) :
    (match llvmLowerCallTerm true callee isDrop argReg dst rt u with
     | .callPlain c d _a _ r ub =>
       match listGet? lprog.fns c with
       | none => .halted (.invalid lst.trace)
       | some cfn =>
         match cfn.isForeign with
         | true =>
           match lprog.foreignSpecs c argVal with
           | .ret v e => .running { lst with cur := { lst.cur with bb := r, stmtIdx := 0, locals := writeLocal lst.cur.locals (match d with | true => 0 | false => dst) v }, trace := appendOptEvent lst.trace e }
           | .unwound e =>
             let tr' := appendOptEvent lst.trace e
             match cfn.hasNoUnwind with
             | true => .halted (.ub tr')
             | false =>
               match ub with
               | true => .halted (.ub tr')
               | false => propagateLlvmUnwind lprog.fns lst.cur.hasNoUnwind lst.stack lst.cleanupDepth tr'
         | false => .halted (.invalid lst.trace)
     | .invoke c d _a _ r pad =>
       match listGet? lprog.fns c with
       | none => .halted (.invalid lst.trace)
       | some cfn =>
         match cfn.isForeign with
         | true =>
           match lprog.foreignSpecs c argVal with
           | .ret v e => .running { lst with cur := { lst.cur with bb := r, stmtIdx := 0, locals := writeLocal lst.cur.locals (match d with | true => 0 | false => dst) v }, trace := appendOptEvent lst.trace e }
           | .unwound e =>
             let tr' := appendOptEvent lst.trace e
             match cfn.hasNoUnwind with
             | true => .halted (.ub tr')
             | false => enterLlvmPad lprog.fns lst.cur lst.stack pad lst.cleanupDepth tr'
         | false => .halted (.invalid lst.trace)
     | _ => .halted (.invalid lst.trace)) =
      llvmDispatchUnwind lprog lst.cur lst.stack u lst.cleanupDepth (appendOptEvent lst.trace evOpt) := by
  cases hget : listGet? lprog.fns callee with
  | none => rw [hget] at hfor; exact False.elim hfor
  | some cfn =>
    rw [hget] at hfor
    obtain ⟨hcf, hnoU⟩ := hfor
    cases u <;> unfold llvmLowerCallTerm llvmDispatchUnwind <;> dsimp only <;>
      (rw [hget]; dsimp only; rw [hcf]; dsimp only; rw [hspec]; dsimp only; rw [hnoU])

theorem llvmLowerCallTerm_callPlain_eq (callUnw : Bool) (callee : FnId) (isDrop : Bool)
    (arg dst : LocalId) (rt : BlockId) (u : UnwindAction)
    (lc : FnId) (ldrop : Bool) (larg ldst : LocalId) (lrt : BlockId) (lub : Bool)
    (h : llvmLowerCallTerm callUnw callee isDrop arg dst rt u =
      .callPlain lc ldrop larg ldst lrt lub) :
    lc = callee ∧ ldrop = isDrop ∧ larg = arg ∧ ldst = dst ∧ lrt = rt := by
  unfold llvmLowerCallTerm at h
  cases callUnw <;> cases u <;> cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem llvmLowerCallTerm_invoke_eq (callUnw : Bool) (callee : FnId) (isDrop : Bool)
    (arg dst : LocalId) (rt : BlockId) (u : UnwindAction)
    (lc : FnId) (ldrop : Bool) (larg ldst : LocalId) (lrt : BlockId) (lpad : LlvmPad)
    (h : llvmLowerCallTerm callUnw callee isDrop arg dst rt u =
      .invoke lc ldrop larg ldst lrt lpad) :
    lc = callee ∧ ldrop = isDrop ∧ larg = arg ∧ ldst = dst ∧ lrt = rt := by
  unfold llvmLowerCallTerm at h
  cases callUnw <;> cases u <;> cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stepMir_llvm_lockstep (prog' : Program)
    (hpost : MirPostPassWF prog') (hfok : ForeignContractOK prog')
    (hnob : PostPassNoBogusUnreachable prog') (mst : MirState) (lst : LlvmState)
    (hsafe : MirRuntimeSafe prog' mst) (hrel : MirLlvmStateRel prog' mst lst) :
    MirLlvmStepRel prog' (stepMir prog' mst) (stepLlvm (llvmLowerProg prog') lst) := by
  have hsafeCopy := hsafe
  have hs := stepMir_preserves_safe prog' hpost hfok hnob mst hsafeCopy
  obtain ⟨fn, hfn, hnonF, hfeq, hdep, htr, hstk⟩ := hrel
  obtain ⟨fnW, hfnW, hact, hstackWF, hstackNB, hdepthEq, htsc, _⟩ := hsafe
  have hfnWEq : fnW = fn := by rw [hfn] at hfnW; cases hfnW; rfl
  rw [hfnWEq] at hstackWF hstackNB
  obtain ⟨fn', blk, hfn', _, hblk, hcleanEq, hstmtLe, hlocals⟩ := hact
  have hfnEq : fn' = fn := by rw [hfn] at hfn'; cases hfn'; rfl
  rw [hfnEq] at hblk hlocals
  have hlfn : listGet? (llvmLowerProg prog').fns lst.cur.fnId = some (llvmLowerFn prog' fn) := by
    unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hfeq.1, hfn]
  have hlnonF : (llvmLowerFn prog' fn).isForeign = false := hnonF
  have hlblk : listGet? (llvmLowerFn prog' fn).blocks lst.cur.bb = some (llvmLowerBlock prog' blk) := by
    unfold llvmLowerFn; dsimp only; rw [listGet?_listMap, hfeq.2.2.1, hblk]
  have hlcleanEq : lst.cur.inCleanup = (llvmLowerBlock prog' blk).isCleanup := by
    rw [hfeq.2.2.2.2.2, hcleanEq]; rfl
  have hfnWF := listGet?_listForall (PostPassFnWF prog') prog'.fns mst.cur.fnId fn hpost.2.2 hfn
  unfold PostPassFnWF at hfnWF; rw [hnonF] at hfnWF
  have hblkWF := listGet?_listForall (PostPassBlockWF prog' fn) fn.blocks mst.cur.bb blk hfnWF.2.2 hblk
  have hfnNB := listGet?_listForall _ prog'.fns mst.cur.fnId fn hnob.2 hfn hnonF
  have hblkNB := listGet?_listForall _ fn.blocks mst.cur.bb blk hfnNB hblk
  cases hsGet : listGet? blk.stmts mst.cur.stmtIdx with
  | some stmt =>
    have hlsGet : listGet? (llvmLowerBlock prog' blk).stmts lst.cur.stmtIdx = some stmt := by
      unfold llvmLowerBlock; dsimp only; rw [hfeq.2.2.2.1]; exact hsGet
    rw [stepMir_stmt_eq hfn hnonF hblk hcleanEq hsGet] at hs ⊢
    rw [stepLlvm_stmt_eq hlfn hlnonF hlblk hlcleanEq hlsGet]
    cases stmt with
    | nop =>
      unfold execStmt at hs ⊢; unfold execLlvmStmt; dsimp only [MirLlvmStepRel] at hs ⊢
      refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.1, by rw [hfeq.2.2.2.1],
        hfeq.2.2.2.2.1, hfeq.2.2.2.2.2⟩, hdep, htr, hstk⟩, hs⟩
    | emit ev =>
      unfold execStmt at hs ⊢; unfold execLlvmStmt; dsimp only [MirLlvmStepRel] at hs ⊢
      refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.1, by rw [hfeq.2.2.2.1],
        hfeq.2.2.2.2.1, hfeq.2.2.2.2.2⟩, hdep, by rw [htr], hstk⟩, hs⟩
    | assignConst dst val =>
      unfold execStmt at hs ⊢; unfold execLlvmStmt; dsimp only [MirLlvmStepRel] at hs ⊢
      refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.1, by rw [hfeq.2.2.2.1],
        by rw [hfeq.2.2.2.2.1], hfeq.2.2.2.2.2⟩, hdep, htr, hstk⟩, hs⟩
    | assignLocal dst src =>
      unfold execStmt readLocal? at hs ⊢; unfold execLlvmStmt readLocal?; dsimp only [MirLlvmStepRel] at hs ⊢
      cases hr : listGet? mst.cur.locals src with
      | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
      | some v =>
        have hrl : listGet? lst.cur.locals src = some v := by rw [hfeq.2.2.2.2.1]; exact hr
        rw [hr] at hs; rw [hrl]; dsimp only at hs ⊢
        refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.1, by rw [hfeq.2.2.2.1],
          by rw [hfeq.2.2.2.2.1], hfeq.2.2.2.2.2⟩, hdep, htr, hstk⟩, hs⟩
  | none =>
    have heqLen : mst.cur.stmtIdx = listLen blk.stmts :=
      listGet?_eq_none_implies_ge blk.stmts mst.cur.stmtIdx hsGet hstmtLe
    have hlsGet : listGet? (llvmLowerBlock prog' blk).stmts lst.cur.stmtIdx = none := by
      unfold llvmLowerBlock; dsimp only; rw [hfeq.2.2.2.1]; exact hsGet
    have hleqLen : lst.cur.stmtIdx = listLen (llvmLowerBlock prog' blk).stmts := by
      unfold llvmLowerBlock; dsimp only; rw [hfeq.2.2.2.1]; exact heqLen
    rw [stepMir_term_eq hfn hnonF hblk hcleanEq hsGet heqLen] at hs ⊢
    rw [stepLlvm_term_eq hlfn hlnonF hlblk hlcleanEq hlsGet hleqLen]
    unfold llvmLowerBlock; dsimp only
    have htermWF := hblkWF.2
    cases ht : blk.term with
    | goto target =>
      rw [ht] at hs
      unfold execTerm at hs ⊢; unfold llvmLowerTerm execLlvmTerm; dsimp only [MirLlvmStepRel] at hs ⊢
      refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, rfl, rfl, hfeq.2.2.2.2.1, hfeq.2.2.2.2.2⟩,
        hdep, htr, hstk⟩, hs⟩
    | branch cond z nz =>
      rw [ht] at hs
      unfold execTerm readLocal? at hs ⊢; unfold llvmLowerTerm execLlvmTerm readLocal?; dsimp only [MirLlvmStepRel] at hs ⊢
      cases hr : listGet? mst.cur.locals cond with
      | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
      | some v =>
        have hrl : listGet? lst.cur.locals cond = some v := by rw [hfeq.2.2.2.2.1]; exact hr
        rw [hr] at hs; rw [hrl]; dsimp only at hs ⊢
        cases v with
        | zero =>
          refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, rfl, rfl, hfeq.2.2.2.2.1, hfeq.2.2.2.2.2⟩,
            hdep, htr, hstk⟩, hs⟩
        | succ _ =>
          refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, rfl, rfl, hfeq.2.2.2.2.1, hfeq.2.2.2.2.2⟩,
            hdep, htr, hstk⟩, hs⟩
    | return_ valReg =>
      rw [ht] at hs
      unfold execTerm readLocal? at hs ⊢; unfold llvmLowerTerm execLlvmTerm readLocal?; dsimp only at hs ⊢
      cases hinc : mst.cur.inCleanup with
      | true => rw [hinc] at hs; dsimp only at hs; exact absurd trivial hs
      | false =>
        have hlinc : lst.cur.inCleanup = false := hfeq.2.2.2.2.2.trans hinc
        rw [hinc] at hs; rw [hlinc]; dsimp only at hs ⊢
        cases hr : listGet? mst.cur.locals valReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some v =>
          have hrl : listGet? lst.cur.locals valReg = some v := by rw [hfeq.2.2.2.2.1]; exact hr
          rw [hr] at hs; rw [hrl]; dsimp only at hs ⊢
          cases hms : mst.stack with
          | nil =>
            rw [hms] at hstk
            cases hls : lst.stack with
            | cons _ _ => rw [hls] at hstk; exact False.elim hstk
            | nil =>
              dsimp only [MirLlvmStepRel, MirLlvmResultEq]
              exact ⟨rfl, htr.symm⟩
          | cons mc mrest =>
            rw [hms] at hstk hs
            cases hls : lst.stack with
            | nil => rw [hls] at hstk; exact False.elim hstk
            | cons lc lrest =>
              rw [hls] at hstk
              obtain ⟨cfn, hcfn, hcfNonF, hcRel, hrestRel⟩ := hstk
              dsimp only at hs ⊢
              refine ⟨⟨cfn, hcfn, hcfNonF, ⟨hcRel.1, hcRel.2.1, hcRel.2.2.2.2.2.1, rfl,
                by rw [hcRel.2.2.1, hcRel.2.2.2.2.1], hcRel.2.2.2.1⟩, hdep, htr, hrestRel⟩, hs⟩
    | unreachable =>
      have htsB := hblkNB.2.1
      have hnc := hblkNB.1
      cases hcu : mst.cur.inCleanup
      · rw [← hcleanEq, hcu] at hnc; exact absurd ht (hnc rfl)
      · cases hts0 : prog'.targetSupportsUnwinding
        · rw [htsc hts0] at hcu; cases hcu
        · exact absurd ht (htsB hts0)
    | unwindTerminate reason =>
      unfold execTerm llvmLowerTerm execLlvmTerm; dsimp only [MirLlvmStepRel, MirLlvmResultEq]
      exact ⟨rfl, htr.symm⟩
    | unwindResume =>
      have htsBody := htermWF.2.1 ht
      obtain ⟨hts, hbu⟩ := htsBody
      have hpt := htermWF.1; rw [ht] at hpt
      have hcurC : mst.cur.inCleanup = true := by rw [hcleanEq, hpt]
      have hlcurC : lst.cur.inCleanup = true := hfeq.2.2.2.2.2.trans hcurC
      rw [ht] at hs
      unfold execTerm at hs ⊢; unfold llvmLowerTerm execLlvmTerm
      rw [hcurC] at hs ⊢; rw [hlcurC]; dsimp only at hs ⊢
      cases hms : mst.stack with
      | nil =>
        cases hls : lst.stack with
        | cons _ _ => rw [hms, hls] at hstk; exact False.elim hstk
        | nil =>
          have hlnoU : lst.cur.hasNoUnwind = false := by rw [hfeq.2.1, hbu]; rfl
          unfold propagateLlvmUnwind
          rw [hlnoU]; dsimp only [MirLlvmStepRel, MirLlvmResultEq]
          exact htr.symm
      | cons mc mrest =>
        rw [hms] at hstk hs hstackWF hstackNB hdepthEq
        cases hls : lst.stack with
        | nil => rw [hls] at hstk; exact False.elim hstk
        | cons lc lrest =>
          rw [hls] at hstk
          rw [hbu] at hstk hstackWF hstackNB
          obtain ⟨cfn, hcfn, hcfNonF, hcRel, hrestRel⟩ := hstk
          obtain ⟨cfn', hcfn', hcWF, hrestWF⟩ := hstackWF
          have hcfnEq1 : cfn' = cfn := by rw [hcfn] at hcfn'; cases hcfn'; rfl
          rw [hcfnEq1] at hrestWF
          obtain ⟨hcNB, cfn2, hcfn2, hrestNB⟩ := hstackNB
          have hcfnEq2 : cfn2 = cfn := by rw [hcfn] at hcfn2; cases hcfn2; rfl
          rw [hcfnEq2] at hrestNB
          obtain ⟨cfn'', _, hcfn'', _, _, _, _, hcloc, hcEdge, _⟩ := hcWF
          have hcfnEq3 : cfn'' = cfn := by rw [hcfn] at hcfn''; cases hcfn''; rfl
          rw [hcfnEq3] at hcloc hcEdge
          have hcNE : mc.unwindOnCall ≠ .unreachable := by
            intro hbad
            cases hcNB hbad with
            | inl htsF => rw [hts] at htsF; cases htsF
            | inr hf => cases hf
          have hdepth' : (match mst.cleanupDepth with | 0 => 0 | d + 1 => d) =
              countCleanupActive mc.inCleanup mrest := by
            unfold countCleanupActive at hdepthEq ⊢
            rw [countCleanupStack_cons] at hdepthEq
            rw [hcurC] at hdepthEq
            cases hcc : mc.inCleanup <;> rw [hcc] at hdepthEq <;> rw [hdepthEq] <;> rfl
          have hlnoU : lst.cur.hasNoUnwind = false := by rw [hfeq.2.1, hbu]; rfl
          unfold propagateLlvmUnwind
          rw [hlnoU]; dsimp only
          let nextM : ActiveFrame := {
            fnId := mc.fnId, bb := mc.retTarget, stmtIdx := 0,
            locals := mc.locals, inCleanup := mc.inCleanup
          }
          let nextL : LlvmActiveFrame := {
            fnId := lc.fnId, hasNoUnwind := lc.hasNoUnwind, bb := lc.retTarget,
            stmtIdx := 0, locals := lc.locals, inCleanup := lc.inCleanup
          }
          have hnextFEq : MirLlvmFrameEq prog' cfn nextM nextL :=
            ⟨hcRel.1, hcRel.2.1, hcRel.2.2.2.2.2.1, rfl, hcRel.2.2.1, hcRel.2.2.2.1⟩
          have hcHandler := hcRel.2.2.2.2.2.2
          dsimp only [MirLlvmContHandlerRel] at hcHandler
          have hsim := dispatchUnwind_llvm_sim prog' hpost hts nextM nextL mrest lrest
            mc.unwindOnCall (match mst.cleanupDepth with | 0 => 0 | d + 1 => d) mst.trace
            cfn hcfn hcfNonF hcloc hnextFEq hcEdge hcNE hdepth' hrestWF hrestNB hrestRel
          rw [hdep, htr]
          cases hmcu : mc.unwindOnCall with
          | unreachable => exact absurd hmcu hcNE
          | terminate r =>
            rw [hmcu] at hcHandler hsim
            rw [hcHandler]
            exact hsim
          | cleanup padBB =>
            rw [hmcu] at hcHandler hsim
            rw [hcHandler]
            exact hsim
          | continue_ =>
            rw [hmcu] at hcHandler hsim
            rw [hcHandler]
            exact hsim
    | call callee argReg dst rt u =>
      rw [ht] at hs
      unfold execTerm readLocal? at hs ⊢; unfold llvmLowerTerm; dsimp only at hs ⊢
      have hcallUnw := llvmLowerCallTerm_handlerRel (calleeCanUnwind prog' callee) callee false argReg dst rt u
      cases hlc : llvmLowerCallTerm (calleeCanUnwind prog' callee) callee false argReg dst rt u with
      | br _ | condBr _ _ _ | ret _ | unreachable | resume | terminateDirect _ | panicPlain _ | panicInvoke _ | panicAbort =>
        rw [hlc] at hcallUnw; exact False.elim hcallUnw
      | callPlain lc ldrop larg ldst lrt lub =>
        rw [hlc] at hcallUnw; dsimp only at hcallUnw
        obtain ⟨hlc1, hlc2, hlc3, hlc4, hlc5⟩ :=
          llvmLowerCallTerm_callPlain_eq (calleeCanUnwind prog' callee) callee false argReg dst rt u
            lc ldrop larg ldst lrt lub hlc
        unfold execLlvmTerm readLocal?
        rw [hlc1, hlc2, hlc3, hlc4, hlc5]; dsimp only
        cases hr : listGet? mst.cur.locals argReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some argVal =>
          have hrl : listGet? lst.cur.locals argReg = some argVal := by rw [hfeq.2.2.2.2.1]; exact hr
          rw [hr] at hs; rw [hrl]; dsimp only at hs ⊢
          unfold enterCall at hs ⊢; unfold enterLlvmCall; dsimp only at hs ⊢
          cases hcget : listGet? prog'.fns callee with
          | none => rw [hcget] at hs; dsimp only at hs; exact absurd trivial hs
          | some cfn =>
            have hlcget : listGet? (llvmLowerProg prog').fns callee = some (llvmLowerFn prog' cfn) := by
              unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hcget]
            rw [hcget] at hs; rw [hlcget]; dsimp only at hs ⊢
            have hccuEq : calleeCanUnwind prog' callee = bodyCanUnwind prog'.strategy cfn := by
              unfold calleeCanUnwind; rw [hcget]
            rw [hccuEq] at hcallUnw
            have hlcf : (llvmLowerFn prog' cfn).isForeign = cfn.isForeign := rfl
            cases hcf : cfn.isForeign with
            | false =>
              rw [hcf] at hs; rw [hlcf, hcf]; dsimp only at hs ⊢
              refine ⟨⟨cfn, hcget, hcf, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hdep, htr, ?_⟩, hs⟩
              exact ⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.2.2.1, hfeq.2.2.2.2.2,
                rfl, rfl, hcallUnw⟩, hstk⟩
            | true =>
              rw [hcf] at hs; rw [hlcf, hcf]; dsimp only at hs ⊢
              cases hfo : prog'.foreignSpecs callee argVal with
              | ret retV evOpt =>
                have hlfo : (llvmLowerProg prog').foreignSpecs callee argVal = .ret retV evOpt := hfo
                rw [hfo] at hs; rw [hlfo]; dsimp only at hs ⊢
                refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, rfl, rfl, by rw [hfeq.2.2.2.2.1], hfeq.2.2.2.2.2⟩,
                  hdep, by rw [htr], hstk⟩, hs⟩
              | unwound evOpt =>
                have hlfo : (llvmLowerProg prog').foreignSpecs callee argVal = .unwound evOpt := hfo
                rw [hfo] at hs; rw [hlfo]; dsimp only at hs ⊢
                have hcbU : bodyCanUnwind prog'.strategy cfn = true := by
                  cases hb0 : bodyCanUnwind prog'.strategy cfn
                  · exact absurd hfo (hfok callee argVal |> fun h => by rw [hcget] at h; exact h hcf hb0 evOpt)
                  · rfl
                have hts : prog'.targetSupportsUnwinding = true := by
                  cases hts0 : prog'.targetSupportsUnwinding
                  · exact absurd hfo (hnob.1 hts0 callee argVal evOpt)
                  · rfl
                have hlnoU : (llvmLowerFn prog' cfn).hasNoUnwind = false := by
                  unfold llvmLowerFn; dsimp only; rw [hcbU]; rfl
                rw [hlnoU]; dsimp only
                rw [hcbU] at hcallUnw
                have hpe := htermWF.2.2; rw [ht] at hpe
                dsimp only [termUnwind?, termCallCanUnwind] at hpe
                rw [hccuEq, hcbU, ← hcleanEq] at hpe
                have huNE : u ≠ .unreachable := by
                  intro hbad
                  have hnb := hblkNB.2.2
                  rw [ht, hbad] at hnb; dsimp only [termUnwind?, termCallCanUnwind] at hnb
                  cases hnb rfl with
                  | inl hf2 => rw [hts] at hf2; cases hf2
                  | inr hf2 => rw [hccuEq, hcbU] at hf2; cases hf2
                have hsim := dispatchUnwind_llvm_sim prog' hpost hts mst.cur lst.cur mst.stack lst.stack
                  u mst.cleanupDepth (appendOptEvent mst.trace evOpt) fn hfn hnonF hlocals
                  hfeq hpe huNE hdepthEq hstackWF hstackNB hstk
                rw [hdep, htr]
                dsimp only [MirLlvmContHandlerRel] at hcallUnw
                cases hu0 : u with
                | cleanup _ => rw [hu0] at hcallUnw; cases hcallUnw
                | terminate _ => rw [hu0] at hcallUnw; cases hcallUnw
                | unreachable => exact absurd hu0 huNE
                | continue_ =>
                  rw [hu0] at hcallUnw hsim
                  have hlub : lub = false := by cases hcallUnw; rfl
                  unfold llvmDispatchUnwind at hsim
                  rw [hlub]; dsimp only
                  exact hsim
      | invoke lc ldrop larg ldst lrt lpad =>
        rw [hlc] at hcallUnw; dsimp only at hcallUnw
        obtain ⟨hlc1, hlc2, hlc3, hlc4, hlc5⟩ :=
          llvmLowerCallTerm_invoke_eq (calleeCanUnwind prog' callee) callee false argReg dst rt u
            lc ldrop larg ldst lrt lpad hlc
        unfold execLlvmTerm readLocal?
        rw [hlc1, hlc2, hlc3, hlc4, hlc5]; dsimp only
        cases hr : listGet? mst.cur.locals argReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some argVal =>
          have hrl : listGet? lst.cur.locals argReg = some argVal := by rw [hfeq.2.2.2.2.1]; exact hr
          rw [hr] at hs; rw [hrl]; dsimp only at hs ⊢
          unfold enterCall at hs ⊢; unfold enterLlvmCall; dsimp only at hs ⊢
          cases hcget : listGet? prog'.fns callee with
          | none => rw [hcget] at hs; dsimp only at hs; exact absurd trivial hs
          | some cfn =>
            have hlcget : listGet? (llvmLowerProg prog').fns callee = some (llvmLowerFn prog' cfn) := by
              unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hcget]
            rw [hcget] at hs; rw [hlcget]; dsimp only at hs ⊢
            have hccuEq : calleeCanUnwind prog' callee = bodyCanUnwind prog'.strategy cfn := by
              unfold calleeCanUnwind; rw [hcget]
            rw [hccuEq] at hcallUnw
            have hlcf : (llvmLowerFn prog' cfn).isForeign = cfn.isForeign := rfl
            cases hcf : cfn.isForeign with
            | false =>
              rw [hcf] at hs; rw [hlcf, hcf]; dsimp only at hs ⊢
              refine ⟨⟨cfn, hcget, hcf, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hdep, htr, ?_⟩, hs⟩
              exact ⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.2.2.1, hfeq.2.2.2.2.2,
                rfl, rfl, hcallUnw⟩, hstk⟩
            | true =>
              rw [hcf] at hs; rw [hlcf, hcf]; dsimp only at hs ⊢
              cases hfo : prog'.foreignSpecs callee argVal with
              | ret retV evOpt =>
                have hlfo : (llvmLowerProg prog').foreignSpecs callee argVal = .ret retV evOpt := hfo
                rw [hfo] at hs; rw [hlfo]; dsimp only at hs ⊢
                refine ⟨⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, rfl, rfl, by rw [hfeq.2.2.2.2.1], hfeq.2.2.2.2.2⟩,
                  hdep, by rw [htr], hstk⟩, hs⟩
              | unwound evOpt =>
                have hlfo : (llvmLowerProg prog').foreignSpecs callee argVal = .unwound evOpt := hfo
                rw [hfo] at hs; rw [hlfo]; dsimp only at hs ⊢
                have hcbU : bodyCanUnwind prog'.strategy cfn = true := by
                  cases hb0 : bodyCanUnwind prog'.strategy cfn
                  · exact absurd hfo (hfok callee argVal |> fun h => by rw [hcget] at h; exact h hcf hb0 evOpt)
                  · rfl
                have hts : prog'.targetSupportsUnwinding = true := by
                  cases hts0 : prog'.targetSupportsUnwinding
                  · exact absurd hfo (hnob.1 hts0 callee argVal evOpt)
                  · rfl
                have hlnoU : (llvmLowerFn prog' cfn).hasNoUnwind = false := by
                  unfold llvmLowerFn; dsimp only; rw [hcbU]; rfl
                rw [hlnoU]; dsimp only
                rw [hcbU] at hcallUnw
                have hpe := htermWF.2.2; rw [ht] at hpe
                dsimp only [termUnwind?, termCallCanUnwind] at hpe
                rw [hccuEq, hcbU, ← hcleanEq] at hpe
                have huNE : u ≠ .unreachable := by
                  intro hbad
                  have hnb := hblkNB.2.2
                  rw [ht, hbad] at hnb; dsimp only [termUnwind?, termCallCanUnwind] at hnb
                  cases hnb rfl with
                  | inl hf2 => rw [hts] at hf2; cases hf2
                  | inr hf2 => rw [hccuEq, hcbU] at hf2; cases hf2
                have hsim := dispatchUnwind_llvm_sim prog' hpost hts mst.cur lst.cur mst.stack lst.stack
                  u mst.cleanupDepth (appendOptEvent mst.trace evOpt) fn hfn hnonF hlocals
                  hfeq hpe huNE hdepthEq hstackWF hstackNB hstk
                rw [hdep, htr]
                dsimp only [MirLlvmContHandlerRel] at hcallUnw
                cases hu0 : u with
                | continue_ => rw [hu0] at hcallUnw; cases hcallUnw
                | unreachable => exact absurd hu0 huNE
                | cleanup padBB =>
                  rw [hu0] at hcallUnw hsim
                  have hlpad : lpad = .cleanupPad padBB := by cases hcallUnw; rfl
                  unfold llvmDispatchUnwind at hsim
                  rw [hlpad]; exact hsim
                | terminate r =>
                  rw [hu0] at hcallUnw hsim
                  have hlpad : lpad = .filterTerminatePad r := by cases hcallUnw; rfl
                  unfold llvmDispatchUnwind at hsim
                  rw [hlpad]; exact hsim
    | drop df argReg rt u =>
      rw [ht] at hs
      unfold execTerm readLocal? at hs ⊢; unfold llvmLowerTerm; dsimp only at hs ⊢
      have hpt := htermWF.1; rw [ht] at hpt
      obtain ⟨_, ⟨dfn, hdfn, hdfNonF, hdfAbi, hdfPinD⟩, _⟩ := hpt
      have hdcuEq : dropCanUnwind prog' df = bodyCanUnwind prog'.strategy dfn :=
        dropCanUnwind_eq_bodyCanUnwind prog' df dfn hdfn hdfNonF hdfAbi hdfPinD
      have hcallUnw := llvmLowerCallTerm_handlerRel (dropCanUnwind prog' df) df true argReg 0 rt u
      cases hlc : llvmLowerCallTerm (dropCanUnwind prog' df) df true argReg 0 rt u with
      | br _ | condBr _ _ _ | ret _ | unreachable | resume | terminateDirect _ | panicPlain _ | panicInvoke _ | panicAbort =>
        rw [hlc] at hcallUnw; exact False.elim hcallUnw
      | callPlain lc ldrop larg ldst lrt lub =>
        rw [hlc] at hcallUnw; dsimp only at hcallUnw
        rw [hdcuEq] at hcallUnw
        obtain ⟨hlc1, hlc2, hlc3, _, hlc5⟩ :=
          llvmLowerCallTerm_callPlain_eq (dropCanUnwind prog' df) df true argReg 0 rt u
            lc ldrop larg ldst lrt lub hlc
        unfold execLlvmTerm readLocal?
        rw [hlc1, hlc2, hlc3, hlc5]; dsimp only
        cases hr : listGet? mst.cur.locals argReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some argVal =>
          have hrl : listGet? lst.cur.locals argReg = some argVal := by rw [hfeq.2.2.2.2.1]; exact hr
          rw [hr] at hs; rw [hrl]; dsimp only at hs ⊢
          unfold enterCall at hs ⊢; unfold enterLlvmCall; dsimp only at hs ⊢
          have hldfn : listGet? (llvmLowerProg prog').fns df = some (llvmLowerFn prog' dfn) := by
            unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hdfn]
          rw [hdfn] at hs ⊢; rw [hldfn]; dsimp only at hs ⊢
          have hldNonF : (llvmLowerFn prog' dfn).isForeign = false := hdfNonF
          rw [hdfNonF] at hs ⊢; rw [hldNonF]; dsimp only at hs ⊢
          refine ⟨⟨dfn, hdfn, hdfNonF, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hdep, htr, ?_⟩, hs⟩
          exact ⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.2.2.1, hfeq.2.2.2.2.2,
            rfl, rfl, hcallUnw⟩, hstk⟩
      | invoke lc ldrop larg ldst lrt lpad =>
        rw [hlc] at hcallUnw; dsimp only at hcallUnw
        rw [hdcuEq] at hcallUnw
        obtain ⟨hlc1, hlc2, hlc3, _, hlc5⟩ :=
          llvmLowerCallTerm_invoke_eq (dropCanUnwind prog' df) df true argReg 0 rt u
            lc ldrop larg ldst lrt lpad hlc
        unfold execLlvmTerm readLocal?
        rw [hlc1, hlc2, hlc3, hlc5]; dsimp only
        cases hr : listGet? mst.cur.locals argReg with
        | none => rw [hr] at hs; dsimp only at hs; exact absurd trivial hs
        | some argVal =>
          have hrl : listGet? lst.cur.locals argReg = some argVal := by rw [hfeq.2.2.2.2.1]; exact hr
          rw [hr] at hs; rw [hrl]; dsimp only at hs ⊢
          unfold enterCall at hs ⊢; unfold enterLlvmCall; dsimp only at hs ⊢
          have hldfn : listGet? (llvmLowerProg prog').fns df = some (llvmLowerFn prog' dfn) := by
            unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hdfn]
          rw [hdfn] at hs ⊢; rw [hldfn]; dsimp only at hs ⊢
          have hldNonF : (llvmLowerFn prog' dfn).isForeign = false := hdfNonF
          rw [hdfNonF] at hs ⊢; rw [hldNonF]; dsimp only at hs ⊢
          refine ⟨⟨dfn, hdfn, hdfNonF, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hdep, htr, ?_⟩, hs⟩
          exact ⟨fn, hfn, hnonF, ⟨hfeq.1, hfeq.2.1, hfeq.2.2.2.2.1, hfeq.2.2.2.2.2,
            rfl, rfl, hcallUnw⟩, hstk⟩
    | panicCall u =>
      rw [ht] at hs
      unfold execTerm at hs ⊢; unfold llvmLowerTerm; dsimp only at hs ⊢
      cases hstrat : prog'.strategy with
      | abort =>
        rw [hstrat] at hs
        have hpu : band (fnCanUnwind .abort false false .rust) prog'.targetSupportsUnwinding = false := rfl
        rw [hpu]
        unfold llvmLowerPanicTerm execLlvmTerm; dsimp only [MirLlvmStepRel, MirLlvmResultEq]
        exact htr.symm
      | unwind =>
        cases hts : prog'.targetSupportsUnwinding with
        | false =>
          rw [hstrat, hts] at hs
          have hpu : band (fnCanUnwind .unwind false false .rust) false = false := rfl
          rw [hpu]
          unfold llvmLowerPanicTerm execLlvmTerm; dsimp only [MirLlvmStepRel, MirLlvmResultEq]
          exact htr.symm
        | true =>
          rw [hstrat, hts] at hs
          have hpu : band (fnCanUnwind .unwind false false .rust) true = true := rfl
          rw [hpu]
          have hpe := htermWF.2.2; rw [ht] at hpe
          dsimp only [termUnwind?, termCallCanUnwind] at hpe
          have hpf : fnCanUnwind prog'.strategy false false .rust = true := by rw [hstrat]; rfl
          rw [hpf, ← hcleanEq] at hpe
          have huNE : u ≠ .unreachable := by
            intro hbad
            have hnb := hblkNB.2.2
            rw [ht, hbad] at hnb; dsimp only [termUnwind?, termCallCanUnwind] at hnb
            cases hnb rfl with
            | inl hf2 => rw [hts] at hf2; cases hf2
            | inr hf2 => rw [hpf] at hf2; cases hf2
          have hsim := dispatchUnwind_llvm_sim prog' hpost hts mst.cur lst.cur mst.stack lst.stack
            u mst.cleanupDepth mst.trace fn hfn hnonF hlocals
            hfeq hpe huNE hdepthEq hstackWF hstackNB hstk
          cases hu0 : u with
          | unreachable => exact absurd hu0 huNE
          | cleanup padBB =>
            rw [hu0] at hsim
            unfold llvmLowerPanicTerm execLlvmTerm; dsimp only
            rw [hdep, htr]
            exact hsim
          | terminate r =>
            rw [hu0] at hsim
            unfold llvmLowerPanicTerm execLlvmTerm; dsimp only
            rw [hdep, htr]
            exact hsim
          | continue_ =>
            rw [hu0] at hsim
            unfold llvmLowerPanicTerm execLlvmTerm; dsimp only
            rw [hdep, htr]
            exact hsim

theorem mir_llvm_run_lockstep (prog' : Program)
    (hpost : MirPostPassWF prog') (hfok : ForeignContractOK prog')
    (hnob : PostPassNoBogusUnreachable prog') (fuel : Nat) (mst : MirState) (lst : LlvmState)
    (hsafe : MirRuntimeSafe prog' mst) (hrel : MirLlvmStateRel prog' mst lst) :
    MirLlvmResultEq (runMir prog' fuel mst) (runLlvm (llvmLowerProg prog') fuel lst) := by
  induction fuel generalizing mst lst with
  | zero => exact trivial
  | succ k ih =>
    have hstep := stepMir_llvm_lockstep prog' hpost hfok hnob mst lst hsafe hrel
    unfold runMir runLlvm
    cases hm : stepMir prog' mst with
    | running mst' =>
      cases hl : stepLlvm (llvmLowerProg prog') lst with
      | halted lres => rw [hm, hl] at hstep; exact False.elim hstep
      | running lst' =>
        rw [hm, hl] at hstep
        exact ih mst' lst' hstep.2 hstep.1
    | halted mres =>
      cases hl : stepLlvm (llvmLowerProg prog') lst with
      | running lst' => rw [hm, hl] at hstep; exact False.elim hstep
      | halted lres =>
        rw [hm, hl] at hstep
        exact hstep

/-- Lockstep simulation theorem between post-`AbortUnwindingCalls` MIR execution
and lowered LLVM IR execution across arbitrary fuel and input arguments. -/
theorem mir_llvm_lockstep_sim (prog : Program)
    (hpre : MirPrePassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PrePassNoBogusUnreachable prog) (fuel arg : Nat) :
    let prog' := abortUnwindingCallsProg prog
    MirLlvmResultEq (evalMirProg prog' fuel arg) (evalLlvmProg (llvmLowerProg prog') fuel arg) := by
  intro prog'
  have hpost := abortUnwindingCallsProg_postWF prog hpre
  have hfok' := abortUnwindingCalls_preserves_foreignContract prog hfok
  have hnob' := abortUnwindingCallsProg_postNoBogus prog hpre hnob
  obtain ⟨st, hinit, hsafe⟩ := initMirState_runtimeSafe prog' arg hpost
  obtain ⟨entry, hentry, henonF⟩ := hpost.2.1
  unfold evalMirProg; rw [hinit]
  unfold initMirState at hinit
  rw [hentry] at hinit; cases hinit
  have hlentry : listGet? (llvmLowerProg prog').fns (llvmLowerProg prog').entryFn =
      some (llvmLowerFn prog' entry) := by
    unfold llvmLowerProg; dsimp only; rw [listGet?_listMap, hentry]
  unfold evalLlvmProg initLlvmState
  rw [hlentry]; dsimp only
  refine mir_llvm_run_lockstep prog' hpost hfok' hnob' fuel _ _ hsafe ?_
  exact ⟨entry, hentry, henonF, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, trivial⟩

/-- **MAIN THEOREM 4 — LLVM `call`/`invoke` & `nounwind` Attribute Soundness**:
For any pre-pass well-formed MIR program `prog` obeying `ForeignContractOK` and
`PrePassNoBogusUnreachable`, letting `prog' := abortUnwindingCallsProg prog` and
`lprog := llvmLowerProg prog'`:
1. Zero UB and zero invalid LLVM states ever occur (`∀ fuel arg, ¬ llvmIsBad (evalLlvmProg lprog fuel arg)`).
2. Whenever any LLVM function (in particular the entry function `lentry`) carries LLVM `nounwind`
   (`lentry.hasNoUnwind = true`), no unwinding exception EVER escapes (`evalLlvmProg lprog fuel arg ≠ .unwound tr`),
   even when invoking foreign `extern "C-unwind"` callees or indirect `extern "C-unwind"` pointers under
   `-C panic=abort` (`invoke` + `landingpad` + `panic_cannot_unwind`).
3. Lowered LLVM IR and post-pass MIR agree identically on returned values, traces, terminations, and aborts. -/
theorem llvm_nounwind_never_escapes (prog : Program)
    (hpre : MirPrePassWF prog) (hfok : ForeignContractOK prog)
    (hnob : PrePassNoBogusUnreachable prog) :
    let prog' := abortUnwindingCallsProg prog
    let lprog := llvmLowerProg prog'
    (∀ fuel arg, ¬ llvmIsBad (evalLlvmProg lprog fuel arg)) ∧
    (∀ entry lentry,
      listGet? prog.fns prog.entryFn = some entry →
      listGet? lprog.fns lprog.entryFn = some lentry →
      lentry.hasNoUnwind = true →
      ∀ fuel arg tr, evalLlvmProg lprog fuel arg ≠ .unwound tr) ∧
    (∀ fuel arg, MirLlvmResultEq (evalMirProg prog' fuel arg) (evalLlvmProg lprog fuel arg)) := by
  intro prog' lprog
  have hmir := abortUnwindingCalls_exact_soundness prog hpre hfok hnob
  refine ⟨?_, ?_, ?_⟩
  · intro fuel arg
    exact mirLlvmResultEq_not_bad (mir_llvm_lockstep_sim prog hpre hfok hnob fuel arg)
      (hmir.2.2.2.1 fuel arg)
  · intro entry lentry hentry hlentry hnoU fuel arg tr hbad
    have hlentry' : listGet? lprog.fns lprog.entryFn = some (llvmLowerFn prog' (abortUnwindingFn prog entry)) := by
      unfold lprog llvmLowerProg prog' abortUnwindingCallsProg; dsimp only
      rw [listGet?_listMap, listGet?_listMap, hentry]
    rw [hlentry'] at hlentry; cases hlentry
    have hbuFalse : bodyCanUnwind prog.strategy entry = false := by
      unfold llvmLowerFn at hnoU; dsimp only at hnoU
      have hpr := abortUnwindingCalls_preserves_bodyCanUnwind prog entry
      change bodyCanUnwind (abortUnwindingCallsProg prog).strategy (abortUnwindingFn prog entry) =
        bodyCanUnwind prog.strategy entry at hpr
      change bnot (bodyCanUnwind prog'.strategy (abortUnwindingFn prog entry)) = true at hnoU
      rw [hpr] at hnoU
      cases hb0 : bodyCanUnwind prog.strategy entry
      · rfl
      · rw [hb0] at hnoU; cases hnoU
    have hmirUnw := mirLlvmResultEq_unwound (mir_llvm_lockstep_sim prog hpre hfok hnob fuel arg) hbad
    exact hmir.2.2.2.2.1 entry hentry hbuFalse fuel arg tr hmirUnw
  · intro fuel arg
    exact mir_llvm_lockstep_sim prog hpre hfok hnob fuel arg

/-! ## Section 13: Concrete Canaries, Negative Counterexamples & `#print axioms` -/

/-- Canary 1: `extern "C"` function calling a panicking helper under `-C panic=unwind`.
`AbortUnwindingCalls` converts `UnwindAction.continue_` to `UnwindAction.terminate .abi`,
LLVM sets `hasNoUnwind = true` (`nounwind`) with `invoke -> filterTerminatePad .abi`,
and execution halts deterministically with `.terminated .abi`. -/
noncomputable def exCAbiPanics : Program := {
  strategy := .unwind
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .c false, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [.emit 10], term := .call 1 1 0 1 .continue_, isCleanup := false },
        { stmts := [.assignConst 0 42], term := .return_ 0, isCleanup := false }
      ] },
    { abi := .rust, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [.emit 11], term := .panicCall .continue_, isCleanup := false }
      ] }
  ]
  foreignSpecs := fun _ _ => .ret 0 none
}

theorem exCAbiPanics_postMir_and_llvm :
    let prog' := abortUnwindingCallsProg exCAbiPanics
    let lprog := llvmLowerProg prog'
    evalMirProg prog' 20 1 = .terminated .abi [10, 11] ∧
    evalLlvmProg lprog 20 1 = .terminated .abi [10, 11] := by
  constructor <;> rfl

/-- Canary 2: `extern "C-unwind"` function panicking under `-C panic=unwind`.
`AbortUnwindingCalls` preserves `UnwindAction.continue_`, LLVM omits `nounwind` (`hasNoUnwind = false`)
and emits `callPlain`, and unwind cleanly escapes as `.unwound [20]`. -/
noncomputable def exCUnwindAbiPanics : Program := {
  strategy := .unwind
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .c true, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [.emit 20], term := .panicCall .continue_, isCleanup := false }
      ] }
  ]
  foreignSpecs := fun _ _ => .ret 0 none
}

theorem exCUnwindAbiPanics_mir_and_llvm :
    let prog' := abortUnwindingCallsProg exCUnwindAbiPanics
    let lprog := llvmLowerProg prog'
    evalMirProg prog' 10 1 = .unwound [20] ∧
    evalLlvmProg lprog 10 1 = .unwound [20] := by
  constructor <;> rfl

/-- Canary 3: `extern "C"` function with a local `Drop` calling foreign `extern "C-unwind"`.
`AbortUnwindingCalls` preserves `.cleanup 1` on `bb0` and rewrites `bb1`'s `UnwindResume` to
`UnwindTerminate .abi`, so drop cleanup emits trace `77` before deterministic `.terminated .abi`. -/
noncomputable def exCAbiWithDropCallsCUnwind : Program := {
  strategy := .unwind
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .c false, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [], term := .call 1 1 0 1 (.cleanup 2), isCleanup := false },
        { stmts := [.assignConst 0 0], term := .return_ 0, isCleanup := false },
        { stmts := [.emit 77], term := .unwindResume, isCleanup := true }
      ] },
    { abi := .c true, isForeign := true, neverUnwind := false, localCount := 2, blocks := [] }
  ]
  foreignSpecs := fun _ _ => .unwound (some 70)
}

theorem exCAbiWithDropCallsCUnwind_runs_cleanup_then_terminates :
    let prog' := abortUnwindingCallsProg exCAbiWithDropCallsCUnwind
    let lprog := llvmLowerProg prog'
    evalMirProg prog' 20 1 = .terminated .abi [70, 77] ∧
    evalLlvmProg lprog 20 1 = .terminated .abi [70, 77] := by
  constructor <;> rfl

/-- Canary 4: Double panic during cleanup (`Drop` panics inside `bb1 (cleanup)`) deterministically
halts with `.terminated .inCleanup` (`panic_in_cleanup`) in both MIR and LLVM IR. -/
noncomputable def exDoublePanicInCleanup : Program := {
  strategy := .unwind
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .rust, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [.emit 30], term := .panicCall (.cleanup 1), isCleanup := false },
        { stmts := [.emit 31], term := .drop 1 1 2 (.terminate .inCleanup), isCleanup := true },
        { stmts := [], term := .unwindResume, isCleanup := true }
      ] },
    { abi := .rust, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [.emit 32], term := .panicCall .continue_, isCleanup := false }
      ] }
  ]
  foreignSpecs := fun _ _ => .ret 0 none
}

theorem exDoublePanicInCleanup_halts_inCleanup :
    let prog' := abortUnwindingCallsProg exDoublePanicInCleanup
    let lprog := llvmLowerProg prog'
    evalMirProg prog' 20 1 = .terminated .inCleanup [30, 31, 32] ∧
    evalLlvmProg lprog 20 1 = .terminated .inCleanup [30, 31, 32] := by
  constructor <;> rfl

/-- Canary 5: Under `-C panic=abort` without unwinding foreign calls, `AbortUnwindingCalls` converts
edges to `.unreachable` and `eraseDeadCleanupProg` strips unreachable cleanup blocks cleanly. -/
noncomputable def exPanicAbortCleanupErased : Program := {
  strategy := .abort
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .rust, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [.emit 40], term := .call 1 1 0 1 (.cleanup 2), isCleanup := false },
        { stmts := [.assignConst 0 99], term := .return_ 0, isCleanup := false },
        { stmts := [.emit 49], term := .unwindResume, isCleanup := true }
      ] },
    { abi := .c false, isForeign := true, neverUnwind := false, localCount := 2, blocks := [] }
  ]
  foreignSpecs := fun _ v => .ret v (some 41)
}

theorem exPanicAbortCleanupErased_exact :
    let prog' := abortUnwindingCallsProg exPanicAbortCleanupErased
    let progE := eraseDeadCleanupProg prog'
    listLen (match listGet? progE.fns 0 with | some fn => fn.blocks | none => []) = 2 ∧
    evalMirProg prog' 20 7 = .returned 99 [40, 41] ∧
    evalMirProg progE 20 7 = .returned 99 [40, 41] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Canary 6: Under `-C panic=abort`, calling foreign `extern "C-unwind"` preserves unwinding on the
callee (`hasNoUnwind = false`), forces `main` (`hasNoUnwind = true`) to attach `UnwindAction.terminate .abi`,
and emits LLVM `invoke -> filterTerminatePad .abi` so external unwinding deterministically traps. -/
noncomputable def exForeignCUnwindUnderPanicAbort : Program := {
  strategy := .abort
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .rust, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [.emit 50], term := .call 1 1 0 1 .continue_, isCleanup := false },
        { stmts := [.assignConst 0 0], term := .return_ 0, isCleanup := false }
      ] },
    { abi := .c true, isForeign := true, neverUnwind := false, localCount := 2, blocks := [] }
  ]
  foreignSpecs := fun _ _ => .unwound (some 51)
}

theorem exForeignCUnwindUnderPanicAbort_traps_no_ub :
    let prog' := abortUnwindingCallsProg exForeignCUnwindUnderPanicAbort
    let lprog := llvmLowerProg prog'
    evalMirProg prog' 10 1 = .terminated .abi [50, 51] ∧
    evalLlvmProg lprog 10 1 = .terminated .abi [50, 51] := by
  constructor <;> rfl

/-- Negative Counterexample 1: Omitting `AbortUnwindingCalls` on `exCAbiPanics` leaves
`hasNoUnwind = true` (`nounwind`) paired with `UnwindAction.continue_`, hitting LLVM UB! -/
theorem negMissingAbortUnwindingCalls_llvmUb :
    evalLlvmProg (llvmLowerProg exCAbiPanics) 20 1 = .ub [10, 11] := by
  rfl

/-- Negative Counterexample 2: Naively assigning `UnwindAction.unreachable` to a foreign
`extern "C-unwind"` call under `-C panic=abort` violates FFI unwind soundness and hits LLVM UB! -/
noncomputable def negForeignCUnwindUnreachable : Program := {
  strategy := .abort
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .rust, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [], term := .call 1 1 0 1 .unreachable, isCleanup := false },
        { stmts := [.assignConst 0 0], term := .return_ 0, isCleanup := false }
      ] },
    { abi := .c true, isForeign := true, neverUnwind := false, localCount := 2, blocks := [] }
  ]
  foreignSpecs := fun _ _ => .unwound none
}

theorem negForeignCUnwindUnreachable_llvmUb :
    evalLlvmProg (llvmLowerProg negForeignCUnwindUnreachable) 10 1 = .ub [] := by
  rfl

/-- Negative Counterexample 3: Using `UnwindAction.continue_` inside a cleanup block instead of
`UnwindAction.terminate .inCleanup` breaks double-panic termination and escapes to `.unwound []`! -/
noncomputable def negCleanupContinueProgram : Program := {
  strategy := .unwind
  targetSupportsUnwinding := true
  panicInDropUnwinds := true
  entryFn := 0
  fns := [
    { abi := .rust, isForeign := false, neverUnwind := false, localCount := 2, blocks := [
        { stmts := [], term := .panicCall (.cleanup 1), isCleanup := false },
        { stmts := [], term := .panicCall .continue_, isCleanup := true }
      ] }
  ]
  foreignSpecs := fun _ _ => .ret 0 none
}

theorem negCleanupContinue_escapesUnwind :
    evalMirProg negCleanupContinueProgram 10 1 = .unwound [] := by
  rfl

end MirUnwindSoundness

#print axioms MirUnwindSoundness.abortUnwindingCalls_exact_soundness
#print axioms MirUnwindSoundness.double_panic_inCleanup_termination
#print axioms MirUnwindSoundness.eraseDeadCleanup_preserves_WF_and_exec
#print axioms MirUnwindSoundness.llvm_nounwind_never_escapes
#print axioms MirUnwindSoundness.mir_llvm_lockstep_sim
