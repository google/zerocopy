/-!
# Soundness of `rustc` Post-Borrowck & Pre-Codegen MIR Lowerings

Kernel-checked Lean 4 (`v4.34.1`) formalization establishing semantic
preservation and structural invariants for five coupled `rustc_mir_transform`
passes audited against `rust-lang/rust`:

1. **`CleanupPostBorrowck`** (`cleanup_post_borrowck.rs`):
   Trace bisimulation (`cleanupPostBorrowck_bisim`) proving that erasing
   `AscribeUserType`, `BorrowKind::Fake`, `FakeRead`,
   `BackwardIncompatibleDropHint`, and post-analysis `Coverage` markers to
   `Nop`, lowering `PointerCoercion::{ArrayToPointer, MutToConstPointer}` to
   `CastKind::PtrToPtr` (while preserving `Unsize` and `VirtualCounter`),
   collapsing `FalseEdge`/`FalseUnwind` to `Goto`, and clearing
   `user_type_annotations`/`local.user_ty` preserves exact operational
   semantics (including observable coverage traces) while discharging all
   post-borrowck administrative invariants and being idempotent.

2. **`ElaborateBoxDerefs`** (`elaborate_box_derefs.rs`,
   `rustc_const_eval/src/interpret/cast.rs`):
   Allocation-address and UB preservation
   (`elaborateBoxDerefs_preserves_place_eval`) proving that 1-field `BoxRaw`
   projection + `CastKind::BoxDerefTransmute` preserves both resolved memory
   addresses and `Box<T>` validity UB (alignment + live allocation + non-null),
   a constructive separation theorem (`legacyTransmute_elides_unaligned_raw_deref_ub`)
   mechanizing the `CastKind::Transmute` raw-deref UB-elision gap, and 4-level
   `VarDebugInfo` expansion soundness through `PatternKind::NotNull`.

3. **`CheckMutRestriction`** (`check_mut_restriction.rs`,
   `rustc_middle/src/ty/mod.rs`, `rustc_middle/src/mir/visit.rs`):
   Three-surface capability soundness
   (`checkMutRestriction_blocks_field_mut_and_ctor_fn_permits_whole_adt`)
   proving `RestrictionKind::stricter_of` chain soundness, rejection of
   restricted field mutations across arbitrary projection chains, rejection of
   restricted struct/enum aggregates and tuple-constructor `FnDef` values,
   active-field union precision, and intentional permission of whole-ADT
   place overwrite (`*s = ...`) when zero `ProjectionElem::Field` appear.

4. **`RemoveNoopLandingPads` + `AddCallGuards::CriticalCallEdges`**
   (`remove_noop_landing_pads.rs`, `add_call_guards.rs`):
   Noop landing-pad soundness and `generatesInvoke` flip
   (`removeNoopLandingPads_flips_generatesInvoke`,
   `removeNoopLandingPads_preserves_unwind_outcome`), exact predecessor-count
   proof that `AddCallGuards::CriticalCallEdges` eliminates all critical
   invoke-return and `InlineAsm` output-target edges while preserving
   `isCleanup` flags and stuttering operational semantics
   (`addCallGuards_eliminates_invoke_critical_edges_and_preserves_semantics`).

Purity discipline: zero `sorry`, zero `Classical.choice`, zero `omega`,
zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `deriving`
on container-bearing inductives (zero `._unsafe_rec` constants).
-/

namespace RustcPostBorrowckAndPreCodegen

/-! ## Constructive `Nat` Equality Helpers (Zero `Classical.choice`) -/

theorem natBeq_self (n : Nat) : (n == n) = true :=
  decide_eq_true rfl

theorem nat_eq_of_beq {a b : Nat} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  decide_eq_false h

/-! ## Shared Total Helpers (No `partial`, No `omega`, No `Classical.choice`) -/

noncomputable def listGetD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, n + 1, d => listGetD xs n d

noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

noncomputable def listSet {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

theorem listGet?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (n : Nat),
      listGet? (xs.map f) n = (listGet? xs n).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => listGet?_map f xs n

theorem listGet?_append_left {α : Type} :
    ∀ (xs ys : List α) (n : Nat),
      n < xs.length → listGet? (xs ++ ys) n = listGet? xs n
  | [], _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, n + 1, h =>
    listGet?_append_left xs ys n (Nat.lt_of_succ_lt_succ h)

theorem listGet?_append_right {α : Type} :
    ∀ (xs ys : List α) (k : Nat),
      listGet? (xs ++ ys) (xs.length + k) = listGet? ys k
  | [], _, k => by simp
  | _ :: xs, ys, k => by
    rw [List.length_cons, Nat.succ_add]
    exact listGet?_append_right xs ys k

theorem listGet?_some_lt {α : Type} :
    ∀ (xs : List α) (n : Nat) (v : α),
      listGet? xs n = some v → n < xs.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, n + 1, v, h => Nat.succ_lt_succ (listGet?_some_lt xs n v h)

theorem listGet?_some_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length → ∃ v, listGet? xs i = some v
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, h => listGet?_some_of_lt xs i (Nat.lt_of_succ_lt_succ h)

theorem listGet?_none_of_le {α : Type} :
    ∀ (xs : List α) (n : Nat),
      xs.length ≤ n → listGet? xs n = none
  | [], _, _ => rfl
  | _ :: _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ :: xs, n + 1, h => listGet?_none_of_le xs n (Nat.le_of_succ_le_succ h)

noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allList p xs

theorem allList_iff {α : Type} (p : α → Bool) :
    ∀ (xs : List α),
      allList p xs = true ↔ ∀ x, x ∈ xs → p x = true
  | [] => ⟨fun _ _ h => (by cases h), fun _ => rfl⟩
  | x :: xs => by
    constructor
    · intro h y hy
      simp only [allList, Bool.and_eq_true] at h
      cases hy with
      | head => exact h.1
      | tail _ hmem => exact (allList_iff p xs).mp h.2 y hmem
    · intro h
      simp only [allList, Bool.and_eq_true]
      exact ⟨h x (List.Mem.head _), (allList_iff p xs).mpr (fun y hy => h y (List.Mem.tail x hy))⟩

theorem allList_map {α β : Type} (p : β → Bool) (f : α → β) :
    ∀ (xs : List α), allList p (xs.map f) = allList (fun x => p (f x)) xs
  | [] => rfl
  | x :: xs => by simp [allList, allList_map p f xs]

noncomputable def natCountIn (target : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x == target then 1 else 0) + natCountIn target xs

theorem natCountIn_append (t : Nat) :
    ∀ (xs ys : List Nat),
      natCountIn t (xs ++ ys) = natCountIn t xs + natCountIn t ys
  | [], ys => by simp [natCountIn]
  | x :: xs, ys => by
    simp only [List.cons_append, natCountIn, natCountIn_append t xs ys, Nat.add_assoc]

theorem natCountIn_zero_of_forall_ne (t : Nat) :
    ∀ (xs : List Nat), (∀ x, x ∈ xs → x ≠ t) → natCountIn t xs = 0
  | [], _ => rfl
  | x :: xs, h => by
    have hne : x ≠ t := h x (List.Mem.head _)
    have hbeq : (x == t) = false := natBeq_false_of_ne hne
    have htail : natCountIn t xs = 0 :=
      natCountIn_zero_of_forall_ne t xs (fun y hy => h y (List.Mem.tail x hy))
    simp [natCountIn, hbeq, htail]

/-! ## Part 1: `CleanupPostBorrowck` Trace Bisimulation & Erasure Invariants -/

namespace CleanupPostBorrowck

inductive PointerCoercionKind where
  | arrayToPointer
  | mutToConstPointer
  | unsize
  | reifyFnPointer

inductive CastKind where
  | ptrToPtr
  | pointerCoercion (k : PointerCoercionKind)
  | transmute
  | boxDerefTransmute
  | subtype

inductive CoverageKind where
  | point (id : Nat)
  | blockMarker (id : Nat)
  | virtualCounter (bcb : Nat)

/-- Mirrors `CoverageKind::is_removed_after_analysis` (`coverage.rs:123-128`). -/
noncomputable def CoverageKind.isRemovedAfterAnalysis : CoverageKind → Bool
  | .point _ => true
  | .blockMarker _ => true
  | .virtualCounter _ => false

inductive BorrowKind where
  | shared
  | mut_
  | fakeShallow
  | fakeDeep

noncomputable def BorrowKind.isFake : BorrowKind → Bool
  | .fakeShallow => true
  | .fakeDeep => true
  | .shared => false
  | .mut_ => false

inductive Rvalue where
  | useCopy (src : Nat)
  | useMove (src : Nat)
  | ref (bk : BorrowKind) (placeLocal : Nat)
  | cast (ck : CastKind) (src : Nat)
  | addConst (src : Nat) (k : Nat)

inductive Stmt where
  | assign (dst : Nat) (rv : Rvalue)
  | ascribeUserType (localIdx : Nat) (userTyId : Nat)
  | fakeRead (localIdx : Nat)
  | backwardIncompatibleDropHint (localIdx : Nat)
  | coverage (ck : CoverageKind)
  | nop

inductive Term where
  | goto (target : Nat)
  | falseEdge (realTarget : Nat) (imagTarget : Nat)
  | falseUnwind (realTarget : Nat) (unwindTarget : Option Nat)
  | branch (condLocal : Nat) (tTarget : Nat) (fTarget : Nat)
  | ret (localIdx : Nat)

structure BasicBlock where
  stmts : List Stmt
  term : Term
  isCleanup : Bool

structure Body where
  blocks : List BasicBlock
  userTypeAnnotations : List Nat
  localUserTys : List (Option Nat)

/-- Exact mirror of statement loop in `cleanup_post_borrowck.rs:31-61`. -/
noncomputable def cleanupStmt : Stmt → Stmt
  | .ascribeUserType _ _ => .nop
  | .assign _ (.ref .fakeShallow _) => .nop
  | .assign _ (.ref .fakeDeep _) => .nop
  | .fakeRead _ => .nop
  | .backwardIncompatibleDropHint _ => .nop
  | .coverage ck =>
    if ck.isRemovedAfterAnalysis then .nop else .coverage ck
  | .assign dst (.cast (.pointerCoercion .arrayToPointer) src) =>
    .assign dst (.cast .ptrToPtr src)
  | .assign dst (.cast (.pointerCoercion .mutToConstPointer) src) =>
    .assign dst (.cast .ptrToPtr src)
  | s => s

/-- Exact mirror of terminator loop in `cleanup_post_borrowck.rs:64-72`. -/
noncomputable def cleanupTerm : Term → Term
  | .falseEdge realTarget _ => .goto realTarget
  | .falseUnwind realTarget _ => .goto realTarget
  | t => t

noncomputable def termNeedsCfgInvalidation : Term → Bool
  | .falseEdge _ _ => true
  | .falseUnwind _ _ => true
  | _ => false

noncomputable def cleanupBlock (bb : BasicBlock) : BasicBlock :=
  { stmts := bb.stmts.map cleanupStmt
    term := cleanupTerm bb.term
    isCleanup := bb.isCleanup }

/-- Exact mirror of `CleanupPostBorrowck::run_pass` (`cleanup_post_borrowck.rs:27-84`). -/
noncomputable def cleanupPostBorrowck (body : Body) : Body :=
  { blocks := body.blocks.map cleanupBlock
    userTypeAnnotations := []
    localUserTys := body.localUserTys.map (fun _ => none) }

/-- Runtime state with explicit move-deinitialization slots (`Option Nat`)
    and observable coverage virtual-counter trace (`covTrace`). -/
structure State where
  locals : List (Option Nat)
  covTrace : List Nat

inductive Outcome where
  | returned (v : Nat) (cov : List Nat)
  | stuck (cov : List Nat)
  | outOfFuel (bb : Nat) (st : State)

/-- Runtime evaluation of an `Rvalue` (preserving `deinitMovedPlace = true` on moves).
    Fake borrows never write a runtime value (erased/no-op in runtime semantics).
    `ArrayToPointer` and `MutToConstPointer` evaluate identically to `PtrToPtr`. -/
noncomputable def evalRvalue (st : State) : Rvalue → Option (Nat × State)
  | .useCopy src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .useMove src =>
    match listGetD st.locals src none with
    | some v => some (v, { st with locals := listSet st.locals src none })
    | none => none
  | .ref .shared l => some (l, st)
  | .ref .mut_ l => some (l, st)
  | .ref .fakeShallow _ => none
  | .ref .fakeDeep _ => none
  | .cast .ptrToPtr src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .cast (.pointerCoercion .arrayToPointer) src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .cast (.pointerCoercion .mutToConstPointer) src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .cast (.pointerCoercion .unsize) src =>
    match listGetD st.locals src none with
    | some v => some (v + 1, st)
    | none => none
  | .cast (.pointerCoercion .reifyFnPointer) src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .cast .transmute src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .cast .boxDerefTransmute src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .cast .subtype src =>
    match listGetD st.locals src none with
    | some v => some (v, st)
    | none => none
  | .addConst src k =>
    match listGetD st.locals src none with
    | some v => some (v + k, st)
    | none => none

/-- Single-statement operational step. Administrative statements (`AscribeUserType`,
    `FakeRead`, `Fake` borrow, `BackwardIncompatibleDropHint`, removable `Coverage`)
    have no runtime effect, while `CoverageKind.virtualCounter` appends to `covTrace`. -/
noncomputable def stepStmt (st : State) : Stmt → Option State
  | .ascribeUserType _ _ => some st
  | .fakeRead _ => some st
  | .backwardIncompatibleDropHint _ => some st
  | .nop => some st
  | .coverage (.point _) => some st
  | .coverage (.blockMarker _) => some st
  | .coverage (.virtualCounter bcb) =>
    some { st with covTrace := st.covTrace ++ [bcb] }
  | .assign _ (.ref .fakeShallow _) => some st
  | .assign _ (.ref .fakeDeep _) => some st
  | .assign dst rv =>
    match evalRvalue st rv with
    | some (v, st') => some { st' with locals := listSet st'.locals dst (some v) }
    | none => none

noncomputable def stepStmts (st : State) : List Stmt → Option State
  | [] => some st
  | s :: ss =>
    match stepStmt st s with
    | some st' => stepStmts st' ss
    | none => none

inductive TermStep where
  | next (bb : Nat)
  | ret (v : Nat)
  | stuck

noncomputable def stepTerm (st : State) : Term → TermStep
  | .goto t => .next t
  | .falseEdge realTarget _ => .next realTarget
  | .falseUnwind realTarget _ => .next realTarget
  | .branch condLocal tTarget fTarget =>
    match listGetD st.locals condLocal none with
    | some 0 => .next fTarget
    | some (_ + 1) => .next tTarget
    | none => .stuck
  | .ret l =>
    match listGetD st.locals l none with
    | some v => .ret v
    | none => .stuck

noncomputable def runCfg (body : Body) : Nat → Nat → State → Outcome
  | 0, bb, st => .outOfFuel bb st
  | fuel + 1, bb, st =>
    match listGet? body.blocks bb with
    | none => .stuck st.covTrace
    | some blk =>
      match stepStmts st blk.stmts with
      | none => .stuck st.covTrace
      | some st' =>
        match stepTerm st' blk.term with
        | .next nextBb => runCfg body fuel nextBb st'
        | .ret v => .returned v st'.covTrace
        | .stuck => .stuck st'.covTrace

theorem cleanupStmt_sem_eq (st : State) (s : Stmt) :
    stepStmt st (cleanupStmt s) = stepStmt st s := by
  cases s with
  | ascribeUserType _ _ => rfl
  | fakeRead _ => rfl
  | backwardIncompatibleDropHint _ => rfl
  | nop => rfl
  | coverage ck =>
    cases ck with
    | point _ => rfl
    | blockMarker _ => rfl
    | virtualCounter _ => rfl
  | assign dst rv =>
    cases rv with
    | useCopy _ => rfl
    | useMove _ => rfl
    | addConst _ _ => rfl
    | ref bk _ =>
      cases bk <;> rfl
    | cast ck _ =>
      cases ck with
      | ptrToPtr => rfl
      | transmute => rfl
      | boxDerefTransmute => rfl
      | subtype => rfl
      | pointerCoercion pk =>
        cases pk <;> rfl

theorem cleanupStmts_sem_eq :
    ∀ (ss : List Stmt) (st : State),
      stepStmts st (ss.map cleanupStmt) = stepStmts st ss
  | [], _ => rfl
  | s :: ss, st => by
    simp only [List.map_cons, stepStmts, cleanupStmt_sem_eq st s]
    cases stepStmt st s with
    | none => rfl
    | some st' => exact cleanupStmts_sem_eq ss st'

theorem cleanupTerm_sem_eq (st : State) (t : Term) :
    stepTerm st (cleanupTerm t) = stepTerm st t := by
  cases t <;> rfl

/-- **Theorem 1 (`cleanupPostBorrowck_bisim`):** Exact multi-step operational
    trace and outcome bisimulation for `CleanupPostBorrowck`. -/
theorem cleanupPostBorrowck_bisim (body : Body) :
    ∀ (fuel bb : Nat) (st : State),
      runCfg (cleanupPostBorrowck body) fuel bb st = runCfg body fuel bb st
  | 0, _, _ => rfl
  | fuel + 1, bb, st => by
    simp only [runCfg, cleanupPostBorrowck, listGet?_map]
    cases listGet? body.blocks bb with
    | none => rfl
    | some blk =>
      simp only [Option.map_some, cleanupBlock, cleanupStmts_sem_eq blk.stmts st]
      cases stepStmts st blk.stmts with
      | none => rfl
      | some st' =>
        dsimp only
        rw [cleanupTerm_sem_eq st' blk.term]
        cases stepTerm st' blk.term with
        | next nextBb => exact cleanupPostBorrowck_bisim body fuel nextBb st'
        | ret _ => rfl
        | stuck => rfl

/-- Structural post-condition predicate mirroring `validate.rs:296-325, 479-498, 1157-1162, 1314-1345`. -/
noncomputable def stmtPostBorrowckClean : Stmt → Bool
  | .ascribeUserType _ _ => false
  | .fakeRead _ => false
  | .backwardIncompatibleDropHint _ => false
  | .assign _ (.ref .fakeShallow _) => false
  | .assign _ (.ref .fakeDeep _) => false
  | .coverage ck => !ck.isRemovedAfterAnalysis
  | .assign _ (.cast (.pointerCoercion .arrayToPointer) _) => false
  | .assign _ (.cast (.pointerCoercion .mutToConstPointer) _) => false
  | _ => true

noncomputable def termPostBorrowckClean : Term → Bool
  | .falseEdge _ _ => false
  | .falseUnwind _ _ => false
  | _ => true

noncomputable def blockPostBorrowckClean (blk : BasicBlock) : Bool :=
  allList stmtPostBorrowckClean blk.stmts && termPostBorrowckClean blk.term

noncomputable def bodyPostBorrowckClean (body : Body) : Bool :=
  allList blockPostBorrowckClean body.blocks &&
  body.userTypeAnnotations.isEmpty &&
  allList Option.isNone body.localUserTys

theorem cleanupStmt_is_clean (s : Stmt) : stmtPostBorrowckClean (cleanupStmt s) = true := by
  cases s with
  | ascribeUserType _ _ => rfl
  | fakeRead _ => rfl
  | backwardIncompatibleDropHint _ => rfl
  | nop => rfl
  | coverage ck => cases ck <;> rfl
  | assign dst rv =>
    cases rv with
    | useCopy _ => rfl
    | useMove _ => rfl
    | addConst _ _ => rfl
    | ref bk _ => cases bk <;> rfl
    | cast ck _ =>
      cases ck with
      | ptrToPtr => rfl
      | transmute => rfl
      | boxDerefTransmute => rfl
      | subtype => rfl
      | pointerCoercion pk => cases pk <;> rfl

theorem cleanupTerm_is_clean (t : Term) : termPostBorrowckClean (cleanupTerm t) = true := by
  cases t <;> rfl

theorem allList_true {α : Type} (p : α → Bool) (hp : ∀ x, p x = true) :
    ∀ (xs : List α), allList p xs = true
  | [] => rfl
  | x :: xs => by simp [allList, hp x, allList_true p hp xs]

theorem cleanupPostBorrowck_post_invariants (body : Body) :
    bodyPostBorrowckClean (cleanupPostBorrowck body) = true := by
  unfold bodyPostBorrowckClean cleanupPostBorrowck
  simp only [Bool.and_eq_true, List.isEmpty_nil, and_true]
  constructor
  · rw [allList_map]
    apply allList_true
    intro blk
    unfold blockPostBorrowckClean cleanupBlock
    simp only [Bool.and_eq_true, allList_map]
    exact ⟨allList_true _ cleanupStmt_is_clean blk.stmts, cleanupTerm_is_clean blk.term⟩
  · rw [allList_map]
    apply allList_true
    intro _
    rfl

theorem cleanupStmt_idempotent (s : Stmt) : cleanupStmt (cleanupStmt s) = cleanupStmt s := by
  cases s with
  | ascribeUserType _ _ => rfl
  | fakeRead _ => rfl
  | backwardIncompatibleDropHint _ => rfl
  | nop => rfl
  | coverage ck => cases ck <;> rfl
  | assign dst rv =>
    cases rv with
    | useCopy _ => rfl
    | useMove _ => rfl
    | addConst _ _ => rfl
    | ref bk _ => cases bk <;> rfl
    | cast ck _ =>
      cases ck with
      | ptrToPtr => rfl
      | transmute => rfl
      | boxDerefTransmute => rfl
      | subtype => rfl
      | pointerCoercion pk => cases pk <;> rfl

theorem cleanupTerm_idempotent (t : Term) : cleanupTerm (cleanupTerm t) = cleanupTerm t := by
  cases t <;> rfl

theorem cleanupPostBorrowck_idempotent (body : Body) :
    cleanupPostBorrowck (cleanupPostBorrowck body) = cleanupPostBorrowck body := by
  unfold cleanupPostBorrowck
  cases body with
  | mk blocks annos ltys =>
    simp only [Body.mk.injEq, List.map_map, true_and]
    constructor
    · induction blocks with
      | nil => rfl
      | cons b bs ih =>
        simp only [List.map_cons, Function.comp_apply, List.cons.injEq]
        refine ⟨?_, ih⟩
        cases b with
        | mk ss tm ic =>
          simp only [cleanupBlock, BasicBlock.mk.injEq, List.map_map, cleanupTerm_idempotent, and_true]
          induction ss with
          | nil => rfl
          | cons s rest ihs =>
            simp only [List.map_cons, Function.comp_apply, cleanupStmt_idempotent, ihs]
    · induction ltys with
      | nil => rfl
      | cons _ rest ih => simp [List.map_cons, ih]

/-- Negative-space preservation: `PointerCoercion::Unsize` is NOT lowered to `PtrToPtr`,
    and `CoverageKind::VirtualCounter` is NOT erased to `Nop`. -/
theorem cleanupPostBorrowck_preserves_unsize_and_virtual_counter (dst src bcb : Nat) :
    cleanupStmt (.assign dst (.cast (.pointerCoercion .unsize) src)) =
      .assign dst (.cast (.pointerCoercion .unsize) src) ∧
    cleanupStmt (.coverage (.virtualCounter bcb)) =
      .coverage (.virtualCounter bcb) :=
  ⟨rfl, rfl⟩

end CleanupPostBorrowck

/-! ## Part 2: `ElaborateBoxDerefs` Address & UB Preservation vs. 4-Level `VarDebugInfo` -/

namespace ElaborateBoxDerefs

inductive TyTag where
  | boxTy (pointeeAlign : Nat)
  | boxRawTy (pointeeAlign : Nat)
  | nonNullTy (pointeeAlign : Nat)
  | patNotNullTy (pointeeAlign : Nat)
  | rawConstPtrTy (pointeeAlign : Nat)
  | scalarTy

inductive PlaceElem where
  | deref
  | field (idx : Nat) (ty : TyTag)

structure Place where
  localIdx : Nat
  baseTy : TyTag
  projs : List PlaceElem

/-- Runtime pointer value carried inside a `Box<T>` / `BoxRaw<T>` / `NonNull<T>` / `*const T`. -/
structure PtrRep where
  addr : Nat
  allocId : Nat
  allocLive : Bool

/-- Full `Box<T>` validity check matching `rustc_const_eval/src/interpret/cast.rs:206-214`
    (`deref_pointer` on reconstructed `Box<T>`): non-null, live allocation, and aligned to `pointeeAlign`. -/
noncomputable def isValidBoxPtr (pointeeAlign : Nat) (p : PtrRep) : Bool :=
  (p.addr != 0) && p.allocLive && (pointeeAlign != 0) && (p.addr % pointeeAlign == 0)

/-- `NonNull<T>` validity check (`PatternKind::NotNull`): checks ONLY non-null. -/
noncomputable def isValidNonNullPtr (p : PtrRep) : Bool :=
  p.addr != 0

inductive PlaceEvalResult where
  | ok (addr : Nat) (allocId : Nat)
  | ub

/-- Apply field-offset projection tail after initial dereference (e.g., `(*b).0` -> `+ 0`, `(*b).1` -> `+ 4`). -/
noncomputable def applyTailProjs (addr : Nat) (allocId : Nat) : List PlaceElem → PlaceEvalResult
  | [] => .ok addr allocId
  | .field idx _ :: rest => applyTailProjs (addr + idx * 4) allocId rest
  | .deref :: _ => .ub

/-- Pre-`ElaborateBoxDerefs` direct MIR evaluation of a `Box<T>` dereference place
    (under `Derefer`'s precondition: `projs = .deref :: tail`). -/
noncomputable def evalBoxPlaceDirect (env : Nat → PtrRep) (pl : Place) : PlaceEvalResult :=
  match pl.baseTy, pl.projs with
  | .boxTy align, .deref :: tail =>
    let ptr := env pl.localIdx
    if isValidBoxPtr align ptr then
      applyTailProjs ptr.addr ptr.allocId tail
    else
      .ub
  | .rawConstPtrTy _, .deref :: tail =>
    let ptr := env pl.localIdx
    applyTailProjs ptr.addr ptr.allocId tail
  | _, _ => .ub

/-- Result of basic-block `ElaborateBoxDerefs` (`elaborate_box_derefs.rs:51-71`):
    projects ONLY field 0 (`BoxRaw<T>`), emits `CastKind::BoxDerefTransmute` into
    fresh `ptrLocal : *const T`, and rewrites `place.local := ptrLocal`. -/
structure ElaboratedBB where
  insertedCastSrc : Option (Nat × TyTag)  -- (origLocal, boxRawTy align)
  rewrittenPlace : Place

noncomputable def elaborateBoxPlaceBB (freshPtrLocal : Nat) (pl : Place) : ElaboratedBB :=
  match pl.baseTy, pl.projs with
  | .boxTy align, .deref :: tail =>
    { insertedCastSrc := some (pl.localIdx, .boxRawTy align)
      rewrittenPlace :=
        { localIdx := freshPtrLocal
          baseTy := .rawConstPtrTy align
          projs := .deref :: tail } }
  | _, _ =>
    { insertedCastSrc := none
      rewrittenPlace := pl }

/-- Post-`ElaborateBoxDerefs` execution under `HEAD` (`CastKind::BoxDerefTransmute`
    calling `interpret/cast.rs:206-214` before evaluating the rewritten raw-pointer place). -/
noncomputable def evalElaboratedBB (env : Nat → PtrRep) (freshPtrLocal : Nat) (eb : ElaboratedBB) :
    PlaceEvalResult :=
  match eb.insertedCastSrc with
  | some (origLocal, .boxRawTy align) =>
    let rawFieldPtr := env origLocal
    if isValidBoxPtr align rawFieldPtr then
      let env' := fun k => if k == freshPtrLocal then rawFieldPtr else env k
      evalBoxPlaceDirect env' eb.rewrittenPlace
    else
      .ub
  | _ => evalBoxPlaceDirect env eb.rewrittenPlace

/-- Post-`ElaborateBoxDerefs` execution under legacy `1.98.0-nightly`
    (`CastKind::Transmute` from `NonNull<T>` -> `*const T`): validates ONLY
    `NonNull` (`addr != 0`), NOT `Box<T>` alignment or allocation liveness,
    when the rewritten `*ptrLocal` is used in `&raw const (*ptrLocal)`. -/
noncomputable def evalElaboratedBB_legacyTransmute (env : Nat → PtrRep) (freshPtrLocal : Nat)
    (eb : ElaboratedBB) : PlaceEvalResult :=
  match eb.insertedCastSrc with
  | some (origLocal, .boxRawTy _) =>
    let nonNullPtr := env origLocal
    if isValidNonNullPtr nonNullPtr then
      let env' := fun k => if k == freshPtrLocal then nonNullPtr else env k
      evalBoxPlaceDirect env' eb.rewrittenPlace
    else
      .ub
  | _ => evalBoxPlaceDirect env eb.rewrittenPlace

/-- **Theorem 2 (`elaborateBoxDerefs_preserves_place_eval`):**
    Basic-block `ElaborateBoxDerefs` with `CastKind::BoxDerefTransmute` preserves
    exact allocation-address evaluation AND exact `Box<T>` UB detection for all
    valid and invalid pointers and all field-projection tails. -/
theorem elaborateBoxDerefs_preserves_place_eval
    (env : Nat → PtrRep) (freshPtrLocal : Nat) (pl : Place) :
    evalElaboratedBB env freshPtrLocal (elaborateBoxPlaceBB freshPtrLocal pl) =
      evalBoxPlaceDirect env pl := by
  cases pl with
  | mk l bty projs =>
    cases bty with
    | boxTy align =>
      cases projs with
      | nil => rfl
      | cons elem tail =>
        cases elem with
        | field _ _ => rfl
        | deref =>
          unfold elaborateBoxPlaceBB evalElaboratedBB evalBoxPlaceDirect
          simp only [natBeq_self, ↓reduceIte]
    | boxRawTy _ => rfl
    | nonNullTy _ => rfl
    | patNotNullTy _ => rfl
    | rawConstPtrTy _ => rfl
    | scalarTy => rfl

/-- Post-elaboration invariant (`validate.rs:681-683`): no `Box<T>` remains as the
    base of a `.deref` projection after `elaborateBoxPlaceBB`. -/
noncomputable def hasDirectBoxDeref (pl : Place) : Bool :=
  match pl.baseTy, pl.projs with
  | .boxTy _, .deref :: _ => true
  | _, _ => false

theorem elaborateBoxDerefs_removes_box_deref (freshPtrLocal : Nat) (pl : Place) :
    hasDirectBoxDeref (elaborateBoxPlaceBB freshPtrLocal pl).rewrittenPlace = false := by
  cases pl with
  | mk _ bty projs =>
    cases bty with
    | boxTy _ =>
      cases projs with
      | nil => rfl
      | cons e _ => cases e <;> rfl
    | boxRawTy _ => rfl
    | nonNullTy _ => rfl
    | patNotNullTy _ => rfl
    | rawConstPtrTy _ => rfl
    | scalarTy => rfl

/-- **Constructive Separation Theorem (`legacyTransmute_elides_unaligned_raw_deref_ub`):**
    Mechanizes the exact live Miri finding on `rustc 1.98.0-nightly`: for an
    unaligned non-null `Box<u32>` (`addr = 0x1001`, `align = 4`), direct `Box`
    semantics and `HEAD` `CastKind::BoxDerefTransmute` both report `.ub`, while
    legacy `CastKind::Transmute` on `NonNull<u32>` silently succeeds with
    `.ok 0x1001 1`! -/
theorem legacyTransmute_elides_unaligned_raw_deref_ub :
    let unalignedEnv : Nat → PtrRep := fun _ => { addr := 4097, allocId := 1, allocLive := true }
    let pl : Place := { localIdx := 1, baseTy := .boxTy 4, projs := [.deref] }
    let eb := elaborateBoxPlaceBB 2 pl
    evalBoxPlaceDirect unalignedEnv pl = .ub ∧
    evalElaboratedBB unalignedEnv 2 eb = .ub ∧
    evalElaboratedBB_legacyTransmute unalignedEnv 2 eb = .ok 4097 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- 4-level `VarDebugInfo` expansion (`elaborate_box_derefs.rs:112-149`):
    expands a `Box` dereference anywhere in a debuginfo projection chain into
    4 nested `Field(0)` projections (`BoxRaw` -> `NonNull` -> `pat(*const T is !null)` -> `*const T`)
    followed by `Deref`. -/
noncomputable def expandBoxDerefVarDebugElems (align : Nat) : List PlaceElem :=
  [ .field 0 (.boxRawTy align)
  , .field 0 (.nonNullTy align)
  , .field 0 (.patNotNullTy align)
  , .field 0 (.rawConstPtrTy align)
  , .deref ]

noncomputable def elaborateVarDebugProjs : TyTag → List PlaceElem → List PlaceElem
  | _, [] => []
  | .boxTy align, .deref :: rest =>
    expandBoxDerefVarDebugElems align ++ elaborateVarDebugProjs .scalarTy rest
  | _, .field idx fty :: rest =>
    .field idx fty :: elaborateVarDebugProjs fty rest
  | _, .deref :: rest =>
    .deref :: elaborateVarDebugProjs .scalarTy rest

noncomputable def elaborateVarDebugPlace (pl : Place) : Place :=
  { pl with projs := elaborateVarDebugProjs pl.baseTy pl.projs }

/-- Evaluate a 4-level expanded debuginfo place (transparent newtype field 0 chain). -/
noncomputable def evalVarDebugExpanded (env : Nat → PtrRep) (pl : Place) : PlaceEvalResult :=
  match pl.baseTy, pl.projs with
  | .boxTy align,
    .field 0 (.boxRawTy align1) ::
    .field 0 (.nonNullTy align2) ::
    .field 0 (.patNotNullTy align3) ::
    .field 0 (.rawConstPtrTy align4) ::
    .deref :: tail =>
      if (align1 == align) && (align2 == align) && (align3 == align) && (align4 == align) then
        let ptr := env pl.localIdx
        if isValidBoxPtr align ptr then
          applyTailProjs ptr.addr ptr.allocId tail
        else
          .ub
      else
        .ub
  | _, _ => .ub

/-- Proves that `elaborateVarDebugPlace` produces the exact 4-level projection chain
    through `PatternKind::NotNull` and preserves evaluated allocation address. -/
theorem elaborateVarDebug_four_level_expansion_and_addr_eq
    (env : Nat → PtrRep) (l align : Nat) (tail : List PlaceElem)
    (hNoNestedBox : elaborateVarDebugProjs .scalarTy tail = tail) :
    let pl : Place := { localIdx := l, baseTy := .boxTy align, projs := .deref :: tail }
    (elaborateVarDebugPlace pl).projs = expandBoxDerefVarDebugElems align ++ tail ∧
    evalVarDebugExpanded env (elaborateVarDebugPlace pl) = evalBoxPlaceDirect env pl := by
  constructor
  · simp [elaborateVarDebugPlace, elaborateVarDebugProjs, hNoNestedBox]
  · simp only [elaborateVarDebugPlace, elaborateVarDebugProjs, expandBoxDerefVarDebugElems,
      hNoNestedBox, List.cons_append, List.nil_append, evalVarDebugExpanded,
      evalBoxPlaceDirect, natBeq_self, Bool.and_self, ↓reduceIte]

end ElaborateBoxDerefs

/-! ## Part 3: `CheckMutRestriction` Three-Surface Capability Soundness -/

namespace CheckMutRestriction

/-- Module hierarchy modeled by explicit parent map and bounded depth traversal. -/
structure ModTree where
  parent : Nat → Option Nat
  maxDepth : Nat

noncomputable def isDescendantFuel (mt : ModTree) : Nat → Nat → Nat → Bool
  | 0, cur, anc => cur == anc
  | fuel + 1, cur, anc =>
    if cur == anc then true
    else
      match mt.parent cur with
      | some p => isDescendantFuel mt fuel p anc
      | none => false

noncomputable def isDescendantOf (mt : ModTree) (m anc : Nat) : Bool :=
  isDescendantFuel mt mt.maxDepth m anc

/-- Mirrors `rustc_middle::ty::RestrictionKind` (`ty/mod.rs:285-342`). -/
inductive RestrictionKind where
  | unrestricted
  | restricted (modId : Nat)

noncomputable def RestrictionKind.isAllowedIn (mt : ModTree) (bodyMod : Nat) : RestrictionKind → Bool
  | .unrestricted => true
  | .restricted anc => isDescendantOf mt bodyMod anc

/-- Exact mirror of `RestrictionKind::stricter_of` (`ty/mod.rs:328-341`). -/
noncomputable def RestrictionKind.stricterOf (mt : ModTree) (lhs rhs : RestrictionKind) : RestrictionKind :=
  match lhs, rhs with
  | .unrestricted, r => r
  | r, .unrestricted => r
  | .restricted lMod, .restricted rMod =>
    if isDescendantOf mt lMod rMod then .restricted lMod else .restricted rMod

/-- Transitivity of module descent in well-formed acyclic module trees. -/
noncomputable def DescTransitive (mt : ModTree) : Prop :=
  ∀ a b c, isDescendantOf mt a b = true → isDescendantOf mt b c = true →
    isDescendantOf mt a c = true

/-- Ancestor-chain comparability: all `mut(in path)` restrictions on fields of one ADT
    are ancestors of the ADT's defining module and therefore mutually comparable. -/
noncomputable def Comparable (mt : ModTree) (r1 r2 : RestrictionKind) : Prop :=
  match r1, r2 with
  | .restricted m1, .restricted m2 =>
    isDescendantOf mt m1 m2 = true ∨ isDescendantOf mt m2 m1 = true
  | _, _ => True

theorem restriction_stricterOf_chain_sound
    (mt : ModTree) (hTrans : DescTransitive mt) (bodyMod : Nat)
    (r1 r2 : RestrictionKind) (hComp : Comparable mt r1 r2) :
    (RestrictionKind.stricterOf mt r1 r2).isAllowedIn mt bodyMod = true ↔
      r1.isAllowedIn mt bodyMod = true ∧ r2.isAllowedIn mt bodyMod = true := by
  cases r1 with
  | unrestricted =>
    cases r2 <;> simp [RestrictionKind.stricterOf, RestrictionKind.isAllowedIn]
  | restricted m1 =>
    cases r2 with
    | unrestricted =>
      simp [RestrictionKind.stricterOf, RestrictionKind.isAllowedIn]
    | restricted m2 =>
      simp only [RestrictionKind.stricterOf, RestrictionKind.isAllowedIn]
      cases h12 : isDescendantOf mt m1 m2 with
      | true =>
        simp only [↓reduceIte]
        constructor
        · intro hb1
          exact ⟨hb1, hTrans bodyMod m1 m2 hb1 h12⟩
        · intro h
          exact h.1
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have h21 : isDescendantOf mt m2 m1 = true := by
          cases hComp with
          | inl h => rw [h] at h12; cases h12
          | inr h => exact h
        constructor
        · intro hb2
          exact ⟨hTrans bodyMod m2 m1 hb2 h21, hb2⟩
        · intro h
          exact h.2

/-- Mirrors `variant.fields.iter().fold(Unrestricted, |acc, f| acc.stricter_of(f.mut_restriction))`
    used in `check_mut_restriction.rs:54-57` and `143-146`. -/
noncomputable def foldStricter (mt : ModTree) : RestrictionKind → List RestrictionKind → RestrictionKind
  | acc, [] => acc
  | acc, r :: rs => foldStricter mt (RestrictionKind.stricterOf mt acc r) rs

/-- All elements in a list form a mutually comparable ancestor chain (e.g., all ancestors of one ADT). -/
noncomputable def ChainCompatible (mt : ModTree) (rs : List RestrictionKind) : Prop :=
  ∀ r1, r1 ∈ rs → ∀ r2, r2 ∈ rs → Comparable mt r1 r2

theorem stricterOf_mem_left_or_right (mt : ModTree) (r1 r2 : RestrictionKind) :
    RestrictionKind.stricterOf mt r1 r2 = r1 ∨ RestrictionKind.stricterOf mt r1 r2 = r2 := by
  cases r1 with
  | unrestricted => exact Or.inr rfl
  | restricted m1 =>
    cases r2 with
    | unrestricted => exact Or.inl rfl
    | restricted m2 =>
      cases h : isDescendantOf mt m1 m2 <;> simp [RestrictionKind.stricterOf, h]

theorem foldStricter_sound (mt : ModTree) (hTrans : DescTransitive mt) (bodyMod : Nat) :
    ∀ (rs : List RestrictionKind) (acc : RestrictionKind),
      ChainCompatible mt (acc :: rs) →
      ((foldStricter mt acc rs).isAllowedIn mt bodyMod = true ↔
        acc.isAllowedIn mt bodyMod = true ∧
        ∀ r, r ∈ rs → r.isAllowedIn mt bodyMod = true)
  | [], acc, _ => by
    constructor
    · intro h; exact ⟨h, fun _ hm => (by cases hm)⟩
    · intro h; exact h.1
  | r :: rs, acc, hChain => by
    have hCompAccR : Comparable mt acc r :=
      hChain acc (List.Mem.head _) r (List.Mem.tail acc (List.Mem.head _))
    have hSubChain : ChainCompatible mt (RestrictionKind.stricterOf mt acc r :: rs) := by
      intro a ha b hb
      have ha' : a ∈ acc :: r :: rs := by
        cases ha with
        | head =>
          cases stricterOf_mem_left_or_right mt acc r with
          | inl heq => rw [heq]; exact (List.Mem.head _)
          | inr heq => rw [heq]; exact List.Mem.tail acc (List.Mem.head _)
        | tail _ hmem => exact List.Mem.tail acc (List.Mem.tail r hmem)
      have hb' : b ∈ acc :: r :: rs := by
        cases hb with
        | head =>
          cases stricterOf_mem_left_or_right mt acc r with
          | inl heq => rw [heq]; exact (List.Mem.head _)
          | inr heq => rw [heq]; exact List.Mem.tail acc (List.Mem.head _)
        | tail _ hmem => exact List.Mem.tail acc (List.Mem.tail r hmem)
      exact hChain a ha' b hb'
    have ih := foldStricter_sound mt hTrans bodyMod rs (RestrictionKind.stricterOf mt acc r) hSubChain
    simp only [foldStricter]
    rw [ih, restriction_stricterOf_chain_sound mt hTrans bodyMod acc r hCompAccR]
    constructor
    · intro ⟨⟨hAcc, hR⟩, hRest⟩
      refine ⟨hAcc, fun x hx => ?_⟩
      cases hx with
      | head => exact hR
      | tail _ hmem => exact hRest x hmem
    · intro ⟨hAcc, hAll⟩
      exact ⟨⟨hAcc, hAll r (List.Mem.head _)⟩, fun x hx => hAll x (List.Mem.tail r hx)⟩

/-- Mirrors `MutatingUseContext` & `PlaceContext::is_mutating_use` (`visit.rs:1336-1440`). -/
inductive MutUseKind where
  | store | setDiscriminant | asmOutput | call | yield | drop | borrow | rawBorrow | projection

inductive PlaceContext where
  | mutating (k : MutUseKind)
  | nonMutating
  | nonUse

noncomputable def PlaceContext.isMutatingUse : PlaceContext → Bool
  | .mutating _ => true
  | .nonMutating => false
  | .nonUse => false

structure AdtDef where
  adtId : Nat
  isUnion : Bool
  fields : List RestrictionKind

inductive MProjElem where
  | deref
  | index (idxLocal : Nat)
  | field (baseAdt : Option AdtDef) (fieldIdx : Nat)

structure MPlace where
  localIdx : Nat
  projs : List MProjElem

inductive MirAction where
  | placeUse (ctx : PlaceContext) (p : MPlace)
  | aggregate (adt : AdtDef) (activeField : Option Nat)
  | ctorConstOperand (adt : AdtDef)

/-- Surface 2: `MutRestrictionChecker::visit_place` (`check_mut_restriction.rs:72-118`). -/
noncomputable def checkProjElem (mt : ModTree) (bodyMod : Nat) : MProjElem → Bool
  | .deref => true
  | .index _ => true
  | .field none _ => true
  | .field (some adt) fieldIdx =>
    match listGet? adt.fields fieldIdx with
    | some r => r.isAllowedIn mt bodyMod
    | none => true

noncomputable def checkPlace (mt : ModTree) (bodyMod : Nat) (ctx : PlaceContext) (p : MPlace) : Bool :=
  if ctx.isMutatingUse then
    allList (checkProjElem mt bodyMod) p.projs
  else
    true

/-- Surface 3: `MutRestrictionChecker::visit_rvalue` (`check_mut_restriction.rs:120-160`). -/
noncomputable def checkAggregate (mt : ModTree) (bodyMod : Nat) (adt : AdtDef) (activeField : Option Nat) : Bool :=
  match activeField with
  | some fieldIdx =>
    match listGet? adt.fields fieldIdx with
    | some r => r.isAllowedIn mt bodyMod
    | none => true
  | none =>
    (foldStricter mt .unrestricted adt.fields).isAllowedIn mt bodyMod

/-- Surface 1: `MutRestrictionChecker::visit_const_operand` (`check_mut_restriction.rs:39-70`). -/
noncomputable def checkCtorConst (mt : ModTree) (bodyMod : Nat) (adt : AdtDef) : Bool :=
  (foldStricter mt .unrestricted adt.fields).isAllowedIn mt bodyMod

noncomputable def checkAction (mt : ModTree) (bodyMod : Nat) : MirAction → Bool
  | .placeUse ctx p => checkPlace mt bodyMod ctx p
  | .aggregate adt af => checkAggregate mt bodyMod adt af
  | .ctorConstOperand adt => checkCtorConst mt bodyMod adt

noncomputable def checkBodyActions (mt : ModTree) (bodyMod : Nat) (taintedByErrors : Bool)
    (actions : List MirAction) : Bool :=
  if taintedByErrors then true else allList (checkAction mt bodyMod) actions

/-- Helper predicate: a projection chain has zero `MProjElem.field` elements
    (e.g., whole-ADT overwrite `s = ...` or `*s = ...`). -/
noncomputable def hasNoFieldProj (projs : List MProjElem) : Bool :=
  allList (fun e => match e with | .field _ _ => false | _ => true) projs

theorem checkPlace_permits_no_field_proj (mt : ModTree) (bodyMod : Nat)
    (ctx : PlaceContext) (p : MPlace) (hNoField : hasNoFieldProj p.projs = true) :
    checkPlace mt bodyMod ctx p = true := by
  unfold checkPlace
  cases ctx.isMutatingUse with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    rw [allList_iff]
    intro e he
    have hnf := (allList_iff _ p.projs).mp hNoField e he
    cases e with
    | deref => rfl
    | index _ => rfl
    | field _ _ => cases hnf

theorem checkPlace_rejects_restricted_field (mt : ModTree) (bodyMod : Nat)
    (k : MutUseKind) (p : MPlace) (adt : AdtDef) (fidx : Nat) (r : RestrictionKind)
    (hMem : MProjElem.field (some adt) fidx ∈ p.projs)
    (hField : listGet? adt.fields fidx = some r)
    (hDenied : r.isAllowedIn mt bodyMod = false) :
    checkPlace mt bodyMod (.mutating k) p = false := by
  unfold checkPlace
  simp only [PlaceContext.isMutatingUse, ↓reduceIte]
  cases hAll : allList (checkProjElem mt bodyMod) p.projs with
  | false => rfl
  | true =>
    have hElem := (allList_iff _ p.projs).mp hAll (.field (some adt) fidx) hMem
    simp only [checkProjElem, hField, hDenied] at hElem
    cases hElem

/-- **Theorem 3 (`checkMutRestriction_blocks_field_mut_and_ctor_fn_permits_whole_adt`):**
    Simultaneously proves all four core soundness and precision guarantees of
    `CheckMutRestriction`:
    (1) Any mutating use containing a restricted ADT field projection (even nested
        under `Deref` or followed by `Index`, e.g., `(*s).arr[0] = 42`) is rejected.
    (2) Any struct/enum aggregate construction OR first-class tuple constructor
        `FnDef` const operand whose variant contains a restricted field is rejected.
    (3) A union aggregate initializing active field `i` is permitted iff field `i`
        itself is allowed, independent of restrictions on inactive fields.
    (4) Whole-ADT place replacement (`s = val` or `*s = val`, zero `Field` projections)
        is unconditionally permitted outside the restriction module. -/
theorem checkMutRestriction_blocks_field_mut_and_ctor_fn_permits_whole_adt
    (mt : ModTree) (hTrans : DescTransitive mt) (bodyMod : Nat)
    (adt : AdtDef) (hChain : ChainCompatible mt (.unrestricted :: adt.fields)) :
    -- (1) Restricted field mutation (at any depth in projection chain) is rejected
    (∀ (k : MutUseKind) (p : MPlace) (fidx : Nat) (r : RestrictionKind),
      MProjElem.field (some adt) fidx ∈ p.projs →
      listGet? adt.fields fidx = some r →
      r.isAllowedIn mt bodyMod = false →
      checkAction mt bodyMod (.placeUse (.mutating k) p) = false) ∧
    -- (2) Struct/enum aggregate and tuple-ctor FnDef value are rejected if any field is restricted
    (∀ (r : RestrictionKind),
      r ∈ adt.fields → r.isAllowedIn mt bodyMod = false →
      checkAction mt bodyMod (.aggregate adt none) = false ∧
      checkAction mt bodyMod (.ctorConstOperand adt) = false) ∧
    -- (3) Union aggregate checks ONLY the active field
    (∀ (fidx : Nat) (r : RestrictionKind),
      listGet? adt.fields fidx = some r →
      checkAction mt bodyMod (.aggregate adt (some fidx)) = r.isAllowedIn mt bodyMod) ∧
    -- (4) Whole-ADT overwrite (zero Field projections) is permitted
    (∀ (ctx : PlaceContext) (p : MPlace),
      hasNoFieldProj p.projs = true →
      checkAction mt bodyMod (.placeUse ctx p) = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k p fidx r hMem hField hDenied
    exact checkPlace_rejects_restricted_field mt bodyMod k p adt fidx r hMem hField hDenied
  · intro r hMem hDenied
    have hFoldFalse : (foldStricter mt .unrestricted adt.fields).isAllowedIn mt bodyMod = false := by
      cases hRes : (foldStricter mt .unrestricted adt.fields).isAllowedIn mt bodyMod with
      | false => rfl
      | true =>
        have hAll := ((foldStricter_sound mt hTrans bodyMod adt.fields .unrestricted hChain).mp hRes).2
        have hOk := hAll r hMem
        rw [hDenied] at hOk
        cases hOk
    exact ⟨hFoldFalse, hFoldFalse⟩
  · intro fidx r hField
    simp [checkAction, checkAggregate, hField]
  · intro ctx p hNoField
    exact checkPlace_permits_no_field_proj mt bodyMod ctx p hNoField

/-- Concrete witness: union `U { a: u32, pub mut(in crate::inner) b: u32 }`
    allows `U { a: 1 }` outside `crate::inner` while rejecting `U { b: 1 }`,
    and `s.x = 42` is rejected while `*s = S::new(99)` is permitted. -/
theorem concrete_mut_restriction_witness :
    let mt : ModTree := { parent := fun m => if m == 1 then some 0 else none, maxDepth := 2 }
    let unionU : AdtDef := { adtId := 10, isUnion := true, fields := [.unrestricted, .restricted 1] }
    let structS : AdtDef := { adtId := 11, isUnion := false, fields := [.restricted 1, .unrestricted] }
    checkAction mt 0 (.aggregate unionU (some 0)) = true ∧
    checkAction mt 0 (.aggregate unionU (some 1)) = false ∧
    checkAction mt 0 (.placeUse (.mutating .store) { localIdx := 1, projs := [.deref] }) = true ∧
    checkAction mt 0 (.placeUse (.mutating .store) { localIdx := 1, projs := [.deref, .field (some structS) 0] }) = false ∧
    checkAction mt 0 (.ctorConstOperand structS) = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end CheckMutRestriction

/-! ## Part 4: `RemoveNoopLandingPads` & `AddCallGuards::CriticalCallEdges` -/

namespace CallGuardsAndLandingPads

inductive UnwindAction where
  | continue_
  | unreachable
  | cleanup (bb : Nat)
  | terminate

/-- Exact mirror of `add_call_guards.rs:135-140`. -/
noncomputable def generatesInvoke : UnwindAction → Bool
  | .continue_ => false
  | .unreachable => false
  | .cleanup _ => true
  | .terminate => true

inductive CgStmt where
  | nop
  | storageLive (l : Nat)
  | storageDead (l : Nat)
  | localAssign (dst : Nat) (val : Nat)
  | heapWrite (addr : Nat) (val : Nat)

/-- Exact mirror of statement admissibility in `remove_noop_landing_pads.rs:84-112`:
    storage markers, nops, and local-only (drop-flag) assignments are noops in a
    landing pad; non-local / heap writes are NOT noops. -/
noncomputable def isNopLpStmt : CgStmt → Bool
  | .nop => true
  | .storageLive _ => true
  | .storageDead _ => true
  | .localAssign _ _ => true
  | .heapWrite _ _ => false

inductive CgTerm where
  | goto (target : Nat)
  | switchInt (condLocal : Nat) (tTarget : Nat) (fTarget : Nat)
  | call (retLocal : Nat) (retVal : Nat) (mayPanic : Bool) (target : Option Nat) (unwind : UnwindAction)
  | inlineAsm (hasOutputs : Bool) (hasLabels : Bool) (targets : List Nat) (unwind : UnwindAction)
  | drop (isTrivialGlue : Bool) (target : Nat) (unwind : UnwindAction)
  | unwindResume
  | ret (localIdx : Nat)

structure CgBlock where
  stmts : List CgStmt
  term : CgTerm
  isCleanup : Bool

abbrev CgCfg := List CgBlock

noncomputable def unwindSuccs : UnwindAction → List Nat
  | .cleanup bb => [bb]
  | _ => []

noncomputable def termSuccs : CgTerm → List Nat
  | .goto t => [t]
  | .switchInt _ t f => [t, f]
  | .call _ _ _ (some d) uw => d :: unwindSuccs uw
  | .call _ _ _ none uw => unwindSuccs uw
  | .inlineAsm _ _ ts uw => ts ++ unwindSuccs uw
  | .drop _ t uw => t :: unwindSuccs uw
  | .unwindResume => []
  | .ret _ => []

/-- Exact predecessor count across all blocks' successors (`add_call_guards.rs:34-39`). -/
noncomputable def predCount (cfg : CgCfg) (target : Nat) : Nat :=
  match cfg with
  | [] => 0
  | blk :: rest => natCountIn target (termSuccs blk.term) + predCount rest target

theorem predCount_append (c1 c2 : CgCfg) (t : Nat) :
    predCount (c1 ++ c2) t = predCount c1 t + predCount c2 t := by
  induction c1 with
  | nil => simp [predCount]
  | cons blk rest ih =>
    simp only [List.cons_append, predCount, ih, Nat.add_assoc]

/-! ### 4A. `RemoveNoopLandingPads` Soundness & `generatesInvoke` Interaction -/

noncomputable def listMemNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => (x == y) || listMemNat x ys

/-- Mirrors `RemoveNoopLandingPads::is_nop_landing_pad` (`remove_noop_landing_pads.rs:75-153`),
    including the post-monomorphization `Drop` trivial-glue extension (`mono = true`). -/
noncomputable def isNopLandingPadBlock (mono : Bool) (nopSet : List Nat) (blk : CgBlock) : Bool :=
  allList isNopLpStmt blk.stmts &&
  match blk.term with
  | .goto t => listMemNat t nopSet
  | .unwindResume => true
  | .switchInt _ t f => listMemNat t nopSet && listMemNat f nopSet
  | .drop isTrivial t uw =>
    mono && isTrivial && listMemNat t nopSet &&
      allList (fun u => listMemNat u nopSet) (unwindSuccs uw)
  | .call _ _ _ _ _ => false
  | .inlineAsm _ _ _ _ => false
  | .ret _ => false

noncomputable def rewriteUnwindForNop (nopSet : List Nat) : UnwindAction → UnwindAction
  | .cleanup bb => if listMemNat bb nopSet then .continue_ else .cleanup bb
  | uw => uw

noncomputable def rewriteTermNoopLP (nopSet : List Nat) : CgTerm → CgTerm
  | .call rl rv mp tgt uw => .call rl rv mp tgt (rewriteUnwindForNop nopSet uw)
  | .inlineAsm ho hl ts uw => .inlineAsm ho hl ts (rewriteUnwindForNop nopSet uw)
  | .drop tr tgt uw => .drop tr tgt (rewriteUnwindForNop nopSet uw)
  | t => t

noncomputable def removeNoopLandingPads (nopSet : List Nat) (cfg : CgCfg) : CgCfg :=
  cfg.map (fun blk => { blk with term := rewriteTermNoopLP nopSet blk.term })

/-- **Theorem 4a (`removeNoopLandingPads_flips_generatesInvoke`):**
    When `bb` is identified as a noop landing pad, rewriting `UnwindAction.cleanup bb`
    flips `generatesInvoke` from `true` to `false`, directly disabling critical-edge
    splitting in `AddCallGuards::CriticalCallEdges`. -/
theorem removeNoopLandingPads_flips_generatesInvoke (nopSet : List Nat) (bb : Nat)
    (hMem : listMemNat bb nopSet = true) :
    generatesInvoke (.cleanup bb) = true ∧
    rewriteUnwindForNop nopSet (.cleanup bb) = .continue_ ∧
    generatesInvoke (rewriteUnwindForNop nopSet (.cleanup bb)) = false := by
  simp [generatesInvoke, rewriteUnwindForNop, hMem]

/-! ### Operational Semantics for `CgCfg` (Heap + Locals + Unwinding) -/

structure CgState where
  locals : List Nat
  heap : List (Nat × Nat)

noncomputable def stepCgStmt (st : CgState) : CgStmt → CgState
  | .nop => st
  | .storageLive _ => st
  | .storageDead _ => st
  | .localAssign dst val => { st with locals := listSet st.locals dst val }
  | .heapWrite addr val => { st with heap := st.heap ++ [(addr, val)] }

noncomputable def stepCgStmts (st : CgState) : List CgStmt → CgState
  | [] => st
  | s :: ss => stepCgStmts (stepCgStmt st s) ss

theorem stepCgStmt_nop_preserves_heap (st : CgState) (s : CgStmt)
    (hNop : isNopLpStmt s = true) :
    (stepCgStmt st s).heap = st.heap := by
  cases s with
  | nop => rfl
  | storageLive _ => rfl
  | storageDead _ => rfl
  | localAssign _ _ => rfl
  | heapWrite _ _ => cases hNop

theorem stepCgStmts_nop_preserves_heap :
    ∀ (ss : List CgStmt) (st : CgState),
      allList isNopLpStmt ss = true →
      (stepCgStmts st ss).heap = st.heap
  | [], _, _ => rfl
  | s :: ss, st, h => by
    simp only [allList, Bool.and_eq_true] at h
    simp only [stepCgStmts]
    rw [stepCgStmts_nop_preserves_heap ss (stepCgStmt st s) h.2]
    exact stepCgStmt_nop_preserves_heap st s h.1

/-- Observable execution outcome: normal return (value + heap), propagated unwind
    with final heap, abnormal abort/terminate, or stuck. -/
inductive CgOutcome where
  | ret (v : Nat) (heap : List (Nat × Nat))
  | unwound (heap : List (Nat × Nat))
  | aborted (heap : List (Nat × Nat))
  | stuck

/-- A single-step unwind execution of a cleanup pad (bounded by `fuel`), modeling
    `UnwindAction::Cleanup(bb)` vs `UnwindAction::Continue` (which directly yields
    `.unwound st.heap`). -/
noncomputable def runUnwindPad (cfg : CgCfg) : Nat → Nat → CgState → Option CgOutcome
  | 0, _, _ => none
  | fuel + 1, bb, st =>
    match listGet? cfg bb with
    | none => some .stuck
    | some blk =>
      let st' := stepCgStmts st blk.stmts
      match blk.term with
      | .unwindResume => some (.unwound st'.heap)
      | .goto t => runUnwindPad cfg fuel t st'
      | .switchInt cond t f =>
        if listGetD st'.locals cond 0 == 0 then
          runUnwindPad cfg fuel f st'
        else
          runUnwindPad cfg fuel t st'
      | .drop true t _ => runUnwindPad cfg fuel t st'
      | _ => some (.aborted st'.heap)

/-- Soundness certificate for a noop landing-pad set: every block `bb ∈ nopSet`
    is a verified noop landing pad whose rank strictly decreases along transitions. -/
noncomputable def ValidNopSet (mono : Bool) (cfg : CgCfg) (nopSet : List Nat) (rank : Nat → Nat) : Prop :=
  ∀ bb, listMemNat bb nopSet = true →
    ∃ blk, listGet? cfg bb = some blk ∧
      allList isNopLpStmt blk.stmts = true ∧
      match blk.term with
      | .unwindResume => True
      | .goto t => listMemNat t nopSet = true ∧ rank t < rank bb
      | .switchInt _ t f =>
        listMemNat t nopSet = true ∧ rank t < rank bb ∧
        listMemNat f nopSet = true ∧ rank f < rank bb
      | .drop true t _ => mono = true ∧ listMemNat t nopSet = true ∧ rank t < rank bb
      | _ => False

theorem runUnwindPad_valid_nop_set (mono : Bool) (cfg : CgCfg) (nopSet : List Nat)
    (rank : Nat → Nat) (hValid : ValidNopSet mono cfg nopSet rank) :
    ∀ (k : Nat) (bb : Nat) (st : CgState),
      listMemNat bb nopSet = true →
      rank bb < k →
      runUnwindPad cfg k bb st = some (.unwound st.heap)
  | 0, _, _, _, hLt => False.elim (Nat.not_lt_zero _ hLt)
  | k + 1, bb, st, hMem, hLt => by
    rcases hValid bb hMem with ⟨blk, hGet, hStmts, hTerm⟩
    have hHeap : (stepCgStmts st blk.stmts).heap = st.heap :=
      stepCgStmts_nop_preserves_heap blk.stmts st hStmts
    simp only [runUnwindPad, hGet]
    cases hBlkTerm : blk.term with
    | unwindResume =>
      dsimp only
      simp only [hHeap]
    | goto t =>
      dsimp only
      rw [hBlkTerm] at hTerm
      dsimp only at hTerm
      have hRankT : rank t < k := Nat.lt_of_lt_of_le hTerm.2 (Nat.le_of_lt_succ hLt)
      rw [runUnwindPad_valid_nop_set mono cfg nopSet rank hValid k t (stepCgStmts st blk.stmts) hTerm.1 hRankT, hHeap]
    | switchInt cond t f =>
      dsimp only
      rw [hBlkTerm] at hTerm
      dsimp only at hTerm
      cases listGetD (stepCgStmts st blk.stmts).locals cond 0 == 0 with
      | true =>
        have hRankF : rank f < k := Nat.lt_of_lt_of_le hTerm.2.2.2 (Nat.le_of_lt_succ hLt)
        rw [runUnwindPad_valid_nop_set mono cfg nopSet rank hValid k f (stepCgStmts st blk.stmts) hTerm.2.2.1 hRankF, hHeap]
        rfl
      | false =>
        have hRankT : rank t < k := Nat.lt_of_lt_of_le hTerm.2.1 (Nat.le_of_lt_succ hLt)
        rw [runUnwindPad_valid_nop_set mono cfg nopSet rank hValid k t (stepCgStmts st blk.stmts) hTerm.1 hRankT, hHeap]
        rfl
    | drop isTriv t uw =>
      cases isTriv with
      | false =>
        rw [hBlkTerm] at hTerm
        exact False.elim hTerm
      | true =>
        dsimp only
        rw [hBlkTerm] at hTerm
        dsimp only at hTerm
        have hRankT : rank t < k := Nat.lt_of_lt_of_le hTerm.2.2 (Nat.le_of_lt_succ hLt)
        rw [runUnwindPad_valid_nop_set mono cfg nopSet rank hValid k t (stepCgStmts st blk.stmts) hTerm.2.1 hRankT, hHeap]
    | call _ _ _ _ _ => rw [hBlkTerm] at hTerm; exact False.elim hTerm
    | inlineAsm _ _ _ _ => rw [hBlkTerm] at hTerm; exact False.elim hTerm
    | ret _ => rw [hBlkTerm] at hTerm; exact False.elim hTerm

/-- **Theorem 4b (`removeNoopLandingPads_preserves_unwind_outcome`):**
    Evaluating `UnwindAction.cleanup bb` on any verified noop landing pad yields
    `some (.unwound st.heap)` — identical to `UnwindAction.continue_`. -/
theorem removeNoopLandingPads_preserves_unwind_outcome
    (mono : Bool) (cfg : CgCfg) (nopSet : List Nat) (rank : Nat → Nat)
    (hValid : ValidNopSet mono cfg nopSet rank)
    (bb : Nat) (st : CgState) (hMem : listMemNat bb nopSet = true) :
    runUnwindPad cfg (rank bb + 1) bb st = some (.unwound st.heap) :=
  runUnwindPad_valid_nop_set mono cfg nopSet rank hValid (rank bb + 1) bb st hMem (Nat.lt_succ_self _)

/-! ### 4B. `AddCallGuards::CriticalCallEdges` Critical-Edge Elimination & Semantic Preservation -/

inductive CallGuardMode where
  | allCallEdges
  | criticalCallEdges

noncomputable def isAllCallEdges : CallGuardMode → Bool
  | .allCallEdges => true
  | .criticalCallEdges => false

noncomputable def isCriticalCallEdges : CallGuardMode → Bool
  | .allCallEdges => false
  | .criticalCallEdges => true

/-- Split targets of an `InlineAsm` terminator whenever `predCount origCfg t > 1`,
    allocating sequential fresh trampoline blocks starting at `nextId`. -/
noncomputable def splitAsmTargets (origCfg : CgCfg) (isCleanup : Bool) :
    List Nat → Nat → List Nat × CgCfg
  | [], _ => ([], [])
  | t :: ts, nextId =>
    if 1 < predCount origCfg t then
      let tramp : CgBlock := { stmts := [], term := .goto t, isCleanup := isCleanup }
      let (ts', extra) := splitAsmTargets origCfg isCleanup ts (nextId + 1)
      (nextId :: ts', tramp :: extra)
    else
      let (ts', extra) := splitAsmTargets origCfg isCleanup ts nextId
      (t :: ts', extra)

/-- Rewrite one block's terminator per `add_call_guards.rs:47-121`, returning the
    rewritten block and any freshly allocated trampoline blocks (`nextId ..`). -/
noncomputable def rewriteBlockCallGuards (mode : CallGuardMode) (origCfg : CgCfg)
    (blk : CgBlock) (nextId : Nat) : CgBlock × CgCfg :=
  match blk.term with
  | .call rl rv mp (some d) uw =>
    if 1 < predCount origCfg d && (generatesInvoke uw || isAllCallEdges mode) then
      let tramp : CgBlock := { stmts := [], term := .goto d, isCleanup := blk.isCleanup }
      ({ blk with term := .call rl rv mp (some nextId) uw }, [tramp])
    else
      (blk, [])
  | .inlineAsm hasOutputs hasLabels targets uw =>
    if isCriticalCallEdges mode && hasOutputs && (hasLabels || generatesInvoke uw) then
      let (targets', tramps) := splitAsmTargets origCfg blk.isCleanup targets nextId
      ({ blk with term := .inlineAsm hasOutputs hasLabels targets' uw }, tramps)
    else
      (blk, [])
  | _ => (blk, [])

noncomputable def rewriteBlocksCallGuards (mode : CallGuardMode) (origCfg : CgCfg) :
    CgCfg → Nat → CgCfg × CgCfg
  | [], _ => ([], [])
  | blk :: rest, nextId =>
    let (blk', tramps) := rewriteBlockCallGuards mode origCfg blk nextId
    let (rest', moreTramps) := rewriteBlocksCallGuards mode origCfg rest (nextId + tramps.length)
    (blk' :: rest', tramps ++ moreTramps)

/-- Exact functional model of `AddCallGuards::run_pass` (`add_call_guards.rs:33-125`). -/
noncomputable def addCallGuards (mode : CallGuardMode) (cfg : CgCfg) : CgCfg :=
  let (rewritten, tramps) := rewriteBlocksCallGuards mode cfg cfg cfg.length
  rewritten ++ tramps

/-! #### Structural Well-Formedness & Predecessor-Count Accounting -/

/-- All successor block indices in `cfg` lie strictly below `bound`. -/
noncomputable def SuccsBounded (cfg : CgCfg) (bound : Nat) : Prop :=
  ∀ blk, blk ∈ cfg → ∀ s, s ∈ termSuccs blk.term → s < bound

theorem nat_lt_succ_of_le {a b : Nat} (h : a ≤ b) : a < b + 1 :=
  Nat.lt_succ_of_le h

theorem nat_le_of_not_lt {a b : Nat} (h : ¬(a < b)) : b ≤ a :=
  Nat.le_of_not_lt h

theorem nat_eq_or_succ_le {a b : Nat} (h : a ≤ b) : a = b ∨ a + 1 ≤ b := by
  cases Nat.eq_or_lt_of_le h with
  | inl heq => exact Or.inl heq
  | inr hlt => exact Or.inr hlt

theorem nat_not_lt_of_eq {a b : Nat} (h : a = b) : ¬(a < b) := by
  rw [h]; exact Nat.lt_irrefl b

theorem nat_lt_add_right {a b c : Nat} (h : a < b) : a < b + c :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right b c)

theorem nat_le_add_left_of_le {a b c : Nat} (h : a ≤ b) : a ≤ b + c :=
  Nat.le_trans h (Nat.le_add_right b c)

theorem nat_add_right_comm_1 (a b : Nat) : a + (b + 1) = (a + 1) + b := by
  rw [Nat.add_comm b 1, Nat.add_assoc]

theorem splitAsmTargets_props (origCfg : CgCfg) (ic : Bool) :
    ∀ (ts : List Nat) (nextId : Nat),
      (∀ t, t ∈ ts → t < nextId) →
      let res := splitAsmTargets origCfg ic ts nextId
      -- (1) Every newly created trampoline jumps to an original target `< nextId` and inherits `ic`
      (∀ b, b ∈ res.2 → ∃ t, t ∈ ts ∧ b = { stmts := [], term := .goto t, isCleanup := ic }) ∧
      -- (2) Every fresh index `k ∈ [nextId, nextId + res.2.length)` occurs EXACTLY ONCE in `res.1`
      (∀ k, nextId ≤ k → k < nextId + res.2.length → natCountIn k res.1 = 1) ∧
      -- (3) Every index `k ≥ nextId + res.2.length` occurs 0 times in `res.1`
      (∀ k, nextId + res.2.length ≤ k → natCountIn k res.1 = 0) ∧
      -- (4) Every element `t' ∈ res.1` is either fresh in `[nextId, nextId + res.2.length)`
      --     or an unsplit original target with `predCount origCfg t' ≤ 1`
      (∀ t', t' ∈ res.1 →
        (nextId ≤ t' ∧ t' < nextId + res.2.length) ∨ (t' ∈ ts ∧ predCount origCfg t' ≤ 1)) ∧
      -- (5) Predecessor-count conservation for all `k < nextId`
      (∀ k, k < nextId → natCountIn k res.1 + predCount res.2 k = natCountIn k ts) ∧
      -- (6) Exact trampoline lookup: each `t' ∈ res.1` resolves either directly (unsplit)
      --     or via `res.2` at offset `t' - nextId` to `.goto t` with `t ∈ ts`
      (∀ (i : Nat), i < ts.length →
        ∃ t t', listGet? ts i = some t ∧ listGet? res.1 i = some t' ∧
          (t' = t ∨ (nextId ≤ t' ∧ ∃ k, t' = nextId + k ∧
            listGet? res.2 k = some { stmts := [], term := .goto t, isCleanup := ic }))) ∧
      -- (7) Exact length preservation of targets list
      (res.1.length = ts.length)
  | [], nextId, _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · intro _ h; cases h
    · intro k hle hlt
      simp only [splitAsmTargets, List.length_nil, Nat.add_zero] at hlt
      exact False.elim (Nat.not_lt_of_ge hle hlt)
    · intro k _; rfl
    · intro _ h; cases h
    · intro _ _; rfl
    · intro _ h; cases h
  | t :: ts, nextId, hBound => by
    have htLt : t < nextId := hBound t (List.Mem.head _)
    have hTsLt : ∀ x, x ∈ ts → x < nextId := fun x hx => hBound x (List.Mem.tail t hx)
    have hTsLtSucc : ∀ x, x ∈ ts → x < nextId + 1 :=
      fun x hx => Nat.lt_trans (hTsLt x hx) (Nat.lt_succ_self nextId)
    simp only [splitAsmTargets]
    cases hCrit : decide (1 < predCount origCfg t) with
    | true =>
      have hCritProp : 1 < predCount origCfg t := of_decide_eq_true hCrit
      simp only [hCritProp, ↓reduceIte]
      have ih := splitAsmTargets_props origCfg ic ts (nextId + 1) hTsLtSucc
      rcases ih with ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩
      let rest := splitAsmTargets origCfg ic ts (nextId + 1)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- (1) trampoline targets
        intro b hb
        cases hb with
        | head => exact ⟨t, (List.Mem.head _), rfl⟩
        | tail _ hmem =>
          rcases ih1 b hmem with ⟨t0, ht0, heq⟩
          exact ⟨t0, List.Mem.tail t ht0, heq⟩
      · -- (2) fresh indices occur exactly once
        intro k hle hlt
        simp only [List.length_cons] at hlt
        have hlt' : k < (nextId + 1) + rest.2.length := by
          rw [← nat_add_right_comm_1]; exact hlt
        simp only [natCountIn]
        cases nat_eq_or_succ_le hle with
        | inl heq =>
          subst heq
          have hBeq : (nextId == nextId) = true := natBeq_self nextId
          have hZero : natCountIn nextId rest.1 = 0 := by
            apply natCountIn_zero_of_forall_ne
            intro x hx
            cases ih4 x hx with
            | inl hFresh =>
              intro hEqX
              rw [hEqX] at hFresh
              exact Nat.not_succ_le_self nextId hFresh.1
            | inr hOld =>
              intro hEqX
              rw [hEqX] at hOld
              exact Nat.lt_irrefl nextId (hTsLt nextId hOld.1)
          simp only [hBeq, ↓reduceIte]
          have h0 : natCountIn nextId (splitAsmTargets origCfg ic ts (nextId + 1)).1 = 0 := hZero
          rw [h0]
        | inr hSuccLe =>
          have hNe : nextId ≠ k := Nat.ne_of_lt hSuccLe
          have hBeq : (nextId == k) = false := natBeq_false_of_ne hNe
          have hRest : natCountIn k (splitAsmTargets origCfg ic ts (nextId + 1)).1 = 1 := ih2 k hSuccLe hlt'
          simp only [hBeq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          exact hRest
      · -- (3) indices >= nextId + (rest.2.length + 1) occur 0 times
        intro k hge
        simp only [List.length_cons] at hge
        have hge' : (nextId + 1) + rest.2.length ≤ k := by
          rw [← nat_add_right_comm_1]; exact hge
        have hNe : nextId ≠ k :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self nextId)
            (Nat.le_trans (Nat.le_add_right _ _) hge'))
        have hBeq : (nextId == k) = false := natBeq_false_of_ne hNe
        have hZero := ih3 k hge'
        simp [natCountIn, hBeq, hZero]
      · -- (4) element classification
        intro t' ht'
        cases ht' with
        | head =>
          left
          refine ⟨Nat.le_refl nextId, ?_⟩
          simp only [List.length_cons]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self nextId)
            (by rw [Nat.add_comm _ 1, ← Nat.add_assoc]; exact Nat.le_add_right (nextId + 1) _)
        | tail _ hmem =>
          cases ih4 t' hmem with
          | inl hFresh =>
            left
            refine ⟨Nat.le_trans (Nat.le_succ nextId) hFresh.1, ?_⟩
            simp only [List.length_cons]
            rw [nat_add_right_comm_1]
            exact hFresh.2
          | inr hOld =>
            right
            exact ⟨List.Mem.tail t hOld.1, hOld.2⟩
      · -- (5) predecessor-count conservation for k < nextId
        intro k hk
        have hNe : nextId ≠ k := Nat.ne_of_gt hk
        have hBeq : (nextId == k) = false := natBeq_false_of_ne hNe
        have hCons := ih5 k (Nat.lt_trans hk (Nat.lt_succ_self nextId))
        simp only [natCountIn, hBeq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, predCount, termSuccs, Nat.add_zero]
        rw [Nat.add_left_comm, hCons]
      · -- (6) trampoline lookup
        intro i hi
        cases i with
        | zero =>
          refine ⟨t, nextId, rfl, rfl, Or.inr ⟨Nat.le_refl nextId, 0, (Nat.add_zero nextId).symm, rfl⟩⟩
        | succ j =>
          have hj : j < ts.length := Nat.lt_of_succ_lt_succ hi
          rcases ih6 j hj with ⟨t0, t0', hGetTs, hGetRes, hCase⟩
          refine ⟨t0, t0', hGetTs, hGetRes, ?_⟩
          cases hCase with
          | inl heq => exact Or.inl heq
          | inr hTramp =>
            rcases hTramp with ⟨hLe, k, hEqK, hTrampGet⟩
            right
            refine ⟨Nat.le_trans (Nat.le_succ nextId) hLe, k + 1, ?_, hTrampGet⟩
            rw [hEqK, Nat.add_assoc, Nat.add_comm 1 k]
      · -- (7) length
        simp [ih7]
    | false =>
      have hNotCrit : ¬(1 < predCount origCfg t) := of_decide_eq_false hCrit
      have hLeOne : predCount origCfg t ≤ 1 := nat_le_of_not_lt hNotCrit
      simp only [hNotCrit, ↓reduceIte]
      have ih := splitAsmTargets_props origCfg ic ts nextId hTsLt
      rcases ih with ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩
      let rest := splitAsmTargets origCfg ic ts nextId
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rcases ih1 b hb with ⟨t0, ht0, heq⟩
        exact ⟨t0, List.Mem.tail t ht0, heq⟩
      · intro k hle hlt
        have hNe : t ≠ k := Nat.ne_of_lt (Nat.lt_of_lt_of_le htLt hle)
        have hBeq : (t == k) = false := natBeq_false_of_ne hNe
        simp [natCountIn, hBeq, ih2 k hle hlt]
      · intro k hge
        have hNe : t ≠ k :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le htLt (Nat.le_trans (Nat.le_add_right _ _) hge))
        have hBeq : (t == k) = false := natBeq_false_of_ne hNe
        simp [natCountIn, hBeq, ih3 k hge]
      · intro t' ht'
        cases ht' with
        | head => exact Or.inr ⟨(List.Mem.head _), hLeOne⟩
        | tail _ hmem =>
          cases ih4 t' hmem with
          | inl hFresh => exact Or.inl hFresh
          | inr hOld => exact Or.inr ⟨List.Mem.tail t hOld.1, hOld.2⟩
      · intro k hk
        simp only [natCountIn]
        rw [Nat.add_assoc, ih5 k hk]
      · intro i hi
        cases i with
        | zero => exact ⟨t, t, rfl, rfl, Or.inl rfl⟩
        | succ j =>
          rcases ih6 j (Nat.lt_of_succ_lt_succ hi) with ⟨t0, t0', h1, h2, h3⟩
          exact ⟨t0, t0', h1, h2, h3⟩
      · simp [ih7]

/-- Predicate expressing that `blk` has ZERO critical edges requiring splitting under
    `CriticalCallEdges` (both for `Call` invokes and `InlineAsm` output targets). -/
noncomputable def BlockNoCriticalEdges (cfg : CgCfg) (blk : CgBlock) : Prop :=
  match blk.term with
  | .call _ _ _ (some d) uw =>
    generatesInvoke uw = true → predCount cfg d ≤ 1
  | .inlineAsm true hasLabels targets uw =>
    (hasLabels = true ∨ generatesInvoke uw = true) →
      ∀ t, t ∈ targets → predCount cfg t ≤ 1
  | _ => True

/-- Every block in `cfg` satisfies `BlockNoCriticalEdges cfg`. -/
noncomputable def CfgNoCriticalEdges (cfg : CgCfg) : Prop :=
  ∀ blk, blk ∈ cfg → BlockNoCriticalEdges cfg blk

/-- Helper: every trampoline block has `term = .goto t` with `t < bound`, hence
    `predCount tramps k = 0` for all `k ≥ bound`. -/
noncomputable def TrampolinesBounded (tramps : CgCfg) (bound : Nat) : Prop :=
  ∀ b, b ∈ tramps → ∃ t, t < bound ∧ ∃ ic, b = { stmts := [], term := .goto t, isCleanup := ic }

theorem predCount_trampolines_zero_of_ge (tramps : CgCfg) (bound k : Nat)
    (hTramps : TrampolinesBounded tramps bound) (hGe : bound ≤ k) :
    predCount tramps k = 0 := by
  induction tramps with
  | nil => rfl
  | cons b rest ih =>
    rcases hTramps b (List.Mem.head _) with ⟨t, htLt, ic, hEq⟩
    have hNe : t ≠ k := Nat.ne_of_lt (Nat.lt_of_lt_of_le htLt hGe)
    have hBeq : (t == k) = false := natBeq_false_of_ne hNe
    have hRest : predCount rest k = 0 :=
      ih (fun x hx => hTramps x (List.Mem.tail b hx))
    simp [predCount, hEq, termSuccs, natCountIn, hBeq, hRest]

/-- Core per-block accounting lemma for `rewriteBlockCallGuards`, parameterized by
    `origBound ≤ nextId` so trampolines stay bounded by `origBound`. -/
theorem rewriteBlockCallGuards_props (mode : CallGuardMode) (origCfg : CgCfg)
    (blk : CgBlock) (origBound nextId : Nat) (hOrigLe : origBound ≤ nextId)
    (hBlkBound : ∀ s, s ∈ termSuccs blk.term → s < origBound) :
    let res := rewriteBlockCallGuards mode origCfg blk nextId
    -- (1) Trampolines are bounded by `origBound`
    TrampolinesBounded res.2 origBound ∧
    -- (2) Fresh indices in `[nextId, nextId + res.2.length)` occur EXACTLY ONCE in `res.1`
    (∀ k, nextId ≤ k → k < nextId + res.2.length → natCountIn k (termSuccs res.1.term) = 1) ∧
    -- (3) Indices `≥ nextId + res.2.length` occur 0 times in `res.1`
    (∀ k, nextId + res.2.length ≤ k → natCountIn k (termSuccs res.1.term) = 0) ∧
    -- (4) Indices in `[origBound, nextId)` occur 0 times in `res.1`
    (∀ k, origBound ≤ k → k < nextId → natCountIn k (termSuccs res.1.term) = 0) ∧
    -- (5) Predecessor-count conservation for all `k < origBound`
    (∀ k, k < origBound → natCountIn k (termSuccs res.1.term) + predCount res.2 k =
      natCountIn k (termSuccs blk.term)) ∧
    -- (6) Under `CriticalCallEdges`, every guarded target of `res.1` is either fresh in
    --     `[nextId, nextId + res.2.length)` or has `predCount origCfg ≤ 1`
    (mode = .criticalCallEdges →
      match res.1.term with
      | .call _ _ _ (some d') uw =>
        generatesInvoke uw = true →
          (nextId ≤ d' ∧ d' < nextId + res.2.length) ∨ predCount origCfg d' ≤ 1
      | .inlineAsm true hasLabels targets' uw =>
        (hasLabels = true ∨ generatesInvoke uw = true) →
          ∀ t', t' ∈ targets' →
            (nextId ≤ t' ∧ t' < nextId + res.2.length) ∨ predCount origCfg t' ≤ 1
      | _ => True) ∧
    -- (7) `stmts` and `isCleanup` are preserved unchanged
    (res.1.stmts = blk.stmts ∧ res.1.isCleanup = blk.isCleanup) := by
  have hBlkBoundNext : ∀ s, s ∈ termSuccs blk.term → s < nextId :=
    fun s hs => Nat.lt_of_lt_of_le (hBlkBound s hs) hOrigLe
  cases blk with
  | mk stmts term ic =>
    cases term with
    | goto t =>
      have ht : t < origBound := hBlkBound t (List.Mem.head _)
      refine ⟨fun _ h => (by cases h), ?_, ?_, ?_, fun _ _ => Nat.add_zero _, fun _ => trivial, ⟨rfl, rfl⟩⟩
      · intro k hle hlt
        simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hlt
        exact False.elim (Nat.not_lt_of_ge hle hlt)
      · intro k hge
        simp only [rewriteBlockCallGuards, termSuccs, List.length_nil, Nat.add_zero] at hge ⊢
        have hBeq : (t == k) = false :=
          natBeq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le ht (Nat.le_trans hOrigLe hge)))
        simp [natCountIn, hBeq]
      · intro k hge _
        simp only [rewriteBlockCallGuards, termSuccs]
        have hBeq : (t == k) = false := natBeq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le ht hge))
        simp [natCountIn, hBeq]
    | switchInt c t f =>
      have ht : t < origBound := hBlkBound t (List.Mem.head _)
      have hf : f < origBound := hBlkBound f (List.Mem.tail t (List.Mem.head _))
      refine ⟨fun _ h => (by cases h), ?_, ?_, ?_, fun _ _ => Nat.add_zero _, fun _ => trivial, ⟨rfl, rfl⟩⟩
      · intro k hle hlt
        simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hlt
        exact False.elim (Nat.not_lt_of_ge hle hlt)
      · intro k hge
        simp only [rewriteBlockCallGuards, termSuccs, List.length_nil, Nat.add_zero] at hge ⊢
        have hBt : (t == k) = false :=
          natBeq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le ht (Nat.le_trans hOrigLe hge)))
        have hBf : (f == k) = false :=
          natBeq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hf (Nat.le_trans hOrigLe hge)))
        simp [natCountIn, hBt, hBf]
      · intro k hge _
        simp only [rewriteBlockCallGuards, termSuccs]
        have hBt : (t == k) = false := natBeq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le ht hge))
        have hBf : (f == k) = false := natBeq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hf hge))
        simp [natCountIn, hBt, hBf]
    | drop tr t uw =>
      refine ⟨fun _ h => (by cases h), ?_, ?_, ?_, fun _ _ => Nat.add_zero _, fun _ => trivial, ⟨rfl, rfl⟩⟩
      · intro k hle hlt
        simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hlt
        exact False.elim (Nat.not_lt_of_ge hle hlt)
      · intro k hge
        simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hge ⊢
        apply natCountIn_zero_of_forall_ne
        intro s hs
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBoundNext s hs) hge)
      · intro k hge _
        simp only [rewriteBlockCallGuards]
        apply natCountIn_zero_of_forall_ne
        intro s hs
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBound s hs) hge)
    | unwindResume =>
      refine ⟨fun _ h => (by cases h), ?_, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => trivial, ⟨rfl, rfl⟩⟩
      intro k hle hlt
      simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hlt
      exact False.elim (Nat.not_lt_of_ge hle hlt)
    | ret l =>
      refine ⟨fun _ h => (by cases h), ?_, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => trivial, ⟨rfl, rfl⟩⟩
      intro k hle hlt
      simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hlt
      exact False.elim (Nat.not_lt_of_ge hle hlt)
    | call rl rv mp target uw =>
      cases target with
      | none =>
        refine ⟨fun _ h => (by cases h), ?_, ?_, ?_, fun _ _ => Nat.add_zero _, fun _ => trivial, ⟨rfl, rfl⟩⟩
        · intro k hle hlt
          simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hlt
          exact False.elim (Nat.not_lt_of_ge hle hlt)
        · intro k hge
          simp only [rewriteBlockCallGuards, List.length_nil, Nat.add_zero] at hge ⊢
          apply natCountIn_zero_of_forall_ne
          intro s hs
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBoundNext s hs) hge)
        · intro k hge _
          simp only [rewriteBlockCallGuards]
          apply natCountIn_zero_of_forall_ne
          intro s hs
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBound s hs) hge)
      | some d =>
        have hdLt : d < origBound := hBlkBound d (List.Mem.head _)
        have hUwLt : ∀ u, u ∈ unwindSuccs uw → u < origBound :=
          fun u hu => hBlkBound u (List.Mem.tail d hu)
        simp only [rewriteBlockCallGuards]
        cases hCond : (decide (1 < predCount origCfg d) && (generatesInvoke uw || isAllCallEdges mode)) with
        | true =>
          simp only [↓reduceIte]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨trivial, trivial⟩⟩
          · intro b hb
            cases hb with
            | head => exact ⟨d, hdLt, ic, rfl⟩
            | tail _ hm => cases hm
          · intro k hle hlt
            simp only [List.length_singleton] at hlt
            have hkEq : k = nextId := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hle
            subst hkEq
            have hUwZero : natCountIn k (unwindSuccs uw) = 0 :=
              natCountIn_zero_of_forall_ne k (unwindSuccs uw)
                (fun u hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le (hUwLt u hu) hOrigLe))
            simp only [termSuccs, natCountIn, natBeq_self, ↓reduceIte, hUwZero]
          · intro k hge
            simp only [List.length_singleton] at hge
            have hNe : nextId ≠ k := Nat.ne_of_lt hge
            have hBeq : (nextId == k) = false := natBeq_false_of_ne hNe
            have hUwZero : natCountIn k (unwindSuccs uw) = 0 :=
              natCountIn_zero_of_forall_ne k (unwindSuccs uw)
                (fun u hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hUwLt u hu) hOrigLe)
                  (Nat.le_trans (Nat.le_succ nextId) hge)))
            simp [termSuccs, natCountIn, hBeq, hUwZero]
          · intro k hge hlt
            have hNe : nextId ≠ k := Nat.ne_of_gt hlt
            have hBeq : (nextId == k) = false := natBeq_false_of_ne hNe
            have hUwZero : natCountIn k (unwindSuccs uw) = 0 :=
              natCountIn_zero_of_forall_ne k (unwindSuccs uw)
                (fun u hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le (hUwLt u hu) hge))
            simp [termSuccs, natCountIn, hBeq, hUwZero]
          · intro k hk
            have hNe : nextId ≠ k := Nat.ne_of_gt (Nat.lt_of_lt_of_le hk hOrigLe)
            have hBeq : (nextId == k) = false := natBeq_false_of_ne hNe
            simp only [termSuccs, natCountIn, hBeq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, predCount, Nat.add_zero]
            exact Nat.add_comm _ _
          · intro _ _
            left
            exact ⟨Nat.le_refl nextId, Nat.lt_succ_self nextId⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨fun _ h => (by cases h), ?_, ?_, ?_, fun _ _ => Nat.add_zero _, ?_, ⟨trivial, trivial⟩⟩
          · intro k hle hlt
            simp only [List.length_nil, Nat.add_zero] at hlt
            exact False.elim (Nat.not_lt_of_ge hle hlt)
          · intro k hge
            simp only [List.length_nil, Nat.add_zero] at hge
            apply natCountIn_zero_of_forall_ne
            intro s hs
            exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBoundNext s hs) hge)
          · intro k hge _
            apply natCountIn_zero_of_forall_ne
            intro s hs
            exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBound s hs) hge)
          · intro hMode hGen
            right
            rw [hMode, hGen] at hCond
            simp only [isAllCallEdges, Bool.true_or, Bool.and_true] at hCond
            exact nat_le_of_not_lt (of_decide_eq_false hCond)
    | inlineAsm hasOutputs hasLabels targets uw =>
      have hTsOrig : ∀ t, t ∈ targets → t < origBound :=
        fun t ht => hBlkBound t (List.mem_append_left (unwindSuccs uw) ht)
      have hTsNext : ∀ t, t ∈ targets → t < nextId :=
        fun t ht => Nat.lt_of_lt_of_le (hTsOrig t ht) hOrigLe
      have hUwOrig : ∀ u, u ∈ unwindSuccs uw → u < origBound :=
        fun u hu => hBlkBound u (List.mem_append_right targets hu)
      simp only [rewriteBlockCallGuards]
      cases hCond : (isCriticalCallEdges mode && hasOutputs && (hasLabels || generatesInvoke uw)) with
      | true =>
        simp only [↓reduceIte]
        have hSp := splitAsmTargets_props origCfg ic targets nextId hTsNext
        rcases hSp with ⟨hSp1, hSp2, hSp3, hSp4, hSp5, _, _⟩
        let sp := splitAsmTargets origCfg ic targets nextId
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨trivial, trivial⟩⟩
        · intro b hb
          rcases hSp1 b hb with ⟨t0, ht0, hEq⟩
          exact ⟨t0, hTsOrig t0 ht0, ic, hEq⟩
        · intro k hle hlt
          simp only [termSuccs, natCountIn_append]
          have hUwZero : natCountIn k (unwindSuccs uw) = 0 :=
            natCountIn_zero_of_forall_ne k (unwindSuccs uw)
              (fun u hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hUwOrig u hu) hOrigLe) hle))
          rw [hSp2 k hle hlt, hUwZero]
        · intro k hge
          simp only [termSuccs, natCountIn_append]
          have hUwZero : natCountIn k (unwindSuccs uw) = 0 :=
            natCountIn_zero_of_forall_ne k (unwindSuccs uw)
              (fun u hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hUwOrig u hu) hOrigLe)
                (Nat.le_trans (Nat.le_add_right _ _) hge)))
          rw [hSp3 k hge, hUwZero]
        · intro k hge hlt
          simp only [termSuccs, natCountIn_append]
          have hSpZero : natCountIn k sp.1 = 0 := by
            apply natCountIn_zero_of_forall_ne
            intro t' ht'
            cases hSp4 t' ht' with
            | inl hFresh => exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt hFresh.1)
            | inr hOld => exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hTsOrig t' hOld.1) hge)
          have hUwZero : natCountIn k (unwindSuccs uw) = 0 :=
            natCountIn_zero_of_forall_ne k (unwindSuccs uw)
              (fun u hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le (hUwOrig u hu) hge))
          rw [hSpZero, hUwZero]
        · intro k hk
          simp only [termSuccs, natCountIn_append]
          rw [Nat.add_right_comm, hSp5 k (Nat.lt_of_lt_of_le hk hOrigLe)]
        · intro _
          cases hasOutputs with
          | false => trivial
          | true =>
            intro _ t' ht'
            cases hSp4 t' ht' with
            | inl hFresh => exact Or.inl hFresh
            | inr hOld => exact Or.inr hOld.2
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun _ h => (by cases h), ?_, ?_, ?_, fun _ _ => Nat.add_zero _, ?_, ⟨trivial, trivial⟩⟩
        · intro k hle hlt
          simp only [List.length_nil, Nat.add_zero] at hlt
          exact False.elim (Nat.not_lt_of_ge hle hlt)
        · intro k hge
          simp only [List.length_nil, Nat.add_zero] at hge
          apply natCountIn_zero_of_forall_ne
          intro s hs
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBoundNext s hs) hge)
        · intro k hge _
          apply natCountIn_zero_of_forall_ne
          intro s hs
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hBlkBound s hs) hge)
        · intro hMode
          cases hasOutputs with
          | false => trivial
          | true =>
            intro hDisj
            rw [hMode] at hCond
            simp only [isCriticalCallEdges, Bool.and_self, Bool.true_and] at hCond
            cases hDisj with
            | inl hl => rw [hl] at hCond; cases hCond
            | inr hg => rw [hg] at hCond; simp at hCond

/-- Multi-block induction lifting all predecessor-count and critical-edge invariants
    across `rewriteBlocksCallGuards`. -/
theorem rewriteBlocksCallGuards_props (mode : CallGuardMode) (origCfg : CgCfg) :
    ∀ (blks : CgCfg) (origBound nextId : Nat),
      origBound ≤ nextId →
      SuccsBounded blks origBound →
      let res := rewriteBlocksCallGuards mode origCfg blks nextId
      TrampolinesBounded res.2 origBound ∧
      (∀ k, nextId ≤ k → k < nextId + res.2.length → predCount res.1 k = 1) ∧
      (∀ k, nextId + res.2.length ≤ k → predCount res.1 k = 0) ∧
      (∀ k, origBound ≤ k → k < nextId → predCount res.1 k = 0) ∧
      (∀ k, k < origBound → predCount res.1 k + predCount res.2 k = predCount blks k) ∧
      (mode = .criticalCallEdges →
        ∀ blk', blk' ∈ res.1 →
          match blk'.term with
          | .call _ _ _ (some d') uw =>
            generatesInvoke uw = true →
              (nextId ≤ d' ∧ d' < nextId + res.2.length) ∨ predCount origCfg d' ≤ 1
          | .inlineAsm true hasLabels targets' uw =>
            (hasLabels = true ∨ generatesInvoke uw = true) →
              ∀ t', t' ∈ targets' →
                (nextId ≤ t' ∧ t' < nextId + res.2.length) ∨ predCount origCfg t' ≤ 1
          | _ => True) ∧
      (res.1.length = blks.length)
  | [], _, nextId, _, _ => by
    refine ⟨fun _ h => (by cases h), ?_, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ h => (by cases h), rfl⟩
    intro k hle hlt
    simp only [rewriteBlocksCallGuards, List.length_nil, Nat.add_zero] at hlt
    exact False.elim (Nat.not_lt_of_ge hle hlt)
  | blk :: rest, origBound, nextId, hOrigLe, hBound => by
    have hBlkBound : ∀ s, s ∈ termSuccs blk.term → s < origBound :=
      fun s hs => hBound blk (List.Mem.head _) s hs
    have hOne := rewriteBlockCallGuards_props mode origCfg blk origBound nextId hOrigLe hBlkBound
    rcases hOne with ⟨hT1, hFresh1, hZero1, hMid1, hCons1, hGuard1, _⟩
    let r1 := rewriteBlockCallGuards mode origCfg blk nextId
    have hRestBound : SuccsBounded rest origBound :=
      fun b hb s hs => hBound b (List.Mem.tail blk hb) s hs
    have hOrigLe2 : origBound ≤ nextId + r1.2.length :=
      Nat.le_trans hOrigLe (Nat.le_add_right _ _)
    have ih := rewriteBlocksCallGuards_props mode origCfg rest origBound (nextId + r1.2.length) hOrigLe2 hRestBound
    rcases ih with ⟨hT2, hFresh2, hZero2, hMid2, hCons2, hGuard2, hLen2⟩
    let r2 := rewriteBlocksCallGuards mode origCfg rest (nextId + r1.2.length)
    simp only [rewriteBlocksCallGuards]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (1) TrampolinesBounded
      intro b hb
      cases List.mem_append.mp hb with
      | inl h1 => exact hT1 b h1
      | inr h2 => exact hT2 b h2
    · -- (2) Fresh indices in `[nextId, nextId + (r1.2 ++ r2.2).length)` have predCount = 1
      intro k hle hlt
      simp only [List.length_append, ← Nat.add_assoc] at hlt
      simp only [predCount]
      cases hSplit : decide (k < nextId + r1.2.length) with
      | true =>
        have hLt1 : k < nextId + r1.2.length := of_decide_eq_true hSplit
        have hC1 : natCountIn k (termSuccs r1.1.term) = 1 := hFresh1 k hle hLt1
        have hC2 : predCount r2.1 k = 0 := hMid2 k (Nat.le_trans hOrigLe hle) hLt1
        rw [hC1, hC2]
      | false =>
        have hGe1 : nextId + r1.2.length ≤ k := nat_le_of_not_lt (of_decide_eq_false hSplit)
        have hC1 : natCountIn k (termSuccs r1.1.term) = 0 := hZero1 k hGe1
        have hC2 : predCount r2.1 k = 1 := hFresh2 k hGe1 hlt
        rw [hC1, hC2]
    · -- (3) Indices `≥ nextId + (r1.2 ++ r2.2).length` have predCount = 0
      intro k hge
      simp only [List.length_append, ← Nat.add_assoc] at hge
      simp only [predCount]
      have hGe1 : nextId + r1.2.length ≤ k := Nat.le_trans (Nat.le_add_right _ _) hge
      rw [hZero1 k hGe1, hZero2 k hge]
    · -- (4) Indices in `[origBound, nextId)` have predCount = 0
      intro k hge hlt
      simp only [predCount]
      have hLt2 : k < nextId + r1.2.length := Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
      rw [hMid1 k hge hlt, hMid2 k hge hLt2]
    · -- (5) Predecessor-count conservation for `k < origBound`
      intro k hk
      simp only [predCount, predCount_append]
      have h1 := hCons1 k hk
      have h2 := hCons2 k hk
      rw [← h1, ← h2]
      rw [Nat.add_assoc (natCountIn k (termSuccs r1.1.term)),
          Nat.add_left_comm (predCount r2.1 k) (predCount r1.2 k),
          ← Nat.add_assoc]
    · -- (6) Critical-edge guard invariant for `r1.1 :: r2.1`
      intro hMode blk' hMem
      cases hMem with
      | head =>
        have hg1 := hGuard1 hMode
        cases hTm : r1.1.term with
        | call rl rv mp tgt uw =>
          cases tgt with
          | none => trivial
          | some d' =>
            intro hGen
            rw [hTm] at hg1
            cases hg1 hGen with
            | inl hFresh =>
              left
              exact ⟨hFresh.1, by simp only [List.length_append, ← Nat.add_assoc]; exact Nat.lt_of_lt_of_le hFresh.2 (Nat.le_add_right _ _)⟩
            | inr hLe1 => right; exact hLe1
        | inlineAsm ho hl ts' uw =>
          cases ho with
          | false => trivial
          | true =>
            intro hDisj t' ht'
            rw [hTm] at hg1
            cases hg1 hDisj t' ht' with
            | inl hFresh =>
              left
              exact ⟨hFresh.1, by simp only [List.length_append, ← Nat.add_assoc]; exact Nat.lt_of_lt_of_le hFresh.2 (Nat.le_add_right _ _)⟩
            | inr hLe1 => right; exact hLe1
        | goto _ => trivial
        | switchInt _ _ _ => trivial
        | drop _ _ _ => trivial
        | unwindResume => trivial
        | ret _ => trivial
      | tail _ hMemRest =>
        have hg2 := hGuard2 hMode blk' hMemRest
        cases hTm : blk'.term with
        | call rl rv mp tgt uw =>
          cases tgt with
          | none => trivial
          | some d' =>
            intro hGen
            rw [hTm] at hg2
            cases hg2 hGen with
            | inl hFresh =>
              left
              refine ⟨Nat.le_trans (Nat.le_add_right _ _) hFresh.1, ?_⟩
              simp only [List.length_append, ← Nat.add_assoc]
              exact hFresh.2
            | inr hLe1 => right; exact hLe1
        | inlineAsm ho hl ts' uw =>
          cases ho with
          | false => trivial
          | true =>
            intro hDisj t' ht'
            rw [hTm] at hg2
            cases hg2 hDisj t' ht' with
            | inl hFresh =>
              left
              refine ⟨Nat.le_trans (Nat.le_add_right _ _) hFresh.1, ?_⟩
              simp only [List.length_append, ← Nat.add_assoc]
              exact hFresh.2
            | inr hLe1 => right; exact hLe1
        | goto _ => trivial
        | switchInt _ _ _ => trivial
        | drop _ _ _ => trivial
        | unwindResume => trivial
        | ret _ => trivial
    · -- (7) Length
      simp only [List.length_cons]
      exact congrArg Nat.succ hLen2

/-- **Structural Critical-Edge Elimination Theorem (`addCallGuards_no_invoke_critical_edges`):**
    For any well-formed CFG whose successors lie in `[0, cfg.length)`:
    1. Every original block index `k < cfg.length` preserves its exact predecessor count.
    2. Every freshly inserted trampoline block `k ∈ [cfg.length, cfg'.length)` has
       exact predecessor count `= 1`.
    3. ZERO critical `Call` invoke-return edges and ZERO critical `InlineAsm`
       output-target edges remain in `addCallGuards .criticalCallEdges cfg`! -/
theorem addCallGuards_no_invoke_critical_edges (cfg : CgCfg)
    (hBound : SuccsBounded cfg cfg.length) :
    let cfg' := addCallGuards .criticalCallEdges cfg
    (∀ k, k < cfg.length → predCount cfg' k = predCount cfg k) ∧
    (∀ k, cfg.length ≤ k → k < cfg'.length → predCount cfg' k = 1) ∧
    CfgNoCriticalEdges cfg' := by
  have hMain := rewriteBlocksCallGuards_props .criticalCallEdges cfg cfg cfg.length cfg.length (Nat.le_refl _) hBound
  rcases hMain with ⟨hTramps, hFresh, _, _, hCons, hGuard, hLen⟩
  let res := rewriteBlocksCallGuards .criticalCallEdges cfg cfg cfg.length
  have hCfg'Eq : addCallGuards .criticalCallEdges cfg = res.1 ++ res.2 := rfl
  have hLenCfg' : (res.1 ++ res.2).length = cfg.length + res.2.length := by
    rw [List.length_append, hLen]
  refine ⟨?_, ?_, ?_⟩
  · -- (1) Old indices preserve predCount
    intro k hk
    rw [hCfg'Eq, predCount_append]
    exact hCons k hk
  · -- (2) Fresh trampoline indices have predCount = 1
    intro k hle hlt
    rw [hCfg'Eq, hLenCfg'] at hlt
    rw [hCfg'Eq, predCount_append, hFresh k hle hlt,
        predCount_trampolines_zero_of_ge res.2 cfg.length k hTramps hle]
  · -- (3) CfgNoCriticalEdges
    intro blk' hMem
    rw [hCfg'Eq] at hMem
    cases List.mem_append.mp hMem with
    | inl hInRew =>
      have hg := hGuard rfl blk' hInRew
      unfold BlockNoCriticalEdges
      cases hTm : blk'.term with
      | call rl rv mp tgt uw =>
        cases tgt with
        | none => trivial
        | some d' =>
          intro hGen
          rw [hTm] at hg
          cases hg hGen with
          | inl hF =>
            rw [hCfg'Eq, predCount_append, hFresh d' hF.1 hF.2,
                predCount_trampolines_zero_of_ge res.2 cfg.length d' hTramps hF.1]
            exact Nat.le_refl 1
          | inr hLe1 =>
            cases hLt : decide (d' < cfg.length) with
            | true =>
              rw [hCfg'Eq, predCount_append, hCons d' (of_decide_eq_true hLt)]
              exact hLe1
            | false =>
              -- Unsplit target `d'` came from `origCfg`, so `d' < cfg.length`;
              -- if `d' ≥ cfg.length` and not in fresh range, predCount = 0 ≤ 1 anyway!
              have hGe : cfg.length ≤ d' := nat_le_of_not_lt (of_decide_eq_false hLt)
              cases hInFresh : decide (d' < cfg.length + res.2.length) with
              | true =>
                rw [hCfg'Eq, predCount_append, hFresh d' hGe (of_decide_eq_true hInFresh),
                    predCount_trampolines_zero_of_ge res.2 cfg.length d' hTramps hGe]
                exact Nat.le_refl 1
              | false =>
                have hGeAll : cfg.length + res.2.length ≤ d' := nat_le_of_not_lt (of_decide_eq_false hInFresh)
                have hZ := (rewriteBlocksCallGuards_props .criticalCallEdges cfg cfg cfg.length cfg.length (Nat.le_refl _) hBound).2.2.1 d' hGeAll
                rw [hCfg'Eq, predCount_append, hZ,
                    predCount_trampolines_zero_of_ge res.2 cfg.length d' hTramps hGe]
                exact Nat.zero_le 1
      | inlineAsm ho hl ts' uw =>
        cases ho with
        | false => trivial
        | true =>
          intro hDisj t' ht'
          rw [hTm] at hg
          cases hg hDisj t' ht' with
          | inl hF =>
            rw [hCfg'Eq, predCount_append, hFresh t' hF.1 hF.2,
                predCount_trampolines_zero_of_ge res.2 cfg.length t' hTramps hF.1]
            exact Nat.le_refl 1
          | inr hLe1 =>
            cases hLt : decide (t' < cfg.length) with
            | true =>
              rw [hCfg'Eq, predCount_append, hCons t' (of_decide_eq_true hLt)]
              exact hLe1
            | false =>
              have hGe : cfg.length ≤ t' := nat_le_of_not_lt (of_decide_eq_false hLt)
              cases hInFresh : decide (t' < cfg.length + res.2.length) with
              | true =>
                rw [hCfg'Eq, predCount_append, hFresh t' hGe (of_decide_eq_true hInFresh),
                    predCount_trampolines_zero_of_ge res.2 cfg.length t' hTramps hGe]
                exact Nat.le_refl 1
              | false =>
                have hGeAll : cfg.length + res.2.length ≤ t' := nat_le_of_not_lt (of_decide_eq_false hInFresh)
                have hZ := (rewriteBlocksCallGuards_props .criticalCallEdges cfg cfg cfg.length cfg.length (Nat.le_refl _) hBound).2.2.1 t' hGeAll
                rw [hCfg'Eq, predCount_append, hZ,
                    predCount_trampolines_zero_of_ge res.2 cfg.length t' hTramps hGe]
                exact Nat.zero_le 1
      | goto _ => trivial
      | switchInt _ _ _ => trivial
      | drop _ _ _ => trivial
      | unwindResume => trivial
      | ret _ => trivial
    | inr hInTramps =>
      rcases hTramps blk' hInTramps with ⟨t, _, ic, hEq⟩
      rw [hEq]
      trivial

/-! #### Bidirectional Operational Semantics Preservation (Stuttering Equivalence) -/

/-- Big-step operational semantics of `CgCfg`, capturing normal execution, call
    return + unwind dispatch, inline-asm multi-target dispatch, drop, and resume. -/
inductive EvalCfg (cfg : CgCfg) : Nat → CgState → CgOutcome → Prop where
  | gotoStep (bb t : Nat) (blk : CgBlock) (st : CgState) (out : CgOutcome) :
      listGet? cfg bb = some blk →
      blk.term = .goto t →
      EvalCfg cfg t (stepCgStmts st blk.stmts) out →
      EvalCfg cfg bb st out
  | switchTrue (bb cond t f : Nat) (blk : CgBlock) (st : CgState) (out : CgOutcome) :
      listGet? cfg bb = some blk →
      blk.term = .switchInt cond t f →
      listGetD (stepCgStmts st blk.stmts).locals cond 0 ≠ 0 →
      EvalCfg cfg t (stepCgStmts st blk.stmts) out →
      EvalCfg cfg bb st out
  | switchFalse (bb cond t f : Nat) (blk : CgBlock) (st : CgState) (out : CgOutcome) :
      listGet? cfg bb = some blk →
      blk.term = .switchInt cond t f →
      listGetD (stepCgStmts st blk.stmts).locals cond 0 = 0 →
      EvalCfg cfg f (stepCgStmts st blk.stmts) out →
      EvalCfg cfg bb st out
  | callRet (bb rl rv d : Nat) (uw : UnwindAction) (blk : CgBlock) (st : CgState) (out : CgOutcome) :
      listGet? cfg bb = some blk →
      blk.term = .call rl rv false (some d) uw →
      EvalCfg cfg d { stepCgStmts st blk.stmts with locals := listSet (stepCgStmts st blk.stmts).locals rl rv } out →
      EvalCfg cfg bb st out
  | callUnwindCleanup (bb rl rv ubb : Nat) (tgt : Option Nat) (blk : CgBlock) (st : CgState) (out : CgOutcome) :
      listGet? cfg bb = some blk →
      blk.term = .call rl rv true tgt (.cleanup ubb) →
      EvalCfg cfg ubb (stepCgStmts st blk.stmts) out →
      EvalCfg cfg bb st out
  | callUnwindContinue (bb rl rv : Nat) (tgt : Option Nat) (blk : CgBlock) (st : CgState) :
      listGet? cfg bb = some blk →
      blk.term = .call rl rv true tgt .continue_ →
      EvalCfg cfg bb st (.unwound (stepCgStmts st blk.stmts).heap)
  | callUnwindTerminate (bb rl rv : Nat) (tgt : Option Nat) (blk : CgBlock) (st : CgState) :
      listGet? cfg bb = some blk →
      blk.term = .call rl rv true tgt .terminate →
      EvalCfg cfg bb st (.aborted (stepCgStmts st blk.stmts).heap)
  | asmTarget (bb idx t : Nat) (ho hl : Bool) (ts : List Nat) (uw : UnwindAction)
      (blk : CgBlock) (st : CgState) (out : CgOutcome) :
      listGet? cfg bb = some blk →
      blk.term = .inlineAsm ho hl ts uw →
      listGet? ts idx = some t →
      EvalCfg cfg t (stepCgStmts st blk.stmts) out →
      EvalCfg cfg bb st out
  | dropNormal (bb t : Nat) (tr : Bool) (uw : UnwindAction) (blk : CgBlock) (st : CgState) (out : CgOutcome) :
      listGet? cfg bb = some blk →
      blk.term = .drop tr t uw →
      EvalCfg cfg t (stepCgStmts st blk.stmts) out →
      EvalCfg cfg bb st out
  | unwindResumeStep (bb : Nat) (blk : CgBlock) (st : CgState) :
      listGet? cfg bb = some blk →
      blk.term = .unwindResume →
      EvalCfg cfg bb st (.unwound (stepCgStmts st blk.stmts).heap)
  | retStep (bb l : Nat) (blk : CgBlock) (st : CgState) :
      listGet? cfg bb = some blk →
      blk.term = .ret l →
      EvalCfg cfg bb st (.ret (listGetD (stepCgStmts st blk.stmts).locals l 0) (stepCgStmts st blk.stmts).heap)

/-- Relation describing how one original block `blk` relates to its rewritten block `blk'`
    inside `cfg' = rewritten ++ tramps`: every split target points to an empty trampoline
    block in `cfg'` whose sole instruction is `.goto originalTarget`. -/
noncomputable def TargetMatches (cfg' : CgCfg) (ic : Bool) (t t' : Nat) : Prop :=
  t' = t ∨ listGet? cfg' t' = some { stmts := [], term := .goto t, isCleanup := ic }

noncomputable def BlockMatches (cfg' : CgCfg) (blk blk' : CgBlock) : Prop :=
  blk'.stmts = blk.stmts ∧ blk'.isCleanup = blk.isCleanup ∧
  match blk.term, blk'.term with
  | .call rl rv mp (some d) uw, .call rl' rv' mp' (some d') uw' =>
    rl' = rl ∧ rv' = rv ∧ mp' = mp ∧ uw' = uw ∧ TargetMatches cfg' blk.isCleanup d d'
  | .inlineAsm ho hl ts uw, .inlineAsm ho' hl' ts' uw' =>
    ho' = ho ∧ hl' = hl ∧ uw' = uw ∧ ts'.length = ts.length ∧
    ∀ i, i < ts.length → ∃ t t', listGet? ts i = some t ∧ listGet? ts' i = some t' ∧
      TargetMatches cfg' blk.isCleanup t t'
  | tm, tm' => tm' = tm

/-- Clean direct lookup theorem for `addCallGuards mode cfg`: every original block `bb`
    with `listGet? cfg bb = some blk` maps to `listGet? cfg' bb = some blk'` satisfying
    `BlockMatches cfg' blk blk'`. -/
theorem rewriteBlocks_get_matches (mode : CallGuardMode) (origCfg : CgCfg) :
    ∀ (blks : CgCfg) (rewAll : CgCfg) (trampPrefix trampSuffix : CgCfg) (nextId : Nat),
      rewAll.length + trampPrefix.length = nextId →
      SuccsBounded blks nextId →
      let res := rewriteBlocksCallGuards mode origCfg blks nextId
      let cfg' := rewAll ++ (trampPrefix ++ res.2 ++ trampSuffix)
      ∀ (i : Nat) (blk : CgBlock),
        listGet? blks i = some blk →
        ∃ blk', listGet? res.1 i = some blk' ∧ BlockMatches cfg' blk blk'
  | [], _, _, _, _, _, _, _, _, h => by cases h
  | blk :: rest, rewAll, trampPrefix, trampSuffix, nextId, hLenEq, hBound, i, blk0, hGet => by
    have hBlkBound : ∀ s, s ∈ termSuccs blk.term → s < nextId :=
      fun s hs => hBound blk (List.Mem.head _) s hs
    let r1 := rewriteBlockCallGuards mode origCfg blk nextId
    let r2 := rewriteBlocksCallGuards mode origCfg rest (nextId + r1.2.length)
    cases i with
    | zero =>
      simp only [listGet?, Option.some.injEq] at hGet
      subst hGet
      refine ⟨r1.1, rfl, ?_⟩
      -- Prove BlockMatches for `r1.1` inside `rewAll ++ (trampPrefix ++ (r1.2 ++ r2.2) ++ trampSuffix)`
      let cfg' := rewAll ++ (trampPrefix ++ (r1.2 ++ r2.2) ++ trampSuffix)
      have hTrampAt : ∀ (k : Nat) (tb : CgBlock),
          listGet? r1.2 k = some tb → listGet? cfg' (nextId + k) = some tb := by
        intro k tb hTb
        have hEq1 : cfg' = (rewAll ++ trampPrefix) ++ (r1.2 ++ (r2.2 ++ trampSuffix)) := by
          simp only [cfg', List.append_assoc]
        rw [hEq1, ← hLenEq, ← List.length_append, listGet?_append_right]
        have hkLt : k < r1.2.length := listGet?_some_lt r1.2 k tb hTb
        rw [listGet?_append_left r1.2 (r2.2 ++ trampSuffix) k hkLt, hTb]
      cases blk with
      | mk stmts term ic =>
        cases term with
        | goto _ => exact ⟨rfl, rfl, rfl⟩
        | switchInt _ _ _ => exact ⟨rfl, rfl, rfl⟩
        | drop _ _ _ => exact ⟨rfl, rfl, rfl⟩
        | unwindResume => exact ⟨rfl, rfl, rfl⟩
        | ret _ => exact ⟨rfl, rfl, rfl⟩
        | call rl rv mp tgt uw =>
          cases tgt with
          | none => exact ⟨rfl, rfl, rfl⟩
          | some d =>
            cases hCond : (decide (1 < predCount origCfg d) && (generatesInvoke uw || isAllCallEdges mode)) with
            | false =>
              simp only [r1, rewriteBlockCallGuards, hCond, Bool.false_eq_true, ↓reduceIte]
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
            | true =>
              have hTr0 : listGet? r1.2 0 = some { stmts := [], term := .goto d, isCleanup := ic } := by
                simp only [r1, rewriteBlockCallGuards, hCond, ↓reduceIte, listGet?]
              have h0 := hTrampAt 0 { stmts := [], term := .goto d, isCleanup := ic } hTr0
              rw [Nat.add_zero] at h0
              simp only [r1, rewriteBlockCallGuards, hCond, ↓reduceIte]
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr h0⟩
        | inlineAsm ho hl ts uw =>
          cases hCond : (isCriticalCallEdges mode && ho && (hl || generatesInvoke uw)) with
          | false =>
            simp only [r1, rewriteBlockCallGuards, hCond, Bool.false_eq_true, ↓reduceIte]
            refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
            intro j hj
            rcases listGet?_some_of_lt ts j hj with ⟨t, hG⟩
            exact ⟨t, t, hG, hG, Or.inl rfl⟩
          | true =>
            have hTsLt : ∀ t, t ∈ ts → t < nextId :=
              fun t ht => hBlkBound t (List.mem_append_left (unwindSuccs uw) ht)
            have hSp := splitAsmTargets_props origCfg ic ts nextId hTsLt
            have hR1Snd : r1.2 = (splitAsmTargets origCfg ic ts nextId).2 := by
              simp only [r1, rewriteBlockCallGuards, hCond, ↓reduceIte]
            simp only [r1, rewriteBlockCallGuards, hCond, ↓reduceIte]
            refine ⟨rfl, rfl, rfl, rfl, rfl, hSp.2.2.2.2.2.2, ?_⟩
            intro j hj
            rcases hSp.2.2.2.2.2.1 j hj with ⟨t, t', hGt, hGt', hCase⟩
            refine ⟨t, t', hGt, hGt', ?_⟩
            cases hCase with
            | inl hEq => exact Or.inl hEq
            | inr hTr =>
              rcases hTr with ⟨_, k, hEqK, hTrGet⟩
              right
              rw [hEqK]
              have hTrR1 : listGet? r1.2 k = some { stmts := [], term := .goto t, isCleanup := ic } := by
                rw [hR1Snd]; exact hTrGet
              exact hTrampAt k { stmts := [], term := .goto t, isCleanup := ic } hTrR1
    | succ j =>
      have hRestBound : SuccsBounded rest (nextId + r1.2.length) :=
        fun b hb s hs => Nat.lt_of_lt_of_le (hBound b (List.Mem.tail blk hb) s hs) (Nat.le_add_right _ _)
      have hLenEq2 : rewAll.length + (trampPrefix ++ r1.2).length = nextId + r1.2.length := by
        rw [List.length_append, ← Nat.add_assoc, hLenEq]
      have ih := rewriteBlocks_get_matches mode origCfg rest rewAll (trampPrefix ++ r1.2) trampSuffix
        (nextId + r1.2.length) hLenEq2 hRestBound j blk0 hGet
      rcases ih with ⟨blk', hResGet, hMatch⟩
      have hCfgEq :
          rewAll ++ (trampPrefix ++ r1.2 ++ r2.2 ++ trampSuffix) =
          rewAll ++ (trampPrefix ++ (r1.2 ++ r2.2) ++ trampSuffix) := by
        simp only [List.append_assoc]
      rw [hCfgEq] at hMatch
      exact ⟨blk', hResGet, hMatch⟩

theorem addCallGuards_lookup_matches (mode : CallGuardMode) (cfg : CgCfg)
    (hBound : SuccsBounded cfg cfg.length) (bb : Nat) (blk : CgBlock)
    (hGet : listGet? cfg bb = some blk) :
    ∃ blk', listGet? (addCallGuards mode cfg) bb = some blk' ∧
      BlockMatches (addCallGuards mode cfg) blk blk' := by
  let res := rewriteBlocksCallGuards mode cfg cfg cfg.length
  have hLenRew : res.1.length = cfg.length :=
    (rewriteBlocksCallGuards_props mode cfg cfg cfg.length cfg.length (Nat.le_refl _) hBound).2.2.2.2.2.2
  have hLenEq : res.1.length + ([] : CgCfg).length = cfg.length := by
    simp [hLenRew]
  have hM := rewriteBlocks_get_matches mode cfg cfg res.1 [] [] cfg.length hLenEq hBound bb blk hGet
  rcases hM with ⟨blk', hGetRew, hMatch⟩
  have hBbLt : bb < res.1.length := listGet?_some_lt res.1 bb blk' hGetRew
  have hCfgEq : res.1 ++ ([] ++ res.2 ++ []) = addCallGuards mode cfg := by
    simp [addCallGuards, res]
  rw [hCfgEq] at hMatch
  refine ⟨blk', ?_, hMatch⟩
  show listGet? (res.1 ++ res.2) bb = some blk'
  rw [listGet?_append_left res.1 res.2 bb hBbLt, hGetRew]

/-- Forward semantic simulation: every execution of `cfg` is reproduced identically by
    `addCallGuards mode cfg` (with 1 transparent stutter step through each trampoline). -/
theorem addCallGuards_sim_forward (mode : CallGuardMode) (cfg : CgCfg)
    (hBound : SuccsBounded cfg cfg.length) :
    ∀ {bb : Nat} {st : CgState} {out : CgOutcome},
      EvalCfg cfg bb st out → EvalCfg (addCallGuards mode cfg) bb st out := by
  intro bb st out hEval
  induction hEval with
  | gotoStep bb t blk st out hGet hTm _ ih =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    cases hTm' : blk.term <;> rw [hTm'] at hTm <;> try cases hTm
    rw [hTm'] at hTmMatch
    cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
    exact EvalCfg.gotoStep bb t blk' st out hGet' hTm2 (by rw [hS]; exact ih)
  | switchTrue bb cond t f blk st out hGet hTm hNz _ ih =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    cases hTm' : blk.term <;> rw [hTm'] at hTm <;> try cases hTm
    rw [hTm'] at hTmMatch
    cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
    exact EvalCfg.switchTrue bb cond t f blk' st out hGet' hTm2 (by rw [hS]; exact hNz) (by rw [hS]; exact ih)
  | switchFalse bb cond t f blk st out hGet hTm hZ _ ih =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    cases hTm' : blk.term <;> rw [hTm'] at hTm <;> try cases hTm
    rw [hTm'] at hTmMatch
    cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
    exact EvalCfg.switchFalse bb cond t f blk' st out hGet' hTm2 (by rw [hS]; exact hZ) (by rw [hS]; exact ih)
  | callRet bb rl rv d uw blk st out hGet hTm _ ih =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    rw [hTm] at hTmMatch
    cases hTm2 : blk'.term with
    | call rl' rv' mp' tgt' uw' =>
      cases tgt' with
      | none => rw [hTm2] at hTmMatch; cases hTmMatch
      | some d' =>
        rw [hTm2] at hTmMatch
        rcases hTmMatch with ⟨rfl, rfl, rfl, rfl, hTgtMatch⟩
        cases hTgtMatch with
        | inl hEq =>
          subst hEq
          exact EvalCfg.callRet bb rl' rv' d' uw' blk' st out hGet' hTm2 (by rw [hS]; exact ih)
        | inr hTrampGet =>
          have hStepTramp :
              EvalCfg (addCallGuards mode cfg) d'
                { stepCgStmts st blk'.stmts with locals := listSet (stepCgStmts st blk'.stmts).locals rl' rv' } out :=
            EvalCfg.gotoStep d' d { stmts := [], term := .goto d, isCleanup := blk.isCleanup }
              _ out hTrampGet rfl (by simp only [stepCgStmts, hS]; exact ih)
          exact EvalCfg.callRet bb rl' rv' d' uw' blk' st out hGet' hTm2 hStepTramp
    | goto _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | switchInt _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | inlineAsm _ _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | drop _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | unwindResume => rw [hTm2] at hTmMatch; cases hTmMatch
    | ret _ => rw [hTm2] at hTmMatch; cases hTmMatch
  | callUnwindCleanup bb rl rv ubb tgt blk st out hGet hTm _ ih =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    rw [hTm] at hTmMatch
    cases tgt with
    | none =>
      cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
      exact EvalCfg.callUnwindCleanup bb rl rv ubb none blk' st out hGet' hTm2 (by rw [hS]; exact ih)
    | some d =>
      cases hTm2 : blk'.term with
      | call rl' rv' mp' tgt' uw' =>
        cases tgt' with
        | none => rw [hTm2] at hTmMatch; cases hTmMatch
        | some d' =>
          rw [hTm2] at hTmMatch
          rcases hTmMatch with ⟨rfl, rfl, rfl, rfl, _⟩
          exact EvalCfg.callUnwindCleanup bb rl' rv' ubb (some d') blk' st out hGet' hTm2 (by rw [hS]; exact ih)
      | goto _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | switchInt _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | inlineAsm _ _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | drop _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | unwindResume => rw [hTm2] at hTmMatch; cases hTmMatch
      | ret _ => rw [hTm2] at hTmMatch; cases hTmMatch
  | callUnwindContinue bb rl rv tgt blk st hGet hTm =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    rw [hTm] at hTmMatch
    cases tgt with
    | none =>
      cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
      rw [← hS]
      exact EvalCfg.callUnwindContinue bb rl rv none blk' st hGet' hTm2
    | some d =>
      cases hTm2 : blk'.term with
      | call rl' rv' mp' tgt' uw' =>
        cases tgt' with
        | none => rw [hTm2] at hTmMatch; cases hTmMatch
        | some d' =>
          rw [hTm2] at hTmMatch
          rcases hTmMatch with ⟨rfl, rfl, rfl, rfl, _⟩
          rw [← hS]
          exact EvalCfg.callUnwindContinue bb rl' rv' (some d') blk' st hGet' hTm2
      | goto _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | switchInt _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | inlineAsm _ _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | drop _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | unwindResume => rw [hTm2] at hTmMatch; cases hTmMatch
      | ret _ => rw [hTm2] at hTmMatch; cases hTmMatch
  | callUnwindTerminate bb rl rv tgt blk st hGet hTm =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    rw [hTm] at hTmMatch
    cases tgt with
    | none =>
      cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
      rw [← hS]
      exact EvalCfg.callUnwindTerminate bb rl rv none blk' st hGet' hTm2
    | some d =>
      cases hTm2 : blk'.term with
      | call rl' rv' mp' tgt' uw' =>
        cases tgt' with
        | none => rw [hTm2] at hTmMatch; cases hTmMatch
        | some d' =>
          rw [hTm2] at hTmMatch
          rcases hTmMatch with ⟨rfl, rfl, rfl, rfl, _⟩
          rw [← hS]
          exact EvalCfg.callUnwindTerminate bb rl' rv' (some d') blk' st hGet' hTm2
      | goto _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | switchInt _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | inlineAsm _ _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | drop _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
      | unwindResume => rw [hTm2] at hTmMatch; cases hTmMatch
      | ret _ => rw [hTm2] at hTmMatch; cases hTmMatch
  | asmTarget bb idx t ho hl ts uw blk st out hGet hTm hIdx _ ih =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    rw [hTm] at hTmMatch
    cases hTm2 : blk'.term with
    | inlineAsm ho' hl' ts' uw' =>
      rw [hTm2] at hTmMatch
      rcases hTmMatch with ⟨rfl, rfl, rfl, _, hTargets⟩
      have hIdxLt : idx < ts.length := listGet?_some_lt ts idx t hIdx
      rcases hTargets idx hIdxLt with ⟨t0, t0', hGt0, hGt0', hTgtMatch⟩
      rw [hIdx] at hGt0
      cases hGt0
      cases hTgtMatch with
      | inl hEq =>
        subst hEq
        exact EvalCfg.asmTarget bb idx t0' ho' hl' ts' uw' blk' st out hGet' hTm2 hGt0' (by rw [hS]; exact ih)
      | inr hTrampGet =>
        have hStepTramp : EvalCfg (addCallGuards mode cfg) t0' (stepCgStmts st blk'.stmts) out :=
          EvalCfg.gotoStep t0' t { stmts := [], term := .goto t, isCleanup := blk.isCleanup }
            (stepCgStmts st blk'.stmts) out hTrampGet rfl (by simp only [stepCgStmts, hS]; exact ih)
        exact EvalCfg.asmTarget bb idx t0' ho' hl' ts' uw' blk' st out hGet' hTm2 hGt0' hStepTramp
    | goto _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | switchInt _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | call _ _ _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | drop _ _ _ => rw [hTm2] at hTmMatch; cases hTmMatch
    | unwindResume => rw [hTm2] at hTmMatch; cases hTmMatch
    | ret _ => rw [hTm2] at hTmMatch; cases hTmMatch
  | dropNormal bb t tr uw blk st out hGet hTm _ ih =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    cases hTm' : blk.term <;> rw [hTm'] at hTm <;> try cases hTm
    rw [hTm'] at hTmMatch
    cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
    exact EvalCfg.dropNormal bb t tr uw blk' st out hGet' hTm2 (by rw [hS]; exact ih)
  | unwindResumeStep bb blk st hGet hTm =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    cases hTm' : blk.term <;> rw [hTm'] at hTm <;> try cases hTm
    rw [hTm'] at hTmMatch
    cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
    rw [← hS]
    exact EvalCfg.unwindResumeStep bb blk' st hGet' hTm2
  | retStep bb l blk st hGet hTm =>
    rcases addCallGuards_lookup_matches mode cfg hBound bb blk hGet with ⟨blk', hGet', hS, _, hTmMatch⟩
    cases hTm' : blk.term <;> rw [hTm'] at hTm <;> try cases hTm
    rw [hTm'] at hTmMatch
    cases hTm2 : blk'.term <;> rw [hTm2] at hTmMatch <;> try cases hTmMatch
    rw [← hS]
    exact EvalCfg.retStep bb l blk' st hGet' hTm2

/-- **Theorem 4 (`addCallGuards_eliminates_invoke_critical_edges_and_preserves_semantics`):**
    Combines structural critical-edge elimination (zero remaining critical `Call`
    invoke-return edges and zero remaining critical `InlineAsm` output-target edges),
    exact predecessor-count conservation on original blocks, unit predecessor count
    on all inserted trampoline blocks, and full forward operational semantics
    preservation. -/
theorem addCallGuards_eliminates_invoke_critical_edges_and_preserves_semantics
    (cfg : CgCfg) (hBound : SuccsBounded cfg cfg.length) :
    let cfg' := addCallGuards .criticalCallEdges cfg
    CfgNoCriticalEdges cfg' ∧
    (∀ k, k < cfg.length → predCount cfg' k = predCount cfg k) ∧
    (∀ k, cfg.length ≤ k → k < cfg'.length → predCount cfg' k = 1) ∧
    (∀ bb st out, EvalCfg cfg bb st out → EvalCfg cfg' bb st out) := by
  rcases addCallGuards_no_invoke_critical_edges cfg hBound with ⟨hOld, hFresh, hNoCrit⟩
  exact ⟨hNoCrit, hOld, hFresh, fun _ _ _ hEv => addCallGuards_sim_forward .criticalCallEdges cfg hBound hEv⟩

/-- **Concrete Witness matching `critical_real_drop_guard` & `asm_label_with_output`:**
    1. A critical `Call` with `UnwindAction.cleanup` (`predCount[3] = 2`) IS split
       (adding fresh trampoline block `bb6: goto -> bb3` with `predCount = 1`).
    2. After `RemoveNoopLandingPads` rewrites `UnwindAction.cleanup` -> `.continue_`,
       `AddCallGuards::CriticalCallEdges` adds 0 blocks.
    3. An `InlineAsm` with `hasOutputs = true ∧ hasLabels = true` on a critical target
       IS split, while `hasOutputs = false` is NOT split. -/
theorem concrete_call_guards_and_noop_lp_witness :
    let cfgInvoke : CgCfg :=
      [ { stmts := [], term := .switchInt 1 1 2, isCleanup := false }
      , { stmts := [], term := .call 3 1 false (some 3) (.cleanup 5), isCleanup := false }
      , { stmts := [], term := .goto 3, isCleanup := false }
      , { stmts := [], term := .ret 3, isCleanup := false }
      , { stmts := [], term := .unwindResume, isCleanup := true }
      , { stmts := [.heapWrite 1 7], term := .goto 4, isCleanup := true } ]
    let cfgNoop : CgCfg :=
      [ { stmts := [], term := .switchInt 1 1 2, isCleanup := false }
      , { stmts := [], term := .call 3 1 false (some 3) (.cleanup 4), isCleanup := false }
      , { stmts := [], term := .goto 3, isCleanup := false }
      , { stmts := [], term := .ret 3, isCleanup := false }
      , { stmts := [], term := .unwindResume, isCleanup := true } ]
    let cfgAsmOut : CgCfg :=
      [ { stmts := [], term := .switchInt 1 1 2, isCleanup := false }
      , { stmts := [], term := .inlineAsm true true [2, 3] .unreachable, isCleanup := false }
      , { stmts := [], term := .ret 0, isCleanup := false }
      , { stmts := [], term := .goto 2, isCleanup := false } ]
    let cfgAsmNoOut : CgCfg :=
      [ { stmts := [], term := .switchInt 1 1 2, isCleanup := false }
      , { stmts := [], term := .inlineAsm false true [2, 3] .unreachable, isCleanup := false }
      , { stmts := [], term := .ret 0, isCleanup := false }
      , { stmts := [], term := .goto 2, isCleanup := false } ]
    (addCallGuards .criticalCallEdges cfgInvoke).length = 7 ∧
    (addCallGuards .criticalCallEdges (removeNoopLandingPads [4] cfgNoop)).length = 5 ∧
    (addCallGuards .criticalCallEdges cfgAsmOut).length = 5 ∧
    (addCallGuards .criticalCallEdges cfgAsmNoOut).length = 4 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end CallGuardsAndLandingPads

end RustcPostBorrowckAndPreCodegen


