/-!
# Formal Semantics and Soundness of `RemoveStorageMarkers` Miri Paradox, `SsaRangePropagation`, `SimplifyComparisonIntegral`, `EarlyOtherwiseBranch`, and `Subtyper`

Standalone Lean 4 (`v4.34.1`, zero external imports) mechanization establishing:
1. Stack-allocation operational semantics with explicit `AllocId` liveness, `&raw const` stack
   borrows, conservative `deinitMovedPlace` (`Operand.move` deinitialization), `Assume`,
   non-optional vs. optional overflow `Assert`, `SwitchInt`, and `CastKind::Subtype`.
2. `RemoveStorageMarkers` policy (`ctx.mir_opt_level() >= 1 && !ctx.emit_lifetime_markers()`)
   paired with `Session::emit_lifetime_markers` (`opt != OptLevel::No`), proving:
   - Unconditional forward refinement (`ForwardRefines`) via an explicit alive-allocation
     simulation invariant (`StorageSimRel`);
   - Strict reverse unsoundness (`ce1_remove_storage_markers_erases_dangling_stack_ptr_ub`)
     explaining the non-monotone `-Copt-level=0 -> -Copt-level=1` Miri paradox;
   - Reallocation `AllocId` collapse (`ce1b_loop_reallocation_merges_distinct_alloc_ids`);
   - Gated policy fix (`!ctx.mir_preserve_ub`) preserving dangling-stack-pointer UB.
3. Exact bidirectional equivalence (`↔`) of `SimplifyComparisonIntegral` (`Eq`/`Ne` target
   ordering, `Move -> Copy` downgrade, `Scalar::Ptr` constant skip) and constructive
   counterexample (`ce2_simplify_cmp_retaining_move_operand_deinits_switch_scrutinee_ub`) proving
   why keeping `Move` on a retained dead comparison triggers UB under `deinitMovedPlace = true`.
4. Soundness of singleton `SsaRangePropagation` (`WrappingRange { start = stop }`, `Assume`,
   non-optional `Assert`, single-predecessor `SwitchInt`, `bool` `otherwise` complement),
   arithmetical and MIR refutation of the docstring claim (`a < 9` does not imply `a < 8`),
   optional overflow check hazard, and constructive multi-predecessor counterexample
   (`ce3_ssa_range_multi_predecessor_join_unsound_without_intersection`).
5. Combinatorial pass-interaction characterization of `EarlyOtherwiseBranch` after
   `UnreachableEnumBranching` (`k = N ∧ N ≥ 3`), issue `95162` non-exhaustive hoisting
   counterexample (`ce4_eob_issue_95162_non_exhaustive_hoist_introduces_ub`), and `Subtyper`
   post-erasure region behavior.
-/

namespace StorageMarkersRangeSwitch

/-! ## Section 1: Constructive List and Natural-Number Helpers -/

def listGet {α : Type} (xs : List α) (n : Nat) : Option α :=
  (Nat.rec (motive := fun _ => List α → Option α)
    (fun l => match l with | [] => none | x :: _ => some x)
    (fun _ ih l => match l with | [] => none | _ :: tl => ih tl)
    n) xs

theorem listGet_nil {α : Type} (n : Nat) : listGet ([] : List α) n = none := by
  cases n <;> rfl

theorem listGet_cons_zero {α : Type} (x : α) (xs : List α) :
    listGet (x :: xs) 0 = some x := rfl

theorem listGet_cons_succ {α : Type} (x : α) (xs : List α) (n : Nat) :
    listGet (x :: xs) (n + 1) = listGet xs n := rfl

def listSet {α : Type} (xs : List α) (n : Nat) (v : α) : Option (List α) :=
  (Nat.rec (motive := fun _ => List α → α → Option (List α))
    (fun l val => match l with | [] => none | _ :: tl => some (val :: tl))
    (fun _ ih l val =>
      match l with
      | [] => none
      | x :: tl =>
        match ih tl val with
        | some tl' => some (x :: tl')
        | none => none)
    n) xs v

theorem listSet_nil {α : Type} (n : Nat) (v : α) : listSet ([] : List α) n v = none := by
  cases n <;> rfl

theorem listSet_cons_zero {α : Type} (x : α) (xs : List α) (v : α) :
    listSet (x :: xs) 0 v = some (v :: xs) := rfl

theorem listSet_cons_succ {α : Type} (x : α) (xs : List α) (n : Nat) (v : α) :
    listSet (x :: xs) (n + 1) v =
      match listSet xs n v with
      | some xs' => some (x :: xs')
      | none => none := rfl

theorem listGet_length_lt {α : Type} {xs : List α} {n : Nat} {v : α}
    (h : listGet xs n = some v) : n < xs.length := by
  induction xs generalizing n with
  | nil => rw [listGet_nil] at h; cases h
  | cons _ _ ih =>
    cases n with
    | zero => exact Nat.zero_lt_succ _
    | succ _ =>
      rw [listGet_cons_succ] at h
      exact Nat.succ_lt_succ (ih h)

theorem listGet_none_of_le {α : Type} {xs : List α} {n : Nat}
    (h : xs.length ≤ n) : listGet xs n = none := by
  induction xs generalizing n with
  | nil => exact listGet_nil n
  | cons _ _ ih =>
    cases n with
    | zero => cases h
    | succ k => exact ih (Nat.le_of_succ_le_succ h)

theorem listSet_exists_of_get {α : Type} {xs : List α} {n : Nat} {old : α}
    (h : listGet xs n = some old) (v : α) : ∃ xs', listSet xs n v = some xs' := by
  induction xs generalizing n with
  | nil => rw [listGet_nil] at h; cases h
  | cons _ _ ih =>
    cases n with
    | zero => exact ⟨_, rfl⟩
    | succ _ =>
      rw [listGet_cons_succ] at h
      rcases ih h with ⟨tl', htl'⟩
      exact ⟨_, by rw [listSet_cons_succ, htl']⟩

theorem listSet_length_eq {α : Type} {xs xs' : List α} {n : Nat} {v : α}
    (h : listSet xs n v = some xs') : xs'.length = xs.length := by
  induction xs generalizing n xs' with
  | nil => rw [listSet_nil] at h; cases h
  | cons _ tl ih =>
    cases n with
    | zero =>
      rw [listSet_cons_zero] at h
      injection h with hEq
      subst hEq
      rfl
    | succ k =>
      rw [listSet_cons_succ] at h
      cases hSub : listSet tl k v with
      | none => rw [hSub] at h; cases h
      | some tl' =>
        rw [hSub] at h
        injection h with hEq
        subst hEq
        exact congrArg Nat.succ (ih hSub)

theorem listGet_listSet_eq {α : Type} {xs xs' : List α} {n : Nat} {v : α}
    (h : listSet xs n v = some xs') : listGet xs' n = some v := by
  induction xs generalizing n xs' with
  | nil => rw [listSet_nil] at h; cases h
  | cons _ tl ih =>
    cases n with
    | zero =>
      rw [listSet_cons_zero] at h
      injection h with hEq
      subst hEq
      rfl
    | succ k =>
      rw [listSet_cons_succ] at h
      cases hSub : listSet tl k v with
      | none => rw [hSub] at h; cases h
      | some tl' =>
        rw [hSub] at h
        injection h with hEq
        subst hEq
        rw [listGet_cons_succ]
        exact ih hSub

theorem listGet_listSet_ne {α : Type} {xs xs' : List α} {n m : Nat} {v : α}
    (h : listSet xs n v = some xs') (hne : m ≠ n) :
    listGet xs' m = listGet xs m := by
  induction xs generalizing n m xs' with
  | nil => rw [listSet_nil] at h; cases h
  | cons _ tl ih =>
    cases n with
    | zero =>
      rw [listSet_cons_zero] at h
      injection h with hEq
      subst hEq
      cases m with
      | zero => exact False.elim (hne rfl)
      | succ _ => rfl
    | succ k =>
      rw [listSet_cons_succ] at h
      cases hSub : listSet tl k v with
      | none => rw [hSub] at h; cases h
      | some tl' =>
        rw [hSub] at h
        injection h with hEq
        subst hEq
        cases m with
        | zero => rfl
        | succ j =>
          have hjk : j ≠ k := fun heq => hne (congrArg Nat.succ heq)
          exact ih hSub hjk

theorem listGet_append_left {α : Type} (xs ys : List α) {n : Nat}
    (h : n < xs.length) : listGet (xs ++ ys) n = listGet xs n := by
  induction xs generalizing n with
  | nil => cases h
  | cons _ _ ih =>
    cases n with
    | zero => rfl
    | succ _ => exact ih (Nat.lt_of_succ_lt_succ h)

theorem listGet_append_exact {α : Type} (xs : List α) (y : α) :
    listGet (xs ++ [y]) xs.length = some y := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem listGet_map {α β : Type} (f : α → β) (xs : List α) (n : Nat) :
    listGet (xs.map f) n = (listGet xs n).map f := by
  induction xs generalizing n with
  | nil => rw [List.map_nil, listGet_nil, listGet_nil]; rfl
  | cons _ _ ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hb))

def natInList (x : Nat) (ys : List Nat) : Bool :=
  List.foldr (fun y ih => Nat.beq x y || ih) false ys

/-! ## Section 2: MIR Syntax and Operational Stack/Heap Semantics -/

abbrev LocalId := Nat
abbrev BlockId := Nat
abbrev AllocId := Nat
abbrev StaticId := Nat

inductive ConstVal where
  | int (n : Int)
  | bool (b : Bool)
  | ptrConst (sid : StaticId)
  deriving DecidableEq, Repr

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  | staticPtr (sid : StaticId)
  | ptr (aid : AllocId)
  deriving DecidableEq, Repr

def constToVal : ConstVal → Val
  | .int n => .int n
  | .bool b => .bool b
  | .ptrConst sid => .staticPtr sid

def isNonStackVal : Val → Prop
  | .ptr _ => False
  | _ => True

structure AllocEntry where
  alive : Bool
  cell : Option Val
  deriving DecidableEq, Repr

inductive LocalSlot where
  | dead
  | direct (cell : Option Val)
  | stack (aid : AllocId)
  deriving DecidableEq, Repr

inductive Operand where
  | copy (loc : LocalId)
  | move (loc : LocalId)
  | const (c : ConstVal)
  deriving DecidableEq, Repr

inductive BinOpKind where
  | eq
  | ne
  | lt
  | add
  deriving DecidableEq, Repr

inductive Rvalue where
  | use (op : Operand)
  | binOp (k : BinOpKind) (lhs rhs : Operand)
  | addrOf (loc : LocalId)
  | derefPtr (ptrOp : Operand)
  | discr (loc : LocalId)
  | subtypeCast (op : Operand)
  deriving DecidableEq, Repr

inductive Stmt where
  | nop
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | assign (dst : LocalId) (rv : Rvalue)
  | storePtr (ptrOp : Operand) (valOp : Operand)
  | assume (op : Operand)
  deriving DecidableEq, Repr

inductive Term where
  | goto (target : BlockId)
  | switchInt (discr : Operand) (arms : List (Int × BlockId)) (otherwise : BlockId)
  | assert (cond : Operand) (expected : Bool) (target : BlockId) (optionalOverflow : Bool)
  | ret
  | unreachable
  deriving DecidableEq, Repr

structure BasicBlock where
  stmts : List Stmt
  term : Term
  deriving DecidableEq, Repr

structure Body where
  numLocals : Nat
  stackBackedLocals : List LocalId
  blocks : List BasicBlock
  deriving DecidableEq, Repr

inductive UbKind where
  | deadLocal
  | uninitRead
  | danglingStackPtr
  | assumeFalse
  | unreachableReached
  | invalidDiscr
  | badOperandType
  | invalidTarget
  deriving DecidableEq, Repr

inductive ExecOutcome where
  | returned (v : Val)
  | panicked
  | ub (kind : UbKind)
  | outOfFuel
  deriving DecidableEq, Repr

structure EvalConfig where
  deinitMovedPlace : Bool
  enforceOptionalOverflow : Bool
  deriving DecidableEq, Repr

structure MachineState where
  pc : BlockId
  stmtIdx : Nat
  locals : List LocalSlot
  heap : List AllocEntry
  deriving DecidableEq, Repr

def allocHeap (heap : List AllocEntry) : AllocId × List AllocEntry :=
  let aid := heap.length
  (aid, heap ++ [{ alive := true, cell := none }])

def freeHeapOpt (heap : List AllocEntry) (aidOpt : Option AllocId) : List AllocEntry :=
  match aidOpt with
  | none => heap
  | some aid =>
    match listGet heap aid with
    | none => heap
    | some e =>
      match listSet heap aid { e with alive := false } with
      | some h' => h'
      | none => heap

theorem freeHeapOpt_length (heap : List AllocEntry) (aidOpt : Option AllocId) :
    (freeHeapOpt heap aidOpt).length = heap.length := by
  cases aidOpt with
  | none => rfl
  | some aid =>
    dsimp only [freeHeapOpt]
    cases hg : listGet heap aid with
    | none => rfl
    | some e =>
      dsimp only
      cases hs : listSet heap aid { e with alive := false } with
      | none => rfl
      | some h' => exact listSet_length_eq hs

theorem freeHeapOpt_get_ne (heap : List AllocEntry) (aidOpt : Option AllocId)
    {a : Nat} (hne : aidOpt ≠ some a) :
    listGet (freeHeapOpt heap aidOpt) a = listGet heap a := by
  cases aidOpt with
  | none => rfl
  | some aid =>
    have hne' : a ≠ aid := fun h => hne (congrArg some h.symm)
    dsimp only [freeHeapOpt]
    cases hg : listGet heap aid with
    | none => rfl
    | some e =>
      dsimp only
      cases hs : listSet heap aid { e with alive := false } with
      | none => rfl
      | some h' => exact listGet_listSet_ne hs hne'

theorem freeHeapOpt_alive_preserved {heap : List AllocEntry} {aidOpt : Option AllocId}
    {a : Nat} {e : AllocEntry}
    (hg : listGet (freeHeapOpt heap aidOpt) a = some e) (hal : e.alive = true) :
    aidOpt ≠ some a ∧ listGet heap a = some e := by
  cases aidOpt with
  | none => exact ⟨(fun h => nomatch h), hg⟩
  | some aid =>
    cases hEq : Nat.beq a aid with
    | true =>
      have ha : a = aid := Nat.eq_of_beq_eq_true hEq
      subst ha
      dsimp only [freeHeapOpt] at hg
      cases hg0 : listGet heap a with
      | none =>
        rw [hg0] at hg
        dsimp only at hg
        rw [hg] at hg0
        cases hg0
      | some e0 =>
        rw [hg0] at hg
        dsimp only at hg
        rcases listSet_exists_of_get hg0 { e0 with alive := false } with ⟨h', hs⟩
        rw [hs] at hg
        dsimp only at hg
        rw [listGet_listSet_eq hs] at hg
        injection hg with he
        subst he
        cases hal
    | false =>
      have hne : a ≠ aid := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
      have hneOpt : some aid ≠ some a := fun h => by injection h with h1; exact hne h1.symm
      rw [freeHeapOpt_get_ne heap (some aid) hneOpt] at hg
      exact ⟨hneOpt, hg⟩

def slotAidOpt : LocalSlot → Option AllocId
  | .stack aid => some aid
  | _ => none

def readLocalCell (st : MachineState) (loc : LocalId) : Except UbKind Val :=
  match listGet st.locals loc with
  | none => .error .deadLocal
  | some .dead => .error .deadLocal
  | some (.direct none) => .error .uninitRead
  | some (.direct (some v)) => .ok v
  | some (.stack aid) =>
    match listGet st.heap aid with
    | none => .error .danglingStackPtr
    | some e =>
      if !e.alive then .error .danglingStackPtr
      else
        match e.cell with
        | none => .error .uninitRead
        | some v => .ok v

def deinitLocalCell (st : MachineState) (loc : LocalId) : MachineState :=
  match listGet st.locals loc with
  | some (.direct _) =>
    match listSet st.locals loc (.direct none) with
    | some ls' => { st with locals := ls' }
    | none => st
  | some (.stack aid) =>
    match listGet st.heap aid with
    | some e =>
      match listSet st.heap aid { e with cell := none } with
      | some h' => { st with heap := h' }
      | none => st
    | none => st
  | _ => st

def writeLocalCell (st : MachineState) (loc : LocalId) (v : Val) :
    Except UbKind MachineState :=
  match listGet st.locals loc with
  | none => .error .deadLocal
  | some .dead => .error .deadLocal
  | some (.direct _) =>
    match listSet st.locals loc (.direct (some v)) with
    | some ls' => .ok { st with locals := ls' }
    | none => .error .deadLocal
  | some (.stack aid) =>
    match listGet st.heap aid with
    | none => .error .danglingStackPtr
    | some e =>
      if !e.alive then .error .danglingStackPtr
      else
        match listSet st.heap aid { e with cell := some v } with
        | some h' => .ok { st with heap := h' }
        | none => .error .danglingStackPtr

def evalOperand (cfg : EvalConfig) (st : MachineState) (op : Operand) :
    Except UbKind (Val × MachineState) :=
  match op with
  | .const c => .ok (constToVal c, st)
  | .copy loc =>
    match readLocalCell st loc with
    | .error k => .error k
    | .ok v => .ok (v, st)
  | .move loc =>
    match readLocalCell st loc with
    | .error k => .error k
    | .ok v =>
      let st' := if cfg.deinitMovedPlace then deinitLocalCell st loc else st
      .ok (v, st')

def evalBinOp (k : BinOpKind) (lhs rhs : Val) : Except UbKind Val :=
  match k, lhs, rhs with
  | .eq, .int a, .int b => .ok (.bool (decide (a = b)))
  | .ne, .int a, .int b => .ok (.bool (decide (a ≠ b)))
  | .lt, .int a, .int b => .ok (.bool (decide (a < b)))
  | .add, .int a, .int b => .ok (.int (a + b))
  | .eq, .bool a, .bool b => .ok (.bool (a == b))
  | .ne, .bool a, .bool b => .ok (.bool (a != b))
  | _, _, _ => .error .badOperandType

def evalRvalue (cfg : EvalConfig) (st : MachineState) (rv : Rvalue) :
    Except UbKind (Val × MachineState) :=
  match rv with
  | .use op => evalOperand cfg st op
  | .subtypeCast op => evalOperand cfg st op
  | .binOp k lhs rhs =>
    match evalOperand cfg st lhs with
    | .error u => .error u
    | .ok (lv, st1) =>
      match evalOperand cfg st1 rhs with
      | .error u => .error u
      | .ok (rvVal, st2) =>
        match evalBinOp k lv rvVal with
        | .error u => .error u
        | .ok res => .ok (res, st2)
  | .addrOf loc =>
    match listGet st.locals loc with
    | some (.stack aid) =>
      match listGet st.heap aid with
      | some e =>
        if e.alive then .ok (.ptr aid, st) else .error .danglingStackPtr
      | none => .error .danglingStackPtr
    | _ => .error .deadLocal
  | .derefPtr ptrOp =>
    match evalOperand cfg st ptrOp with
    | .error u => .error u
    | .ok (.ptr aid, st1) =>
      match listGet st1.heap aid with
      | none => .error .danglingStackPtr
      | some e =>
        if !e.alive then .error .danglingStackPtr
        else
          match e.cell with
          | none => .error .uninitRead
          | some v => .ok (v, st1)
    | .ok (_, _) => .error .badOperandType
  | .discr loc =>
    match readLocalCell st loc with
    | .error u => .error u
    | .ok (.int n) =>
      if decide (0 ≤ n) then .ok (.int n, st) else .error .invalidDiscr
    | .ok _ => .error .badOperandType

def lookupSwitchTarget (v : Int) (arms : List (Int × BlockId)) (otherwise : BlockId) :
    BlockId :=
  List.foldr (fun p ih => if decide (v = p.1) then p.2 else ih) otherwise arms

def discrBits : Val → Except UbKind Int
  | .int n => .ok n
  | .bool b => .ok (if b then 1 else 0)
  | .staticPtr _ => .error .badOperandType
  | .ptr _ => .error .badOperandType

def stepStmt (cfg : EvalConfig) (body : Body) (st : MachineState) (s : Stmt) :
    Except UbKind MachineState :=
  match s with
  | .nop => .ok { st with stmtIdx := st.stmtIdx + 1 }
  | .storageLive loc =>
    match listGet st.locals loc with
    | none => .error .deadLocal
    | some oldSlot =>
      let h1 := freeHeapOpt st.heap (slotAidOpt oldSlot)
      if natInList loc body.stackBackedLocals then
        let (aid, h2) := allocHeap h1
        match listSet st.locals loc (.stack aid) with
        | some ls' => .ok { st with locals := ls', heap := h2, stmtIdx := st.stmtIdx + 1 }
        | none => .error .deadLocal
      else
        match listSet st.locals loc (.direct none) with
        | some ls' => .ok { st with locals := ls', heap := h1, stmtIdx := st.stmtIdx + 1 }
        | none => .error .deadLocal
  | .storageDead loc =>
    if Nat.beq loc 0 then .error .deadLocal
    else
      match listGet st.locals loc with
      | none => .error .deadLocal
      | some oldSlot =>
        let h1 := freeHeapOpt st.heap (slotAidOpt oldSlot)
        match listSet st.locals loc .dead with
        | some ls' => .ok { st with locals := ls', heap := h1, stmtIdx := st.stmtIdx + 1 }
        | none => .error .deadLocal
  | .assign dst rv =>
    match evalRvalue cfg st rv with
    | .error u => .error u
    | .ok (val, st1) =>
      match writeLocalCell st1 dst val with
      | .error u => .error u
      | .ok st2 => .ok { st2 with stmtIdx := st2.stmtIdx + 1 }
  | .storePtr ptrOp valOp =>
    match evalOperand cfg st ptrOp with
    | .error u => .error u
    | .ok (.ptr aid, st1) =>
      match evalOperand cfg st1 valOp with
      | .error u => .error u
      | .ok (v, st2) =>
        match listGet st2.heap aid with
        | none => .error .danglingStackPtr
        | some e =>
          if !e.alive then .error .danglingStackPtr
          else
            match listSet st2.heap aid { e with cell := some v } with
            | some h' => .ok { st2 with heap := h', stmtIdx := st2.stmtIdx + 1 }
            | none => .error .danglingStackPtr
    | .ok (_, _) => .error .badOperandType
  | .assume op =>
    match evalOperand cfg st op with
    | .error u => .error u
    | .ok (.bool true, st1) => .ok { st1 with stmtIdx := st1.stmtIdx + 1 }
    | .ok (.bool false, _) => .error .assumeFalse
    | .ok (_, _) => .error .badOperandType

inductive TermStepResult where
  | cont (st : MachineState)
  | stop (out : ExecOutcome)
  deriving DecidableEq, Repr

def stepTerm (cfg : EvalConfig) (st : MachineState) (t : Term) : TermStepResult :=
  match t with
  | .goto tgt => .cont { st with pc := tgt, stmtIdx := 0 }
  | .switchInt discr arms otherwise =>
    match evalOperand cfg st discr with
    | .error u => .stop (.ub u)
    | .ok (v, st1) =>
      match discrBits v with
      | .error u => .stop (.ub u)
      | .ok bits =>
        let tgt := lookupSwitchTarget bits arms otherwise
        .cont { st1 with pc := tgt, stmtIdx := 0 }
  | .assert cond expected tgt optionalOverflow =>
    if optionalOverflow && !cfg.enforceOptionalOverflow then
      .cont { st with pc := tgt, stmtIdx := 0 }
    else
      match evalOperand cfg st cond with
      | .error u => .stop (.ub u)
      | .ok (.bool b, st1) =>
        if b == expected then .cont { st1 with pc := tgt, stmtIdx := 0 }
        else .stop .panicked
      | .ok (_, _) => .stop (.ub .badOperandType)
  | .ret =>
    match readLocalCell st 0 with
    | .error u => .stop (.ub u)
    | .ok v => .stop (.returned v)
  | .unreachable => .stop (.ub .unreachableReached)

def runBody (cfg : EvalConfig) (body : Body) (st : MachineState) (fuel : Nat) :
    ExecOutcome :=
  (Nat.rec (motive := fun _ => MachineState → ExecOutcome)
    (fun _ => .outOfFuel)
    (fun _ ih curSt =>
      match listGet body.blocks curSt.pc with
      | none => .ub .invalidTarget
      | some bb =>
        match listGet bb.stmts curSt.stmtIdx with
        | some s =>
          match stepStmt cfg body curSt s with
          | .error u => .ub u
          | .ok st' => ih st'
        | none =>
          match stepTerm cfg curSt bb.term with
          | .stop out => out
          | .cont st' => ih st')
    fuel) st

/-! ### Initial State Construction (`always_storage_live_locals` Semantics) -/

def initScopedLoop (stackLocals : List LocalId) (idx remaining : Nat) : List LocalSlot :=
  (Nat.rec (motive := fun _ => Nat → List LocalSlot)
    (fun _ => [])
    (fun _ ih i =>
      let slot : LocalSlot :=
        if Nat.beq i 0 then
          if natInList 0 stackLocals then .dead else .direct none
        else .dead
      slot :: ih (i + 1))
    remaining) idx

def initScopedState (body : Body) : MachineState :=
  { pc := 0
    stmtIdx := 0
    locals := initScopedLoop body.stackBackedLocals 0 body.numLocals
    heap := [] }

def initFrameLiveLoop (stackLocals : List LocalId) (idx remaining : Nat)
    (heap : List AllocEntry) : List LocalSlot × List AllocEntry :=
  (Nat.rec (motive := fun _ => Nat → List AllocEntry → List LocalSlot × List AllocEntry)
    (fun _ hp => ([], hp))
    (fun _ ih i hp =>
      if natInList i stackLocals then
        let (aid, h1) := allocHeap hp
        let (rest, h2) := ih (i + 1) h1
        (.stack aid :: rest, h2)
      else
        let (rest, h2) := ih (i + 1) hp
        (.direct none :: rest, h2))
    remaining) idx heap

def initFrameLiveState (body : Body) : MachineState :=
  let (ls, hp) := initFrameLiveLoop body.stackBackedLocals 0 body.numLocals []
  { pc := 0, stmtIdx := 0, locals := ls, heap := hp }

/-! ## Section 3: `RemoveStorageMarkers` Policy, Forward Refinement, and Miri Paradox -/

inductive OptLevel where
  | no
  | o1
  | o2
  | o3
  | sizeS
  | sizeZ
  deriving DecidableEq, Repr

structure SessionFlags where
  optLevel : OptLevel
  mirOptLevel : Nat
  mirPreserveUb : Bool
  sanitizersNeedLifetimes : Bool
  codegenEmitRetag : Bool
  disableRemoveStorageMarkers : Bool := false
  deriving DecidableEq, Repr

def emitLifetimeMarkers (s : SessionFlags) : Bool :=
  (s.optLevel != .no) || s.sanitizersNeedLifetimes || s.codegenEmitRetag

def removeStorageMarkersEnabled (s : SessionFlags) : Bool :=
  !s.disableRemoveStorageMarkers &&
    decide (s.mirOptLevel ≥ 1) && !emitLifetimeMarkers s

def fixedRemoveStorageMarkersEnabled (s : SessionFlags) : Bool :=
  !s.disableRemoveStorageMarkers &&
    decide (s.mirOptLevel ≥ 1) && !emitLifetimeMarkers s && !s.mirPreserveUb

def stripStorageStmt : Stmt → Stmt
  | .storageLive _ => .nop
  | .storageDead _ => .nop
  | s => s

def passRemoveStorageMarkers (b : Body) : Body :=
  { b with blocks := b.blocks.map (fun bb => { bb with stmts := bb.stmts.map stripStorageStmt }) }

def evalWithMiriPipeline (flags : SessionFlags) (cfg : EvalConfig) (b : Body)
    (fuel : Nat) : ExecOutcome :=
  if removeStorageMarkersEnabled flags then
    let b' := passRemoveStorageMarkers b
    runBody cfg b' (initFrameLiveState b') fuel
  else
    runBody cfg b (initScopedState b) fuel

def evalWithFixedPipeline (flags : SessionFlags) (cfg : EvalConfig) (b : Body)
    (fuel : Nat) : ExecOutcome :=
  if fixedRemoveStorageMarkersEnabled flags then
    let b' := passRemoveStorageMarkers b
    runBody cfg b' (initFrameLiveState b') fuel
  else
    runBody cfg b (initScopedState b) fuel

theorem removeStorageMarkers_ignores_mirPreserveUb (s : SessionFlags) :
    removeStorageMarkersEnabled { s with mirPreserveUb := true } =
      removeStorageMarkersEnabled { s with mirPreserveUb := false } := rfl

theorem emitLifetimeMarkers_opt0_vs_opt1 :
    emitLifetimeMarkers
      { optLevel := .no, mirOptLevel := 2, mirPreserveUb := true,
        sanitizersNeedLifetimes := false, codegenEmitRetag := false } = false ∧
    emitLifetimeMarkers
      { optLevel := .o1, mirOptLevel := 2, mirPreserveUb := true,
        sanitizersNeedLifetimes := false, codegenEmitRetag := false } = true :=
  ⟨rfl, rfl⟩

def ForwardRefines (outSrc outTgt : ExecOutcome) : Prop :=
  (∀ v, isNonStackVal v → outSrc = .returned v → outTgt = .returned v) ∧
  (outSrc = .panicked → outTgt = .panicked)

def ReverseUbSound (outSrc outTgt : ExecOutcome) : Prop :=
  ∀ k, outSrc = .ub k → ∃ k', outTgt = .ub k'

/-! ### Simulation Relation and Universal Forward Refinement Theorem -/

def ValSim (allocMap : Nat → Option Nat) : Val → Val → Prop
  | .int n, .int m => n = m
  | .bool a, .bool b => a = b
  | .staticPtr s1, .staticPtr s2 => s1 = s2
  | .ptr aS, .ptr aT => allocMap aS = some aT
  | _, _ => False

def OptValSim (allocMap : Nat → Option Nat) : Option Val → Option Val → Prop
  | none, _ => True
  | some vS, some vT => ValSim allocMap vS vT
  | some _, none => False

structure StorageSimRel (stackLocals : List LocalId) (allocMap : Nat → Option Nat)
    (targetOf : LocalId → Option AllocId) (stSrc stTgt : MachineState) : Prop where
  pcEq : stSrc.pc = stTgt.pc
  stmtEq : stSrc.stmtIdx = stTgt.stmtIdx
  lenEq : stSrc.locals.length = stTgt.locals.length
  mapBounded : ∀ a t, allocMap a = some t → a < stSrc.heap.length
  targetUnique : ∀ i j aT, targetOf i = some aT → targetOf j = some aT → i = j
  tgtLocalsOk : ∀ i,
    match listGet stTgt.locals i with
    | none => targetOf i = none
    | some .dead => False
    | some (.direct _) => natInList i stackLocals = false ∧ targetOf i = none
    | some (.stack aT) =>
      natInList i stackLocals = true ∧
      targetOf i = some aT ∧
      ∃ eT, listGet stTgt.heap aT = some eT ∧ eT.alive = true
  srcLocalsOk : ∀ i,
    match listGet stSrc.locals i, listGet stTgt.locals i with
    | none, none => True
    | some .dead, some _ => True
    | some (.direct oS), some (.direct oT) =>
      natInList i stackLocals = false ∧ OptValSim allocMap oS oT
    | some (.stack aS), some (.stack aT) =>
      natInList i stackLocals = true ∧ allocMap aS = some aT ∧
      ∃ eS eT, listGet stSrc.heap aS = some eS ∧ listGet stTgt.heap aT = some eT ∧
        eS.alive = true ∧ eT.alive = true ∧ OptValSim allocMap eS.cell eT.cell
    | _, _ => False
  srcHeapOk : ∀ aS eS,
    listGet stSrc.heap aS = some eS →
    eS.alive = true →
    ∃ i aT eT,
      listGet stSrc.locals i = some (.stack aS) ∧
      targetOf i = some aT ∧
      allocMap aS = some aT ∧
      listGet stTgt.heap aT = some eT ∧
      eT.alive = true ∧
      OptValSim allocMap eS.cell eT.cell
  aliveInj : ∀ aS1 aS2 aT e1 e2,
    listGet stSrc.heap aS1 = some e1 → e1.alive = true →
    listGet stSrc.heap aS2 = some e2 → e2.alive = true →
    allocMap aS1 = some aT → allocMap aS2 = some aT →
    aS1 = aS2

theorem valSim_mono {m1 m2 : Nat → Option Nat}
    (hMono : ∀ a t, m1 a = some t → m2 a = some t)
    {v1 v2 : Val} (h : ValSim m1 v1 v2) : ValSim m2 v1 v2 := by
  cases v1 with
  | int _ => cases v2 <;> exact h
  | bool _ => cases v2 <;> exact h
  | staticPtr _ => cases v2 <;> exact h
  | ptr a =>
    cases v2 with
    | int _ => exact h
    | bool _ => exact h
    | staticPtr _ => exact h
    | ptr t => exact hMono a t h

theorem optValSim_mono {m1 m2 : Nat → Option Nat}
    (hMono : ∀ a t, m1 a = some t → m2 a = some t)
    {o1 o2 : Option Val} (h : OptValSim m1 o1 o2) : OptValSim m2 o1 o2 := by
  cases o1 with
  | none => trivial
  | some _ =>
    cases o2 with
    | none => exact h
    | some _ => exact valSim_mono hMono h

theorem valSim_binOp {m : Nat → Option Nat} {k : BinOpKind}
    {lS lT rS rT vS : Val} (hl : ValSim m lS lT) (hr : ValSim m rS rT)
    (hEval : evalBinOp k lS rS = .ok vS) :
    ∃ vT, evalBinOp k lT rT = .ok vT ∧ ValSim m vS vT := by
  cases lS with
  | int a =>
    cases lT with
    | int a' =>
      have ha : a = a' := hl
      subst ha
      cases rS with
      | int b =>
        cases rT with
        | int b' =>
          have hb : b = b' := hr
          subst hb
          cases k <;> cases hEval <;> exact ⟨_, rfl, rfl⟩
        | bool _ => exact False.elim hr
        | staticPtr _ => exact False.elim hr
        | ptr _ => exact False.elim hr
      | bool _ => cases k <;> cases hEval
      | staticPtr _ => cases k <;> cases hEval
      | ptr _ => cases k <;> cases hEval
    | bool _ => exact False.elim hl
    | staticPtr _ => exact False.elim hl
    | ptr _ => exact False.elim hl
  | bool a =>
    cases lT with
    | int _ => exact False.elim hl
    | bool a' =>
      have ha : a = a' := hl
      subst ha
      cases rS with
      | bool b =>
        cases rT with
        | bool b' =>
          have hb : b = b' := hr
          subst hb
          cases k <;> cases hEval <;> exact ⟨_, rfl, rfl⟩
        | int _ => exact False.elim hr
        | staticPtr _ => exact False.elim hr
        | ptr _ => exact False.elim hr
      | int _ => cases k <;> cases hEval
      | staticPtr _ => cases k <;> cases hEval
      | ptr _ => cases k <;> cases hEval
    | staticPtr _ => exact False.elim hl
    | ptr _ => exact False.elim hl
  | staticPtr _ => cases k <;> cases hEval
  | ptr _ => cases k <;> cases hEval

theorem valSim_discrBits {m : Nat → Option Nat} {vS vT : Val} {bits : Int}
    (hv : ValSim m vS vT) (h : discrBits vS = .ok bits) :
    discrBits vT = .ok bits := by
  cases vS with
  | int a =>
    cases vT with
    | int b =>
      have heq : a = b := hv
      subst heq
      exact h
    | bool _ => exact False.elim hv
    | staticPtr _ => exact False.elim hv
    | ptr _ => exact False.elim hv
  | bool a =>
    cases vT with
    | bool b =>
      have heq : a = b := hv
      subst heq
      exact h
    | int _ => exact False.elim hv
    | staticPtr _ => exact False.elim hv
    | ptr _ => exact False.elim hv
  | staticPtr _ => cases h
  | ptr _ => cases h

theorem valSim_nonStack_eq {m : Nat → Option Nat} {vS vT : Val}
    (hNon : isNonStackVal vS) (hv : ValSim m vS vT) : vT = vS := by
  cases vS with
  | int _ => cases vT with | int _ => exact congrArg Val.int hv.symm | bool _ => exact False.elim hv | staticPtr _ => exact False.elim hv | ptr _ => exact False.elim hv
  | bool _ => cases vT with | bool _ => exact congrArg Val.bool hv.symm | int _ => exact False.elim hv | staticPtr _ => exact False.elim hv | ptr _ => exact False.elim hv
  | staticPtr _ => cases vT with | staticPtr _ => exact congrArg Val.staticPtr hv.symm | int _ => exact False.elim hv | bool _ => exact False.elim hv | ptr _ => exact False.elim hv
  | ptr _ => exact False.elim hNon

theorem sim_readLocalCell {stackLocals : List LocalId} {m : Nat → Option Nat}
    {targetOf : LocalId → Option AllocId} {stSrc stTgt : MachineState}
    (hSim : StorageSimRel stackLocals m targetOf stSrc stTgt)
    {loc : LocalId} {vS : Val} (hRead : readLocalCell stSrc loc = .ok vS) :
    ∃ vT, readLocalCell stTgt loc = .ok vT ∧ ValSim m vS vT := by
  have hLoc := hSim.srcLocalsOk loc
  unfold readLocalCell at hRead ⊢
  cases hSL : listGet stSrc.locals loc with
  | none => rw [hSL] at hRead; cases hRead
  | some slotS =>
    rw [hSL] at hRead hLoc
    cases hTL : listGet stTgt.locals loc with
    | none => rw [hTL] at hLoc; cases slotS <;> exact False.elim hLoc
    | some slotT =>
      rw [hTL] at hLoc
      cases slotS with
      | dead => cases hRead
      | direct oS =>
        cases slotT with
        | dead => exact False.elim hLoc
        | stack _ => exact False.elim hLoc
        | direct oT =>
          dsimp only at hRead hLoc ⊢
          cases oS with
          | none => cases hRead
          | some vS0 =>
            injection hRead with hv; subst hv
            cases oT with
            | none => exact False.elim hLoc.2
            | some vT0 => exact ⟨vT0, rfl, hLoc.2⟩
      | stack aS =>
        cases slotT with
        | dead => exact False.elim hLoc
        | direct _ => exact False.elim hLoc
        | stack aT =>
          dsimp only at hRead hLoc ⊢
          rcases hLoc with ⟨_, _, eS, eT, hES, hET, hEA, hTA, hCell⟩
          rw [hES] at hRead
          simp only [hEA, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRead
          cases hEC : eS.cell with
          | none => rw [hEC] at hRead; cases hRead
          | some vS0 =>
            rw [hEC] at hRead hCell
            injection hRead with hv; subst hv
            rw [hET]
            simp only [hTA, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases hTC : eT.cell with
            | none => rw [hTC] at hCell; exact False.elim hCell
            | some vT0 => rw [hTC] at hCell; exact ⟨vT0, rfl, hCell⟩

theorem sim_deinitLocalCell {stackLocals : List LocalId} {m : Nat → Option Nat}
    {targetOf : LocalId → Option AllocId} {stSrc stTgt : MachineState}
    (hSim : StorageSimRel stackLocals m targetOf stSrc stTgt)
    (loc : LocalId) :
    StorageSimRel stackLocals m targetOf (deinitLocalCell stSrc loc) (deinitLocalCell stTgt loc) := by
  have hLoc := hSim.srcLocalsOk loc
  unfold deinitLocalCell
  cases hSL : listGet stSrc.locals loc with
  | none =>
    rw [hSL] at hLoc
    cases hTL : listGet stTgt.locals loc with
    | none => exact hSim
    | some _ => rw [hTL] at hLoc; exact False.elim hLoc
  | some slotS =>
    cases hTL : listGet stTgt.locals loc with
    | none => rw [hSL, hTL] at hLoc; cases slotS <;> exact False.elim hLoc
    | some slotT =>
      rw [hSL, hTL] at hLoc
      cases slotS with
      | dead =>
        cases slotT with
        | dead =>
          have hT := hSim.tgtLocalsOk loc; rw [hTL] at hT; exact False.elim hT
        | direct _ =>
          dsimp only
          rcases listSet_exists_of_get hTL (.direct none) with ⟨lsT', hSetT⟩
          rw [hSetT]
          refine
            { pcEq := hSim.pcEq, stmtEq := hSim.stmtEq,
              lenEq := by rw [listSet_length_eq hSetT]; exact hSim.lenEq,
              mapBounded := hSim.mapBounded,
              targetUnique := hSim.targetUnique, tgtLocalsOk := ?_, srcLocalsOk := ?_,
              srcHeapOk := hSim.srcHeapOk, aliveInj := hSim.aliveInj }
          · intro i
            have hPrev := hSim.tgtLocalsOk i
            cases hEq : Nat.beq i loc with
            | true =>
              have hil := Nat.eq_of_beq_eq_true hEq; subst hil
              rw [listGet_listSet_eq hSetT]; rw [hTL] at hPrev; exact hPrev
            | false =>
              have hne : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              rw [listGet_listSet_ne hSetT hne]; exact hPrev
          · intro i
            have hPrev := hSim.srcLocalsOk i
            cases hEq : Nat.beq i loc with
            | true =>
              have hil := Nat.eq_of_beq_eq_true hEq; subst hil
              rw [hSL, listGet_listSet_eq hSetT]; trivial
            | false =>
              have hne : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              rw [listGet_listSet_ne hSetT hne]; exact hPrev
        | stack aT =>
          have hT := hSim.tgtLocalsOk loc; rw [hTL] at hT
          dsimp only at hT ⊢
          rcases hT with ⟨_, hofLoc, eT, hGT, _⟩
          rcases listSet_exists_of_get hGT { eT with cell := none } with ⟨hT', hSetH⟩
          rw [hGT]; dsimp only; rw [hSetH]; dsimp only
          refine
            { pcEq := hSim.pcEq, stmtEq := hSim.stmtEq, lenEq := hSim.lenEq,
              mapBounded := hSim.mapBounded,
              targetUnique := hSim.targetUnique, tgtLocalsOk := ?_, srcLocalsOk := ?_,
              srcHeapOk := ?_, aliveInj := hSim.aliveInj }
          · intro i
            have hPrev := hSim.tgtLocalsOk i
            cases hTi : listGet stTgt.locals i with
            | none => rw [hTi] at hPrev; exact hPrev
            | some sT =>
              rw [hTi] at hPrev
              cases sT with
              | dead => exact False.elim hPrev
              | direct _ => exact hPrev
              | stack aT' =>
                rcases hPrev with ⟨hn, hof, e0, hg0, ha0⟩
                refine ⟨hn, hof, ?_⟩
                cases hEq : Nat.beq aT' aT with
                | true =>
                  have ha : aT' = aT := Nat.eq_of_beq_eq_true hEq; subst ha
                  rw [hGT] at hg0; injection hg0 with heq; subst heq
                  exact ⟨{ eT with cell := none }, listGet_listSet_eq hSetH, ha0⟩
                | false =>
                  have hne : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
                  exact ⟨e0, by rw [listGet_listSet_ne hSetH hne]; exact hg0, ha0⟩
          · intro i
            have hPrev := hSim.srcLocalsOk i
            cases hSi : listGet stSrc.locals i with
            | none =>
              cases hTi : listGet stTgt.locals i with
              | none => rw [hSi, hTi] at hPrev; exact hPrev
              | some _ => rw [hSi, hTi] at hPrev; exact False.elim hPrev
            | some sS =>
              rw [hSi] at hPrev
              cases hTi : listGet stTgt.locals i with
              | none => rw [hTi] at hPrev; cases sS <;> exact hPrev
              | some sT =>
                rw [hTi] at hPrev
                cases sS with
                | dead => trivial
                | direct _ =>
                  cases sT with
                  | dead => exact False.elim hPrev | stack _ => exact False.elim hPrev
                  | direct _ => exact hPrev
                | stack aS =>
                  cases sT with
                  | dead => exact hPrev
                  | direct _ => exact hPrev
                  | stack aT' =>
                    rcases hPrev with ⟨hn, hm, eS, e0, hgS, hg0, hEa, hEta, hOv⟩
                    refine ⟨hn, hm, eS, ?_⟩
                    cases hEq : Nat.beq aT' aT with
                    | false =>
                      have hne : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
                      exact ⟨e0, hgS, by rw [listGet_listSet_ne hSetH hne]; exact hg0, hEa, hEta, hOv⟩
                    | true =>
                      have ha : aT' = aT := Nat.eq_of_beq_eq_true hEq; subst ha
                      have hTgtI := hSim.tgtLocalsOk i; rw [hTi] at hTgtI
                      have hiLoc := hSim.targetUnique i loc aT' hTgtI.2.1 hofLoc
                      subst hiLoc; rw [hSL] at hSi; cases hSi
          · intro aS eS hgS hEa
            rcases hSim.srcHeapOk aS eS hgS hEa with ⟨i, aT', e0, hSi, hof, hm, hg0, hEta, hOv⟩
            have hne : i ≠ loc := fun hEq => by subst hEq; rw [hSL] at hSi; cases hSi
            have haNe : aT' ≠ aT := fun hEq => hne (hSim.targetUnique i loc aT (hEq ▸ hof) hofLoc)
            exact ⟨i, aT', e0, hSi, hof, hm, by rw [listGet_listSet_ne hSetH haNe]; exact hg0, hEta, hOv⟩
      | direct oS =>
        cases slotT with
        | dead => exact False.elim hLoc
        | stack _ => exact False.elim hLoc
        | direct _ =>
          dsimp only at hLoc ⊢
          rcases listSet_exists_of_get hSL (.direct none) with ⟨lsS', hSetS⟩
          rcases listSet_exists_of_get hTL (.direct none) with ⟨lsT', hSetT⟩
          rw [hSetS, hSetT]
          refine
            { pcEq := hSim.pcEq, stmtEq := hSim.stmtEq,
              lenEq := by rw [listSet_length_eq hSetS, listSet_length_eq hSetT]; exact hSim.lenEq,
              mapBounded := hSim.mapBounded,
              targetUnique := hSim.targetUnique, tgtLocalsOk := ?_, srcLocalsOk := ?_,
              srcHeapOk := ?_, aliveInj := hSim.aliveInj }
          · intro i
            have hPrev := hSim.tgtLocalsOk i
            cases hEq : Nat.beq i loc with
            | true =>
              have hil := Nat.eq_of_beq_eq_true hEq; subst hil
              rw [listGet_listSet_eq hSetT]; rw [hTL] at hPrev; exact hPrev
            | false =>
              have hne : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              rw [listGet_listSet_ne hSetT hne]; exact hPrev
          · intro i
            have hPrev := hSim.srcLocalsOk i
            cases hEq : Nat.beq i loc with
            | true =>
              have hil := Nat.eq_of_beq_eq_true hEq; subst hil
              rw [listGet_listSet_eq hSetS, listGet_listSet_eq hSetT]; exact ⟨hLoc.1, trivial⟩
            | false =>
              have hne : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              rw [listGet_listSet_ne hSetS hne, listGet_listSet_ne hSetT hne]; exact hPrev
          · intro aS eS hgS hEa
            rcases hSim.srcHeapOk aS eS hgS hEa with ⟨i, aT', e0, hSi, hof, hm, hg0, hEta, hOv⟩
            have hne : i ≠ loc := fun hEq => by subst hEq; rw [hSL] at hSi; cases hSi
            exact ⟨i, aT', e0, by rw [listGet_listSet_ne hSetS hne]; exact hSi, hof, hm, hg0, hEta, hOv⟩
      | stack aS =>
        cases slotT with
        | dead => exact False.elim hLoc
        | direct _ => exact False.elim hLoc
        | stack aT =>
          dsimp only at hLoc ⊢
          rcases hLoc with ⟨_, hmLoc, eS, eT, hGS, hGT, hEa, hEta, _⟩
          have hTgtLoc := hSim.tgtLocalsOk loc; rw [hTL] at hTgtLoc; dsimp only at hTgtLoc
          rcases listSet_exists_of_get hGS { eS with cell := none } with ⟨hS', hSetHS⟩
          rcases listSet_exists_of_get hGT { eT with cell := none } with ⟨hT', hSetHT⟩
          rw [hGS]; dsimp only; rw [hSetHS]; dsimp only; rw [hGT]; dsimp only; rw [hSetHT]; dsimp only
          refine
            { pcEq := hSim.pcEq, stmtEq := hSim.stmtEq, lenEq := hSim.lenEq,
              mapBounded := fun a t hm => by
                rw [listSet_length_eq hSetHS]; exact hSim.mapBounded a t hm,
              targetUnique := hSim.targetUnique,
              tgtLocalsOk := ?_, srcLocalsOk := ?_, srcHeapOk := ?_, aliveInj := ?_ }
          · intro i
            have hPrev := hSim.tgtLocalsOk i
            cases hTi : listGet stTgt.locals i with
            | none => rw [hTi] at hPrev; exact hPrev
            | some sT =>
              rw [hTi] at hPrev
              cases sT with
              | dead => exact False.elim hPrev
              | direct _ => exact hPrev
              | stack aT' =>
                rcases hPrev with ⟨hn, hof, e0, hg0, ha0⟩
                refine ⟨hn, hof, ?_⟩
                cases hEq : Nat.beq aT' aT with
                | true =>
                  have ha : aT' = aT := Nat.eq_of_beq_eq_true hEq; subst ha
                  rw [hGT] at hg0; injection hg0 with heq; subst heq
                  exact ⟨{ eT with cell := none }, listGet_listSet_eq hSetHT, ha0⟩
                | false =>
                  have hne : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
                  exact ⟨e0, by rw [listGet_listSet_ne hSetHT hne]; exact hg0, ha0⟩
          · intro i
            have hPrev := hSim.srcLocalsOk i
            cases hSi : listGet stSrc.locals i with
            | none =>
              cases hTi : listGet stTgt.locals i with
              | none => rw [hSi, hTi] at hPrev; exact hPrev
              | some _ => rw [hSi, hTi] at hPrev; exact False.elim hPrev
            | some sS =>
              rw [hSi] at hPrev
              cases hTi : listGet stTgt.locals i with
              | none => rw [hTi] at hPrev; cases sS <;> exact hPrev
              | some sT =>
                rw [hTi] at hPrev
                cases sS with
                | dead => trivial
                | direct _ =>
                  cases sT with
                  | dead => exact False.elim hPrev | stack _ => exact False.elim hPrev
                  | direct _ => exact hPrev
                | stack aS' =>
                  cases sT with
                  | dead => exact hPrev
                  | direct _ => exact hPrev
                  | stack aT' =>
                    rcases hPrev with ⟨hn, hm, eS0, eT0, hgS0, hgT0, hEa0, hEta0, hOv0⟩
                    refine ⟨hn, hm, ?_⟩
                    cases hEqS : Nat.beq aS' aS <;> cases hEqT : Nat.beq aT' aT
                    · have hneS : aS' ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at hEqS; cases hEqS
                      have hneT : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEqT; cases hEqT
                      exact ⟨eS0, eT0, by rw [listGet_listSet_ne hSetHS hneS]; exact hgS0,
                        by rw [listGet_listSet_ne hSetHT hneT]; exact hgT0, hEa0, hEta0, hOv0⟩
                    · have haT : aT' = aT := Nat.eq_of_beq_eq_true hEqT; subst haT
                      have hTgtI := hSim.tgtLocalsOk i; rw [hTi] at hTgtI
                      have hil := hSim.targetUnique i loc aT' hTgtI.2.1 hTgtLoc.2.1
                      subst hil; rw [hSL] at hSi; injection hSi with hsi; injection hsi with hsa
                      rw [hsa, Nat.beq_refl] at hEqS; cases hEqS
                    · have haS : aS' = aS := Nat.eq_of_beq_eq_true hEqS; subst haS
                      rw [hGS] at hgS0; injection hgS0 with hs0; subst hs0
                      have hneT : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEqT; cases hEqT
                      exact ⟨{ eS with cell := none }, eT0, listGet_listSet_eq hSetHS,
                        by rw [listGet_listSet_ne hSetHT hneT]; exact hgT0, hEa, hEta0, trivial⟩
                    · have haS : aS' = aS := Nat.eq_of_beq_eq_true hEqS
                      have haT : aT' = aT := Nat.eq_of_beq_eq_true hEqT
                      subst haS; subst haT
                      rw [hGS] at hgS0; injection hgS0 with hs0; subst hs0
                      rw [hGT] at hgT0; injection hgT0 with ht0; subst ht0
                      exact ⟨{ eS with cell := none }, { eT with cell := none },
                        listGet_listSet_eq hSetHS, listGet_listSet_eq hSetHT, hEa, hEta, trivial⟩
          · intro aS' eS' hgS' hEa'
            cases hEqS : Nat.beq aS' aS with
            | true =>
              have haS : aS' = aS := Nat.eq_of_beq_eq_true hEqS; subst haS
              rw [listGet_listSet_eq hSetHS] at hgS'; injection hgS' with heq; subst heq
              exact ⟨loc, aT, { eT with cell := none }, hSL, hTgtLoc.2.1, hmLoc,
                listGet_listSet_eq hSetHT, hEta, trivial⟩
            | false =>
              have hneS : aS' ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at hEqS; cases hEqS
              rw [listGet_listSet_ne hSetHS hneS] at hgS'
              rcases hSim.srcHeapOk aS' eS' hgS' hEa' with ⟨i, aT', e0, hSi, hof, hm, hg0, hEta0, hOv0⟩
              have haT : aT' ≠ aT := by
                intro heq; subst heq
                have hil := hSim.targetUnique i loc aT' hof hTgtLoc.2.1
                subst hil; rw [hSL] at hSi; injection hSi with hss; injection hss with hsa
                exact hneS hsa.symm
              exact ⟨i, aT', e0, hSi, hof, hm,
                by rw [listGet_listSet_ne hSetHT haT]; exact hg0, hEta0, hOv0⟩
          · intro a1 a2 aT' e1 e2 hg1 he1 hg2 he2 hm1 hm2
            have hg1' : listGet stSrc.heap a1 = some (if Nat.beq a1 aS then eS else e1) := by
              cases h1 : Nat.beq a1 aS with
              | true => have hEq := Nat.eq_of_beq_eq_true h1; subst hEq; exact hGS
              | false =>
                have hne : a1 ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at h1; cases h1
                rw [listGet_listSet_ne hSetHS hne] at hg1; exact hg1
            have hg2' : listGet stSrc.heap a2 = some (if Nat.beq a2 aS then eS else e2) := by
              cases h2 : Nat.beq a2 aS with
              | true => have hEq := Nat.eq_of_beq_eq_true h2; subst hEq; exact hGS
              | false =>
                have hne : a2 ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at h2; cases h2
                rw [listGet_listSet_ne hSetHS hne] at hg2; exact hg2
            have he1' : (if Nat.beq a1 aS then eS else e1).alive = true := by
              cases Nat.beq a1 aS with | true => exact hEa | false => exact he1
            have he2' : (if Nat.beq a2 aS then eS else e2).alive = true := by
              cases Nat.beq a2 aS with | true => exact hEa | false => exact he2
            exact hSim.aliveInj a1 a2 aT' _ _ hg1' he1' hg2' he2' hm1 hm2

theorem sim_evalOperand {cfg : EvalConfig} {stackLocals : List LocalId}
    {m : Nat → Option Nat} {targetOf : LocalId → Option AllocId}
    {stSrc stTgt : MachineState}
    (hSim : StorageSimRel stackLocals m targetOf stSrc stTgt)
    {op : Operand} {vS : Val} {stSrc1 : MachineState}
    (hEval : evalOperand cfg stSrc op = .ok (vS, stSrc1)) :
    ∃ vT stTgt1, evalOperand cfg stTgt op = .ok (vT, stTgt1) ∧
      ValSim m vS vT ∧ StorageSimRel stackLocals m targetOf stSrc1 stTgt1 := by
  cases op with
  | const c =>
    injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
    have hvs : ValSim m (constToVal c) (constToVal c) := by cases c <;> rfl
    exact ⟨constToVal c, stTgt, rfl, hvs, hSim⟩
  | copy loc =>
    dsimp only [evalOperand] at hEval ⊢
    cases hR : readLocalCell stSrc loc with
    | error _ => rw [hR] at hEval; cases hEval
    | ok _ =>
      rw [hR] at hEval; injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
      rcases sim_readLocalCell hSim hR with ⟨vT, hRT, hvs⟩
      rw [hRT]; exact ⟨vT, stTgt, rfl, hvs, hSim⟩
  | move loc =>
    dsimp only [evalOperand] at hEval ⊢
    cases hR : readLocalCell stSrc loc with
    | error _ => rw [hR] at hEval; cases hEval
    | ok _ =>
      rw [hR] at hEval; injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
      rcases sim_readLocalCell hSim hR with ⟨vT, hRT, hvs⟩
      rw [hRT]
      cases cfg.deinitMovedPlace with
      | false => exact ⟨vT, stTgt, rfl, hvs, hSim⟩
      | true => exact ⟨vT, deinitLocalCell stTgt loc, rfl, hvs, sim_deinitLocalCell hSim loc⟩

theorem sim_writeLocalCell {stackLocals : List LocalId} {m : Nat → Option Nat}
    {targetOf : LocalId → Option AllocId} {stSrc stTgt : MachineState}
    (hSim : StorageSimRel stackLocals m targetOf stSrc stTgt)
    {dst : LocalId} {vS vT : Val} (hv : ValSim m vS vT)
    {stSrc1 : MachineState} (hW : writeLocalCell stSrc dst vS = .ok stSrc1) :
    ∃ stTgt1, writeLocalCell stTgt dst vT = .ok stTgt1 ∧
      StorageSimRel stackLocals m targetOf stSrc1 stTgt1 := by
  have hLoc := hSim.srcLocalsOk dst
  unfold writeLocalCell at hW ⊢
  cases hSL : listGet stSrc.locals dst with
  | none => rw [hSL] at hW; cases hW
  | some slotS =>
    rw [hSL] at hW hLoc
    cases hTL : listGet stTgt.locals dst with
    | none => rw [hTL] at hLoc; cases slotS <;> exact False.elim hLoc
    | some slotT =>
      rw [hTL] at hLoc
      cases slotS with
      | dead => cases hW
      | direct _ =>
        cases slotT with
        | dead => exact False.elim hLoc
        | stack _ => exact False.elim hLoc
        | direct _ =>
          dsimp only at hW hLoc ⊢
          rcases listSet_exists_of_get hSL (.direct (some vS)) with ⟨lsS', hSetS⟩
          rcases listSet_exists_of_get hTL (.direct (some vT)) with ⟨lsT', hSetT⟩
          rw [hSetS] at hW; injection hW with hst; subst hst; rw [hSetT]
          refine ⟨{ stTgt with locals := lsT' }, rfl, ?_⟩
          refine
            { pcEq := hSim.pcEq, stmtEq := hSim.stmtEq,
              lenEq := by rw [listSet_length_eq hSetS, listSet_length_eq hSetT]; exact hSim.lenEq,
              mapBounded := hSim.mapBounded,
              targetUnique := hSim.targetUnique, tgtLocalsOk := ?_, srcLocalsOk := ?_,
              srcHeapOk := ?_, aliveInj := hSim.aliveInj }
          · intro i
            have hPrev := hSim.tgtLocalsOk i
            cases hEq : Nat.beq i dst with
            | true =>
              have hid := Nat.eq_of_beq_eq_true hEq; subst hid
              rw [listGet_listSet_eq hSetT]; rw [hTL] at hPrev; exact hPrev
            | false =>
              have hne : i ≠ dst := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              rw [listGet_listSet_ne hSetT hne]; exact hPrev
          · intro i
            have hPrev := hSim.srcLocalsOk i
            cases hEq : Nat.beq i dst with
            | true =>
              have hid := Nat.eq_of_beq_eq_true hEq; subst hid
              rw [listGet_listSet_eq hSetS, listGet_listSet_eq hSetT]; exact ⟨hLoc.1, hv⟩
            | false =>
              have hne : i ≠ dst := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              rw [listGet_listSet_ne hSetS hne, listGet_listSet_ne hSetT hne]; exact hPrev
          · intro aS eS hgS hEa
            rcases hSim.srcHeapOk aS eS hgS hEa with ⟨i, aT', e0, hSi, hof, hm, hg0, hEta, hOv⟩
            have hne : i ≠ dst := fun hEq => by subst hEq; rw [hSL] at hSi; cases hSi
            exact ⟨i, aT', e0, by rw [listGet_listSet_ne hSetS hne]; exact hSi, hof, hm, hg0, hEta, hOv⟩
      | stack aS =>
        cases slotT with
        | dead => exact False.elim hLoc
        | direct _ => exact False.elim hLoc
        | stack aT =>
          dsimp only at hW hLoc ⊢
          rcases hLoc with ⟨_, hmDst, eS, eT, hGS, hGT, hEa, hEta, _⟩
          have hTgtDst := hSim.tgtLocalsOk dst; rw [hTL] at hTgtDst; dsimp only at hTgtDst
          rcases listSet_exists_of_get hGS { eS with cell := some vS } with ⟨hS', hSetHS⟩
          rcases listSet_exists_of_get hGT { eT with cell := some vT } with ⟨hT', hSetHT⟩
          rw [hGS] at hW; dsimp only at hW; rw [hEa] at hW
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hW
          have hSetHS' := hSetHS; rw [hEa] at hSetHS'
          rw [hSetHS'] at hW; dsimp only at hW
          injection hW with hst; subst hst
          rw [hGT]; dsimp only; rw [hEta]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hSetHT' := hSetHT; rw [hEta] at hSetHT'
          rw [hSetHT']; dsimp only
          refine ⟨{ stTgt with heap := hT' }, rfl, ?_⟩
          refine
            { pcEq := hSim.pcEq, stmtEq := hSim.stmtEq, lenEq := hSim.lenEq,
              mapBounded := fun a t hm => by
                rw [listSet_length_eq hSetHS]; exact hSim.mapBounded a t hm,
              targetUnique := hSim.targetUnique,
              tgtLocalsOk := ?_, srcLocalsOk := ?_, srcHeapOk := ?_, aliveInj := ?_ }
          · intro i
            have hPrev := hSim.tgtLocalsOk i
            cases hTi : listGet stTgt.locals i with
            | none => rw [hTi] at hPrev; exact hPrev
            | some sT =>
              rw [hTi] at hPrev
              cases sT with
              | dead => exact False.elim hPrev
              | direct _ => exact hPrev
              | stack aT' =>
                rcases hPrev with ⟨hn, hof, e0, hg0, ha0⟩
                refine ⟨hn, hof, ?_⟩
                cases hEq : Nat.beq aT' aT with
                | true =>
                  have ha : aT' = aT := Nat.eq_of_beq_eq_true hEq; subst ha
                  rw [hGT] at hg0; injection hg0 with heq; subst heq
                  exact ⟨{ eT with cell := some vT }, listGet_listSet_eq hSetHT, ha0⟩
                | false =>
                  have hne : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
                  exact ⟨e0, by rw [listGet_listSet_ne hSetHT hne]; exact hg0, ha0⟩
          · intro i
            have hPrev := hSim.srcLocalsOk i
            cases hSi : listGet stSrc.locals i with
            | none =>
              cases hTi : listGet stTgt.locals i with
              | none => rw [hSi, hTi] at hPrev; exact hPrev
              | some _ => rw [hSi, hTi] at hPrev; exact False.elim hPrev
            | some sS =>
              rw [hSi] at hPrev
              cases hTi : listGet stTgt.locals i with
              | none => rw [hTi] at hPrev; cases sS <;> exact hPrev
              | some sT =>
                rw [hTi] at hPrev
                cases sS with
                | dead => trivial
                | direct _ =>
                  cases sT with
                  | dead => exact False.elim hPrev | stack _ => exact False.elim hPrev
                  | direct _ => exact hPrev
                | stack aS' =>
                  cases sT with
                  | dead => exact hPrev
                  | direct _ => exact hPrev
                  | stack aT' =>
                    rcases hPrev with ⟨hn, hm, eS0, eT0, hgS0, hgT0, hEa0, hEta0, hOv0⟩
                    refine ⟨hn, hm, ?_⟩
                    cases hEqS : Nat.beq aS' aS <;> cases hEqT : Nat.beq aT' aT
                    · have hneS : aS' ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at hEqS; cases hEqS
                      have hneT : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEqT; cases hEqT
                      exact ⟨eS0, eT0, by rw [listGet_listSet_ne hSetHS hneS]; exact hgS0,
                        by rw [listGet_listSet_ne hSetHT hneT]; exact hgT0, hEa0, hEta0, hOv0⟩
                    · have haT : aT' = aT := Nat.eq_of_beq_eq_true hEqT; subst haT
                      have hTgtI := hSim.tgtLocalsOk i; rw [hTi] at hTgtI
                      have hid := hSim.targetUnique i dst aT' hTgtI.2.1 hTgtDst.2.1
                      subst hid; rw [hSL] at hSi; injection hSi with hsi; injection hsi with hsa
                      rw [hsa, Nat.beq_refl] at hEqS; cases hEqS
                    · have haS : aS' = aS := Nat.eq_of_beq_eq_true hEqS; subst haS
                      have hneT : aT' ≠ aT := fun h => by subst h; rw [Nat.beq_refl] at hEqT; cases hEqT
                      have haTEq : aT' = aT := by injection (hm.symm.trans hmDst)
                      exact False.elim (hneT haTEq)
                    · have haS : aS' = aS := Nat.eq_of_beq_eq_true hEqS
                      have haT : aT' = aT := Nat.eq_of_beq_eq_true hEqT
                      subst haS; subst haT
                      rw [hGS] at hgS0; injection hgS0 with hs0; subst hs0
                      rw [hGT] at hgT0; injection hgT0 with ht0; subst ht0
                      exact ⟨{ eS with cell := some vS }, { eT with cell := some vT },
                        listGet_listSet_eq hSetHS, listGet_listSet_eq hSetHT, hEa, hEta, hv⟩
          · intro aS' eS' hgS' hEa'
            cases hEqS : Nat.beq aS' aS with
            | true =>
              have haS : aS' = aS := Nat.eq_of_beq_eq_true hEqS; subst haS
              rw [listGet_listSet_eq hSetHS] at hgS'; injection hgS' with heq; subst heq
              exact ⟨dst, aT, { eT with cell := some vT }, hSL, hTgtDst.2.1, hmDst,
                listGet_listSet_eq hSetHT, hEta, hv⟩
            | false =>
              have hneS : aS' ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at hEqS; cases hEqS
              rw [listGet_listSet_ne hSetHS hneS] at hgS'
              rcases hSim.srcHeapOk aS' eS' hgS' hEa' with ⟨i, aT', e0, hSi, hof, hm, hg0, hEta0, hOv0⟩
              have haT : aT' ≠ aT := by
                intro heq; subst heq
                have hid := hSim.targetUnique i dst aT' hof hTgtDst.2.1
                subst hid; rw [hSL] at hSi; injection hSi with hss; injection hss with hsa
                exact hneS hsa.symm
              exact ⟨i, aT', e0, hSi, hof, hm,
                by rw [listGet_listSet_ne hSetHT haT]; exact hg0, hEta0, hOv0⟩
          · intro a1 a2 aT' e1 e2 hg1 he1 hg2 he2 hm1 hm2
            have hg1' : listGet stSrc.heap a1 = some (if Nat.beq a1 aS then eS else e1) := by
              cases h1 : Nat.beq a1 aS with
              | true => have hEq := Nat.eq_of_beq_eq_true h1; subst hEq; exact hGS
              | false =>
                have hne : a1 ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at h1; cases h1
                rw [listGet_listSet_ne hSetHS hne] at hg1; exact hg1
            have hg2' : listGet stSrc.heap a2 = some (if Nat.beq a2 aS then eS else e2) := by
              cases h2 : Nat.beq a2 aS with
              | true => have hEq := Nat.eq_of_beq_eq_true h2; subst hEq; exact hGS
              | false =>
                have hne : a2 ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at h2; cases h2
                rw [listGet_listSet_ne hSetHS hne] at hg2; exact hg2
            have he1' : (if Nat.beq a1 aS then eS else e1).alive = true := by
              cases Nat.beq a1 aS with | true => exact hEa | false => exact he1
            have he2' : (if Nat.beq a2 aS then eS else e2).alive = true := by
              cases Nat.beq a2 aS with | true => exact hEa | false => exact he2
            exact hSim.aliveInj a1 a2 aT' _ _ hg1' he1' hg2' he2' hm1 hm2

theorem sim_evalRvalue {cfg : EvalConfig} {stackLocals : List LocalId}
    {m : Nat → Option Nat} {targetOf : LocalId → Option AllocId}
    {stSrc stTgt : MachineState}
    (hSim : StorageSimRel stackLocals m targetOf stSrc stTgt)
    {rv : Rvalue} {vS : Val} {stSrc1 : MachineState}
    (hEval : evalRvalue cfg stSrc rv = .ok (vS, stSrc1)) :
    ∃ vT stTgt1, evalRvalue cfg stTgt rv = .ok (vT, stTgt1) ∧
      ValSim m vS vT ∧ StorageSimRel stackLocals m targetOf stSrc1 stTgt1 := by
  cases rv with
  | use op => exact sim_evalOperand hSim hEval
  | subtypeCast op => exact sim_evalOperand hSim hEval
  | binOp k lhs rhs =>
    dsimp only [evalRvalue] at hEval ⊢
    cases hL : evalOperand cfg stSrc lhs with
    | error _ => rw [hL] at hEval; cases hEval
    | ok lpair =>
      rcases lpair with ⟨lv, stS1⟩
      rw [hL] at hEval; dsimp only at hEval
      rcases sim_evalOperand hSim hL with ⟨lT, stTgt1, hLT, hlSim, hSim1⟩
      rw [hLT]; dsimp only
      cases hR : evalOperand cfg stS1 rhs with
      | error _ => rw [hR] at hEval; cases hEval
      | ok rpair =>
        rcases rpair with ⟨rvVal, stS2⟩
        rw [hR] at hEval; dsimp only at hEval
        rcases sim_evalOperand hSim1 hR with ⟨rT, stTgt2, hRT, hrSim, hSim2⟩
        rw [hRT]; dsimp only
        cases hB : evalBinOp k lv rvVal with
        | error _ => rw [hB] at hEval; cases hEval
        | ok resS =>
          rw [hB] at hEval; dsimp only at hEval; injection hEval with hp; injection hp with hres hst; subst hres; subst hst
          rcases valSim_binOp hlSim hrSim hB with ⟨resT, hBT, hresSim⟩
          rw [hBT]; exact ⟨resT, stTgt2, rfl, hresSim, hSim2⟩
  | addrOf loc =>
    dsimp only [evalRvalue] at hEval ⊢
    have hLoc := hSim.srcLocalsOk loc
    cases hSL : listGet stSrc.locals loc with
    | none => rw [hSL] at hEval; cases hEval
    | some sS =>
      rw [hSL] at hEval hLoc
      cases sS with
      | dead => cases hEval
      | direct _ => cases hEval
      | stack aS =>
        cases hTL : listGet stTgt.locals loc with
        | none => rw [hTL] at hLoc; exact False.elim hLoc
        | some sT =>
          rw [hTL] at hLoc
          cases sT with
          | dead => exact False.elim hLoc
          | direct _ => exact False.elim hLoc
          | stack aT =>
            dsimp only at hEval hLoc ⊢
            rcases hLoc with ⟨_, hm, eS, eT, hGS, hGT, hEa, hEta, _⟩
            rw [hGS] at hEval; simp only [hEa, ↓reduceIte] at hEval
            injection hEval with hp; injection hp with hv hs; subst hv; subst hs
            rw [hGT]; simp only [hEta, ↓reduceIte]; exact ⟨.ptr aT, stTgt, rfl, hm, hSim⟩
  | derefPtr ptrOp =>
    dsimp only [evalRvalue] at hEval ⊢
    cases hP : evalOperand cfg stSrc ptrOp with
    | error _ => rw [hP] at hEval; cases hEval
    | ok ppair =>
      rcases ppair with ⟨pv, ps⟩
      rw [hP] at hEval
      rcases sim_evalOperand hSim hP with ⟨pT, stTgt1, hPT, hpSim, hSim1⟩
      rw [hPT]
      cases pv with
      | int _ => cases hEval
      | bool _ => cases hEval
      | staticPtr _ => cases hEval
      | ptr aS =>
        cases pT with
        | int _ => exact False.elim hpSim
        | bool _ => exact False.elim hpSim
        | staticPtr _ => exact False.elim hpSim
        | ptr aT =>
          dsimp only at hEval ⊢
          cases hGS : listGet ps.heap aS with
          | none => rw [hGS] at hEval; cases hEval
          | some eS =>
            rw [hGS] at hEval; dsimp only at hEval
            cases hEa : eS.alive with
            | false => rw [hEa] at hEval; cases hEval
            | true =>
              rw [hEa] at hEval
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hEval
              rcases hSim1.srcHeapOk aS eS hGS hEa with ⟨_, aT', eT, _, _, hm', hGT, hEta, hCell⟩
              have haEq : aT' = aT := by
                have h1 : some aT' = some aT := hm'.symm.trans hpSim
                injection h1
              subst haEq
              rw [hGT]; dsimp only; rw [hEta]
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              cases hEC : eS.cell with
              | none => rw [hEC] at hEval; cases hEval
              | some _ =>
                rw [hEC] at hEval hCell; dsimp only at hEval
                injection hEval with hp; injection hp with hv hs; subst hv; subst hs
                cases hTC : eT.cell with
                | none => rw [hTC] at hCell; exact False.elim hCell
                | some vT0 => rw [hTC] at hCell; exact ⟨vT0, stTgt1, rfl, hCell, hSim1⟩
  | discr loc =>
    dsimp only [evalRvalue] at hEval ⊢
    cases hR : readLocalCell stSrc loc with
    | error _ => rw [hR] at hEval; cases hEval
    | ok vS0 =>
      rw [hR] at hEval
      rcases sim_readLocalCell hSim hR with ⟨vT, hRT, hvSim⟩
      rw [hRT]
      cases vS0 with
      | bool _ => cases hEval
      | staticPtr _ => cases hEval
      | ptr _ => cases hEval
      | int n =>
        cases vT with
        | bool _ => exact False.elim hvSim
        | staticPtr _ => exact False.elim hvSim
        | ptr _ => exact False.elim hvSim
        | int k =>
          have hnk : n = k := hvSim; subst hnk
          dsimp only at hEval ⊢
          cases hNonneg : decide (0 ≤ n) with
          | false => rw [hNonneg] at hEval; cases hEval
          | true =>
            rw [hNonneg] at hEval
            injection hEval with hp; injection hp with hv hs; subst hv; subst hs
            exact ⟨.int n, stTgt, rfl, rfl, hSim⟩

theorem sim_stepStmt_strip {cfg : EvalConfig} {body : Body}
    {m : Nat → Option Nat} {targetOf : LocalId → Option AllocId}
    {stSrc stTgt : MachineState}
    (hSim : StorageSimRel body.stackBackedLocals m targetOf stSrc stTgt)
    {s : Stmt} {stSrc1 : MachineState}
    (hStep : stepStmt cfg body stSrc s = .ok stSrc1) :
    ∃ m' stTgt1,
      stepStmt cfg (passRemoveStorageMarkers body) stTgt (stripStorageStmt s) = .ok stTgt1 ∧
      StorageSimRel (passRemoveStorageMarkers body).stackBackedLocals m' targetOf stSrc1 stTgt1 := by
  cases s with
  | nop =>
    injection hStep with hst; subst hst
    exact ⟨m, { stTgt with stmtIdx := stTgt.stmtIdx + 1 }, rfl,
      { pcEq := hSim.pcEq, stmtEq := congrArg Nat.succ hSim.stmtEq, lenEq := hSim.lenEq,
        mapBounded := hSim.mapBounded,
        targetUnique := hSim.targetUnique, tgtLocalsOk := hSim.tgtLocalsOk,
        srcLocalsOk := hSim.srcLocalsOk, srcHeapOk := hSim.srcHeapOk, aliveInj := hSim.aliveInj }⟩
  | storageLive loc =>
    dsimp only [stepStmt, stripStorageStmt] at hStep ⊢
    have hLoc := hSim.srcLocalsOk loc
    cases hSL : listGet stSrc.locals loc with
    | none => rw [hSL] at hStep; cases hStep
    | some oldSlot =>
      rw [hSL] at hStep hLoc
      dsimp only at hStep
      cases hTL : listGet stTgt.locals loc with
      | none => rw [hTL] at hLoc; cases oldSlot <;> exact False.elim hLoc
      | some slotT =>
        rw [hTL] at hLoc
        have hTgtLoc := hSim.tgtLocalsOk loc; rw [hTL] at hTgtLoc
        cases hIn : natInList loc body.stackBackedLocals with
        | false =>
          rw [hIn] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep
          rcases listSet_exists_of_get hSL (.direct none) with ⟨lsS', hSetS⟩
          rw [hSetS] at hStep; injection hStep with hst; subst hst
          have hNoOldStack : slotAidOpt oldSlot = none := by
            cases oldSlot with
            | dead => rfl | direct _ => rfl
            | stack _ =>
              cases slotT with
              | dead => exact False.elim hLoc | direct _ => exact False.elim hLoc
              | stack _ => rw [hLoc.1] at hIn; cases hIn
          have hFreeEq : freeHeapOpt stSrc.heap (slotAidOpt oldSlot) = stSrc.heap := by
            rw [hNoOldStack]; rfl
          have hSlotTDirect : ∃ oT, slotT = .direct oT := by
            cases slotT with
            | dead => exact False.elim hTgtLoc | direct oT => exact ⟨oT, rfl⟩
            | stack _ => rw [hTgtLoc.1] at hIn; cases hIn
          rcases hSlotTDirect with ⟨oT, hST⟩
          refine ⟨m, { stTgt with stmtIdx := stTgt.stmtIdx + 1 }, rfl, ?_⟩
          refine
            { pcEq := hSim.pcEq, stmtEq := congrArg Nat.succ hSim.stmtEq,
              lenEq := by rw [listSet_length_eq hSetS]; exact hSim.lenEq,
              mapBounded := fun a t hm => by rw [hFreeEq]; exact hSim.mapBounded a t hm,
              targetUnique := hSim.targetUnique,
              tgtLocalsOk := hSim.tgtLocalsOk, srcLocalsOk := ?_, srcHeapOk := ?_,
              aliveInj := fun a1 a2 aT' e1 e2 hg1 he1 hg2 he2 hm1 hm2 => by
                rw [hFreeEq] at hg1 hg2; exact hSim.aliveInj a1 a2 aT' e1 e2 hg1 he1 hg2 he2 hm1 hm2 }
          · intro i
            cases hEq : Nat.beq i loc with
            | true =>
              have hil := Nat.eq_of_beq_eq_true hEq; subst hil
              rw [listGet_listSet_eq hSetS, hTL, hST]; exact ⟨hIn, trivial⟩
            | false =>
              have hne : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              rw [listGet_listSet_ne hSetS hne, hFreeEq]; exact hSim.srcLocalsOk i
          · intro aS eS hgS hEa
            rw [hFreeEq] at hgS
            rcases hSim.srcHeapOk aS eS hgS hEa with ⟨i, aT', e0, hSi, hof, hm, hg0, hEta, hOv⟩
            have hne : i ≠ loc := by
              intro hEq; subst hEq; rw [hSL] at hSi; injection hSi with hs
              rw [hs] at hNoOldStack
              cases hNoOldStack
            exact ⟨i, aT', e0, by rw [listGet_listSet_ne hSetS hne]; exact hSi, hof, hm, hg0, hEta, hOv⟩
        | true =>
          rw [hIn] at hStep; simp only [↓reduceIte] at hStep
          have hSlotTStack : ∃ aT, slotT = .stack aT := by
            cases slotT with
            | dead => exact False.elim hTgtLoc | direct _ => rw [hTgtLoc.1] at hIn; cases hIn
            | stack aT => exact ⟨aT, rfl⟩
          rcases hSlotTStack with ⟨aT, hST⟩; subst hST
          rcases hTgtLoc with ⟨_, hofLoc, eT, hGT, hEta⟩
          rcases listSet_exists_of_get hSL (.stack (freeHeapOpt stSrc.heap (slotAidOpt oldSlot)).length) with ⟨lsS', hSetS⟩
          dsimp only [allocHeap] at hStep
          rw [hSetS] at hStep; injection hStep with hst; subst hst
          let h1 := freeHeapOpt stSrc.heap (slotAidOpt oldSlot)
          let aidNew := h1.length
          let m' : Nat → Option Nat := fun a => if Nat.beq a aidNew then some aT else m a
          have hAidLen : aidNew = stSrc.heap.length := freeHeapOpt_length stSrc.heap (slotAidOpt oldSlot)
          have hMono : ∀ a t, m a = some t → m' a = some t := by
            intro a t hm
            have hlt : a < aidNew := hAidLen.symm ▸ hSim.mapBounded a t hm
            have hne : a ≠ aidNew := Nat.ne_of_lt hlt
            dsimp [m']; rw [nat_beq_false_of_ne hne]; exact hm
          have hNewMap : m' aidNew = some aT := by dsimp [m']; rw [Nat.beq_refl]; simp only [↓reduceIte]
          have hOldDead : ∀ a e, listGet h1 a = some e → e.alive = true → a < aidNew ∧ slotAidOpt oldSlot ≠ some a := by
            intro a e hg ha
            exact ⟨listGet_length_lt hg, (freeHeapOpt_alive_preserved hg ha).1⟩
          refine ⟨m', { stTgt with stmtIdx := stTgt.stmtIdx + 1 }, rfl, ?_⟩
          refine
            { pcEq := hSim.pcEq, stmtEq := congrArg Nat.succ hSim.stmtEq,
              lenEq := by rw [listSet_length_eq hSetS]; exact hSim.lenEq,
              mapBounded := ?_, targetUnique := hSim.targetUnique,
              tgtLocalsOk := hSim.tgtLocalsOk, srcLocalsOk := ?_, srcHeapOk := ?_, aliveInj := ?_ }
          · intro a t hm
            dsimp [m'] at hm
            cases hEq : Nat.beq a aidNew with
            | true =>
              have ha := Nat.eq_of_beq_eq_true hEq; subst ha
              exact listGet_length_lt (listGet_append_exact h1 _)
            | false =>
              rw [hEq] at hm
              have hlt : a < aidNew := hAidLen.symm ▸ hSim.mapBounded a t hm
              exact Nat.lt_trans hlt (by dsimp [allocHeap]; rw [List.length_append]; exact Nat.lt_succ_self _)
          · intro i
            cases hEq : Nat.beq i loc with
            | true =>
              have hil := Nat.eq_of_beq_eq_true hEq; subst hil
              rw [listGet_listSet_eq hSetS, hTL]
              refine ⟨hIn, hNewMap, { alive := true, cell := none }, eT,
                listGet_append_exact h1 _, hGT, rfl, hEta, trivial⟩
            | false =>
              have hne : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              have hPrev := hSim.srcLocalsOk i
              rw [listGet_listSet_ne hSetS hne]
              cases hSi : listGet stSrc.locals i with
              | none => rw [hSi] at hPrev; cases hTi : listGet stTgt.locals i with | none => trivial | some _ => rw [hTi] at hPrev; exact False.elim hPrev
              | some sS =>
                rw [hSi] at hPrev
                cases hTi : listGet stTgt.locals i with
                | none => rw [hTi] at hPrev; cases sS <;> exact False.elim hPrev
                | some sT =>
                  rw [hTi] at hPrev
                  cases sS with
                  | dead => trivial
                  | direct oS =>
                    cases sT with
                    | dead => exact False.elim hPrev | stack _ => exact False.elim hPrev
                    | direct oT => exact ⟨hPrev.1, optValSim_mono hMono hPrev.2⟩
                  | stack aS =>
                    cases sT with
                    | dead => exact False.elim hPrev | direct _ => exact False.elim hPrev
                    | stack aT' =>
                      rcases hPrev with ⟨hn, hm, eS, eT', hGS, hGT', hEa, hEta', hOv⟩
                      have hTgtI := hSim.tgtLocalsOk i; rw [hTi] at hTgtI
                      have hNotOld : slotAidOpt oldSlot ≠ some aS := by
                        intro hEqOld
                        cases oldSlot with
                        | dead => cases hEqOld | direct _ => cases hEqOld
                        | stack aOld =>
                          injection hEqOld with haEq
                          have hmOld : m aS = some aT := haEq ▸ hLoc.2.1
                          have haTEq : some aT' = some aT := hm.symm.trans hmOld
                          injection haTEq with htEq; subst htEq
                          exact hne (hSim.targetUnique i loc aT' hTgtI.2.1 hofLoc)
                      have haSlt : aS < aidNew := hAidLen.symm ▸ hSim.mapBounded aS aT' hm
                      have hG1 : listGet h1 aS = some eS := by
                        rw [freeHeapOpt_get_ne stSrc.heap (slotAidOpt oldSlot) hNotOld]; exact hGS
                      refine ⟨hn, hMono aS aT' hm, eS, eT',
                        by dsimp [allocHeap]; rw [listGet_append_left h1 _ haSlt]; exact hG1,
                        hGT', hEa, hEta', optValSim_mono hMono hOv⟩
          · intro aS eS hgS hEa
            dsimp [allocHeap] at hgS
            cases hEq : Nat.beq aS aidNew with
            | true =>
              have ha := Nat.eq_of_beq_eq_true hEq; subst ha
              rw [listGet_append_exact h1 _] at hgS; injection hgS with he; subst he
              exact ⟨loc, aT, eT, listGet_listSet_eq hSetS, hofLoc, hNewMap, hGT, hEta, trivial⟩
            | false =>
              have hneA : aS ≠ aidNew := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
              have hltLen : aS < h1.length + 1 := by
                have hL := listGet_length_lt hgS; rw [List.length_append] at hL; exact hL
              have haSlt : aS < h1.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hltLen) hneA
              rw [listGet_append_left h1 _ haSlt] at hgS
              have hPrev := freeHeapOpt_alive_preserved hgS hEa
              rcases hSim.srcHeapOk aS eS hPrev.2 hEa with ⟨i, aT', eT', hSi, hof, hm, hGT', hEta', hOv⟩
              have hneLoc : i ≠ loc := by
                intro hil; subst hil; rw [hSL] at hSi; injection hSi with hsi
                rw [hsi] at hPrev; exact hPrev.1 rfl
              exact ⟨i, aT', eT', by rw [listGet_listSet_ne hSetS hneLoc]; exact hSi,
                hof, hMono aS aT' hm, hGT', hEta', optValSim_mono hMono hOv⟩
          · intro a1 a2 aT' e1 e2 hg1 he1 hg2 he2 hm1 hm2
            dsimp [allocHeap] at hg1 hg2
            cases h1Eq : Nat.beq a1 aidNew <;> cases h2Eq : Nat.beq a2 aidNew
            · have hn1 : a1 ≠ aidNew := fun h => by subst h; rw [Nat.beq_refl] at h1Eq; cases h1Eq
              have hn2 : a2 ≠ aidNew := fun h => by subst h; rw [Nat.beq_refl] at h2Eq; cases h2Eq
              have hl1 : a1 < h1.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by have h := listGet_length_lt hg1; rw [List.length_append] at h; exact h)) hn1
              have hl2 : a2 < h1.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by have h := listGet_length_lt hg2; rw [List.length_append] at h; exact h)) hn2
              rw [listGet_append_left h1 _ hl1] at hg1
              rw [listGet_append_left h1 _ hl2] at hg2
              dsimp [m'] at hm1 hm2; rw [h1Eq] at hm1; rw [h2Eq] at hm2
              exact hSim.aliveInj a1 a2 aT' e1 e2 (freeHeapOpt_alive_preserved hg1 he1).2
                he1 (freeHeapOpt_alive_preserved hg2 he2).2 he2 hm1 hm2
            · have hn1 : a1 ≠ aidNew := fun h => by subst h; rw [Nat.beq_refl] at h1Eq; cases h1Eq
              have ha2 := Nat.eq_of_beq_eq_true h2Eq; subst ha2
              have hl1 : a1 < h1.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by have h := listGet_length_lt hg1; rw [List.length_append] at h; exact h)) hn1
              rw [listGet_append_left h1 _ hl1] at hg1
              dsimp [m'] at hm1 hm2; rw [h1Eq] at hm1; rw [Nat.beq_refl] at hm2
              simp only [↓reduceIte] at hm2
              have haT' : aT = aT' := by injection hm2
              have hP1 := freeHeapOpt_alive_preserved hg1 he1
              rcases hSim.srcHeapOk a1 e1 hP1.2 he1 with ⟨i, aTi, _, hSi, hof, hm1', _, _, _⟩
              have haTiEq : aTi = aT' := by
                have h := hm1'.symm.trans hm1
                injection h
              have hTgtI := hSim.tgtLocalsOk i
              have hil := hSim.targetUnique i loc aT (haT' ▸ haTiEq ▸ hof) hofLoc
              subst hil; rw [hSL] at hSi; injection hSi with hsi
              rw [hsi] at hP1; exact False.elim (hP1.1 rfl)
            · have ha1 := Nat.eq_of_beq_eq_true h1Eq; subst ha1
              have hn2 : a2 ≠ aidNew := fun h => by subst h; rw [Nat.beq_refl] at h2Eq; cases h2Eq
              have hl2 : a2 < h1.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by have h := listGet_length_lt hg2; rw [List.length_append] at h; exact h)) hn2
              rw [listGet_append_left h1 _ hl2] at hg2
              dsimp [m'] at hm1 hm2; rw [Nat.beq_refl] at hm1; rw [h2Eq] at hm2
              simp only [↓reduceIte] at hm1
              have haT' : aT = aT' := by injection hm1
              have hP2 := freeHeapOpt_alive_preserved hg2 he2
              rcases hSim.srcHeapOk a2 e2 hP2.2 he2 with ⟨i, aTi, _, hSi, hof, hm2', _, _, _⟩
              have haTiEq : aTi = aT' := by
                have h := hm2'.symm.trans hm2
                injection h
              have hil := hSim.targetUnique i loc aT (haT' ▸ haTiEq ▸ hof) hofLoc
              subst hil; rw [hSL] at hSi; injection hSi with hsi
              rw [hsi] at hP2; exact False.elim (hP2.1 rfl)
            · have ha1 := Nat.eq_of_beq_eq_true h1Eq
              have ha2 := Nat.eq_of_beq_eq_true h2Eq
              exact ha1.trans ha2.symm
  | storageDead loc =>
    dsimp only [stepStmt, stripStorageStmt] at hStep ⊢
    cases hZ : Nat.beq loc 0 with
    | true => rw [hZ] at hStep; cases hStep
    | false =>
      rw [hZ] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep
      have hLoc := hSim.srcLocalsOk loc
      cases hSL : listGet stSrc.locals loc with
      | none => rw [hSL] at hStep; cases hStep
      | some oldSlot =>
        rw [hSL] at hStep hLoc
        dsimp only at hStep hLoc
        rcases listSet_exists_of_get hSL .dead with ⟨lsS', hSetS⟩
        rw [hSetS] at hStep; injection hStep with hst; subst hst
        refine ⟨m, { stTgt with stmtIdx := stTgt.stmtIdx + 1 }, rfl, ?_⟩
        refine
          { pcEq := hSim.pcEq, stmtEq := congrArg Nat.succ hSim.stmtEq,
            lenEq := by rw [listSet_length_eq hSetS]; exact hSim.lenEq,
            mapBounded := fun a t hm => by rw [freeHeapOpt_length]; exact hSim.mapBounded a t hm,
            targetUnique := hSim.targetUnique,
            tgtLocalsOk := hSim.tgtLocalsOk, srcLocalsOk := ?_, srcHeapOk := ?_, aliveInj := ?_ }
        · intro i
          cases hEq : Nat.beq i loc with
          | true =>
            have hil := Nat.eq_of_beq_eq_true hEq; subst hil
            rw [listGet_listSet_eq hSetS]; dsimp only
            cases hTi : listGet stTgt.locals i with
            | none => rw [hTi] at hLoc; cases oldSlot <;> exact False.elim hLoc
            | some sT => cases sT <;> dsimp only <;> trivial
          | false =>
            have hne : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
            have hPrev := hSim.srcLocalsOk i
            rw [listGet_listSet_ne hSetS hne]
            cases hSi : listGet stSrc.locals i with
            | none =>
              cases hTi : listGet stTgt.locals i with
              | none => rw [hSi, hTi] at hPrev; exact hPrev
              | some _ => rw [hSi, hTi] at hPrev; exact False.elim hPrev
            | some sS =>
              rw [hSi] at hPrev
              cases hTi : listGet stTgt.locals i with
              | none => rw [hTi] at hPrev; cases sS <;> exact False.elim hPrev
              | some sT =>
                rw [hTi] at hPrev
                cases sS with
                | dead => cases sT <;> trivial
                | direct _ =>
                  cases sT with
                  | dead => exact False.elim hPrev
                  | stack _ => exact False.elim hPrev
                  | direct _ => dsimp only at hPrev ⊢; exact hPrev
                | stack aS =>
                  cases sT with
                  | dead => exact hPrev | direct _ => exact hPrev
                  | stack aT' =>
                    rcases hPrev with ⟨hn, hm, eS, eT', hGS, hGT', hEa, hEta', hOv⟩
                    have hNotOld : slotAidOpt oldSlot ≠ some aS := by
                      intro hEqOld
                      cases oldSlot with
                      | dead => cases hEqOld | direct _ => cases hEqOld
                      | stack aOld =>
                        injection hEqOld with haEq; subst haEq
                        cases hTL : listGet stTgt.locals loc with
                        | none => rw [hTL] at hLoc; exact False.elim hLoc
                        | some sTL =>
                          rw [hTL] at hLoc
                          cases sTL with
                          | dead => exact False.elim hLoc | direct _ => exact False.elim hLoc
                          | stack aTL =>
                            have hTgtLoc := hSim.tgtLocalsOk loc; rw [hTL] at hTgtLoc
                            have hTgtI := hSim.tgtLocalsOk i; rw [hTi] at hTgtI
                            have haEq2 : aT' = aTL := by injection (hm.symm.trans hLoc.2.1)
                            exact hne (hSim.targetUnique i loc aTL (haEq2 ▸ hTgtI.2.1) hTgtLoc.2.1)
                    refine ⟨hn, hm, eS, eT', ?_, hGT', hEa, hEta', hOv⟩
                    rw [freeHeapOpt_get_ne stSrc.heap (slotAidOpt oldSlot) hNotOld]; exact hGS
        · intro aS eS hgS hEa
          have hP := freeHeapOpt_alive_preserved hgS hEa
          rcases hSim.srcHeapOk aS eS hP.2 hEa with ⟨i, aT', eT', hSi, hof, hm, hGT', hEta', hOv⟩
          have hne : i ≠ loc := by
            intro hil; subst hil; rw [hSL] at hSi; injection hSi with hsi
            rw [hsi] at hP; exact hP.1 rfl
          exact ⟨i, aT', eT', by rw [listGet_listSet_ne hSetS hne]; exact hSi, hof, hm, hGT', hEta', hOv⟩
        · intro a1 a2 aT' e1 e2 hg1 he1 hg2 he2 hm1 hm2
          exact hSim.aliveInj a1 a2 aT' e1 e2
            (freeHeapOpt_alive_preserved hg1 he1).2 he1
            (freeHeapOpt_alive_preserved hg2 he2).2 he2 hm1 hm2
  | assign dst rv =>
    dsimp only [stepStmt, stripStorageStmt] at hStep ⊢
    cases hR : evalRvalue cfg stSrc rv with
    | error _ => rw [hR] at hStep; cases hStep
    | ok pair =>
      rcases pair with ⟨vrv, srv⟩
      rw [hR] at hStep; dsimp only at hStep
      rcases sim_evalRvalue hSim hR with ⟨vT, stTgt1, hRT, hvSim, hSim1⟩
      rw [hRT]; dsimp only
      cases hW : writeLocalCell srv dst vrv with
      | error _ => rw [hW] at hStep; cases hStep
      | ok stSrc2 =>
        rw [hW] at hStep; dsimp only at hStep; injection hStep with hst; subst hst
        rcases sim_writeLocalCell hSim1 hvSim hW with ⟨stTgt2, hWT, hSim2⟩
        rw [hWT]; dsimp only
        exact ⟨m, { stTgt2 with stmtIdx := stTgt2.stmtIdx + 1 }, rfl,
          { pcEq := hSim2.pcEq, stmtEq := congrArg Nat.succ hSim2.stmtEq, lenEq := hSim2.lenEq,
            mapBounded := hSim2.mapBounded,
            targetUnique := hSim2.targetUnique, tgtLocalsOk := hSim2.tgtLocalsOk,
            srcLocalsOk := hSim2.srcLocalsOk, srcHeapOk := hSim2.srcHeapOk, aliveInj := hSim2.aliveInj }⟩
  | storePtr ptrOp valOp =>
    dsimp only [stepStmt, stripStorageStmt] at hStep ⊢
    cases hP : evalOperand cfg stSrc ptrOp with
    | error _ => rw [hP] at hStep; cases hStep
    | ok ppair =>
      rcases ppair with ⟨pv, ps⟩
      rw [hP] at hStep
      rcases sim_evalOperand hSim hP with ⟨pT, stTgt1, hPT, hpSim, hSim1⟩
      rw [hPT]
      cases pv with
      | int _ => cases hStep
      | bool _ => cases hStep
      | staticPtr _ => cases hStep
      | ptr aS =>
        cases pT with
        | int _ => exact False.elim hpSim | bool _ => exact False.elim hpSim | staticPtr _ => exact False.elim hpSim
        | ptr aT =>
          dsimp only at hStep ⊢
          cases hV : evalOperand cfg ps valOp with
          | error _ => rw [hV] at hStep; cases hStep
          | ok vpair =>
            rcases vpair with ⟨vv, vs⟩
            rw [hV] at hStep; dsimp only at hStep
            rcases sim_evalOperand hSim1 hV with ⟨vT, stTgt2, hVT, hvSim, hSim2⟩
            rw [hVT]
            cases hGS : listGet vs.heap aS with
            | none => rw [hGS] at hStep; cases hStep
            | some eS =>
              rw [hGS] at hStep; dsimp only at hStep
              cases hEa : eS.alive with
              | false => rw [hEa] at hStep; cases hStep
              | true =>
                rw [hEa] at hStep; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
                rcases hSim2.srcHeapOk aS eS hGS hEa with ⟨owner, aT', eT, hSOwn, hofOwn, hm', hGT, hEta, _⟩
                have haEq : aT' = aT := by injection (hm'.symm.trans hpSim)
                subst haEq
                rcases listSet_exists_of_get hGS { eS with cell := some vv } with ⟨hS', hSetHS⟩
                rcases listSet_exists_of_get hGT { eT with cell := some vT } with ⟨hT', hSetHT⟩
                have hSetHS' := hSetHS; rw [hEa] at hSetHS'
                rw [hSetHS'] at hStep; dsimp only at hStep; injection hStep with hst; subst hst
                dsimp only; rw [hGT]; dsimp only; rw [hEta]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                have hSetHT' := hSetHT; rw [hEta] at hSetHT'
                rw [hSetHT']; dsimp only
                refine ⟨m, { stTgt2 with heap := hT', stmtIdx := stTgt2.stmtIdx + 1 }, rfl, ?_⟩
                refine
                  { pcEq := hSim2.pcEq, stmtEq := congrArg Nat.succ hSim2.stmtEq, lenEq := hSim2.lenEq,
                    mapBounded := fun a t hm => by rw [listSet_length_eq hSetHS]; exact hSim2.mapBounded a t hm,
                    targetUnique := hSim2.targetUnique,
                    tgtLocalsOk := ?_, srcLocalsOk := ?_, srcHeapOk := ?_, aliveInj := ?_ }
                · intro i
                  have hPrev := hSim2.tgtLocalsOk i
                  cases hTi : listGet stTgt2.locals i with
                  | none => rw [hTi] at hPrev; exact hPrev
                  | some sT =>
                    rw [hTi] at hPrev
                    cases sT with
                    | dead => exact False.elim hPrev | direct _ => exact hPrev
                    | stack aT0 =>
                      rcases hPrev with ⟨hn, hof, e0, hg0, ha0⟩
                      refine ⟨hn, hof, ?_⟩
                      cases hEq : Nat.beq aT0 aT' with
                      | true =>
                        have ha := Nat.eq_of_beq_eq_true hEq; subst ha
                        rw [hGT] at hg0; injection hg0 with heq; subst heq
                        exact ⟨{ eT with cell := some vT }, listGet_listSet_eq hSetHT, ha0⟩
                      | false =>
                        have hne : aT0 ≠ aT' := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
                        exact ⟨e0, by rw [listGet_listSet_ne hSetHT hne]; exact hg0, ha0⟩
                · intro i
                  have hPrev := hSim2.srcLocalsOk i
                  cases hSi : listGet vs.locals i with
                  | none =>
                    cases hTi : listGet stTgt2.locals i with
                    | none => rw [hSi, hTi] at hPrev; exact hPrev
                    | some _ => rw [hSi, hTi] at hPrev; exact False.elim hPrev
                  | some sS =>
                    rw [hSi] at hPrev
                    cases hTi : listGet stTgt2.locals i with
                    | none => rw [hTi] at hPrev; cases sS <;> exact hPrev
                    | some sT =>
                      rw [hTi] at hPrev
                      cases sS with
                      | dead => trivial
                      | direct _ =>
                        cases sT with
                        | dead => exact False.elim hPrev | stack _ => exact False.elim hPrev
                        | direct _ => exact hPrev
                      | stack aS0 =>
                        cases sT with
                        | dead => exact False.elim hPrev | direct _ => exact False.elim hPrev
                        | stack aT0 =>
                          rcases hPrev with ⟨hn, hm, eS0, eT0, hgS0, hgT0, hEa0, hEta0, hOv0⟩
                          refine ⟨hn, hm, ?_⟩
                          cases hEqS : Nat.beq aS0 aS <;> cases hEqT : Nat.beq aT0 aT'
                          · have hnS : aS0 ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at hEqS; cases hEqS
                            have hnT : aT0 ≠ aT' := fun h => by subst h; rw [Nat.beq_refl] at hEqT; cases hEqT
                            exact ⟨eS0, eT0, by rw [listGet_listSet_ne hSetHS hnS]; exact hgS0,
                              by rw [listGet_listSet_ne hSetHT hnT]; exact hgT0, hEa0, hEta0, hOv0⟩
                          · have haT := Nat.eq_of_beq_eq_true hEqT; subst haT
                            have hTgtI := hSim2.tgtLocalsOk i; rw [hTi] at hTgtI
                            have hio := hSim2.targetUnique i owner aT0 hTgtI.2.1 hofOwn
                            subst hio; rw [hSOwn] at hSi; injection hSi with hsi; injection hsi with hsa
                            rw [hsa, Nat.beq_refl] at hEqS; cases hEqS
                          · have haS := Nat.eq_of_beq_eq_true hEqS; subst haS
                            have hnT : aT0 ≠ aT' := fun h => by subst h; rw [Nat.beq_refl] at hEqT; cases hEqT
                            have heqT : aT0 = aT' := by injection (hm.symm.trans hm')
                            exact False.elim (hnT heqT)
                          · have haS := Nat.eq_of_beq_eq_true hEqS; have haT := Nat.eq_of_beq_eq_true hEqT
                            subst haS; subst haT
                            rw [hGS] at hgS0; injection hgS0 with hs0; subst hs0
                            rw [hGT] at hgT0; injection hgT0 with ht0; subst ht0
                            exact ⟨{ eS with cell := some vv }, { eT with cell := some vT },
                              listGet_listSet_eq hSetHS, listGet_listSet_eq hSetHT, hEa, hEta, hvSim⟩
                · intro aS' eS' hgS' hEa'
                  cases hEqS : Nat.beq aS' aS with
                  | true =>
                    have haS := Nat.eq_of_beq_eq_true hEqS; subst haS
                    rw [listGet_listSet_eq hSetHS] at hgS'; injection hgS' with heq; subst heq
                    exact ⟨owner, aT', { eT with cell := some vT }, hSOwn, hofOwn, hm',
                      listGet_listSet_eq hSetHT, hEta, hvSim⟩
                  | false =>
                    have hnS : aS' ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at hEqS; cases hEqS
                    rw [listGet_listSet_ne hSetHS hnS] at hgS'
                    rcases hSim2.srcHeapOk aS' eS' hgS' hEa' with ⟨i, aT0, e0, hSi, hof, hm, hg0, hEta0, hOv0⟩
                    have hnT : aT0 ≠ aT' := by
                      intro heq; subst heq
                      have hio := hSim2.targetUnique i owner aT0 hof hofOwn
                      subst hio; rw [hSOwn] at hSi; injection hSi with hss; injection hss with hsa
                      exact hnS hsa.symm
                    exact ⟨i, aT0, e0, hSi, hof, hm, by rw [listGet_listSet_ne hSetHT hnT]; exact hg0, hEta0, hOv0⟩
                · intro a1 a2 aT0 e1 e2 hg1 he1 hg2 he2 hm1 hm2
                  have hg1' : listGet vs.heap a1 = some (if Nat.beq a1 aS then eS else e1) := by
                    cases h1 : Nat.beq a1 aS with
                    | true => have h := Nat.eq_of_beq_eq_true h1; subst h; exact hGS
                    | false =>
                      have hne : a1 ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at h1; cases h1
                      rw [listGet_listSet_ne hSetHS hne] at hg1; exact hg1
                  have hg2' : listGet vs.heap a2 = some (if Nat.beq a2 aS then eS else e2) := by
                    cases h2 : Nat.beq a2 aS with
                    | true => have h := Nat.eq_of_beq_eq_true h2; subst h; exact hGS
                    | false =>
                      have hne : a2 ≠ aS := fun h => by subst h; rw [Nat.beq_refl] at h2; cases h2
                      rw [listGet_listSet_ne hSetHS hne] at hg2; exact hg2
                  have he1' : (if Nat.beq a1 aS then eS else e1).alive = true := by
                    cases Nat.beq a1 aS with | true => exact hEa | false => exact he1
                  have he2' : (if Nat.beq a2 aS then eS else e2).alive = true := by
                    cases Nat.beq a2 aS with | true => exact hEa | false => exact he2
                  exact hSim2.aliveInj a1 a2 aT0 _ _ hg1' he1' hg2' he2' hm1 hm2
  | assume op =>
    dsimp only [stepStmt, stripStorageStmt] at hStep ⊢
    cases hO : evalOperand cfg stSrc op with
    | error _ => rw [hO] at hStep; cases hStep
    | ok opair =>
      rcases opair with ⟨ov, os⟩
      rw [hO] at hStep
      rcases sim_evalOperand hSim hO with ⟨vT, stTgt1, hOT, hvSim, hSim1⟩
      rw [hOT]
      cases ov with
      | int _ => cases hStep
      | staticPtr _ => cases hStep
      | ptr _ => cases hStep
      | bool b =>
        cases vT with
        | int _ => exact False.elim hvSim | staticPtr _ => exact False.elim hvSim | ptr _ => exact False.elim hvSim
        | bool bT =>
          have hbb : b = bT := hvSim; subst hbb
          cases b with
          | false => cases hStep
          | true =>
            injection hStep with hst; subst hst
            exact ⟨m, { stTgt1 with stmtIdx := stTgt1.stmtIdx + 1 }, rfl,
              { pcEq := hSim1.pcEq, stmtEq := congrArg Nat.succ hSim1.stmtEq, lenEq := hSim1.lenEq,
                mapBounded := hSim1.mapBounded,
                targetUnique := hSim1.targetUnique, tgtLocalsOk := hSim1.tgtLocalsOk,
                srcLocalsOk := hSim1.srcLocalsOk, srcHeapOk := hSim1.srcHeapOk, aliveInj := hSim1.aliveInj }⟩

theorem sim_runBody_strip {cfg : EvalConfig} {body : Body}
    {targetOf : LocalId → Option AllocId} :
    ∀ fuel m stSrc stTgt,
      StorageSimRel body.stackBackedLocals m targetOf stSrc stTgt →
      ForwardRefines (runBody cfg body stSrc fuel)
        (runBody cfg (passRemoveStorageMarkers body) stTgt fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _
    exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
  | succ fuel' ih =>
    intro m stSrc stTgt hSim
    dsimp only [runBody]
    cases hBB : listGet body.blocks stSrc.pc with
    | none =>
      exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
    | some bb =>
      have hBBT : listGet (passRemoveStorageMarkers body).blocks stTgt.pc =
          some { bb with stmts := bb.stmts.map stripStorageStmt } := by
        dsimp [passRemoveStorageMarkers]
        rw [← hSim.pcEq, listGet_map, hBB]
        rfl
      rw [hBBT]; dsimp only
      cases hSt : listGet bb.stmts stSrc.stmtIdx with
      | some s =>
        have hStT : listGet (bb.stmts.map stripStorageStmt) stTgt.stmtIdx =
            some (stripStorageStmt s) := by
          rw [← hSim.stmtEq, listGet_map, hSt]; rfl
        rw [hStT]; dsimp only
        cases hStep : stepStmt cfg body stSrc s with
        | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
        | ok stSrc1 =>
          rcases sim_stepStmt_strip hSim hStep with ⟨m', stTgt1, hStepT, hSim1⟩
          rw [hStepT]; dsimp only
          exact ih m' stSrc1 stTgt1 hSim1
      | none =>
        have hStT : listGet (bb.stmts.map stripStorageStmt) stTgt.stmtIdx = none := by
          rw [← hSim.stmtEq, listGet_map, hSt]; rfl
        rw [hStT]; dsimp only
        cases hTerm : bb.term with
        | goto tgt =>
          exact ih m { stSrc with pc := tgt, stmtIdx := 0 } { stTgt with pc := tgt, stmtIdx := 0 }
            ({ pcEq := rfl, stmtEq := rfl, lenEq := hSim.lenEq, mapBounded := hSim.mapBounded,
               targetUnique := hSim.targetUnique,
               tgtLocalsOk := hSim.tgtLocalsOk, srcLocalsOk := hSim.srcLocalsOk,
               srcHeapOk := hSim.srcHeapOk, aliveInj := hSim.aliveInj })
        | unreachable => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
        | ret =>
          dsimp only [stepTerm]
          cases hR : readLocalCell stSrc 0 with
          | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
          | ok vS =>
            rcases sim_readLocalCell hSim hR with ⟨vT, hRT, hvSim⟩
            rw [hRT]
            refine ⟨(fun v hNon hEq => ?_), (fun h => by cases h)⟩
            injection hEq with hvv; subst hvv
            rw [valSim_nonStack_eq hNon hvSim]
        | switchInt discr arms otherwise =>
          dsimp only [stepTerm]
          cases hOp : evalOperand cfg stSrc discr with
          | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
          | ok pair =>
            rcases pair with ⟨vp, sp⟩
            rcases sim_evalOperand hSim hOp with ⟨vT, stTgt1, hOpT, hvSim, hSim1⟩
            rw [hOpT]; dsimp only
            cases hBits : discrBits vp with
            | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
            | ok bits =>
              rw [valSim_discrBits hvSim hBits]; dsimp only
              let tgt := lookupSwitchTarget bits arms otherwise
              exact ih m { sp with pc := tgt, stmtIdx := 0 } { stTgt1 with pc := tgt, stmtIdx := 0 }
                ({ pcEq := rfl, stmtEq := rfl, lenEq := hSim1.lenEq, mapBounded := hSim1.mapBounded,
                   targetUnique := hSim1.targetUnique,
                   tgtLocalsOk := hSim1.tgtLocalsOk, srcLocalsOk := hSim1.srcLocalsOk,
                   srcHeapOk := hSim1.srcHeapOk, aliveInj := hSim1.aliveInj })
        | assert cond expected tgt optOvf =>
          dsimp only [stepTerm]
          cases hSkip : (optOvf && !cfg.enforceOptionalOverflow) with
          | true =>
            simp only [↓reduceIte]
            exact ih m { stSrc with pc := tgt, stmtIdx := 0 } { stTgt with pc := tgt, stmtIdx := 0 }
              ({ pcEq := rfl, stmtEq := rfl, lenEq := hSim.lenEq, mapBounded := hSim.mapBounded,
                 targetUnique := hSim.targetUnique,
                 tgtLocalsOk := hSim.tgtLocalsOk, srcLocalsOk := hSim.srcLocalsOk,
                 srcHeapOk := hSim.srcHeapOk, aliveInj := hSim.aliveInj })
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases hOp : evalOperand cfg stSrc cond with
            | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
            | ok pair =>
              rcases pair with ⟨vp, sp⟩
              rcases sim_evalOperand hSim hOp with ⟨vT, stTgt1, hOpT, hvSim, hSim1⟩
              rw [hOpT]
              cases vp with
              | int _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
              | staticPtr _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
              | ptr _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
              | bool b =>
                cases vT with
                | int _ => exact False.elim hvSim | staticPtr _ => exact False.elim hvSim | ptr _ => exact False.elim hvSim
                | bool bT =>
                  have hbb : b = bT := hvSim; subst hbb
                  dsimp only
                  cases hMatch : (b == expected) with
                  | false => exact ⟨(fun _ _ h => by cases h), (fun h => by exact h)⟩
                  | true =>
                    exact ih m { sp with pc := tgt, stmtIdx := 0 } { stTgt1 with pc := tgt, stmtIdx := 0 }
                      ({ pcEq := rfl, stmtEq := rfl, lenEq := hSim1.lenEq, mapBounded := hSim1.mapBounded,
                         targetUnique := hSim1.targetUnique,
                         tgtLocalsOk := hSim1.tgtLocalsOk, srcLocalsOk := hSim1.srcLocalsOk,
                         srcHeapOk := hSim1.srcHeapOk, aliveInj := hSim1.aliveInj })

theorem initScopedLoop_length (stackLocals : List LocalId) (idx rem : Nat) :
    (initScopedLoop stackLocals idx rem).length = rem := by
  induction rem generalizing idx with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ (ih (idx + 1))

theorem initScopedLoop_get (stackLocals : List LocalId) (idx rem k : Nat) :
    (k < rem →
      (idx + k = 0 → listGet (initScopedLoop stackLocals idx rem) k =
        some (if natInList 0 stackLocals then .dead else .direct none)) ∧
      (idx + k ≠ 0 → listGet (initScopedLoop stackLocals idx rem) k = some .dead)) ∧
    (rem ≤ k → listGet (initScopedLoop stackLocals idx rem) k = none) := by
  induction rem generalizing idx k with
  | zero =>
    refine ⟨fun h => False.elim (Nat.not_lt_zero _ h), fun _ => listGet_nil k⟩
  | succ r ih =>
    cases k with
    | zero =>
      refine ⟨fun _ => ⟨fun h0 => ?_, fun hne => ?_⟩, fun h => False.elim (Nat.not_succ_le_zero _ h)⟩
      · rw [Nat.add_zero] at h0; subst h0; rfl
      · rw [Nat.add_zero] at hne; dsimp [initScopedLoop]; rw [nat_beq_false_of_ne hne]; rfl
    | succ j =>
      have hRec := ih (idx + 1) j
      have hAdd : (idx + 1) + j = idx + (j + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 j, ← Nat.add_assoc]
      refine ⟨fun hlt => ?_, fun hle => ?_⟩
      · have hj : j < r := Nat.lt_of_succ_lt_succ hlt
        rcases hRec.1 hj with ⟨hZ, hNZ⟩
        exact ⟨fun h0 => hZ (hAdd.trans h0), fun hne => hNZ (fun h => hne (hAdd.symm.trans h))⟩
      · exact hRec.2 (Nat.le_of_succ_le_succ hle)

structure FrameInitHeapInv (heap : List AllocEntry) : Prop where
  allAlive : ∀ a, a < heap.length → listGet heap a = some { alive := true, cell := none }

theorem frameInitHeapInv_alloc {heap : List AllocEntry} (h : FrameInitHeapInv heap) :
    FrameInitHeapInv (allocHeap heap).2 := by
  refine ⟨fun a hlt => ?_⟩
  dsimp [allocHeap] at hlt ⊢
  rw [List.length_append] at hlt
  cases hEq : Nat.beq a heap.length with
  | true =>
    have ha := Nat.eq_of_beq_eq_true hEq; subst ha
    exact listGet_append_exact heap _
  | false =>
    have hne : a ≠ heap.length := fun h0 => by subst h0; rw [Nat.beq_refl] at hEq; cases hEq
    have hlt' : a < heap.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hne
    rw [listGet_append_left heap _ hlt']
    exact h.allAlive a hlt'

theorem initFrameLiveLoop_spec (stackLocals : List LocalId) (idx rem : Nat)
    (heap : List AllocEntry) (hInv : FrameInitHeapInv heap) :
    let (ls, hp) := initFrameLiveLoop stackLocals idx rem heap
    ls.length = rem ∧
    heap.length ≤ hp.length ∧
    FrameInitHeapInv hp ∧
    (∀ k, k < rem →
      if natInList (idx + k) stackLocals then
        ∃ aT, listGet ls k = some (.stack aT) ∧ heap.length ≤ aT ∧ aT < hp.length
      else
        listGet ls k = some (.direct none)) ∧
    (∀ k, rem ≤ k → listGet ls k = none) ∧
    (∀ k1 k2 aT1 aT2, listGet ls k1 = some (.stack aT1) → listGet ls k2 = some (.stack aT2) →
      aT1 = aT2 → k1 = k2) := by
  induction rem generalizing idx heap with
  | zero =>
    refine ⟨rfl, Nat.le_refl _, hInv, fun _ h => False.elim (Nat.not_lt_zero _ h),
      fun _ _ => listGet_nil _, fun k1 _ _ _ hg1 => by rw [listGet_nil] at hg1; cases hg1⟩
  | succ r ih =>
    dsimp [initFrameLiveLoop]
    cases hIn : natInList idx stackLocals with
    | true =>
      simp only [↓reduceIte]
      have hRec := ih (idx + 1) (allocHeap heap).2 (frameInitHeapInv_alloc hInv)
      dsimp at hRec
      rcases hRec with ⟨hLen, hHpLen, hHpInv, hAtK, hGeNone, hInj⟩
      have hAllocLen : (allocHeap heap).2.length = heap.length + 1 := by
        dsimp [allocHeap]; rw [List.length_append]; rfl
      refine ⟨congrArg Nat.succ hLen, Nat.le_trans (by rw [hAllocLen]; exact Nat.le_succ _) hHpLen, hHpInv, ?_, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero =>
          rw [Nat.add_zero, hIn]; simp only [↓reduceIte]
          exact ⟨heap.length, rfl, Nat.le_refl _, Nat.lt_of_lt_of_le (by rw [hAllocLen]; exact Nat.lt_succ_self _) hHpLen⟩
        | succ j =>
          have hj := hAtK j (Nat.lt_of_succ_lt_succ hk)
          have hAdd : (idx + 1) + j = idx + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j, ← Nat.add_assoc]
          rw [← hAdd]
          cases hInJ : natInList ((idx + 1) + j) stackLocals with
          | true =>
            rw [hInJ] at hj; simp only [↓reduceIte] at hj ⊢
            rcases hj with ⟨aT, hg, hle, hlt⟩
            exact ⟨aT, hg, Nat.le_trans (by rw [hAllocLen]; exact Nat.le_succ _) hle, hlt⟩
          | false => rw [hInJ] at hj; simp only [Bool.false_eq_true, ↓reduceIte] at hj ⊢; exact hj
      · intro k hle
        cases k with
        | zero => cases hle
        | succ j => exact hGeNone j (Nat.le_of_succ_le_succ hle)
      · intro k1 k2 aT1 aT2 hg1 hg2 haEq
        cases k1 with
        | zero =>
          injection hg1 with h1; injection h1 with ha1
          cases k2 with
          | zero => rfl
          | succ j2 =>
            have hg2s : listGet (initFrameLiveLoop stackLocals (idx + 1) r (allocHeap heap).snd).1 j2 =
                some (.stack aT2) := hg2
            cases hLt : natInList ((idx + 1) + j2) stackLocals with
            | true =>
              have hj2 := hAtK j2 (by rw [← hLen]; exact listGet_length_lt hg2s)
              rw [hLt] at hj2; simp only [↓reduceIte] at hj2
              rcases hj2 with ⟨aT2', hg2', hle2, _⟩
              rw [hg2'] at hg2s; injection hg2s with h2; injection h2 with ha2
              dsimp only [allocHeap] at hAllocLen hle2 ha1 ha2
              rw [hAllocLen, ha2, ← haEq, ← ha1] at hle2
              exact False.elim (Nat.not_succ_le_self _ hle2)
            | false =>
              have hj2 := hAtK j2 (by rw [← hLen]; exact listGet_length_lt hg2s)
              rw [hLt] at hj2; simp only [Bool.false_eq_true, ↓reduceIte] at hj2
              rw [hj2] at hg2s; cases hg2s
        | succ j1 =>
          cases k2 with
          | zero =>
            injection hg2 with h2; injection h2 with ha2
            have hg1s : listGet (initFrameLiveLoop stackLocals (idx + 1) r (allocHeap heap).snd).1 j1 =
                some (.stack aT1) := hg1
            have hj1 := hAtK j1 (by rw [← hLen]; exact listGet_length_lt hg1s)
            cases hLt : natInList ((idx + 1) + j1) stackLocals with
            | true =>
              rw [hLt] at hj1; simp only [↓reduceIte] at hj1
              rcases hj1 with ⟨aT1', hg1', hle1, _⟩
              rw [hg1'] at hg1s; injection hg1s with h1; injection h1 with ha1
              dsimp only [allocHeap] at hAllocLen hle1 ha1 ha2
              rw [hAllocLen, ha1, haEq, ← ha2] at hle1
              exact False.elim (Nat.not_succ_le_self _ hle1)
            | false =>
              rw [hLt] at hj1; simp only [Bool.false_eq_true, ↓reduceIte] at hj1
              rw [hj1] at hg1s; cases hg1s
          | succ j2 => exact congrArg Nat.succ (hInj j1 j2 aT1 aT2 hg1 hg2 haEq)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hRec := ih (idx + 1) heap hInv
      dsimp at hRec
      rcases hRec with ⟨hLen, hHpLen, hHpInv, hAtK, hGeNone, hInj⟩
      refine ⟨congrArg Nat.succ hLen, hHpLen, hHpInv, ?_, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => rw [Nat.add_zero, hIn]; rfl
        | succ j =>
          have hj := hAtK j (Nat.lt_of_succ_lt_succ hk)
          have hAdd : (idx + 1) + j = idx + (j + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 j, ← Nat.add_assoc]
          rw [← hAdd]; exact hj
      · intro k hle
        cases k with
        | zero => cases hle
        | succ j => exact hGeNone j (Nat.le_of_succ_le_succ hle)
      · intro k1 k2 aT1 aT2 hg1 hg2 haEq
        cases k1 with
        | zero => cases hg1
        | succ j1 =>
          cases k2 with
          | zero => cases hg2
          | succ j2 => exact congrArg Nat.succ (hInj j1 j2 aT1 aT2 hg1 hg2 haEq)

def initFrameTargetOf (b : Body) (i : LocalId) : Option AllocId :=
  match listGet (initFrameLiveLoop b.stackBackedLocals 0 b.numLocals []).1 i with
  | some (.stack aT) => some aT
  | _ => none

theorem init_sim_rel (b : Body) :
    StorageSimRel b.stackBackedLocals (fun _ => none) (initFrameTargetOf b)
      (initScopedState b) (initFrameLiveState (passRemoveStorageMarkers b)) := by
  have hFrame := initFrameLiveLoop_spec b.stackBackedLocals 0 b.numLocals [] ⟨fun _ h => by cases h⟩
  dsimp [initFrameLiveState, passRemoveStorageMarkers, initScopedState] at hFrame ⊢
  rcases hFrame with ⟨hLen, _, hHpInv, hAtK, hGeNone, hInj⟩
  refine
    { pcEq := rfl, stmtEq := rfl,
      lenEq := by rw [initScopedLoop_length, hLen],
      mapBounded := (fun _ _ h => by cases h),
      targetUnique := ?_, tgtLocalsOk := ?_, srcLocalsOk := ?_,
      srcHeapOk := (fun _ _ h => by rw [listGet_nil] at h; cases h),
      aliveInj := (fun _ _ _ _ _ h => by rw [listGet_nil] at h; cases h) }
  · intro i j aT hi hj
    dsimp [initFrameTargetOf] at hi hj
    cases hGi : listGet (initFrameLiveLoop b.stackBackedLocals 0 b.numLocals []).1 i with
    | none => rw [hGi] at hi; cases hi
    | some si =>
      rw [hGi] at hi
      cases si with
      | dead => cases hi | direct _ => cases hi
      | stack aTi =>
        injection hi with ha1
        cases hGj : listGet (initFrameLiveLoop b.stackBackedLocals 0 b.numLocals []).1 j with
        | none => rw [hGj] at hj; cases hj
        | some sj =>
          rw [hGj] at hj
          cases sj with
          | dead => cases hj | direct _ => cases hj
          | stack aTj =>
            injection hj with ha2
            exact hInj i j aTi aTj hGi hGj (ha1.trans ha2.symm)
  · intro i
    dsimp only [initFrameTargetOf]
    cases hGi : listGet (initFrameLiveLoop b.stackBackedLocals 0 b.numLocals []).1 i with
    | none => rfl
    | some si =>
      have hlt : i < b.numLocals := Nat.lt_of_lt_of_eq (listGet_length_lt hGi) hLen
      have hk := hAtK i hlt
      rw [Nat.zero_add] at hk
      cases hIn : natInList i b.stackBackedLocals with
      | true =>
        rw [hIn] at hk; simp only [↓reduceIte] at hk
        rcases hk with ⟨aT, hg, _, hltHp⟩
        rw [hg] at hGi; injection hGi with hs; subst hs
        exact ⟨rfl, rfl, { alive := true, cell := none }, hHpInv.allAlive aT hltHp, rfl⟩
      | false =>
        rw [hIn] at hk; simp only [Bool.false_eq_true, ↓reduceIte] at hk
        rw [hk] at hGi; injection hGi with hs; subst hs
        exact ⟨rfl, rfl⟩
  · intro i
    dsimp only
    cases hGi : listGet (initFrameLiveLoop b.stackBackedLocals 0 b.numLocals []).1 i with
    | none =>
      have hGe : b.numLocals ≤ i := by
        cases Nat.lt_or_ge i b.numLocals with
        | inr hle => exact hle
        | inl hlt =>
          have hk := hAtK i hlt
          rw [Nat.zero_add] at hk
          cases hIn : natInList i b.stackBackedLocals with
          | true => rw [hIn] at hk; simp only [↓reduceIte] at hk; rcases hk with ⟨aT, hg, _⟩; rw [hg] at hGi; cases hGi
          | false => rw [hIn] at hk; simp only [Bool.false_eq_true, ↓reduceIte] at hk; rw [hk] at hGi; cases hGi
      rw [(initScopedLoop_get b.stackBackedLocals 0 b.numLocals i).2 hGe]
      trivial
    | some si =>
      have hlt : i < b.numLocals := Nat.lt_of_lt_of_eq (listGet_length_lt hGi) hLen
      have hSc := (initScopedLoop_get b.stackBackedLocals 0 b.numLocals i).1 hlt
      rw [Nat.zero_add] at hSc
      cases hZ : Nat.beq i 0 with
      | true =>
        have hi0 := Nat.eq_of_beq_eq_true hZ; subst hi0
        rw [hSc.1 rfl]
        have hk := hAtK 0 hlt
        rw [Nat.zero_add] at hk
        cases hIn0 : natInList 0 b.stackBackedLocals with
        | true =>
          simp only [↓reduceIte]
        | false =>
          rw [hIn0] at hk; simp only [Bool.false_eq_true, ↓reduceIte] at hk
          rw [hk] at hGi; injection hGi with hs; subst hs
          simp only [Bool.false_eq_true, ↓reduceIte]
          trivial
      | false =>
        have hne : i ≠ 0 := fun h => by subst h; rw [Nat.beq_refl] at hZ; cases hZ
        rw [hSc.2 hne]
        cases si <;> trivial

theorem forwardRefines_removeStorageMarkers (cfg : EvalConfig) (b : Body) (fuel : Nat) :
    ForwardRefines
      (runBody cfg b (initScopedState b) fuel)
      (runBody cfg (passRemoveStorageMarkers b) (initFrameLiveState (passRemoveStorageMarkers b)) fuel) :=
  sim_runBody_strip fuel _ _ _ (init_sim_rel b)

/-! ### Miri Paradox & Fixed Policy Soundness -/

def miriMir0Opt0 : SessionFlags :=
  { optLevel := .no, mirOptLevel := 0, mirPreserveUb := true,
    sanitizersNeedLifetimes := false, codegenEmitRetag := false }

def miriMir1Opt0 : SessionFlags :=
  { optLevel := .no, mirOptLevel := 1, mirPreserveUb := true,
    sanitizersNeedLifetimes := false, codegenEmitRetag := false }

def miriMir2Opt0 : SessionFlags :=
  { optLevel := .no, mirOptLevel := 2, mirPreserveUb := true,
    sanitizersNeedLifetimes := false, codegenEmitRetag := false }

def miriMir2Opt1 : SessionFlags :=
  { optLevel := .o1, mirOptLevel := 2, mirPreserveUb := true,
    sanitizersNeedLifetimes := false, codegenEmitRetag := false }

def miriMir1Opt0DisableRsm : SessionFlags :=
  { optLevel := .no, mirOptLevel := 1, mirPreserveUb := true,
    sanitizersNeedLifetimes := false, codegenEmitRetag := false,
    disableRemoveStorageMarkers := true }

def miriDefaultCfg : EvalConfig :=
  { deinitMovedPlace := false, enforceOptionalOverflow := true }

def danglingStackPtrBody : Body :=
  { numLocals := 3
    stackBackedLocals := [1]
    blocks :=
      [ { stmts :=
            [ .storageLive 1
            , .assign 1 (.use (.const (.int 42)))
            , .storageLive 2
            , .assign 2 (.addrOf 1)
            , .storageDead 1
            , .assign 0 (.derefPtr (.copy 2))
            , .storageDead 2
            ]
          term := .ret } ] }

theorem miri_paradox_non_monotone_in_opt_level :
    evalWithMiriPipeline miriMir0Opt0 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    evalWithMiriPipeline miriMir1Opt0 miriDefaultCfg danglingStackPtrBody 20 = .returned (.int 42) ∧
    evalWithMiriPipeline miriMir2Opt0 miriDefaultCfg danglingStackPtrBody 20 = .returned (.int 42) ∧
    evalWithMiriPipeline miriMir2Opt1 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    evalWithMiriPipeline miriMir1Opt0DisableRsm miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fixedRemoveStorageMarkers_preserves_ub_when_mirPreserveUb :
    evalWithFixedPipeline miriMir0Opt0 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    evalWithFixedPipeline miriMir1Opt0 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    evalWithFixedPipeline miriMir2Opt0 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    evalWithFixedPipeline miriMir2Opt1 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 4: `SimplifyComparisonIntegral` Bidirectional Equivalence (`↔`) -/

def downgradeMoveOperand (x : LocalId) : Operand → Operand
  | .move loc => if Nat.beq loc x then .copy x else .move loc
  | op => op

def isSimpleLocalOperand (x : LocalId) : Operand → Bool
  | .copy loc => Nat.beq loc x
  | .move loc => Nat.beq loc x
  | .const _ => false

def isValidSciBinOp (b x : LocalId) (k : Int) (op : BinOpKind) (lhs rhs : Operand) : Bool :=
  (op == .eq || op == .ne) &&
  !Nat.beq b x &&
  ((isSimpleLocalOperand x lhs && rhs == .const (.int k)) ||
   (lhs == .const (.int k) && isSimpleLocalOperand x rhs))

def rewriteSciTerm (x : LocalId) (k : Int) (op : BinOpKind) (armVal : Int)
    (bbArm bbOth : BlockId) : Term :=
  let armIsFalse := decide (armVal = 0)
  let (bbTrue, bbFalse) :=
    match op with
    | .eq => if armIsFalse then (bbOth, bbArm) else (bbArm, bbOth)
    | .ne => if armIsFalse then (bbArm, bbOth) else (bbOth, bbArm)
    | _ => (bbArm, bbOth)
  .switchInt (.copy x) [(k, bbTrue)] bbFalse

def rewriteSciBlock (b x : LocalId) (k : Int) (op : BinOpKind) (lhs rhs : Operand)
    (armVal : Int) (bbArm bbOth : BlockId) : BasicBlock :=
  { stmts := [.assign b (.binOp op (downgradeMoveOperand x lhs) (downgradeMoveOperand x rhs))]
    term := rewriteSciTerm x k op armVal bbArm bbOth }

def sciPassBlock (b x : LocalId) (bb : BasicBlock) : BasicBlock :=
  match bb.stmts, bb.term with
  | [.assign dst (.binOp op lhs rhs)], .switchInt (.copy discrLoc) [(armVal, bbArm)] bbOth =>
    if Nat.beq dst b && Nat.beq discrLoc b then
      match lhs, rhs with
      | .copy xl, .const (.int k) | .move xl, .const (.int k) =>
        if (op == .eq || op == .ne) && !Nat.beq b x && Nat.beq xl x &&
           (decide (armVal = 0) || decide (armVal = 1)) then
          rewriteSciBlock b x k op lhs rhs armVal bbArm bbOth
        else bb
      | .const (.int k), .copy xr | .const (.int k), .move xr =>
        if (op == .eq || op == .ne) && !Nat.beq b x && Nat.beq xr x &&
           (decide (armVal = 0) || decide (armVal = 1)) then
          rewriteSciBlock b x k op lhs rhs armVal bbArm bbOth
        else bb
      | _, _ => bb
    else bb
  | _, _ => bb

theorem simplifyCmp_rejects_ptr_const (b x : LocalId) (sid : StaticId)
    (op : BinOpKind) (armVal : Int) (bbArm bbOth : BlockId) :
    let bb : BasicBlock :=
      { stmts := [.assign b (.binOp op (.copy x) (.const (.ptrConst sid)))]
        term := .switchInt (.copy b) [(armVal, bbArm)] bbOth }
    sciPassBlock b x bb = bb := by
  dsimp [sciPassBlock]
  cases Nat.beq b b <;> rfl

theorem decide_eq_comm (n k : Int) : decide (n = k) = decide (k = n) := by
  cases h : decide (n = k) with
  | true =>
    have heq : n = k := of_decide_eq_true h
    exact (decide_eq_true heq.symm).symm
  | false =>
    cases h2 : decide (k = n) with
    | false => rfl
    | true =>
      have heq : k = n := of_decide_eq_true h2
      have h1 : decide (n = k) = true := decide_eq_true heq.symm
      rw [h1] at h
      cases h

theorem decide_ne_comm (n k : Int) : decide (n ≠ k) = decide (k ≠ n) := by
  cases h : decide (n ≠ k) with
  | true =>
    have hne : n ≠ k := of_decide_eq_true h
    have h2 : decide (k ≠ n) = true := decide_eq_true (fun hkn => hne hkn.symm)
    exact h2.symm
  | false =>
    cases h2 : decide (k ≠ n) with
    | false => rfl
    | true =>
      have hne : k ≠ n := of_decide_eq_true h2
      have h1 : decide (n ≠ k) = true := decide_eq_true (fun hnk => hne hnk.symm)
      rw [h1] at h
      cases h

private theorem bool_ite_true {α : Type} (a b : α) : (if true = true then a else b) = a := rfl
private theorem bool_ite_false {α : Type} (a b : α) : (if false = true then a else b) = b := rfl
private theorem sci_listGet_succ_one {α : Type} (x : α) : listGet [x] (0 + 1) = none := rfl

theorem sci_target_eq (op : BinOpKind) (armVal n k : Int) (bbArm bbOth : BlockId)
    (hop : op = .eq ∨ op = .ne) (harm : armVal = 0 ∨ armVal = 1) :
    lookupSwitchTarget
      (if (match op with | .eq => decide (n = k) | .ne => decide (n ≠ k) | _ => false) then 1 else 0)
      [(armVal, bbArm)] bbOth =
    let pair :=
      match op with
      | .eq => if decide (armVal = 0) then (bbOth, bbArm) else (bbArm, bbOth)
      | .ne => if decide (armVal = 0) then (bbArm, bbOth) else (bbOth, bbArm)
      | _ => (bbArm, bbOth)
    lookupSwitchTarget n [(k, pair.1)] pair.2 := by
  have hbt : (if true = true then (1 : Int) else 0) = 1 := rfl
  have hbf : (if false = true then (1 : Int) else 0) = 0 := rfl
  have h00 : decide ((0 : Int) = 0) = true := decide_eq_true rfl
  have h11 : decide ((1 : Int) = 1) = true := decide_eq_true rfl
  have h10 : decide ((1 : Int) = 0) = false := decide_eq_false (by intro h; cases h)
  have h01 : decide ((0 : Int) = 1) = false := decide_eq_false (by intro h; cases h)
  cases hop with
  | inl heq =>
    subst heq
    cases harm with
    | inl ha0 =>
      subst ha0
      cases hnk : decide (n = k) with
      | true =>
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hbt, h10, h00]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])
      | false =>
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hbf, h00]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])
    | inr ha1 =>
      subst ha1
      cases hnk : decide (n = k) with
      | true =>
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hbt, h11, h10]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])
      | false =>
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hbf, h01, h10]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])
  | inr hne =>
    subst hne
    cases harm with
    | inl ha0 =>
      subst ha0
      cases hnk : decide (n = k) with
      | true =>
        have hneF : decide (n ≠ k) = false :=
          decide_eq_false (fun hne0 => hne0 (of_decide_eq_true hnk))
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hneF, hbf, h00]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])
      | false =>
        have hneT : decide (n ≠ k) = true :=
          decide_eq_true (fun h => by have hr : decide (n = k) = true := decide_eq_true h; rw [hr] at hnk; cases hnk)
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hneT, hbt, h10, h00]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])
    | inr ha1 =>
      subst ha1
      cases hnk : decide (n = k) with
      | true =>
        have hneF : decide (n ≠ k) = false :=
          decide_eq_false (fun hne0 => hne0 (of_decide_eq_true hnk))
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hneF, hbf, h01, h10]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])
      | false =>
        have hneT : decide (n ≠ k) = true :=
          decide_eq_true (fun h => by have hr : decide (n = k) = true := decide_eq_true h; rw [hr] at hnk; cases hnk)
        dsimp only [lookupSwitchTarget, List.foldr]
        rw [hnk, hneT, hbt, h11, h10]
        repeat (first | rw [bool_ite_true] | rw [bool_ite_false])

theorem sci_valid_shapes {b x : LocalId} {k : Int} {op : BinOpKind} {lhs rhs : Operand}
    (h : isValidSciBinOp b x k op lhs rhs = true) :
    ((lhs = .copy x ∨ lhs = .move x) ∧ rhs = .const (.int k)) ∨
    (lhs = .const (.int k) ∧ (rhs = .copy x ∨ rhs = .move x)) := by
  unfold isValidSciBinOp at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h with ⟨_, hSides⟩
  cases hSides with
  | inl hL =>
    have hL1 : lhs = .copy x ∨ lhs = .move x := by
      cases lhs with
      | copy xl => exact Or.inl (congrArg Operand.copy (Nat.eq_of_beq_eq_true hL.1))
      | move xl => exact Or.inr (congrArg Operand.move (Nat.eq_of_beq_eq_true hL.1))
      | const _ => cases hL.1
    have hR1 : rhs = .const (.int k) := by
      cases rhs with
      | copy _ => cases hL.2 | move _ => cases hL.2
      | const c =>
        cases c with
        | bool _ => cases hL.2 | ptrConst _ => cases hL.2
        | int n =>
          have hEq : Operand.const (.int n) = Operand.const (.int k) := eq_of_beq hL.2
          injection hEq with hEq'
          injection hEq' with hnk
          subst hnk
          rfl
    exact Or.inl ⟨hL1, hR1⟩
  | inr hR =>
    have hL2 : lhs = .const (.int k) := by
      cases lhs with
      | copy _ => cases hR.1 | move _ => cases hR.1
      | const c =>
        cases c with
        | bool _ => cases hR.1 | ptrConst _ => cases hR.1
        | int n =>
          have hEq : Operand.const (.int n) = Operand.const (.int k) := eq_of_beq hR.1
          injection hEq with hEq'
          injection hEq' with hnk
          subst hnk
          rfl
    have hR2 : rhs = .copy x ∨ rhs = .move x := by
      cases rhs with
      | copy xr => exact Or.inl (congrArg Operand.copy (Nat.eq_of_beq_eq_true hR.2))
      | move xr => exact Or.inr (congrArg Operand.move (Nat.eq_of_beq_eq_true hR.2))
      | const _ => cases hR.2
    exact Or.inr ⟨hL2, hR2⟩

def opMentionsLocal (x : LocalId) : Operand → Bool
  | .copy loc | .move loc => Nat.beq loc x
  | .const _ => false

def rvMentionsLocal (x : LocalId) : Rvalue → Bool
  | .use op | .subtypeCast op | .derefPtr op => opMentionsLocal x op
  | .binOp _ l r => opMentionsLocal x l || opMentionsLocal x r
  | .addrOf loc | .discr loc => Nat.beq loc x

def stmtMentionsLocal (x : LocalId) : Stmt → Bool
  | .nop => false
  | .storageLive loc | .storageDead loc => Nat.beq loc x
  | .assign dst rv => Nat.beq dst x || rvMentionsLocal x rv
  | .storePtr p v => opMentionsLocal x p || opMentionsLocal x v
  | .assume op => opMentionsLocal x op

def termMentionsLocal (x : LocalId) : Term → Bool
  | .goto _ | .ret | .unreachable => false
  | .switchInt op _ _ | .assert op _ _ _ => opMentionsLocal x op

def blockMentionsLocal (x : LocalId) (bb : BasicBlock) : Bool :=
  bb.stmts.any (stmtMentionsLocal x) || termMentionsLocal x bb.term

def armListTargetsGe1 (arms : List (Int × BlockId)) : Bool :=
  List.foldr (fun p ih => decide (p.2 ≥ 1) && ih) true arms

theorem armListTargetsGe1_lookup {v : Int} {arms : List (Int × BlockId)} {oth : BlockId}
    (ha : armListTargetsGe1 arms = true) (ho : decide (oth ≥ 1) = true) :
    lookupSwitchTarget v arms oth ≥ 1 := by
  induction arms with
  | nil => exact of_decide_eq_true ho
  | cons hd tl ih =>
    dsimp only [armListTargetsGe1, List.foldr] at ha
    simp only [Bool.and_eq_true] at ha
    dsimp only [lookupSwitchTarget, List.foldr]
    cases decide (v = hd.1) with
    | true => exact of_decide_eq_true ha.1
    | false => exact ih ha.2

def termTargetsGe1 : Term → Bool
  | .goto tgt => decide (tgt ≥ 1)
  | .switchInt _ arms oth => armListTargetsGe1 arms && decide (oth ≥ 1)
  | .assert _ _ tgt _ => decide (tgt ≥ 1)
  | .ret | .unreachable => true

def bodyTailSafeForSciMove (x : LocalId) (bs : List BasicBlock) : Bool :=
  List.foldr (fun b ih => !blockMentionsLocal x b && termTargetsGe1 b.term && ih) true bs

theorem bodyTailSafe_get {x : LocalId} {bs : List BasicBlock}
    (h : bodyTailSafeForSciMove x bs = true) {n : Nat} {bb : BasicBlock}
    (hg : listGet bs n = some bb) :
    blockMentionsLocal x bb = false ∧ termTargetsGe1 bb.term = true := by
  induction bs generalizing n with
  | nil => rw [listGet_nil] at hg; cases hg
  | cons b tl ih =>
    dsimp only [bodyTailSafeForSciMove, List.foldr] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    cases n with
    | zero => injection hg with heq; subst heq; exact h.1
    | succ k => exact ih h.2 hg

theorem listAny_false_get {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.any p = false) {n : Nat} {v : α} (hg : listGet xs n = some v) :
    p v = false := by
  induction xs generalizing n with
  | nil => rw [listGet_nil] at hg; cases hg
  | cons x tl ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    cases n with
    | zero => injection hg with heq; subst heq; exact h.1
    | succ k => exact ih h.2 hg

def StateAgreeExcept (x : LocalId) (st1 st2 : MachineState) : Prop :=
  st1.pc = st2.pc ∧ st1.stmtIdx = st2.stmtIdx ∧ st1.heap = st2.heap ∧
  st1.locals.length = st2.locals.length ∧
  (∀ i, i ≠ x → listGet st1.locals i = listGet st2.locals i)

theorem deinitLocalCell_pc_eq (st : MachineState) (loc : LocalId) :
    (deinitLocalCell st loc).pc = st.pc := by
  dsimp only [deinitLocalCell]
  cases listGet st.locals loc with
  | none => rfl
  | some s =>
    cases s with
    | dead => rfl
    | direct _ =>
      dsimp only
      cases listSet st.locals loc (.direct none) <;> rfl
    | stack aid =>
      dsimp only
      cases listGet st.heap aid with
      | none => rfl
      | some e =>
        dsimp only
        cases listSet st.heap aid { e with cell := none } <;> rfl

theorem evalOperand_pc_eq (cfg : EvalConfig) (st : MachineState) (op : Operand)
    {v : Val} {st' : MachineState} (h : evalOperand cfg st op = .ok (v, st')) :
    st'.pc = st.pc := by
  cases op with
  | const _ => injection h with h1; injection h1 with _ hs; subst hs; rfl
  | copy loc =>
    dsimp only [evalOperand] at h
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at h; cases h
    | ok _ => rw [hR] at h; injection h with h1; injection h1 with _ hs; subst hs; rfl
  | move loc =>
    dsimp only [evalOperand] at h
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at h; cases h
    | ok _ =>
      rw [hR] at h; injection h with h1; injection h1 with _ hs; subst hs
      cases cfg.deinitMovedPlace with
      | false => rfl
      | true => exact deinitLocalCell_pc_eq st loc

theorem evalRvalue_pc_eq (cfg : EvalConfig) (st : MachineState) (rv : Rvalue)
    {v : Val} {st' : MachineState} (h : evalRvalue cfg st rv = .ok (v, st')) :
    st'.pc = st.pc := by
  cases rv with
  | use op | subtypeCast op => exact evalOperand_pc_eq cfg st op h
  | binOp k l r =>
    dsimp only [evalRvalue] at h
    cases hL : evalOperand cfg st l with
    | error _ => rw [hL] at h; cases h
    | ok pl =>
      rcases pl with ⟨vl, sl⟩; rw [hL] at h; dsimp only at h
      cases hR : evalOperand cfg sl r with
      | error _ => rw [hR] at h; cases h
      | ok pr =>
        rcases pr with ⟨vr, sr⟩; rw [hR] at h; dsimp only at h
        cases hB : evalBinOp k vl vr with
        | error _ => rw [hB] at h; cases h
        | ok _ =>
          rw [hB] at h; injection h with h1; injection h1 with _ hs; subst hs
          exact (evalOperand_pc_eq cfg sl r hR).trans (evalOperand_pc_eq cfg st l hL)
  | addrOf loc =>
    dsimp only [evalRvalue] at h
    cases hG : listGet st.locals loc with
    | none => rw [hG] at h; cases h
    | some sl =>
      rw [hG] at h
      cases sl with
      | dead => cases h
      | direct _ => cases h
      | stack aid =>
        dsimp only at h
        cases hH : listGet st.heap aid with
        | none => rw [hH] at h; cases h
        | some e =>
          rw [hH] at h; dsimp only at h
          cases hA : e.alive with
          | false => rw [hA] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
          | true => rw [hA] at h; simp only [↓reduceIte] at h; injection h with h1; injection h1 with _ hs; subst hs; rfl
  | derefPtr op =>
    dsimp only [evalRvalue] at h
    cases hO : evalOperand cfg st op with
    | error _ => rw [hO] at h; cases h
    | ok po =>
      rcases po with ⟨vp, sp⟩; rw [hO] at h
      cases vp with
      | int _ => cases h
      | bool _ => cases h
      | staticPtr _ => cases h
      | ptr aid =>
        dsimp only at h
        cases hH : listGet sp.heap aid with
        | none => rw [hH] at h; cases h
        | some e =>
          rw [hH] at h; dsimp only at h
          cases hA : e.alive with
          | false => rw [hA] at h; simp only [Bool.not_false, ↓reduceIte] at h; cases h
          | true =>
            rw [hA] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases hC : e.cell with
            | none => rw [hC] at h; cases h
            | some _ =>
              rw [hC] at h; dsimp only at h; injection h with h1; injection h1 with _ hs; subst hs
              exact evalOperand_pc_eq cfg st op hO
  | discr loc =>
    dsimp only [evalRvalue] at h
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at h; cases h
    | ok v0 =>
      rw [hR] at h
      cases v0 with
      | bool _ => cases h | staticPtr _ => cases h | ptr _ => cases h
      | int n =>
        dsimp only at h
        cases hD : decide (0 ≤ n) with
        | false => rw [hD] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
        | true => rw [hD] at h; simp only [↓reduceIte] at h; injection h with h1; injection h1 with _ hs; subst hs; rfl

theorem writeLocalCell_pc_eq (st : MachineState) (dst : LocalId) (v : Val)
    {st' : MachineState} (h : writeLocalCell st dst v = .ok st') :
    st'.pc = st.pc := by
  dsimp only [writeLocalCell] at h
  cases hG : listGet st.locals dst with
  | none => rw [hG] at h; cases h
  | some s =>
    rw [hG] at h
    cases s with
    | dead => cases h
    | direct _ =>
      dsimp only at h
      cases hS : listSet st.locals dst (.direct (some v)) with
      | none => rw [hS] at h; cases h
      | some _ => rw [hS] at h; dsimp only at h; injection h with hs; subst hs; rfl
    | stack aid =>
      dsimp only at h
      cases hH : listGet st.heap aid with
      | none => rw [hH] at h; cases h
      | some e =>
        rw [hH] at h; rcases e with ⟨ea, ec⟩; dsimp only at h
        cases ea with
        | false => simp only [Bool.not_false, ↓reduceIte] at h; cases h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hS : listSet st.heap aid { alive := true, cell := some v } with
          | none => rw [hS] at h; dsimp only at h; cases h
          | some _ => rw [hS] at h; dsimp only at h; injection h with hs; subst hs; rfl

theorem stepStmt_pc_eq (cfg : EvalConfig) (body : Body) (st : MachineState) (s : Stmt)
    {st' : MachineState} (h : stepStmt cfg body st s = .ok st') :
    st'.pc = st.pc := by
  cases s with
  | nop => injection h with hs; subst hs; rfl
  | storageLive loc =>
    dsimp only [stepStmt] at h
    cases hG : listGet st.locals loc with
    | none => rw [hG] at h; cases h
    | some _ =>
      rw [hG] at h; dsimp only at h
      cases hIn : natInList loc body.stackBackedLocals with
      | true =>
        rw [hIn] at h; simp only [↓reduceIte] at h
        cases hS : listSet st.locals loc (.stack _) with
        | none => rw [hS] at h; cases h
        | some _ => rw [hS] at h; dsimp only at h; injection h with hs; subst hs; rfl
      | false =>
        rw [hIn] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hS : listSet st.locals loc (.direct none) with
        | none => rw [hS] at h; cases h
        | some _ => rw [hS] at h; dsimp only at h; injection h with hs; subst hs; rfl
  | storageDead loc =>
    dsimp only [stepStmt] at h
    cases hZ : Nat.beq loc 0 with
    | true => rw [hZ] at h; simp only [↓reduceIte] at h; cases h
    | false =>
      rw [hZ] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hG : listGet st.locals loc with
      | none => rw [hG] at h; cases h
      | some _ =>
        rw [hG] at h; dsimp only at h
        cases hS : listSet st.locals loc .dead with
        | none => rw [hS] at h; cases h
        | some _ => rw [hS] at h; dsimp only at h; injection h with hs; subst hs; rfl
  | assign dst rv =>
    dsimp only [stepStmt] at h
    cases hR : evalRvalue cfg st rv with
    | error _ => rw [hR] at h; cases h
    | ok pr =>
      rcases pr with ⟨vr, sr⟩; rw [hR] at h; dsimp only at h
      cases hW : writeLocalCell sr dst vr with
      | error _ => rw [hW] at h; cases h
      | ok sw =>
        rw [hW] at h; dsimp only at h; injection h with hs; subst hs
        exact (writeLocalCell_pc_eq sr dst vr hW).trans (evalRvalue_pc_eq cfg st rv hR)
  | storePtr p v =>
    dsimp only [stepStmt] at h
    cases hP : evalOperand cfg st p with
    | error _ => rw [hP] at h; cases h
    | ok pp =>
      rcases pp with ⟨vp, sp⟩; rw [hP] at h
      cases vp with
      | int _ => cases h | bool _ => cases h | staticPtr _ => cases h
      | ptr aid =>
        dsimp only at h
        cases hV : evalOperand cfg sp v with
        | error _ => rw [hV] at h; cases h
        | ok pv =>
          rcases pv with ⟨vv, sv⟩; rw [hV] at h; dsimp only at h
          cases hH : listGet sv.heap aid with
          | none => rw [hH] at h; cases h
          | some e =>
            rw [hH] at h; rcases e with ⟨ea, ec⟩; dsimp only at h
            cases ea with
            | false => simp only [Bool.not_false, ↓reduceIte] at h; cases h
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              cases hS : listSet sv.heap aid { alive := true, cell := some vv } with
              | none => rw [hS] at h; dsimp only at h; cases h
              | some _ =>
                rw [hS] at h; dsimp only at h; injection h with hs; subst hs
                exact (evalOperand_pc_eq cfg sp v hV).trans (evalOperand_pc_eq cfg st p hP)
  | assume op =>
    dsimp only [stepStmt] at h
    cases hO : evalOperand cfg st op with
    | error _ => rw [hO] at h; cases h
    | ok po =>
      rcases po with ⟨vo, so⟩; rw [hO] at h
      cases vo with
      | int _ => cases h | staticPtr _ => cases h | ptr _ => cases h
      | bool b =>
        cases b with
        | false => cases h
        | true =>
          injection h with hs
          have hpc := evalOperand_pc_eq cfg st op hO
          rw [← hs]
          exact hpc

theorem agree_evalOperand_not_mentioned {cfg : EvalConfig} {x : LocalId}
    {st1 st2 : MachineState} (hAg : StateAgreeExcept x st1 st2)
    {op : Operand} (hNo : opMentionsLocal x op = false) :
    (∀ u, evalOperand cfg st1 op = .error u → evalOperand cfg st2 op = .error u) ∧
    (∀ v st1', evalOperand cfg st1 op = .ok (v, st1') →
      ∃ st2', evalOperand cfg st2 op = .ok (v, st2') ∧ StateAgreeExcept x st1' st2') := by
  cases op with
  | const c =>
    exact ⟨(fun _ h => by cases h), (fun v st1' h => by
      injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩
  | copy loc =>
    have hne : loc ≠ x := fun h => by subst h; simp [opMentionsLocal] at hNo
    have hEqLoc := hAg.2.2.2.2 loc hne
    have hReadEq : readLocalCell st1 loc = readLocalCell st2 loc := by
      unfold readLocalCell; rw [hEqLoc, hAg.2.2.1]
    dsimp only [evalOperand]
    rw [← hReadEq]
    cases hR : readLocalCell st1 loc with
    | error _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
    | ok _ => exact ⟨(fun _ h => by cases h), (fun _ _ h => by
        injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩
  | move loc =>
    have hne : loc ≠ x := fun h => by subst h; simp [opMentionsLocal] at hNo
    have hEqLoc := hAg.2.2.2.2 loc hne
    have hReadEq : readLocalCell st1 loc = readLocalCell st2 loc := by
      unfold readLocalCell; rw [hEqLoc, hAg.2.2.1]
    dsimp only [evalOperand]
    rw [← hReadEq]
    cases hR : readLocalCell st1 loc with
    | error _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
    | ok _ =>
      cases cfg.deinitMovedPlace with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨(fun _ h => by cases h), (fun _ _ h => by
          injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩
      | true =>
        simp only [↓reduceIte]
        dsimp only [deinitLocalCell]
        rw [← hEqLoc, ← hAg.2.2.1]
        cases hG : listGet st1.locals loc with
        | none =>
          dsimp only
          exact ⟨(fun _ h => by cases h), (fun _ _ h => by
            injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩
        | some sl =>
          have hG2 : listGet st2.locals loc = some sl := hEqLoc ▸ hG
          cases sl with
          | dead =>
            exact ⟨(fun _ h => by cases h), (fun _ _ h => by
              injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩
          | direct _ =>
            dsimp only
            rcases listSet_exists_of_get hG (.direct none) with ⟨ls1', hS1⟩
            rcases listSet_exists_of_get hG2 (.direct none) with ⟨ls2', hS2⟩
            rw [hS1, hS2]; dsimp only
            refine ⟨(fun _ h => by cases h), (fun _ _ h => ?_)⟩
            injection h with h1; injection h1 with hv hs; subst hv; subst hs
            refine ⟨_, rfl, hAg.1, hAg.2.1, rfl,
              by rw [listSet_length_eq hS1, listSet_length_eq hS2]; exact hAg.2.2.2.1, ?_⟩
            intro i hix
            cases hEqI : Nat.beq i loc with
            | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hS1, listGet_listSet_eq hS2]
            | false =>
              have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
              rw [listGet_listSet_ne hS1 hneI, listGet_listSet_ne hS2 hneI]; exact hAg.2.2.2.2 i hix
          | stack aid =>
            dsimp only
            cases hGH : listGet st1.heap aid with
            | none =>
              dsimp only
              exact ⟨(fun _ h => by cases h), (fun _ _ h => by
                injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩
            | some e =>
              rcases listSet_exists_of_get hGH { e with cell := none } with ⟨hp', hSH⟩
              dsimp only
              rw [hSH]; dsimp only
              exact ⟨(fun _ h => by cases h), (fun _ _ h => by
                injection h with h1; injection h1 with hv hs; subst hv; subst hs
                exact ⟨_, rfl, hAg.1, hAg.2.1, rfl, hAg.2.2.2.1, hAg.2.2.2.2⟩)⟩

theorem agree_writeLocalCell_not_mentioned {x : LocalId} {st1 st2 : MachineState}
    (hAg : StateAgreeExcept x st1 st2) {dst : LocalId} (hne : dst ≠ x) (v : Val) :
    (∀ u, writeLocalCell st1 dst v = .error u → writeLocalCell st2 dst v = .error u) ∧
    (∀ st1', writeLocalCell st1 dst v = .ok st1' →
      ∃ st2', writeLocalCell st2 dst v = .ok st2' ∧ StateAgreeExcept x st1' st2') := by
  have hEqLoc := hAg.2.2.2.2 dst hne
  dsimp only [writeLocalCell]
  rw [← hEqLoc]
  cases hG : listGet st1.locals dst with
  | none => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
  | some sl =>
    cases sl with
    | dead => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
    | direct _ =>
      dsimp only
      rcases listSet_exists_of_get hG (.direct (some v)) with ⟨ls1', hS1⟩
      have hG2 : listGet st2.locals dst = some (.direct _) := hEqLoc ▸ hG
      rcases listSet_exists_of_get hG2 (.direct (some v)) with ⟨ls2', hS2⟩
      rw [hS1, hS2]; dsimp only
      refine ⟨(fun _ h => by cases h), (fun st1' h => ?_)⟩
      injection h with hst; subst hst
      refine ⟨{ st2 with locals := ls2' }, rfl, hAg.1, hAg.2.1, hAg.2.2.1,
        by rw [listSet_length_eq hS1, listSet_length_eq hS2]; exact hAg.2.2.2.1, ?_⟩
      intro i hix
      cases hEqI : Nat.beq i dst with
      | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hS1, listGet_listSet_eq hS2]
      | false =>
        have hneI : i ≠ dst := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
        rw [listGet_listSet_ne hS1 hneI, listGet_listSet_ne hS2 hneI]; exact hAg.2.2.2.2 i hix
    | stack aid =>
      dsimp only
      rw [← hAg.2.2.1]
      cases hGH : listGet st1.heap aid with
      | none => dsimp only; exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | some e =>
        dsimp only
        cases hEa : e.alive with
        | false =>
          simp only [Bool.not_false, ↓reduceIte]
          exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
        | true =>
          rcases listSet_exists_of_get hGH { e with cell := some v } with ⟨hp', hSH⟩
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hSH' := hSH; rw [hEa] at hSH'
          rw [hSH']
          refine ⟨(fun _ h => by cases h), (fun st1' h => ?_)⟩
          injection h with hst; subst hst
          exact ⟨{ st2 with heap := hp' }, rfl, hAg.1, hAg.2.1, rfl, hAg.2.2.2.1, hAg.2.2.2.2⟩

theorem agree_evalRvalue_not_mentioned {cfg : EvalConfig} {x : LocalId}
    {st1 st2 : MachineState} (hAg : StateAgreeExcept x st1 st2)
    {rv : Rvalue} (hNo : rvMentionsLocal x rv = false) :
    (∀ u, evalRvalue cfg st1 rv = .error u → evalRvalue cfg st2 rv = .error u) ∧
    (∀ v st1', evalRvalue cfg st1 rv = .ok (v, st1') →
      ∃ st2', evalRvalue cfg st2 rv = .ok (v, st2') ∧ StateAgreeExcept x st1' st2') := by
  cases rv with
  | use op => exact agree_evalOperand_not_mentioned hAg hNo
  | subtypeCast op => exact agree_evalOperand_not_mentioned hAg hNo
  | binOp k l r =>
    simp only [rvMentionsLocal, Bool.or_eq_false_iff] at hNo
    have hL := agree_evalOperand_not_mentioned (cfg := cfg) hAg hNo.1
    dsimp only [evalRvalue]
    cases hEL : evalOperand cfg st1 l with
    | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hL.1 u hEL]), (fun _ _ h => by cases h)⟩
    | ok pl =>
      rcases pl with ⟨vl, sl⟩
      rcases hL.2 vl sl hEL with ⟨st2L, hEL2, hAgL⟩
      rw [hEL2]; dsimp only
      have hR := agree_evalOperand_not_mentioned (cfg := cfg) hAgL hNo.2
      cases hER : evalOperand cfg sl r with
      | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hR.1 u hER]), (fun _ _ h => by cases h)⟩
      | ok pr =>
        rcases pr with ⟨vr, sr⟩
        rcases hR.2 vr sr hER with ⟨st2R, hER2, hAgR⟩
        rw [hER2]; dsimp only
        cases hB : evalBinOp k vl vr with
        | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rfl), (fun _ _ h => by cases h)⟩
        | ok res => exact ⟨(fun _ h => by cases h), (fun v s h => by injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2R, rfl, hAgR⟩)⟩
  | addrOf loc =>
    have hne : loc ≠ x := fun h => by subst h; simp [rvMentionsLocal] at hNo
    have hEq := hAg.2.2.2.2 loc hne
    dsimp only [evalRvalue]; rw [← hEq, ← hAg.2.2.1]
    cases hG : listGet st1.locals loc with
    | none => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
    | some sl =>
      cases sl with
      | dead => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | direct _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | stack aid =>
        dsimp only
        cases hH : listGet st1.heap aid with
        | none => dsimp only; exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
        | some e =>
          rcases e with ⟨ea, ec⟩
          dsimp only
          cases ea with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
          | true => simp only [↓reduceIte]; exact ⟨(fun _ h => by cases h), (fun v s h => by injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩
  | derefPtr op =>
    have hO := agree_evalOperand_not_mentioned (cfg := cfg) hAg hNo
    dsimp only [evalRvalue]
    cases hEO : evalOperand cfg st1 op with
    | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hO.1 u hEO]), (fun _ _ h => by cases h)⟩
    | ok po =>
      rcases po with ⟨vp, sp⟩
      rcases hO.2 vp sp hEO with ⟨st2O, hEO2, hAgO⟩
      rw [hEO2]
      cases vp with
      | int _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | bool _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | staticPtr _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | ptr aid =>
        dsimp only
        rw [← hAgO.2.2.1]
        cases listGet sp.heap aid with
        | none => dsimp only; exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
        | some e =>
          rcases e with ⟨ea, ec⟩
          dsimp only
          cases ea with
          | false => simp only [Bool.not_false, ↓reduceIte]; exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases ec with
            | none => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
            | some v0 => exact ⟨(fun _ h => by cases h), (fun v s h => by injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2O, rfl, hAgO⟩)⟩
  | discr loc =>
    have hne : loc ≠ x := fun h => by subst h; simp [rvMentionsLocal] at hNo
    have hEq := hAg.2.2.2.2 loc hne
    have hREq : readLocalCell st1 loc = readLocalCell st2 loc := by unfold readLocalCell; rw [hEq, hAg.2.2.1]
    dsimp only [evalRvalue]; rw [← hREq]
    cases readLocalCell st1 loc with
    | error _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
    | ok v0 =>
      cases v0 with
      | bool _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | staticPtr _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | ptr _ => exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
      | int n =>
        cases hD : decide (0 ≤ n) with
        | false =>
          simp only [hD, Bool.false_eq_true, ↓reduceIte]
          exact ⟨(fun _ h => h), (fun _ _ h => by cases h)⟩
        | true =>
          simp only [hD, ↓reduceIte]
          exact ⟨(fun _ h => by cases h), (fun v s h => by injection h with h1; injection h1 with hv hs; subst hv; subst hs; exact ⟨st2, rfl, hAg⟩)⟩

theorem agree_stepStmt_not_mentioned {cfg : EvalConfig} {body1 body2 : Body}
    (hStack : body1.stackBackedLocals = body2.stackBackedLocals)
    {x : LocalId} {st1 st2 : MachineState} (hAg : StateAgreeExcept x st1 st2)
    {s : Stmt} (hNo : stmtMentionsLocal x s = false) :
    (∀ u, stepStmt cfg body1 st1 s = .error u → stepStmt cfg body2 st2 s = .error u) ∧
    (∀ st1', stepStmt cfg body1 st1 s = .ok st1' →
      ∃ st2', stepStmt cfg body2 st2 s = .ok st2' ∧ StateAgreeExcept x st1' st2') := by
  cases s with
  | nop =>
    exact ⟨(fun _ h => by cases h), (fun st1' h => by
      injection h with hst; subst hst
      exact ⟨{ st2 with stmtIdx := st2.stmtIdx + 1 }, rfl, hAg.1, congrArg Nat.succ hAg.2.1, hAg.2.2.1, hAg.2.2.2.1, hAg.2.2.2.2⟩)⟩
  | storageLive loc =>
    have hne : loc ≠ x := fun h => by subst h; simp [stmtMentionsLocal] at hNo
    have hG := hAg.2.2.2.2 loc hne
    dsimp only [stepStmt]
    rw [← hG, ← hAg.2.2.1, ← hStack]
    cases h1 : listGet st1.locals loc with
    | none => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
    | some oldSlot =>
      let hFree := freeHeapOpt st1.heap (slotAidOpt oldSlot)
      have h2 : listGet st2.locals loc = some oldSlot := hG ▸ h1
      cases natInList loc body1.stackBackedLocals with
      | true =>
        simp only [↓reduceIte]
        rcases listSet_exists_of_get h1 (.stack hFree.length) with ⟨ls1', hS1⟩
        rcases listSet_exists_of_get h2 (.stack hFree.length) with ⟨ls2', hS2⟩
        dsimp only [allocHeap]
        rw [hS1, hS2]
        refine ⟨(fun _ h => by cases h), (fun st1' h => ?_)⟩
        injection h with hst; subst hst
        refine ⟨_, rfl, hAg.1, congrArg Nat.succ hAg.2.1, rfl,
          by rw [listSet_length_eq hS1, listSet_length_eq hS2]; exact hAg.2.2.2.1, ?_⟩
        intro i hix
        cases hEqI : Nat.beq i loc with
        | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hS1, listGet_listSet_eq hS2]
        | false =>
          have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
          rw [listGet_listSet_ne hS1 hneI, listGet_listSet_ne hS2 hneI]; exact hAg.2.2.2.2 i hix
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases listSet_exists_of_get h1 (.direct none) with ⟨ls1', hS1⟩
        rcases listSet_exists_of_get h2 (.direct none) with ⟨ls2', hS2⟩
        rw [hS1, hS2]
        refine ⟨(fun _ h => by cases h), (fun st1' h => ?_)⟩
        injection h with hst; subst hst
        refine ⟨_, rfl, hAg.1, congrArg Nat.succ hAg.2.1, rfl,
          by rw [listSet_length_eq hS1, listSet_length_eq hS2]; exact hAg.2.2.2.1, ?_⟩
        intro i hix
        cases hEqI : Nat.beq i loc with
        | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hS1, listGet_listSet_eq hS2]
        | false =>
          have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
          rw [listGet_listSet_ne hS1 hneI, listGet_listSet_ne hS2 hneI]; exact hAg.2.2.2.2 i hix
  | storageDead loc =>
    have hne : loc ≠ x := fun h => by subst h; simp [stmtMentionsLocal] at hNo
    have hG := hAg.2.2.2.2 loc hne
    dsimp only [stepStmt]
    rw [← hG, ← hAg.2.2.1]
    cases Nat.beq loc 0 with
    | true => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases h1 : listGet st1.locals loc with
      | none => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | some oldSlot =>
        have h2 : listGet st2.locals loc = some oldSlot := hG ▸ h1
        rcases listSet_exists_of_get h1 .dead with ⟨ls1', hS1⟩
        rcases listSet_exists_of_get h2 .dead with ⟨ls2', hS2⟩
        rw [hS1, hS2]
        refine ⟨(fun _ h => by cases h), (fun st1' h => ?_)⟩
        injection h with hst; subst hst
        refine ⟨_, rfl, hAg.1, congrArg Nat.succ hAg.2.1, rfl,
          by rw [listSet_length_eq hS1, listSet_length_eq hS2]; exact hAg.2.2.2.1, ?_⟩
        intro i hix
        cases hEqI : Nat.beq i loc with
        | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hS1, listGet_listSet_eq hS2]
        | false =>
          have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
          rw [listGet_listSet_ne hS1 hneI, listGet_listSet_ne hS2 hneI]; exact hAg.2.2.2.2 i hix
  | assign dst rv =>
    simp only [stmtMentionsLocal, Bool.or_eq_false_iff] at hNo
    have hneDst : dst ≠ x := fun h => by subst h; simp at hNo
    have hR := agree_evalRvalue_not_mentioned (cfg := cfg) hAg hNo.2
    dsimp only [stepStmt]
    cases hER : evalRvalue cfg st1 rv with
    | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hR.1 u hER]), (fun _ h => by cases h)⟩
    | ok pair =>
      rcases pair with ⟨vv, sv⟩
      rcases hR.2 vv sv hER with ⟨st2R, hER2, hAgR⟩
      rw [hER2]; dsimp only
      have hW := agree_writeLocalCell_not_mentioned hAgR hneDst vv
      cases hEW : writeLocalCell sv dst vv with
      | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hW.1 u hEW]), (fun _ h => by cases h)⟩
      | ok sw =>
        rcases hW.2 sw hEW with ⟨st2W, hEW2, hAgW⟩
        rw [hEW2]; dsimp only
        exact ⟨(fun _ h => by cases h), (fun st1' h => by
          injection h with hst; subst hst
          exact ⟨{ st2W with stmtIdx := st2W.stmtIdx + 1 }, rfl, hAgW.1, congrArg Nat.succ hAgW.2.1, hAgW.2.2⟩)⟩
  | storePtr p v =>
    simp only [stmtMentionsLocal, Bool.or_eq_false_iff] at hNo
    have hP := agree_evalOperand_not_mentioned (cfg := cfg) hAg hNo.1
    dsimp only [stepStmt]
    cases hEP : evalOperand cfg st1 p with
    | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hP.1 u hEP]), (fun _ h => by cases h)⟩
    | ok pp =>
      rcases pp with ⟨vp, sp⟩
      rcases hP.2 vp sp hEP with ⟨st2P, hEP2, hAgP⟩
      rw [hEP2]
      cases vp with
      | int _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | bool _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | staticPtr _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | ptr aid =>
        dsimp only
        have hV := agree_evalOperand_not_mentioned (cfg := cfg) hAgP hNo.2
        cases hEV : evalOperand cfg sp v with
        | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hV.1 u hEV]), (fun _ h => by cases h)⟩
        | ok pv =>
          rcases pv with ⟨vv, sv⟩
          rcases hV.2 vv sv hEV with ⟨st2V, hEV2, hAgV⟩
          rw [hEV2]; dsimp only
          rw [← hAgV.2.2.1]
          cases hGH : listGet sv.heap aid with
          | none => dsimp only; exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
          | some e =>
            rcases e with ⟨ea, ec⟩
            dsimp only
            cases ea with
            | false =>
              simp only [Bool.not_false, ↓reduceIte]
              exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
            | true =>
              rcases listSet_exists_of_get hGH { alive := true, cell := some vv } with ⟨hp', hSH⟩
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rw [hSH]
              exact ⟨(fun _ h => by cases h), (fun st1' h => by
                injection h with hst; subst hst
                exact ⟨{ st2V with heap := hp', stmtIdx := st2V.stmtIdx + 1 }, rfl,
                  hAgV.1, congrArg Nat.succ hAgV.2.1, rfl, hAgV.2.2.2.1, hAgV.2.2.2.2⟩)⟩
  | assume op =>
    have hO := agree_evalOperand_not_mentioned (cfg := cfg) hAg hNo
    dsimp only [stepStmt]
    cases hEO : evalOperand cfg st1 op with
    | error u => exact ⟨(fun u' h => by injection h with hu; subst hu; rw [hO.1 u hEO]), (fun _ h => by cases h)⟩
    | ok po =>
      rcases po with ⟨vo, so⟩
      rcases hO.2 vo so hEO with ⟨st2O, hEO2, hAgO⟩
      rw [hEO2]
      cases vo with
      | int _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | staticPtr _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | ptr _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | bool b =>
        cases b with
        | false => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
        | true =>
          exact ⟨(fun _ h => by cases h), (fun st1' h => by
            injection h with hst; subst hst
            exact ⟨{ st2O with stmtIdx := st2O.stmtIdx + 1 }, rfl, hAgO.1, congrArg Nat.succ hAgO.2.1, hAgO.2.2⟩)⟩

theorem agree_stepTerm_not_mentioned {cfg : EvalConfig} {x : LocalId} (hx0 : x ≠ 0)
    {st1 st2 : MachineState} (hAg : StateAgreeExcept x st1 st2)
    {t : Term} (hNo : termMentionsLocal x t = false) (hGe : termTargetsGe1 t = true) :
    (∀ out, stepTerm cfg st1 t = .stop out → stepTerm cfg st2 t = .stop out) ∧
    (∀ st1', stepTerm cfg st1 t = .cont st1' →
      ∃ st2', stepTerm cfg st2 t = .cont st2' ∧ st1'.pc ≥ 1 ∧ StateAgreeExcept x st1' st2') := by
  cases t with
  | goto tgt =>
    exact ⟨(fun _ h => by cases h), (fun st1' h => by
      injection h with hst; subst hst
      exact ⟨{ st2 with pc := tgt, stmtIdx := 0 }, rfl, of_decide_eq_true hGe, rfl, rfl, hAg.2.2⟩)⟩
  | unreachable => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
  | ret =>
    have h0ne : (0 : LocalId) ≠ x := fun h => hx0 h.symm
    have hEq0 := hAg.2.2.2.2 0 h0ne
    have hReadEq : readLocalCell st1 0 = readLocalCell st2 0 := by
      unfold readLocalCell; rw [hEq0, hAg.2.2.1]
    dsimp only [stepTerm]; rw [← hReadEq]
    cases readLocalCell st1 0 with
    | error _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
    | ok _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
  | switchInt discr arms oth =>
    have hO := agree_evalOperand_not_mentioned (cfg := cfg) hAg hNo
    dsimp only [stepTerm]
    cases hEO : evalOperand cfg st1 discr with
    | error u => exact ⟨(fun _ h => by injection h with hu; subst hu; rw [hO.1 u hEO]), (fun _ h => by cases h)⟩
    | ok po =>
      rcases po with ⟨vo, so⟩
      rcases hO.2 vo so hEO with ⟨st2O, hEO2, hAgO⟩
      rw [hEO2]; dsimp only
      cases discrBits vo with
      | error _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
      | ok bits =>
        dsimp only [termTargetsGe1] at hGe
        simp only [Bool.and_eq_true] at hGe
        have hTgtGe : lookupSwitchTarget bits arms oth ≥ 1 := armListTargetsGe1_lookup hGe.1 hGe.2
        exact ⟨(fun _ h => by cases h), (fun st1' h => by
          injection h with hst; subst hst
          exact ⟨{ st2O with pc := lookupSwitchTarget bits arms oth, stmtIdx := 0 }, rfl,
            hTgtGe, rfl, rfl, hAgO.2.2⟩)⟩
  | assert cond exp tgt optOvf =>
    dsimp only [stepTerm]
    cases (optOvf && !cfg.enforceOptionalOverflow) with
    | true =>
      simp only [↓reduceIte]
      exact ⟨(fun _ h => by cases h), (fun st1' h => by
        injection h with hst; subst hst
        exact ⟨{ st2 with pc := tgt, stmtIdx := 0 }, rfl, of_decide_eq_true hGe, rfl, rfl, hAg.2.2⟩)⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hO := agree_evalOperand_not_mentioned (cfg := cfg) hAg hNo
      cases hEO : evalOperand cfg st1 cond with
      | error u => exact ⟨(fun _ h => by injection h with hu; subst hu; rw [hO.1 u hEO]), (fun _ h => by cases h)⟩
      | ok po =>
        rcases po with ⟨vo, so⟩
        rcases hO.2 vo so hEO with ⟨st2O, hEO2, hAgO⟩
        rw [hEO2]
        cases vo with
        | int _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
        | staticPtr _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
        | ptr _ => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
        | bool b =>
          dsimp only
          cases (b == exp) with
          | false => exact ⟨(fun _ h => h), (fun _ h => by cases h)⟩
          | true =>
            exact ⟨(fun _ h => by cases h), (fun st1' h => by
              injection h with hst; subst hst
              exact ⟨{ st2O with pc := tgt, stmtIdx := 0 }, rfl, of_decide_eq_true hGe, rfl, rfl, hAgO.2.2⟩)⟩

theorem agree_runBody_tail {cfg : EvalConfig} {body1 body2 : Body}
    {x : LocalId} (hx0 : x ≠ 0) {tailBlocks : List BasicBlock}
    (hStack : body1.stackBackedLocals = body2.stackBackedLocals)
    (hTail1 : ∀ k, listGet body1.blocks (k + 1) = listGet tailBlocks k)
    (hTail2 : ∀ k, listGet body2.blocks (k + 1) = listGet tailBlocks k)
    (hSafe : bodyTailSafeForSciMove x tailBlocks = true) :
    ∀ fuel st1 st2,
      st1.pc ≥ 1 → StateAgreeExcept x st1 st2 →
      runBody cfg body1 st1 fuel = runBody cfg body2 st2 fuel := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; rfl
  | succ f' ih =>
    intro st1 st2 hpc1 hAg
    cases hP : st1.pc with
    | zero => rw [hP] at hpc1; cases hpc1
    | succ pk =>
      have hpc2 : st2.pc = pk + 1 := hAg.1.symm.trans hP
      dsimp only [runBody]
      rw [hP, hpc2, hTail1 pk, hTail2 pk]
      cases hBB : listGet tailBlocks pk with
      | none => rfl
      | some bb =>
        dsimp only
        have hBBInv := bodyTailSafe_get hSafe hBB
        simp only [blockMentionsLocal, Bool.or_eq_false_iff] at hBBInv
        rw [← hAg.2.1]
        cases hSt : listGet bb.stmts st1.stmtIdx with
        | some s =>
          dsimp only
          have hSNo := listAny_false_get hBBInv.1.1 hSt
          have hStep := agree_stepStmt_not_mentioned (cfg := cfg) hStack hAg hSNo
          cases hE : stepStmt cfg body1 st1 s with
          | error u => dsimp only; rw [hStep.1 u hE]
          | ok st1' =>
            dsimp only
            rcases hStep.2 st1' hE with ⟨st2', hE2, hAg'⟩
            rw [hE2]; dsimp only
            have hpc1' : st1'.pc ≥ 1 := by
              rw [stepStmt_pc_eq cfg body1 st1 s hE, hP]; exact Nat.succ_pos _
            exact ih st1' st2' hpc1' hAg'
        | none =>
          dsimp only
          have hTerm := agree_stepTerm_not_mentioned (cfg := cfg) hx0 hAg hBBInv.1.2 hBBInv.2
          cases hE : stepTerm cfg st1 bb.term with
          | stop out => dsimp only; rw [hTerm.1 out hE]
          | cont st1' =>
            dsimp only
            rcases hTerm.2 st1' hE with ⟨st2', hE2, hpc1', hAg'⟩
            rw [hE2]; dsimp only
            exact ih st1' st2' hpc1' hAg'

theorem deinitLocalCell_direct_agree {x : LocalId} {st : MachineState} {oX : Option Val}
    (hGX : listGet st.locals x = some (.direct oX)) :
    StateAgreeExcept x st (deinitLocalCell st x) := by
  dsimp only [deinitLocalCell]
  rw [hGX]; dsimp only
  rcases listSet_exists_of_get hGX (.direct none) with ⟨ls', hSet⟩
  rw [hSet]; dsimp only
  refine ⟨rfl, rfl, rfl, (listSet_length_eq hSet).symm, ?_⟩
  intro i hix
  exact (listGet_listSet_ne hSet hix).symm

theorem evalRvalue_sci_agree (cfg : EvalConfig) (b x : LocalId) (k : Int)
    (op : BinOpKind) (hop : op = .eq ∨ op = .ne)
    (lhs rhs : Operand) (hValid : isValidSciBinOp b x k op lhs rhs = true)
    (st : MachineState) (oX : Option Val)
    (hGX : listGet st.locals x = some (.direct oX)) :
    (oX = none →
      evalRvalue cfg st (.binOp op (downgradeMoveOperand x lhs) (downgradeMoveOperand x rhs)) = .error .uninitRead ∧
      evalRvalue cfg st (.binOp op lhs rhs) = .error .uninitRead) ∧
    (∀ vx, oX = some vx → (∀ n, vx ≠ .int n) →
      ∃ u, evalRvalue cfg st (.binOp op (downgradeMoveOperand x lhs) (downgradeMoveOperand x rhs)) = .error u ∧
           evalRvalue cfg st (.binOp op lhs rhs) = .error u) ∧
    (∀ n : Int, oX = some (.int n) →
      let bRes := match op with | .eq => decide (n = k) | .ne => decide (n ≠ k) | _ => false
      evalRvalue cfg st (.binOp op (downgradeMoveOperand x lhs) (downgradeMoveOperand x rhs)) =
        .ok (.bool bRes, st) ∧
      ∃ stS, evalRvalue cfg st (.binOp op lhs rhs) = .ok (.bool bRes, stS) ∧
        StateAgreeExcept x st stS) := by
  have hShapes := sci_valid_shapes hValid
  refine ⟨?_, ?_, ?_⟩
  · intro hNone; subst hNone
    have hR : readLocalCell st x = .error .uninitRead := by unfold readLocalCell; rw [hGX]
    rcases hShapes with ⟨hL | hL, hRhs⟩ | ⟨hLhs, hRop | hRop⟩ <;>
      subst_vars <;>
      · dsimp only [evalRvalue, downgradeMoveOperand]
        try simp only [Nat.beq_refl, ↓reduceIte]
        dsimp only [evalOperand, constToVal]
        rw [hR]
        exact ⟨rfl, rfl⟩
  · intro vx hSome hNonInt; subst hSome
    have hR : readLocalCell st x = .ok vx := by unfold readLocalCell; rw [hGX]
    refine ⟨.badOperandType, ?_⟩
    have hBinL : evalBinOp op vx (.int k) = .error .badOperandType := by
      cases vx with
      | int m => exact False.elim (hNonInt m rfl)
      | bool _ => cases hop with | inl h => subst h; rfl | inr h => subst h; rfl
      | staticPtr _ => cases hop with | inl h => subst h; rfl | inr h => subst h; rfl
      | ptr _ => cases hop with | inl h => subst h; rfl | inr h => subst h; rfl
    have hBinR : evalBinOp op (.int k) vx = .error .badOperandType := by
      cases vx with
      | int m => exact False.elim (hNonInt m rfl)
      | bool _ => cases hop with | inl h => subst h; rfl | inr h => subst h; rfl
      | staticPtr _ => cases hop with | inl h => subst h; rfl | inr h => subst h; rfl
      | ptr _ => cases hop with | inl h => subst h; rfl | inr h => subst h; rfl
    rcases hShapes with ⟨hL | hL, hRhs⟩ | ⟨hLhs, hRop | hRop⟩ <;>
      subst_vars <;>
      · dsimp only [evalRvalue, downgradeMoveOperand]
        try simp only [Nat.beq_refl, ↓reduceIte]
        dsimp only [evalOperand, constToVal]
        rw [hR]; dsimp only
        first | rw [hBinL] | rw [hBinR]
        exact ⟨rfl, rfl⟩
  · intro n hSome; subst hSome
    have hR : readLocalCell st x = .ok (.int n) := by unfold readLocalCell; rw [hGX]
    have hCommEq : decide (k = n) = decide (n = k) := (decide_eq_comm n k).symm
    have hCommNe : decide (k ≠ n) = decide (n ≠ k) := (decide_ne_comm n k).symm
    have hAgDeinit := deinitLocalCell_direct_agree hGX
    have hAgSelf : StateAgreeExcept x st st := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    rcases hShapes with ⟨hL | hL, hRhs⟩ | ⟨hLhs, hRop | hRop⟩
    · subst hL; subst hRhs
      dsimp only [evalRvalue, downgradeMoveOperand, evalOperand, constToVal]
      rw [hR]; dsimp only
      cases hop with
      | inl hEq => subst hEq; exact ⟨rfl, st, rfl, hAgSelf⟩
      | inr hNe => subst hNe; exact ⟨rfl, st, rfl, hAgSelf⟩
    · subst hL; subst hRhs
      dsimp only [evalRvalue, downgradeMoveOperand]
      simp only [Nat.beq_refl, ↓reduceIte]
      dsimp only [evalOperand, constToVal]
      rw [hR]; dsimp only
      cases hD : cfg.deinitMovedPlace with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hop with
        | inl hEq => subst hEq; exact ⟨rfl, st, rfl, hAgSelf⟩
        | inr hNe => subst hNe; exact ⟨rfl, st, rfl, hAgSelf⟩
      | true =>
        simp only [↓reduceIte]
        cases hop with
        | inl hEq => subst hEq; exact ⟨rfl, deinitLocalCell st x, rfl, hAgDeinit⟩
        | inr hNe => subst hNe; exact ⟨rfl, deinitLocalCell st x, rfl, hAgDeinit⟩
    · subst hLhs; subst hRop
      dsimp only [evalRvalue, downgradeMoveOperand, evalOperand, constToVal]
      rw [hR]; dsimp only
      cases hop with
      | inl hEq => subst hEq; dsimp only [evalBinOp]; rw [hCommEq]; exact ⟨rfl, st, rfl, hAgSelf⟩
      | inr hNe => subst hNe; dsimp only [evalBinOp]; rw [hCommNe]; exact ⟨rfl, st, rfl, hAgSelf⟩
    · subst hLhs; subst hRop
      dsimp only [evalRvalue, downgradeMoveOperand]
      simp only [Nat.beq_refl, ↓reduceIte]
      dsimp only [evalOperand, constToVal]
      rw [hR]; dsimp only
      cases hD : cfg.deinitMovedPlace with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hop with
        | inl hEq => subst hEq; dsimp only [evalBinOp]; rw [hCommEq]; exact ⟨rfl, st, rfl, hAgSelf⟩
        | inr hNe => subst hNe; dsimp only [evalBinOp]; rw [hCommNe]; exact ⟨rfl, st, rfl, hAgSelf⟩
      | true =>
        simp only [↓reduceIte]
        cases hop with
        | inl hEq => subst hEq; dsimp only [evalBinOp]; rw [hCommEq]; exact ⟨rfl, deinitLocalCell st x, rfl, hAgDeinit⟩
        | inr hNe => subst hNe; dsimp only [evalBinOp]; rw [hCommNe]; exact ⟨rfl, deinitLocalCell st x, rfl, hAgDeinit⟩

/-- Exact bidirectional equivalence (`runBody ... = runBody ...`, hence `↔` on every
    `ExecOutcome` including `.returned`, `.panicked`, and `.ub`) for `SimplifyComparisonIntegral`,
    covering `Eq`/`Ne`, both `[0, otherwise]` and `[1, otherwise]` layouts, `Move -> Copy`
    downgrade under both `deinitMovedPlace` modes, and safe continuation across all tail blocks. -/
theorem simplifyCmp_bidirectional_iff
    (cfg : EvalConfig) (b x : LocalId) (k : Int)
    (op : BinOpKind) (hop : op = .eq ∨ op = .ne)
    (lhs rhs : Operand)
    (hValid : isValidSciBinOp b x k op lhs rhs = true)
    (armVal : Int) (hArm : armVal = 0 ∨ armVal = 1)
    (bbArm bbOth : BlockId) (stackLocs : List LocalId) (tailBlocks : List BasicBlock)
    (hxNe0 : x ≠ 0)
    (hTailSafe : bodyTailSafeForSciMove x tailBlocks = true)
    (hArmGe : bbArm ≥ 1) (hOthGe : bbOth ≥ 1)
    (st : MachineState) (fuel : Nat)
    (hpc0 : st.pc = 0) (hsi0 : st.stmtIdx = 0)
    (hX : ∃ oX, listGet st.locals x = some (.direct oX))
    (hB : ∃ oB, listGet st.locals b = some (.direct oB)) :
    let bbSrc : BasicBlock :=
      { stmts := [.assign b (.binOp op lhs rhs)]
        term := .switchInt (.copy b) [(armVal, bbArm)] bbOth }
    let bbTgt : BasicBlock := rewriteSciBlock b x k op lhs rhs armVal bbArm bbOth
    let bodySrc : Body := { numLocals := 0, stackBackedLocals := stackLocs, blocks := bbSrc :: tailBlocks }
    let bodyTgt : Body := { numLocals := 0, stackBackedLocals := stackLocs, blocks := bbTgt :: tailBlocks }
    runBody cfg bodyTgt st fuel = runBody cfg bodySrc st fuel := by
  rcases hX with ⟨oX, hGX⟩
  rcases hB with ⟨oB, hGB⟩
  rcases st with ⟨spc, ssi, sloc, sheap⟩
  dsimp only at hpc0 hsi0
  subst hpc0; subst hsi0
  have hBX : b ≠ x := by
    unfold isValidSciBinOp at hValid
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hValid
    intro hEq; rw [hEq, Nat.beq_refl] at hValid; cases hValid.1.2
  have hXB : x ≠ b := fun h => hBX h.symm
  cases hop with
  | inl hEq =>
    subst hEq
    cases fuel with
    | zero => rfl
    | succ f1 =>
      have hSci := evalRvalue_sci_agree cfg b x k .eq (Or.inl rfl) lhs rhs hValid { pc := 0, stmtIdx := 0, locals := sloc, heap := sheap } oX hGX
      dsimp only [runBody, rewriteSciBlock]
      rw [listGet_cons_zero, listGet_cons_zero]; dsimp only
      rw [listGet_cons_zero, listGet_cons_zero]; dsimp only [stepStmt]
      cases oX with
      | none =>
        rcases hSci.1 rfl with ⟨hT, hS⟩
        rw [hT, hS]
      | some vx =>
        cases vx with
        | bool bv =>
          rcases hSci.2.1 (.bool bv) rfl (fun _ h => by cases h) with ⟨u, hT, hS⟩
          rw [hT, hS]
        | staticPtr sid =>
          rcases hSci.2.1 (.staticPtr sid) rfl (fun _ h => by cases h) with ⟨u, hT, hS⟩
          rw [hT, hS]
        | ptr aid =>
          rcases hSci.2.1 (.ptr aid) rfl (fun _ h => by cases h) with ⟨u, hT, hS⟩
          rw [hT, hS]
        | int n =>
          rcases hSci.2.2 n rfl with ⟨hTgtEval, stS0, hSrcEval, hAg0⟩
          rw [hTgtEval, hSrcEval]; dsimp only
          let bRes := decide (n = k)
          rcases listSet_exists_of_get hGB (.direct (some (.bool bRes))) with ⟨lsT, hSetT⟩
          have hWTgt : writeLocalCell { pc := 0, stmtIdx := 0, locals := sloc, heap := sheap } b (.bool bRes) = .ok { pc := 0, stmtIdx := 0, locals := lsT, heap := sheap } := by
            dsimp only [writeLocalCell]; rw [hGB, hSetT]
          have hW := agree_writeLocalCell_not_mentioned hAg0 hBX (.bool bRes)
          rcases hW.2 { pc := 0, stmtIdx := 0, locals := lsT, heap := sheap } hWTgt with ⟨stS1, hWSrc, hAg1⟩
          rw [hWTgt, hWSrc]; dsimp only
          have hGetB_Src : listGet stS1.locals b = some (.direct (some (.bool bRes))) := by
            have hEqB := hAg1.2.2.2.2 b hBX
            rw [← hEqB]; exact listGet_listSet_eq hSetT
          have hGetX_Tgt : listGet lsT x = some (.direct (some (.int n))) := by
            rw [listGet_listSet_ne hSetT hXB]; exact hGX
          cases f1 with
          | zero => rfl
          | succ f2 =>
            have hpcS1 : stS1.pc = 0 := hAg1.1.symm
            have hsiS1 : stS1.stmtIdx = 0 := hAg1.2.1.symm
            dsimp only [runBody]
            rw [hpcS1, hsiS1, listGet_cons_zero, listGet_cons_zero]
            dsimp only
            rw [sci_listGet_succ_one, sci_listGet_succ_one]
            dsimp only [stepTerm, rewriteSciTerm, evalOperand, readLocalCell, discrBits]
            rw [hGetX_Tgt, hGetB_Src]; dsimp only
            have hTgtEq := sci_target_eq .eq armVal n k bbArm bbOth (Or.inl rfl) hArm
            dsimp only at hTgtEq
            rw [← hTgtEq]
            let tgt := lookupSwitchTarget (if bRes then 1 else 0) [(armVal, bbArm)] bbOth
            have hTgtGe : tgt ≥ 1 := armListTargetsGe1_lookup
              (by simp only [armListTargetsGe1, List.foldr, Bool.and_true]; exact decide_eq_true hArmGe)
              (decide_eq_true hOthGe)
            have hAg2 : StateAgreeExcept x { pc := tgt, stmtIdx := 0, locals := lsT, heap := sheap }
                { stS1 with pc := tgt, stmtIdx := 0 } :=
              ⟨rfl, rfl, hAg1.2.2.1, hAg1.2.2.2.1, hAg1.2.2.2.2⟩
            exact agree_runBody_tail
              (body1 := { numLocals := 0, stackBackedLocals := stackLocs, blocks := rewriteSciBlock b x k .eq lhs rhs armVal bbArm bbOth :: tailBlocks })
              (body2 := { numLocals := 0, stackBackedLocals := stackLocs, blocks := { stmts := [.assign b (.binOp .eq lhs rhs)], term := .switchInt (.copy b) [(armVal, bbArm)] bbOth } :: tailBlocks })
              hxNe0 rfl (fun _ => rfl) (fun _ => rfl) hTailSafe f2 _ _ hTgtGe hAg2
  | inr hNe =>
    subst hNe
    cases fuel with
    | zero => rfl
    | succ f1 =>
      have hSci := evalRvalue_sci_agree cfg b x k .ne (Or.inr rfl) lhs rhs hValid { pc := 0, stmtIdx := 0, locals := sloc, heap := sheap } oX hGX
      dsimp only [runBody, rewriteSciBlock]
      rw [listGet_cons_zero, listGet_cons_zero]; dsimp only
      rw [listGet_cons_zero, listGet_cons_zero]; dsimp only [stepStmt]
      cases oX with
      | none =>
        rcases hSci.1 rfl with ⟨hT, hS⟩
        rw [hT, hS]
      | some vx =>
        cases vx with
        | bool bv =>
          rcases hSci.2.1 (.bool bv) rfl (fun _ h => by cases h) with ⟨u, hT, hS⟩
          rw [hT, hS]
        | staticPtr sid =>
          rcases hSci.2.1 (.staticPtr sid) rfl (fun _ h => by cases h) with ⟨u, hT, hS⟩
          rw [hT, hS]
        | ptr aid =>
          rcases hSci.2.1 (.ptr aid) rfl (fun _ h => by cases h) with ⟨u, hT, hS⟩
          rw [hT, hS]
        | int n =>
          rcases hSci.2.2 n rfl with ⟨hTgtEval, stS0, hSrcEval, hAg0⟩
          rw [hTgtEval, hSrcEval]; dsimp only
          let bRes := decide (n ≠ k)
          rcases listSet_exists_of_get hGB (.direct (some (.bool bRes))) with ⟨lsT, hSetT⟩
          have hWTgt : writeLocalCell { pc := 0, stmtIdx := 0, locals := sloc, heap := sheap } b (.bool bRes) = .ok { pc := 0, stmtIdx := 0, locals := lsT, heap := sheap } := by
            dsimp only [writeLocalCell]; rw [hGB, hSetT]
          have hW := agree_writeLocalCell_not_mentioned hAg0 hBX (.bool bRes)
          rcases hW.2 { pc := 0, stmtIdx := 0, locals := lsT, heap := sheap } hWTgt with ⟨stS1, hWSrc, hAg1⟩
          rw [hWTgt, hWSrc]; dsimp only
          have hGetB_Src : listGet stS1.locals b = some (.direct (some (.bool bRes))) := by
            have hEqB := hAg1.2.2.2.2 b hBX
            rw [← hEqB]; exact listGet_listSet_eq hSetT
          have hGetX_Tgt : listGet lsT x = some (.direct (some (.int n))) := by
            rw [listGet_listSet_ne hSetT hXB]; exact hGX
          cases f1 with
          | zero => rfl
          | succ f2 =>
            have hpcS1 : stS1.pc = 0 := hAg1.1.symm
            have hsiS1 : stS1.stmtIdx = 0 := hAg1.2.1.symm
            dsimp only [runBody]
            rw [hpcS1, hsiS1, listGet_cons_zero, listGet_cons_zero]
            dsimp only
            rw [sci_listGet_succ_one, sci_listGet_succ_one]
            dsimp only [stepTerm, rewriteSciTerm, evalOperand, readLocalCell, discrBits]
            rw [hGetX_Tgt, hGetB_Src]; dsimp only
            have hTgtEq := sci_target_eq .ne armVal n k bbArm bbOth (Or.inr rfl) hArm
            dsimp only at hTgtEq
            rw [← hTgtEq]
            let tgt := lookupSwitchTarget (if bRes then 1 else 0) [(armVal, bbArm)] bbOth
            have hTgtGe : tgt ≥ 1 := armListTargetsGe1_lookup
              (by simp only [armListTargetsGe1, List.foldr, Bool.and_true]; exact decide_eq_true hArmGe)
              (decide_eq_true hOthGe)
            have hAg2 : StateAgreeExcept x { pc := tgt, stmtIdx := 0, locals := lsT, heap := sheap }
                { stS1 with pc := tgt, stmtIdx := 0 } :=
              ⟨rfl, rfl, hAg1.2.2.1, hAg1.2.2.2.1, hAg1.2.2.2.2⟩
            exact agree_runBody_tail
              (body1 := { numLocals := 0, stackBackedLocals := stackLocs, blocks := rewriteSciBlock b x k .ne lhs rhs armVal bbArm bbOth :: tailBlocks })
              (body2 := { numLocals := 0, stackBackedLocals := stackLocs, blocks := { stmts := [.assign b (.binOp .ne lhs rhs)], term := .switchInt (.copy b) [(armVal, bbArm)] bbOth } :: tailBlocks })
              hxNe0 rfl (fun _ => rfl) (fun _ => rfl) hTailSafe f2 _ _ hTgtGe hAg2
/-! ## Section 5: `SsaRangePropagation` Soundness and Hazards -/

structure WrappingRange where
  start : Int
  stop : Int
  deriving DecidableEq, Repr

def WrappingRange.contains (r : WrappingRange) (v : Int) : Bool :=
  decide (r.start ≤ v) && decide (v ≤ r.stop)

def tryAsConstant (r : WrappingRange) : Option Int :=
  if decide (r.start = r.stop) then some r.start else none

def ssaMaxSwitchTargets : Nat := 16

def countTargetMatches (arms : List (Int × BlockId)) (tgt : BlockId) : Nat :=
  List.foldr (fun p ih => (if Nat.beq p.2 tgt then 1 else 0) + ih) 0 arms

def findUniqueArmVal (arms : List (Int × BlockId)) (tgt : BlockId) : Option Int :=
  List.foldr (fun p ih => if Nat.beq p.2 tgt then some p.1 else ih) none arms

def ssaSwitchUniqueVal (arms : List (Int × BlockId)) (oth tgt : BlockId)
    (hasUniquePred : Bool) (isBool : Bool) : Option ConstVal :=
  if hasUniquePred && decide (arms.length + 1 < ssaMaxSwitchTargets) then
    if Nat.beq tgt oth then
      if isBool then
        match arms with
        | [(0, a0)] => if !Nat.beq a0 oth then some (.bool true) else none
        | [(1, a1)] => if !Nat.beq a1 oth then some (.bool false) else none
        | _ => none
      else none
    else
      if Nat.beq (countTargetMatches arms tgt) 1 then
        match findUniqueArmVal arms tgt with
        | some k => some (.int k)
        | none => none
      else none
  else none

theorem wrappingRange_tryAsConstant_iff (r : WrappingRange) (hOrd : r.start ≤ r.stop) (k : Int) :
    tryAsConstant r = some k ↔ (r.contains k = true ∧ ∀ v, r.contains v = true → v = k) := by
  constructor
  · intro h
    dsimp [tryAsConstant] at h
    cases hEq : decide (r.start = r.stop) with
    | false => rw [hEq] at h; cases h
    | true =>
      rw [hEq] at h
      simp only [↓reduceIte] at h
      injection h with hsk
      have hss : r.start = r.stop := of_decide_eq_true hEq
      have hrk1 : r.start = k := hsk
      have hrk2 : r.stop = k := hss.symm.trans hsk
      refine ⟨?_, ?_⟩
      · dsimp [WrappingRange.contains]
        rw [hrk1, hrk2]
        simp only [Bool.and_eq_true]
        exact ⟨decide_eq_true (Int.le_refl k), decide_eq_true (Int.le_refl k)⟩
      · intro v hv
        dsimp [WrappingRange.contains] at hv
        simp only [Bool.and_eq_true] at hv
        have h1 : k ≤ v := hrk1 ▸ of_decide_eq_true hv.1
        have h2 : v ≤ k := hrk2 ▸ of_decide_eq_true hv.2
        exact Int.le_antisymm h2 h1
  · intro h
    rcases h with ⟨_, hAll⟩
    have hStartC : r.contains r.start = true := by
      dsimp [WrappingRange.contains]
      simp only [Bool.and_eq_true]
      exact ⟨decide_eq_true (Int.le_refl _), decide_eq_true hOrd⟩
    have hStopC : r.contains r.stop = true := by
      dsimp [WrappingRange.contains]
      simp only [Bool.and_eq_true]
      exact ⟨decide_eq_true hOrd, decide_eq_true (Int.le_refl _)⟩
    have hsk : r.start = k := hAll r.start hStartC
    have htk : r.stop = k := hAll r.stop hStopC
    have hss : r.start = r.stop := hsk.trans htk.symm
    dsimp [tryAsConstant]
    have hEq : decide (r.start = r.stop) = true := decide_eq_true hss
    rw [hEq]; simp only [↓reduceIte, hsk]

def replaceOpCopy (x : LocalId) (c : ConstVal) : Operand → Operand
  | .copy loc => if Nat.beq loc x then .const c else .copy loc
  | op => op

def replaceOpMoveCopy (x : LocalId) (c : ConstVal) : Operand → Operand
  | .copy loc => if Nat.beq loc x then .const c else .copy loc
  | .move loc => if Nat.beq loc x then .const c else .move loc
  | op => op

def replaceRvOp (f : Operand → Operand) : Rvalue → Rvalue
  | .use op => .use (f op)
  | .binOp k l r => .binOp k (f l) (f r)
  | .addrOf loc => .addrOf loc
  | .derefPtr op => .derefPtr (f op)
  | .discr loc => .discr loc
  | .subtypeCast op => .subtypeCast (f op)

def replaceStmtOp (f : Operand → Operand) : Stmt → Stmt
  | .assign dst rv => .assign dst (replaceRvOp f rv)
  | .storePtr p v => .storePtr (f p) (f v)
  | .assume op => .assume (f op)
  | s => s

def replaceTermOp (f : Operand → Operand) : Term → Term
  | .switchInt op arms oth => .switchInt (f op) arms oth
  | .assert cond exp tgt opt => .assert (f cond) exp tgt opt
  | t => t

def replaceBodyOp (f : Operand → Operand) (b : Body) : Body :=
  { b with blocks := b.blocks.map (fun bb =>
      { stmts := bb.stmts.map (replaceStmtOp f), term := replaceTermOp f bb.term }) }

def opPreservesMoveX (x : LocalId) : Operand → Bool
  | .move loc => !Nat.beq loc x
  | _ => true

def rvPreservesMoveX (x : LocalId) : Rvalue → Bool
  | .use op | .subtypeCast op | .derefPtr op => opPreservesMoveX x op
  | .binOp _ l r => opPreservesMoveX x l && opPreservesMoveX x r
  | .addrOf loc => !Nat.beq loc x
  | .discr _ => true

def ssaStmtNoWriteX (x : LocalId) : Stmt → Bool
  | .nop => true
  | .storageLive loc | .storageDead loc => !Nat.beq loc x
  | .assign dst _ => !Nat.beq dst x
  | .storePtr _ _ | .assume _ => true

def ssaStmtSafeCopyX (x : LocalId) (s : Stmt) : Bool :=
  ssaStmtNoWriteX x s &&
  match s with
  | .assign _ rv => rvPreservesMoveX x rv
  | .storePtr p v => opPreservesMoveX x p && opPreservesMoveX x v
  | .assume op => opPreservesMoveX x op
  | _ => true

def ssaTermSafeCopyX (x : LocalId) : Term → Bool
  | .switchInt op _ _ | .assert op _ _ _ => opPreservesMoveX x op
  | _ => true

def ssaBlockSafeCopyX (x : LocalId) (bb : BasicBlock) : Bool :=
  bb.stmts.all (ssaStmtSafeCopyX x) && ssaTermSafeCopyX x bb.term

def ssaBodySafeCopyX (x : LocalId) (bbs : List BasicBlock) : Bool :=
  List.foldr (fun bb ih => ssaBlockSafeCopyX x bb && ih) true bbs

def ssaBodyNoWriteX (x : LocalId) (bbs : List BasicBlock) : Bool :=
  List.foldr (fun bb ih => bb.stmts.all (ssaStmtNoWriteX x) && ih) true bbs

theorem ssaBodySafeCopy_get {x : LocalId} {bbs : List BasicBlock}
    (h : ssaBodySafeCopyX x bbs = true) {n : Nat} {bb : BasicBlock}
    (hg : listGet bbs n = some bb) :
    ssaBlockSafeCopyX x bb = true := by
  induction bbs generalizing n with
  | nil => rw [listGet_nil] at hg; cases hg
  | cons b tl ih =>
    dsimp only [ssaBodySafeCopyX, List.foldr] at h
    simp only [Bool.and_eq_true] at h
    cases n with
    | zero => injection hg with heq; subst heq; exact h.1
    | succ k => exact ih h.2 hg

theorem ssaBodyNoWrite_get {x : LocalId} {bbs : List BasicBlock}
    (h : ssaBodyNoWriteX x bbs = true) {n : Nat} {bb : BasicBlock}
    (hg : listGet bbs n = some bb) :
    bb.stmts.all (ssaStmtNoWriteX x) = true := by
  induction bbs generalizing n with
  | nil => rw [listGet_nil] at hg; cases hg
  | cons b tl ih =>
    dsimp only [ssaBodyNoWriteX, List.foldr] at h
    simp only [Bool.and_eq_true] at h
    cases n with
    | zero => injection hg with heq; subst heq; exact h.1
    | succ k => exact ih h.2 hg

theorem listAll_true_get {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.all p = true) {n : Nat} {v : α} (hg : listGet xs n = some v) :
    p v = true := by
  induction xs generalizing n with
  | nil => rw [listGet_nil] at hg; cases hg
  | cons x tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases n with
    | zero => injection hg with heq; subst heq; exact h.1
    | succ k => exact ih h.2 hg

theorem evalOperand_preserves_direct_x (cfg : EvalConfig) (x : LocalId) (oX : Option Val)
    {st : MachineState} (hX : listGet st.locals x = some (.direct oX))
    {op : Operand} (hNo : opPreservesMoveX x op = true)
    {v : Val} {st' : MachineState} (hEval : evalOperand cfg st op = .ok (v, st')) :
    listGet st'.locals x = some (.direct oX) := by
  cases op with
  | const _ =>
    injection hEval with h1; injection h1 with _ hs; subst hs; exact hX
  | copy loc =>
    dsimp only [evalOperand] at hEval
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at hEval; cases hEval
    | ok _ => rw [hR] at hEval; injection hEval with h1; injection h1 with _ hs; subst hs; exact hX
  | move loc =>
    have hne : x ≠ loc := fun h => by subst h; simp [opPreservesMoveX] at hNo
    dsimp only [evalOperand] at hEval
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at hEval; cases hEval
    | ok _ =>
      rw [hR] at hEval; injection hEval with h1; injection h1 with _ hs; subst hs
      cases hD : cfg.deinitMovedPlace with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hX
      | true =>
        simp only [↓reduceIte, deinitLocalCell]
        cases hL : listGet st.locals loc with
        | none => dsimp only; exact hX
        | some s =>
          cases s with
          | dead => exact hX
          | direct _ =>
            dsimp only
            cases hS : listSet st.locals loc (.direct none) with
            | none => exact hX
            | some _ => dsimp only; rw [listGet_listSet_ne hS hne]; exact hX
          | stack aid =>
            dsimp only
            cases hH : listGet st.heap aid with
            | none => dsimp only; exact hX
            | some e => dsimp only; cases hS : listSet st.heap aid { e with cell := none } <;> exact hX

theorem evalRvalue_preserves_direct_x (cfg : EvalConfig) (x : LocalId) (vX : Val)
    {st : MachineState} (hX : listGet st.locals x = some (.direct (some vX)))
    {rv : Rvalue} (hNo : rvPreservesMoveX x rv = true)
    {v : Val} {st' : MachineState} (hEval : evalRvalue cfg st rv = .ok (v, st')) :
    listGet st'.locals x = some (.direct (some vX)) := by
  cases rv with
  | use op | subtypeCast op => exact evalOperand_preserves_direct_x cfg x (some vX) hX hNo hEval
  | addrOf loc =>
    dsimp only [evalRvalue] at hEval
    cases hG : listGet st.locals loc with
    | none => rw [hG] at hEval; cases hEval
    | some sl =>
      rw [hG] at hEval
      cases sl with
      | dead => cases hEval | direct _ => cases hEval
      | stack aid =>
        dsimp only at hEval
        cases hH : listGet st.heap aid with
        | none => rw [hH] at hEval; cases hEval
        | some e =>
          rw [hH] at hEval; rcases e with ⟨ea, ec⟩; dsimp only at hEval
          cases ea with
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hEval; cases hEval
          | true => simp only [↓reduceIte] at hEval; injection hEval with h1; injection h1 with _ hs; subst hs; exact hX
  | discr loc =>
    dsimp only [evalRvalue] at hEval
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at hEval; cases hEval
    | ok v0 =>
      rw [hR] at hEval
      cases v0 with
      | bool _ => cases hEval | staticPtr _ => cases hEval | ptr _ => cases hEval
      | int n =>
        dsimp only at hEval
        cases hD : decide (0 ≤ n) with
        | false => rw [hD] at hEval; simp only [Bool.false_eq_true, ↓reduceIte] at hEval; cases hEval
        | true => rw [hD] at hEval; simp only [↓reduceIte] at hEval; injection hEval with h1; injection h1 with _ hs; subst hs; exact hX
  | derefPtr op =>
    dsimp only [evalRvalue] at hEval
    cases hO : evalOperand cfg st op with
    | error _ => rw [hO] at hEval; cases hEval
    | ok po =>
      rcases po with ⟨vp, sp⟩; rw [hO] at hEval
      have hX1 := evalOperand_preserves_direct_x cfg x (some vX) hX hNo hO
      cases vp with
      | int _ => cases hEval | bool _ => cases hEval | staticPtr _ => cases hEval
      | ptr aid =>
        dsimp only at hEval
        cases hH : listGet sp.heap aid with
        | none => rw [hH] at hEval; cases hEval
        | some e =>
          rw [hH] at hEval; dsimp only at hEval
          cases hA : e.alive with
          | false => rw [hA] at hEval; simp only [Bool.not_false, ↓reduceIte] at hEval; cases hEval
          | true =>
            rw [hA] at hEval; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hEval
            cases hC : e.cell with
            | none => rw [hC] at hEval; cases hEval
            | some _ => rw [hC] at hEval; injection hEval with h1; injection h1 with _ hs; subst hs; exact hX1
  | binOp k l r =>
    simp only [rvPreservesMoveX, Bool.and_eq_true] at hNo
    dsimp only [evalRvalue] at hEval
    cases hL : evalOperand cfg st l with
    | error _ => rw [hL] at hEval; cases hEval
    | ok pl =>
      rcases pl with ⟨vl, sl⟩; rw [hL] at hEval; dsimp only at hEval
      have hX1 := evalOperand_preserves_direct_x cfg x (some vX) hX hNo.1 hL
      cases hR : evalOperand cfg sl r with
      | error _ => rw [hR] at hEval; cases hEval
      | ok pr =>
        rcases pr with ⟨vr, sr⟩; rw [hR] at hEval; dsimp only at hEval
        have hX2 := evalOperand_preserves_direct_x cfg x (some vX) hX1 hNo.2 hR
        cases hB : evalBinOp k vl vr with
        | error _ => rw [hB] at hEval; cases hEval
        | ok _ => rw [hB] at hEval; injection hEval with h1; injection h1 with _ hs; subst hs; exact hX2

theorem writeLocalCell_ne_preserves_direct_x {x dst : LocalId} (hne : x ≠ dst) (oX : Option Val)
    {st st' : MachineState} (hX : listGet st.locals x = some (.direct oX))
    {v : Val} (hW : writeLocalCell st dst v = .ok st') :
    listGet st'.locals x = some (.direct oX) := by
  dsimp only [writeLocalCell] at hW
  cases hG : listGet st.locals dst with
  | none => rw [hG] at hW; cases hW
  | some s =>
    rw [hG] at hW
    cases s with
    | dead => cases hW
    | direct _ =>
      dsimp only at hW
      cases hS : listSet st.locals dst (.direct (some v)) with
      | none => rw [hS] at hW; cases hW
      | some _ => rw [hS] at hW; dsimp only at hW; injection hW with hst; subst hst; exact (listGet_listSet_ne hS hne).symm ▸ hX
    | stack aid =>
      dsimp only at hW
      cases hH : listGet st.heap aid with
      | none => rw [hH] at hW; cases hW
      | some e =>
        rw [hH] at hW; rcases e with ⟨ea, ec⟩; dsimp only at hW
        cases ea with
        | false => simp only [Bool.not_false, ↓reduceIte] at hW; cases hW
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hW
          cases hS : listSet st.heap aid { alive := true, cell := some v } with
          | none => rw [hS] at hW; dsimp only at hW; cases hW
          | some _ => rw [hS] at hW; dsimp only at hW; injection hW with hst; subst hst; exact hX

theorem stepStmt_safeCopy_preserves_x (cfg : EvalConfig) (body : Body) (x : LocalId) (vX : Val)
    {st : MachineState} (hX : listGet st.locals x = some (.direct (some vX)))
    {s : Stmt} (hSafe : ssaStmtSafeCopyX x s = true)
    {st' : MachineState} (hStep : stepStmt cfg body st s = .ok st') :
    listGet st'.locals x = some (.direct (some vX)) := by
  cases s with
  | nop => injection hStep with hst; subst hst; exact hX
  | storageLive loc =>
    dsimp only [ssaStmtSafeCopyX, ssaStmtNoWriteX] at hSafe
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hSafe
    have hne : x ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hSafe; cases hSafe.1
    dsimp only [stepStmt] at hStep
    cases hG : listGet st.locals loc with
    | none => rw [hG] at hStep; cases hStep
    | some _ =>
      rw [hG] at hStep; dsimp only at hStep
      cases hIn : natInList loc body.stackBackedLocals with
      | true =>
        rw [hIn] at hStep; simp only [↓reduceIte] at hStep
        cases hS : listSet st.locals loc (.stack _) with
        | none => rw [hS] at hStep; cases hStep
        | some _ => rw [hS] at hStep; dsimp only at hStep; injection hStep with hst; subst hst; exact (listGet_listSet_ne hS hne).symm ▸ hX
      | false =>
        rw [hIn] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep
        cases hS : listSet st.locals loc (.direct none) with
        | none => rw [hS] at hStep; cases hStep
        | some _ => rw [hS] at hStep; dsimp only at hStep; injection hStep with hst; subst hst; exact (listGet_listSet_ne hS hne).symm ▸ hX
  | storageDead loc =>
    dsimp only [ssaStmtSafeCopyX, ssaStmtNoWriteX] at hSafe
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hSafe
    have hne : x ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hSafe; cases hSafe.1
    dsimp only [stepStmt] at hStep
    cases hZ : Nat.beq loc 0 with
    | true => rw [hZ] at hStep; simp only [↓reduceIte] at hStep; cases hStep
    | false =>
      rw [hZ] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep
      cases hG : listGet st.locals loc with
      | none => rw [hG] at hStep; cases hStep
      | some _ =>
        rw [hG] at hStep; dsimp only at hStep
        cases hS : listSet st.locals loc .dead with
        | none => rw [hS] at hStep; cases hStep
        | some _ => rw [hS] at hStep; dsimp only at hStep; injection hStep with hst; subst hst; exact (listGet_listSet_ne hS hne).symm ▸ hX
  | assign dst rv =>
    dsimp only [ssaStmtSafeCopyX, ssaStmtNoWriteX] at hSafe
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hSafe
    have hne : x ≠ dst := fun h => by subst h; rw [Nat.beq_refl] at hSafe; cases hSafe.1
    dsimp only [stepStmt] at hStep
    cases hR : evalRvalue cfg st rv with
    | error _ => rw [hR] at hStep; cases hStep
    | ok pr =>
      rcases pr with ⟨vr, sr⟩; rw [hR] at hStep; dsimp only at hStep
      have hX1 := evalRvalue_preserves_direct_x cfg x vX hX hSafe.2 hR
      cases hW : writeLocalCell sr dst vr with
      | error _ => rw [hW] at hStep; cases hStep
      | ok sw =>
        rw [hW] at hStep; dsimp only at hStep; injection hStep with hst; subst hst
        dsimp only
        exact writeLocalCell_ne_preserves_direct_x hne (some vX) hX1 hW
  | storePtr p v =>
    dsimp only [ssaStmtSafeCopyX] at hSafe
    simp only [Bool.and_eq_true] at hSafe
    dsimp only [stepStmt] at hStep
    cases hP : evalOperand cfg st p with
    | error _ => rw [hP] at hStep; cases hStep
    | ok pp =>
      rcases pp with ⟨vp, sp⟩; rw [hP] at hStep
      have hX1 := evalOperand_preserves_direct_x cfg x (some vX) hX hSafe.2.1 hP
      cases vp with
      | int _ => cases hStep | bool _ => cases hStep | staticPtr _ => cases hStep
      | ptr aid =>
        dsimp only at hStep
        cases hV : evalOperand cfg sp v with
        | error _ => rw [hV] at hStep; cases hStep
        | ok pv =>
          rcases pv with ⟨vv, sv⟩; rw [hV] at hStep; dsimp only at hStep
          have hX2 := evalOperand_preserves_direct_x cfg x (some vX) hX1 hSafe.2.2 hV
          cases hH : listGet sv.heap aid with
          | none => rw [hH] at hStep; cases hStep
          | some e =>
            rw [hH] at hStep; rcases e with ⟨ea, ec⟩; dsimp only at hStep
            cases ea with
            | false => simp only [Bool.not_false, ↓reduceIte] at hStep; cases hStep
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
              cases hS : listSet sv.heap aid { alive := true, cell := some vv } with
              | none => rw [hS] at hStep; dsimp only at hStep; cases hStep
              | some _ => rw [hS] at hStep; dsimp only at hStep; injection hStep with hst; subst hst; exact hX2
  | assume op =>
    dsimp only [ssaStmtSafeCopyX] at hSafe
    simp only [Bool.and_eq_true] at hSafe
    dsimp only [stepStmt] at hStep
    cases hO : evalOperand cfg st op with
    | error _ => rw [hO] at hStep; cases hStep
    | ok po =>
      rcases po with ⟨vo, so⟩; rw [hO] at hStep
      have hX1 := evalOperand_preserves_direct_x cfg x (some vX) hX hSafe.2 hO
      cases vo with
      | int _ => cases hStep | staticPtr _ => cases hStep | ptr _ => cases hStep
      | bool b =>
        cases b with
        | false => cases hStep
        | true => injection hStep with hst; subst hst; exact hX1

theorem replaceOpCopy_evalOperand (cfg : EvalConfig) (x : LocalId) (c : ConstVal)
    {st : MachineState} (hX : listGet st.locals x = some (.direct (some (constToVal c))))
    (op : Operand) :
    evalOperand cfg st (replaceOpCopy x c op) = evalOperand cfg st op := by
  cases op with
  | const _ => rfl
  | move _ => rfl
  | copy loc =>
    dsimp only [replaceOpCopy]
    cases hEq : Nat.beq loc x with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      have hlx : loc = x := Nat.eq_of_beq_eq_true hEq
      subst hlx
      simp only [↓reduceIte, evalOperand, readLocalCell, hX]

theorem replaceRvCopy_evalRvalue (cfg : EvalConfig) (x : LocalId) (c : ConstVal)
    {st : MachineState} (hX : listGet st.locals x = some (.direct (some (constToVal c))))
    {rv : Rvalue} (hSafe : rvPreservesMoveX x rv = true) :
    evalRvalue cfg st (replaceRvOp (replaceOpCopy x c) rv) = evalRvalue cfg st rv := by
  cases rv with
  | use op => exact replaceOpCopy_evalOperand cfg x c hX op
  | subtypeCast op => exact replaceOpCopy_evalOperand cfg x c hX op
  | addrOf _ => rfl
  | discr _ => rfl
  | derefPtr op =>
    dsimp only [replaceRvOp, evalRvalue]
    rw [replaceOpCopy_evalOperand cfg x c hX op]
  | binOp k l r =>
    simp only [rvPreservesMoveX, Bool.and_eq_true] at hSafe
    dsimp only [replaceRvOp, evalRvalue]
    rw [replaceOpCopy_evalOperand cfg x c hX l]
    cases hL : evalOperand cfg st l with
    | error _ => rfl
    | ok pl =>
      rcases pl with ⟨vl, sl⟩
      dsimp only
      have hXsl := evalOperand_preserves_direct_x cfg x (some (constToVal c)) hX hSafe.1 hL
      rw [replaceOpCopy_evalOperand cfg x c hXsl r]

theorem replaceStmtCopy_stepStmt (cfg : EvalConfig) (body : Body) (x : LocalId) (c : ConstVal)
    {st : MachineState} (hX : listGet st.locals x = some (.direct (some (constToVal c))))
    {s : Stmt} (hSafe : ssaStmtSafeCopyX x s = true) :
    stepStmt cfg (replaceBodyOp (replaceOpCopy x c) body) st (replaceStmtOp (replaceOpCopy x c) s) =
    stepStmt cfg body st s := by
  cases s with
  | nop => rfl
  | storageDead loc => rfl
  | storageLive loc => rfl
  | assign dst rv =>
    dsimp only [ssaStmtSafeCopyX] at hSafe
    simp only [Bool.and_eq_true] at hSafe
    dsimp only [replaceStmtOp, stepStmt]
    rw [replaceRvCopy_evalRvalue cfg x c hX hSafe.2]
  | storePtr p v =>
    dsimp only [ssaStmtSafeCopyX] at hSafe
    simp only [Bool.and_eq_true] at hSafe
    dsimp only [replaceStmtOp, stepStmt]
    rw [replaceOpCopy_evalOperand cfg x c hX p]
    cases hP : evalOperand cfg st p with
    | error _ => rfl
    | ok pp =>
      rcases pp with ⟨vp, sp⟩
      have hXsp := evalOperand_preserves_direct_x cfg x (some (constToVal c)) hX hSafe.2.1 hP
      cases vp with
      | int _ | bool _ | staticPtr _ => rfl
      | ptr aid => dsimp only; rw [replaceOpCopy_evalOperand cfg x c hXsp v]
  | assume op =>
    dsimp only [replaceStmtOp, stepStmt]
    rw [replaceOpCopy_evalOperand cfg x c hX op]

theorem replaceTermCopy_stepTerm (cfg : EvalConfig) (x : LocalId) (c : ConstVal)
    {st : MachineState} (hX : listGet st.locals x = some (.direct (some (constToVal c))))
    (t : Term) :
    stepTerm cfg st (replaceTermOp (replaceOpCopy x c) t) = stepTerm cfg st t := by
  cases t with
  | goto _ | ret | unreachable => rfl
  | switchInt op arms oth =>
    dsimp only [replaceTermOp, stepTerm]
    rw [replaceOpCopy_evalOperand cfg x c hX op]
  | assert cond exp tgt opt =>
    dsimp only [replaceTermOp, stepTerm]
    rw [replaceOpCopy_evalOperand cfg x c hX cond]

theorem ssaRange_copy_region_eq (cfg : EvalConfig) (x : LocalId) (c : ConstVal)
    (body : Body) (hSafe : ssaBodySafeCopyX x body.blocks = true) :
    ∀ fuel st,
      listGet st.locals x = some (.direct (some (constToVal c))) →
      runBody cfg (replaceBodyOp (replaceOpCopy x c) body) st fuel = runBody cfg body st fuel := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ f' ih =>
    intro st hX
    dsimp only [runBody, replaceBodyOp]
    rw [listGet_map]
    cases hBB : listGet body.blocks st.pc with
    | none => rfl
    | some bb =>
      dsimp only [Option.map]
      have hBBsafe := ssaBodySafeCopy_get hSafe hBB
      dsimp only [ssaBlockSafeCopyX] at hBBsafe
      simp only [Bool.and_eq_true] at hBBsafe
      rw [listGet_map]; dsimp only [Option.map]
      cases hSt : listGet bb.stmts st.stmtIdx with
      | some s =>
        dsimp only
        have hSsafe := listAll_true_get hBBsafe.1 hSt
        have hStepEq := replaceStmtCopy_stepStmt cfg body x c hX hSsafe
        dsimp only [replaceBodyOp] at hStepEq
        rw [hStepEq]
        cases hStep : stepStmt cfg body st s with
        | error _ => rfl
        | ok st' =>
          have hX' := stepStmt_safeCopy_preserves_x cfg body x (constToVal c) hX hSsafe hStep
          exact ih st' hX'
      | none =>
        dsimp only
        rw [replaceTermCopy_stepTerm cfg x c hX bb.term]
        cases hT : stepTerm cfg st bb.term with
        | stop _ => rfl
        | cont st' =>
          dsimp only
          have hX' : listGet st'.locals x = some (.direct (some (constToVal c))) := by
            cases hTerm : bb.term with
            | goto _ => rw [hTerm] at hT; injection hT with hs; subst hs; exact hX
            | ret =>
              rw [hTerm] at hT; dsimp only [stepTerm] at hT
              cases hRL : readLocalCell st 0 with
              | error _ => rw [hRL] at hT; cases hT
              | ok _ => rw [hRL] at hT; cases hT
            | unreachable => rw [hTerm] at hT; dsimp only [stepTerm] at hT; cases hT
            | switchInt op _ _ =>
              rw [hTerm] at hT hBBsafe; dsimp only [ssaTermSafeCopyX] at hBBsafe
              dsimp only [stepTerm] at hT
              cases hO : evalOperand cfg st op with
              | error _ => rw [hO] at hT; cases hT
              | ok po =>
                rcases po with ⟨vo, so⟩; rw [hO] at hT; dsimp only at hT
                have hX1 := evalOperand_preserves_direct_x cfg x (some (constToVal c)) hX hBBsafe.2 hO
                cases hDB : discrBits vo with
                | error _ => rw [hDB] at hT; cases hT
                | ok _ =>
                  rw [hDB] at hT; dsimp only at hT; injection hT with hs; subst hs; exact hX1
            | assert cond exp tgt opt =>
              rw [hTerm] at hT hBBsafe; dsimp only [ssaTermSafeCopyX] at hBBsafe
              dsimp only [stepTerm] at hT
              cases hSkip : (opt && !cfg.enforceOptionalOverflow) with
              | true => rw [hSkip] at hT; simp only [↓reduceIte] at hT; injection hT with hs; subst hs; exact hX
              | false =>
                rw [hSkip] at hT; simp only [Bool.false_eq_true, ↓reduceIte] at hT
                cases hO : evalOperand cfg st cond with
                | error _ => rw [hO] at hT; cases hT
                | ok po =>
                  rcases po with ⟨vo, so⟩; rw [hO] at hT
                  have hX1 := evalOperand_preserves_direct_x cfg x (some (constToVal c)) hX hBBsafe.2 hO
                  cases vo with
                  | int _ | staticPtr _ | ptr _ => cases hT
                  | bool b =>
                    dsimp only at hT
                    cases hB : (b == exp) with
                    | true => rw [hB] at hT; simp only [↓reduceIte] at hT; injection hT with hs; subst hs; exact hX1
                    | false => rw [hB] at hT; simp only [Bool.false_eq_true, ↓reduceIte] at hT; cases hT
          exact ih st' hX'

/-- Entry facts + exact region equivalence (`↔`) for singleton `SsaRangePropagation`
    on `Assume`, non-optional `Assert`, unique-predecessor `SwitchInt`, and `Copy` uses. -/
theorem ssaRangeProp_singleton_copy_exact_iff (cfg : EvalConfig) (x : LocalId) (c : ConstVal)
    (r : WrappingRange) (hOrd : r.start ≤ r.stop) (k : Int)
    (body : Body) (hSafe : ssaBodySafeCopyX x body.blocks = true)
    (st : MachineState) (fuel : Nat)
    (hAssumeOrDirect : listGet st.locals x = some (.direct (some (constToVal c)))) :
    (tryAsConstant r = some k ↔ (r.contains k = true ∧ ∀ v, r.contains v = true → v = k)) ∧
    (runBody cfg (replaceBodyOp (replaceOpCopy x c) body) st fuel = runBody cfg body st fuel) ∧
    (∀ st' body', stepStmt cfg body' st (.assume (.copy x)) = .ok st' →
      listGet st.locals x = some (.direct (some (.bool true)))) := by
  refine ⟨wrappingRange_tryAsConstant_iff r hOrd k, ssaRange_copy_region_eq cfg x c body hSafe fuel st hAssumeOrDirect, ?_⟩
  intro _ _ hAss
  dsimp only [stepStmt, evalOperand, readLocalCell] at hAss
  rw [hAssumeOrDirect] at hAss; dsimp only at hAss
  cases hC : constToVal c with
  | int _ | staticPtr _ | ptr _ => rw [hC] at hAss; cases hAss
  | bool b =>
    rw [hC] at hAss
    cases b with
    | false => cases hAss
    | true => rw [hAssumeOrDirect, hC]

def MoveConstSim (x : LocalId) (vC : Val) (stS stT : MachineState) : Prop :=
  stS.pc = stT.pc ∧ stS.stmtIdx = stT.stmtIdx ∧ stS.heap = stT.heap ∧
  stS.locals.length = stT.locals.length ∧
  listGet stT.locals x = some (.direct (some vC)) ∧
  (listGet stS.locals x = some (.direct (some vC)) ∨ listGet stS.locals x = some (.direct none)) ∧
  (∀ i, i ≠ x → listGet stS.locals i = listGet stT.locals i)

theorem moveConstSim_evalOperand {cfg : EvalConfig} {x : LocalId} {c : ConstVal}
    {stS stT : MachineState} (hSim : MoveConstSim x (constToVal c) stS stT)
    {op : Operand} {vS : Val} {stS1 : MachineState}
    (hEval : evalOperand cfg stS op = .ok (vS, stS1)) :
    ∃ stT1, evalOperand cfg stT (replaceOpMoveCopy x c op) = .ok (vS, stT1) ∧
      MoveConstSim x (constToVal c) stS1 stT1 := by
  rcases hSim with ⟨hpc, hsi, hhp, hlen, hXT, hXS, hNe⟩
  cases op with
  | const c0 =>
    injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
    exact ⟨stT, rfl, hpc, hsi, hhp, hlen, hXT, hXS, hNe⟩
  | copy loc =>
    cases hEq : Nat.beq loc x with
    | true =>
      have hlx := Nat.eq_of_beq_eq_true hEq; subst hlx
      dsimp only [replaceOpMoveCopy]; rw [Nat.beq_refl]; simp only [↓reduceIte]
      dsimp only [evalOperand, readLocalCell] at hEval
      rcases hXS with hXS1 | hXS0
      · rw [hXS1] at hEval; injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
        exact ⟨stT, rfl, hpc, hsi, hhp, hlen, hXT, Or.inl hXS1, hNe⟩
      · rw [hXS0] at hEval; cases hEval
    | false =>
      have hne : loc ≠ x := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
      dsimp only [replaceOpMoveCopy]; rw [hEq]; simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [evalOperand] at hEval ⊢
      have hREq : readLocalCell stS loc = readLocalCell stT loc := by
        unfold readLocalCell; rw [hNe loc hne, hhp]
      rw [← hREq]
      cases hR : readLocalCell stS loc with
      | error _ => rw [hR] at hEval; cases hEval
      | ok _ =>
        rw [hR] at hEval; injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
        exact ⟨stT, rfl, hpc, hsi, hhp, hlen, hXT, hXS, hNe⟩
  | move loc =>
    cases hEq : Nat.beq loc x with
    | true =>
      have hlx := Nat.eq_of_beq_eq_true hEq; subst hlx
      dsimp only [replaceOpMoveCopy]; rw [Nat.beq_refl]; simp only [↓reduceIte]
      dsimp only [evalOperand, readLocalCell] at hEval
      rcases hXS with hXS1 | hXS0
      · rw [hXS1] at hEval; injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
        refine ⟨stT, rfl, ?_⟩
        cases hD : cfg.deinitMovedPlace with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hpc, hsi, hhp, hlen, hXT, Or.inl hXS1, hNe⟩
        | true =>
          simp only [↓reduceIte, deinitLocalCell]
          rw [hXS1]; dsimp only
          rcases listSet_exists_of_get hXS1 (.direct none) with ⟨lsS', hSetS⟩
          rw [hSetS]
          refine ⟨hpc, hsi, hhp, (listSet_length_eq hSetS).trans hlen, hXT,
            Or.inr (listGet_listSet_eq hSetS), ?_⟩
          intro i hix
          rw [listGet_listSet_ne hSetS hix]; exact hNe i hix
      · rw [hXS0] at hEval; cases hEval
    | false =>
      have hne : loc ≠ x := fun h => by subst h; rw [Nat.beq_refl] at hEq; cases hEq
      dsimp only [replaceOpMoveCopy]; rw [hEq]; simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [evalOperand] at hEval ⊢
      have hEqLoc := hNe loc hne
      have hREq : readLocalCell stS loc = readLocalCell stT loc := by
        unfold readLocalCell; rw [hEqLoc, hhp]
      rw [← hREq]
      cases hR : readLocalCell stS loc with
      | error _ => rw [hR] at hEval; cases hEval
      | ok _ =>
        rw [hR] at hEval; injection hEval with h1; injection h1 with hv hs; subst hv; subst hs
        cases hD : cfg.deinitMovedPlace with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨stT, rfl, hpc, hsi, hhp, hlen, hXT, hXS, hNe⟩
        | true =>
          simp only [↓reduceIte, deinitLocalCell]
          rw [← hEqLoc]
          cases hG : listGet stS.locals loc with
          | none => dsimp only; exact ⟨stT, rfl, hpc, hsi, hhp, hlen, hXT, hXS, hNe⟩
          | some sl =>
            cases sl with
            | dead => exact ⟨stT, rfl, hpc, hsi, hhp, hlen, hXT, hXS, hNe⟩
            | direct _ =>
              dsimp only
              rcases listSet_exists_of_get hG (.direct none) with ⟨lsS', hSetS⟩
              have hG2 : listGet stT.locals loc = some (.direct _) := hEqLoc ▸ hG
              rcases listSet_exists_of_get hG2 (.direct none) with ⟨lsT', hSetT⟩
              rw [hSetS, hSetT]; dsimp only
              refine ⟨_, rfl, hpc, hsi, hhp,
                by rw [listSet_length_eq hSetS, listSet_length_eq hSetT]; exact hlen,
                by rw [listGet_listSet_ne hSetT hne.symm]; exact hXT,
                ?_, ?_⟩
              · rcases hXS with hXS1 | hXS0
                · exact Or.inl (by rw [listGet_listSet_ne hSetS hne.symm]; exact hXS1)
                · exact Or.inr (by rw [listGet_listSet_ne hSetS hne.symm]; exact hXS0)
              · intro i hix
                cases hEqI : Nat.beq i loc with
                | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hSetS, listGet_listSet_eq hSetT]
                | false =>
                  have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
                  rw [listGet_listSet_ne hSetS hneI, listGet_listSet_ne hSetT hneI]; exact hNe i hix
            | stack aid =>
              dsimp only
              rw [← hhp]
              cases hGH : listGet stS.heap aid with
              | none => dsimp only; exact ⟨stT, rfl, hpc, hsi, hhp, hlen, hXT, hXS, hNe⟩
              | some e =>
                rcases listSet_exists_of_get hGH { e with cell := none } with ⟨hp', hSH⟩
                dsimp only
                rw [hSH]; dsimp only
                exact ⟨_, rfl, hpc, hsi, rfl, hlen, hXT, hXS, hNe⟩

theorem ssaRangeProp_singleton_move_forward_refines (cfg : EvalConfig) (x : LocalId) (c : ConstVal)
    (body : Body) (hSafe : ssaBodyNoWriteX x body.blocks = true)
    (st : MachineState) (fuel : Nat)
    (hInitX : listGet st.locals x = some (.direct (some (constToVal c)))) :
    ForwardRefines
      (runBody cfg body st fuel)
      (runBody cfg (replaceBodyOp (replaceOpMoveCopy x c) body) st fuel) := by
  have hMain : ∀ fl stS stT, MoveConstSim x (constToVal c) stS stT →
      ForwardRefines (runBody cfg body stS fl)
        (runBody cfg (replaceBodyOp (replaceOpMoveCopy x c) body) stT fl) := by
    intro fl
    induction fl with
    | zero => intro _ _ _; exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
    | succ fl' ih =>
      intro stS stT hSim
      dsimp only [runBody, replaceBodyOp]
      rw [listGet_map, ← hSim.1]
      cases hBB : listGet body.blocks stS.pc with
      | none => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
      | some bb =>
        dsimp only [Option.map]
        have hNoW := ssaBodyNoWrite_get hSafe hBB
        rw [listGet_map, ← hSim.2.1]; dsimp only [Option.map]
        cases hSt : listGet bb.stmts stS.stmtIdx with
        | some s =>
          dsimp only
          have hsNoW := listAll_true_get hNoW hSt
          cases hStep : stepStmt cfg body stS s with
          | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
          | ok stS1 =>
            have stepMatch : ∃ stT1,
                stepStmt cfg (replaceBodyOp (replaceOpMoveCopy x c) body) stT
                  (replaceStmtOp (replaceOpMoveCopy x c) s) = .ok stT1 ∧
                MoveConstSim x (constToVal c) stS1 stT1 := by
              cases s with
              | nop =>
                injection hStep with hs; subst hs
                exact ⟨{ stT with stmtIdx := stT.stmtIdx + 1 }, rfl,
                  hSim.1, congrArg Nat.succ hSim.2.1, hSim.2.2.1, hSim.2.2.2.1,
                  hSim.2.2.2.2.1, hSim.2.2.2.2.2.1, hSim.2.2.2.2.2.2⟩
              | storageLive loc =>
                dsimp only [ssaStmtNoWriteX, Bool.not_eq_true'] at hsNoW
                have hne : loc ≠ x := fun h => by subst h; rw [Nat.beq_refl] at hsNoW; cases hsNoW
                dsimp only [replaceStmtOp, stepStmt] at hStep ⊢
                rw [← hSim.2.2.2.2.2.2 loc hne, ← hSim.2.2.1]
                dsimp only [replaceBodyOp]
                cases h1 : listGet stS.locals loc with
                | none => rw [h1] at hStep; cases hStep
                | some oldSlot =>
                  rw [h1] at hStep; dsimp only at hStep ⊢
                  have h2 : listGet stT.locals loc = some oldSlot := hSim.2.2.2.2.2.2 loc hne ▸ h1
                  rcases Bool.eq_false_or_eq_true (natInList loc body.stackBackedLocals) with hIn | hIn
                  · simp only [hIn, ↓reduceIte] at hStep ⊢
                    rcases listSet_exists_of_get h1 (.stack (allocHeap (freeHeapOpt stS.heap (slotAidOpt oldSlot))).1) with ⟨lsS', hSS⟩
                    rcases listSet_exists_of_get h2 (.stack (allocHeap (freeHeapOpt stS.heap (slotAidOpt oldSlot))).1) with ⟨lsT', hST⟩
                    rw [hSS] at hStep; dsimp only at hStep; injection hStep with hst; subst hst
                    rw [hST]; dsimp only
                    refine ⟨_, rfl, hSim.1, congrArg Nat.succ hSim.2.1, rfl,
                      by rw [listSet_length_eq hSS, listSet_length_eq hST]; exact hSim.2.2.2.1,
                      by rw [listGet_listSet_ne hST hne.symm]; exact hSim.2.2.2.2.1, ?_, ?_⟩
                    · rcases hSim.2.2.2.2.2.1 with h1x | h0x
                      · exact Or.inl (by rw [listGet_listSet_ne hSS hne.symm]; exact h1x)
                      · exact Or.inr (by rw [listGet_listSet_ne hSS hne.symm]; exact h0x)
                    · intro i hix
                      cases hEqI : Nat.beq i loc with
                      | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hSS, listGet_listSet_eq hST]
                      | false =>
                        have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
                        rw [listGet_listSet_ne hSS hneI, listGet_listSet_ne hST hneI]; exact hSim.2.2.2.2.2.2 i hix
                  · simp only [hIn, Bool.false_eq_true, ↓reduceIte] at hStep ⊢
                    rcases listSet_exists_of_get h1 (.direct none) with ⟨lsS', hSS⟩
                    rcases listSet_exists_of_get h2 (.direct none) with ⟨lsT', hST⟩
                    rw [hSS] at hStep; dsimp only at hStep; injection hStep with hst; subst hst
                    rw [hST]; dsimp only
                    refine ⟨_, rfl, hSim.1, congrArg Nat.succ hSim.2.1, rfl,
                      by rw [listSet_length_eq hSS, listSet_length_eq hST]; exact hSim.2.2.2.1,
                      by rw [listGet_listSet_ne hST hne.symm]; exact hSim.2.2.2.2.1, ?_, ?_⟩
                    · rcases hSim.2.2.2.2.2.1 with h1x | h0x
                      · exact Or.inl (by rw [listGet_listSet_ne hSS hne.symm]; exact h1x)
                      · exact Or.inr (by rw [listGet_listSet_ne hSS hne.symm]; exact h0x)
                    · intro i hix
                      cases hEqI : Nat.beq i loc with
                      | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hSS, listGet_listSet_eq hST]
                      | false =>
                        have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
                        rw [listGet_listSet_ne hSS hneI, listGet_listSet_ne hST hneI]; exact hSim.2.2.2.2.2.2 i hix
              | storageDead loc =>
                dsimp only [ssaStmtNoWriteX, Bool.not_eq_true'] at hsNoW
                have hne : loc ≠ x := fun h => by subst h; rw [Nat.beq_refl] at hsNoW; cases hsNoW
                dsimp only [replaceStmtOp, stepStmt] at hStep ⊢
                rw [← hSim.2.2.2.2.2.2 loc hne, ← hSim.2.2.1]
                cases hZ : Nat.beq loc 0 with
                | true => rw [hZ] at hStep; simp only [↓reduceIte] at hStep; cases hStep
                | false =>
                  rw [hZ] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep ⊢
                  cases h1 : listGet stS.locals loc with
                  | none => rw [h1] at hStep; cases hStep
                  | some oldSlot =>
                    rw [h1] at hStep; dsimp only at hStep
                    have h2 : listGet stT.locals loc = some oldSlot := hSim.2.2.2.2.2.2 loc hne ▸ h1
                    rcases listSet_exists_of_get h1 .dead with ⟨lsS', hSS⟩
                    rcases listSet_exists_of_get h2 .dead with ⟨lsT', hST⟩
                    rw [hSS] at hStep; dsimp only at hStep; injection hStep with hst; subst hst
                    rw [hST]; dsimp only
                    refine ⟨_, rfl, hSim.1, congrArg Nat.succ hSim.2.1, rfl,
                      by rw [listSet_length_eq hSS, listSet_length_eq hST]; exact hSim.2.2.2.1,
                      by rw [listGet_listSet_ne hST hne.symm]; exact hSim.2.2.2.2.1, ?_, ?_⟩
                    · rcases hSim.2.2.2.2.2.1 with h1x | h0x
                      · exact Or.inl (by rw [listGet_listSet_ne hSS hne.symm]; exact h1x)
                      · exact Or.inr (by rw [listGet_listSet_ne hSS hne.symm]; exact h0x)
                    · intro i hix
                      cases hEqI : Nat.beq i loc with
                      | true => have hil := Nat.eq_of_beq_eq_true hEqI; subst hil; rw [listGet_listSet_eq hSS, listGet_listSet_eq hST]
                      | false =>
                        have hneI : i ≠ loc := fun h => by subst h; rw [Nat.beq_refl] at hEqI; cases hEqI
                        rw [listGet_listSet_ne hSS hneI, listGet_listSet_ne hST hneI]; exact hSim.2.2.2.2.2.2 i hix
              | assign dst rv =>
                dsimp only [ssaStmtNoWriteX, Bool.not_eq_true'] at hsNoW
                have hne : dst ≠ x := fun h => by subst h; rw [Nat.beq_refl] at hsNoW; cases hsNoW
                have rvMatch : ∃ vR sr stTR,
                    evalRvalue cfg stS rv = .ok (vR, sr) ∧
                    evalRvalue cfg stT (replaceRvOp (replaceOpMoveCopy x c) rv) = .ok (vR, stTR) ∧
                    MoveConstSim x (constToVal c) sr stTR := by
                  cases rv with
                  | use op | subtypeCast op =>
                    dsimp only [stepStmt, evalRvalue] at hStep
                    cases hO : evalOperand cfg stS op with
                    | error _ => rw [hO] at hStep; cases hStep
                    | ok po =>
                      rcases po with ⟨vo, so⟩
                      rcases moveConstSim_evalOperand hSim hO with ⟨stT1, hOT, hSim1⟩
                      exact ⟨vo, so, stT1, hO, hOT, hSim1⟩
                  | binOp k l r =>
                    dsimp only [stepStmt, evalRvalue] at hStep
                    cases hL : evalOperand cfg stS l with
                    | error _ => rw [hL] at hStep; cases hStep
                    | ok pl =>
                      rcases pl with ⟨vl, sl⟩; rw [hL] at hStep; dsimp only at hStep
                      rcases moveConstSim_evalOperand hSim hL with ⟨stT1, hLT, hSim1⟩
                      cases hR : evalOperand cfg sl r with
                      | error _ => rw [hR] at hStep; cases hStep
                      | ok pr =>
                        rcases pr with ⟨vr, sr⟩; rw [hR] at hStep; dsimp only at hStep
                        rcases moveConstSim_evalOperand hSim1 hR with ⟨stT2, hRT, hSim2⟩
                        cases hB : evalBinOp k vl vr with
                        | error _ => rw [hB] at hStep; cases hStep
                        | ok res =>
                          refine ⟨res, sr, stT2, ?_, ?_, hSim2⟩
                          · dsimp only [evalRvalue]; rw [hL]; dsimp only; rw [hR]; dsimp only; rw [hB]
                          · dsimp only [replaceRvOp, evalRvalue]; rw [hLT]; dsimp only; rw [hRT]; dsimp only; rw [hB]
                  | addrOf loc =>
                    dsimp only [stepStmt, evalRvalue] at hStep
                    have hneLoc : loc ≠ x := by
                      intro hEq; subst hEq
                      rcases hSim.2.2.2.2.2.1 with h1x | h0x
                      · rw [h1x] at hStep; dsimp only at hStep; cases hStep
                      · rw [h0x] at hStep; dsimp only at hStep; cases hStep
                    dsimp only [evalRvalue]
                    have hGeq := hSim.2.2.2.2.2.2 loc hneLoc
                    cases hG : listGet stS.locals loc with
                    | none => rw [hG] at hStep; cases hStep
                    | some sl =>
                      rw [hG] at hStep
                      cases sl with
                      | dead => cases hStep
                      | direct _ => cases hStep
                      | stack aid =>
                        dsimp only at hStep
                        cases hH : listGet stS.heap aid with
                        | none => rw [hH] at hStep; cases hStep
                        | some e =>
                          rw [hH] at hStep; dsimp only at hStep
                          cases hA : e.alive with
                          | false => rw [hA] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep; cases hStep
                          | true =>
                            rw [hA] at hStep; simp only [↓reduceIte] at hStep
                            refine ⟨.ptr aid, stS, stT, ?_, ?_, hSim⟩
                            · dsimp only [evalRvalue]; rw [hH]; dsimp only; rw [hA]; simp only [↓reduceIte]
                            · dsimp only [replaceRvOp, evalRvalue]; rw [← hGeq, ← hSim.2.2.1, hG]; dsimp only; rw [hH]; dsimp only; rw [hA]; simp only [↓reduceIte]
                  | derefPtr ptrOp =>
                    dsimp only [stepStmt, evalRvalue] at hStep
                    cases hO : evalOperand cfg stS ptrOp with
                    | error _ => rw [hO] at hStep; cases hStep
                    | ok po =>
                      rcases po with ⟨vp, sp⟩; rw [hO] at hStep
                      rcases moveConstSim_evalOperand hSim hO with ⟨stT1, hOT, hSim1⟩
                      cases vp with
                      | int _ | bool _ | staticPtr _ => cases hStep
                      | ptr aid =>
                        dsimp only at hStep
                        cases hH : listGet sp.heap aid with
                        | none => rw [hH] at hStep; cases hStep
                        | some e =>
                          rw [hH] at hStep; dsimp only at hStep
                          cases hA : e.alive with
                          | false => rw [hA] at hStep; simp only [Bool.not_false, ↓reduceIte] at hStep; cases hStep
                          | true =>
                            rw [hA] at hStep; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
                            cases hC : e.cell with
                            | none => rw [hC] at hStep; cases hStep
                            | some v0 =>
                              refine ⟨v0, sp, stT1, ?_, ?_, hSim1⟩
                              · dsimp only [evalRvalue]; rw [hO]; dsimp only; rw [hH]; dsimp only; rw [hA]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [hC]
                              · dsimp only [replaceRvOp, evalRvalue]; rw [hOT]; dsimp only; rw [← hSim1.2.2.1, hH]; dsimp only; rw [hA]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [hC]
                  | discr loc =>
                    dsimp only [stepStmt, evalRvalue] at hStep
                    cases hEqLoc : Nat.beq loc x with
                    | true =>
                      have hlx := Nat.eq_of_beq_eq_true hEqLoc; subst hlx
                      dsimp only [readLocalCell] at hStep
                      rcases hSim.2.2.2.2.2.1 with h1x | h0x
                      · rw [h1x] at hStep; dsimp only at hStep
                        cases hCV : constToVal c with
                        | bool _ | staticPtr _ | ptr _ => rw [hCV] at hStep; cases hStep
                        | int n =>
                          rw [hCV] at hStep; dsimp only at hStep
                          cases hD : decide (0 ≤ n) with
                          | false => rw [hD] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep; cases hStep
                          | true =>
                            refine ⟨.int n, stS, stT, ?_, ?_, ?_⟩
                            · dsimp only [evalRvalue, readLocalCell]; rw [h1x, hCV]; dsimp only; rw [hD]; simp only [↓reduceIte]
                            · dsimp only [replaceRvOp, evalRvalue, readLocalCell]; rw [hSim.2.2.2.2.1, hCV]; dsimp only; rw [hD]; simp only [↓reduceIte]
                            · rw [← hCV]; exact hSim
                      · rw [h0x] at hStep; cases hStep
                    | false =>
                      have hneLoc : loc ≠ x := fun h => by subst h; rw [Nat.beq_refl] at hEqLoc; cases hEqLoc
                      have hREq : readLocalCell stS loc = readLocalCell stT loc := by
                        unfold readLocalCell; rw [hSim.2.2.2.2.2.2 loc hneLoc, hSim.2.2.1]
                      cases hR : readLocalCell stS loc with
                      | error _ => rw [hR] at hStep; cases hStep
                      | ok v0 =>
                        rw [hR] at hStep
                        cases v0 with
                        | bool _ | staticPtr _ | ptr _ => cases hStep
                        | int n =>
                          dsimp only at hStep
                          cases hD : decide (0 ≤ n) with
                          | false => rw [hD] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep; cases hStep
                          | true =>
                            refine ⟨.int n, stS, stT, ?_, ?_, hSim⟩
                            · dsimp only [evalRvalue]; rw [hR]; dsimp only; rw [hD]; simp only [↓reduceIte]
                            · dsimp only [replaceRvOp, evalRvalue]; rw [← hREq, hR]; dsimp only; rw [hD]; simp only [↓reduceIte]
                rcases rvMatch with ⟨vR, sr, stTR, hERs, hERt, hSimR⟩
                dsimp only [replaceStmtOp, stepStmt] at hStep ⊢
                rw [hERs] at hStep; dsimp only at hStep
                rw [hERt]; dsimp only
                have hAgR : StateAgreeExcept x sr stTR :=
                  ⟨hSimR.1, hSimR.2.1, hSimR.2.2.1, hSimR.2.2.2.1, hSimR.2.2.2.2.2.2⟩
                have hW := agree_writeLocalCell_not_mentioned hAgR hne vR
                cases hEW : writeLocalCell sr dst vR with
                | error _ => rw [hEW] at hStep; cases hStep
                | ok sw =>
                  rcases hW.2 sw hEW with ⟨stTW, hEWt, hAgW⟩
                  rw [hEW] at hStep; dsimp only at hStep; injection hStep with hs; subst hs
                  rw [hEWt]; dsimp only
                  have hXT' : listGet stTW.locals x = some (.direct (some (constToVal c))) :=
                    writeLocalCell_ne_preserves_direct_x hne.symm (some (constToVal c)) hSimR.2.2.2.2.1 hEWt
                  have hXS' : listGet sw.locals x = some (.direct (some (constToVal c))) ∨
                      listGet sw.locals x = some (.direct none) := by
                    rcases hSimR.2.2.2.2.2.1 with h1x | h0x
                    · exact Or.inl (writeLocalCell_ne_preserves_direct_x hne.symm (some (constToVal c)) h1x hEW)
                    · exact Or.inr (writeLocalCell_ne_preserves_direct_x hne.symm none h0x hEW)
                  exact ⟨{ stTW with stmtIdx := stTW.stmtIdx + 1 }, rfl,
                    hAgW.1, congrArg Nat.succ hAgW.2.1, hAgW.2.2.1, hAgW.2.2.2.1, hXT', hXS', hAgW.2.2.2.2⟩
              | storePtr p v =>
                dsimp only [replaceStmtOp, stepStmt] at hStep ⊢
                cases hP : evalOperand cfg stS p with
                | error _ => rw [hP] at hStep; cases hStep
                | ok pp =>
                  rcases pp with ⟨vp, sp⟩; rw [hP] at hStep
                  rcases moveConstSim_evalOperand hSim hP with ⟨stT1, hOT, hSim1⟩
                  rw [hOT]
                  cases vp with
                  | int _ | bool _ | staticPtr _ => cases hStep
                  | ptr aid =>
                    dsimp only at hStep ⊢
                    cases hV : evalOperand cfg sp v with
                    | error _ => rw [hV] at hStep; cases hStep
                    | ok pv =>
                      rcases pv with ⟨vv, sv⟩; rw [hV] at hStep; dsimp only at hStep
                      rcases moveConstSim_evalOperand hSim1 hV with ⟨stT2, hVT, hSim2⟩
                      rw [hVT]; dsimp only
                      rw [← hSim2.2.2.1]
                      cases hH : listGet sv.heap aid with
                      | none => rw [hH] at hStep; cases hStep
                      | some e =>
                        rw [hH] at hStep; dsimp only at hStep
                        rcases e with ⟨ea, ec⟩
                        dsimp only at hStep ⊢
                        cases ea with
                        | false => simp only [Bool.not_false, ↓reduceIte] at hStep; cases hStep
                        | true =>
                          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep ⊢
                          rcases listSet_exists_of_get hH { alive := true, cell := some vv } with ⟨hp', hSH⟩
                          rw [hSH] at hStep; dsimp only at hStep; injection hStep with hst; subst hst
                          rw [hSH]; dsimp only
                          exact ⟨{ stT2 with heap := hp', stmtIdx := stT2.stmtIdx + 1 }, rfl,
                            hSim2.1, congrArg Nat.succ hSim2.2.1, rfl, hSim2.2.2.2.1,
                            hSim2.2.2.2.2.1, hSim2.2.2.2.2.2.1, hSim2.2.2.2.2.2.2⟩
              | assume op =>
                dsimp only [replaceStmtOp, stepStmt] at hStep ⊢
                cases hO : evalOperand cfg stS op with
                | error _ => rw [hO] at hStep; cases hStep
                | ok po =>
                  rcases po with ⟨vo, so⟩; rw [hO] at hStep
                  rcases moveConstSim_evalOperand hSim hO with ⟨stT1, hOT, hSim1⟩
                  rw [hOT]
                  cases vo with
                  | int _ | staticPtr _ | ptr _ => cases hStep
                  | bool b =>
                    cases b with
                    | false => cases hStep
                    | true =>
                      injection hStep with hst; subst hst
                      exact ⟨{ stT1 with stmtIdx := stT1.stmtIdx + 1 }, rfl,
                        hSim1.1, congrArg Nat.succ hSim1.2.1, hSim1.2.2⟩
            rcases stepMatch with ⟨stT1, hStepT, hSim1⟩
            dsimp only [replaceBodyOp] at hStepT
            rw [hStepT]; dsimp only
            exact ih stS1 stT1 hSim1
        | none =>
          dsimp only
          cases hTerm : bb.term with
          | goto tgt =>
            dsimp only [replaceTermOp, stepTerm]
            exact ih { stS with pc := tgt, stmtIdx := 0 } { stT with pc := tgt, stmtIdx := 0 }
              ⟨rfl, rfl, hSim.2.2.1, hSim.2.2.2.1, hSim.2.2.2.2.1, hSim.2.2.2.2.2.1, hSim.2.2.2.2.2.2⟩
          | unreachable => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
          | ret =>
            dsimp only [replaceTermOp, stepTerm]
            cases hEq0 : Nat.beq 0 x with
            | true =>
              have h0x := Nat.eq_of_beq_eq_true hEq0; subst h0x
              rcases hSim.2.2.2.2.2.1 with h1x | h0x
              · have hR1 : readLocalCell stS 0 = .ok (constToVal c) := by unfold readLocalCell; rw [h1x]
                have hR2 : readLocalCell stT 0 = .ok (constToVal c) := by unfold readLocalCell; rw [hSim.2.2.2.2.1]
                rw [hR1, hR2]
                refine ⟨(fun v _ hEq => by dsimp only at hEq ⊢; injection hEq with hV; rw [hV]), (fun h => by dsimp only at h; cases h)⟩
              · have hR1 : readLocalCell stS 0 = .error .uninitRead := by unfold readLocalCell; rw [h0x]
                rw [hR1]; exact ⟨(fun _ _ h => by dsimp only at h; cases h), (fun h => by dsimp only at h; cases h)⟩
            | false =>
              have hne : (0 : LocalId) ≠ x := fun h => by subst h; rw [Nat.beq_refl] at hEq0; cases hEq0
              have hREq : readLocalCell stS 0 = readLocalCell stT 0 := by
                unfold readLocalCell; rw [hSim.2.2.2.2.2.2 0 hne, hSim.2.2.1]
              rw [← hREq]
              cases readLocalCell stS 0 with
              | error _ => exact ⟨(fun _ _ h => by dsimp only at h; cases h), (fun h => by dsimp only at h; cases h)⟩
              | ok v => refine ⟨(fun v' _ hEq => by dsimp only at hEq ⊢; injection hEq with hV; rw [hV]), (fun h => by dsimp only at h; cases h)⟩
          | switchInt op arms oth =>
            dsimp only [replaceTermOp, stepTerm]
            cases hO : evalOperand cfg stS op with
            | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
            | ok po =>
              rcases po with ⟨vo, so⟩
              rcases moveConstSim_evalOperand hSim hO with ⟨stT1, hOT, hSim1⟩
              rw [hOT]; dsimp only
              cases hD : discrBits vo with
              | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
              | ok bits =>
                let tgt := lookupSwitchTarget bits arms oth
                exact ih { so with pc := tgt, stmtIdx := 0 } { stT1 with pc := tgt, stmtIdx := 0 }
                  ⟨rfl, rfl, hSim1.2.2.1, hSim1.2.2.2.1, hSim1.2.2.2.2.1, hSim1.2.2.2.2.2.1, hSim1.2.2.2.2.2.2⟩
          | assert cond exp tgt opt =>
            dsimp only [replaceTermOp, stepTerm]
            cases hSkip : (opt && !cfg.enforceOptionalOverflow) with
            | true =>
              simp only [↓reduceIte]
              exact ih { stS with pc := tgt, stmtIdx := 0 } { stT with pc := tgt, stmtIdx := 0 }
                ⟨rfl, rfl, hSim.2.2.1, hSim.2.2.2.1, hSim.2.2.2.2.1, hSim.2.2.2.2.2.1, hSim.2.2.2.2.2.2⟩
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases hO : evalOperand cfg stS cond with
              | error _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
              | ok po =>
                rcases po with ⟨vo, so⟩
                rcases moveConstSim_evalOperand hSim hO with ⟨stT1, hOT, hSim1⟩
                rw [hOT]
                cases vo with
                | int _ | staticPtr _ | ptr _ => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
                | bool b =>
                  dsimp only
                  cases hM : (b == exp) with
                  | false => exact ⟨(fun _ _ h => by cases h), (fun h => by exact h)⟩
                  | true =>
                    exact ih { so with pc := tgt, stmtIdx := 0 } { stT1 with pc := tgt, stmtIdx := 0 }
                      ⟨rfl, rfl, hSim1.2.2.1, hSim1.2.2.2.1, hSim1.2.2.2.2.1, hSim1.2.2.2.2.2.1, hSim1.2.2.2.2.2.2⟩
  exact hMain fuel st st ⟨rfl, rfl, rfl, rfl, hInitX, Or.inl hInitX, fun _ _ => rfl⟩

/-! ### `SsaRangePropagation` Docstring Refutation and Optional Overflow Hazard -/

def docstringExampleBody : Body :=
  { numLocals := 4
    stackBackedLocals := []
    blocks :=
      [ { stmts := [.assign 2 (.binOp .lt (.copy 1) (.const (.int 9)))]
          term := .switchInt (.copy 2) [(1, 1)] 2 }
      , { stmts :=
            [ .assign 3 (.binOp .lt (.copy 1) (.const (.int 8)))
            , .assign 0 (.use (.copy 3)) ]
          term := .ret }
      , { stmts := [.assign 0 (.use (.const (.bool false)))]
          term := .ret } ] }

def docstringWrongFoldedBody : Body :=
  { numLocals := 4
    stackBackedLocals := []
    blocks :=
      [ { stmts := [.assign 2 (.binOp .lt (.copy 1) (.const (.int 9)))]
          term := .switchInt (.copy 2) [(1, 1)] 2 }
      , { stmts := [.assign 0 (.use (.const (.bool true)))]
          term := .ret }
      , { stmts := [.assign 0 (.use (.const (.bool false)))]
          term := .ret } ] }

theorem ssaRangeProp_docstring_counterexample_at_8 :
    let rAtBTrue : WrappingRange := { start := 0, stop := 8 }
    let cfg : EvalConfig := { deinitMovedPlace := true, enforceOptionalOverflow := false }
    let st8 : MachineState :=
      { pc := 0, stmtIdx := 0, heap := []
        locals := [.direct none, .direct (some (.int 8)), .direct none, .direct none] }
    tryAsConstant rAtBTrue = none ∧
    decide ((8 : Int) < 9) = true ∧
    decide ((8 : Int) < 8) = false ∧
    runBody cfg docstringExampleBody st8 20 = .returned (.bool false) ∧
    runBody cfg docstringWrongFoldedBody st8 20 = .returned (.bool true) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def optOverflowAssertBody : Body :=
  { numLocals := 2
    stackBackedLocals := []
    blocks :=
      [ { stmts := [], term := .assert (.copy 1) true 1 true }
      , { stmts := [.assign 0 (.use (.copy 1))], term := .ret } ] }

def optOverflowUnsafePropagatedBody : Body :=
  { numLocals := 2
    stackBackedLocals := []
    blocks :=
      [ { stmts := [], term := .assert (.copy 1) true 1 true }
      , { stmts := [.assign 0 (.use (.const (.bool true)))], term := .ret } ] }

theorem ssaRangeProp_optional_overflow_assert_unsound_if_propagated :
    let releaseCfg : EvalConfig := { deinitMovedPlace := true, enforceOptionalOverflow := false }
    let debugCfg : EvalConfig := { deinitMovedPlace := true, enforceOptionalOverflow := true }
    let stFalse : MachineState :=
      { pc := 0, stmtIdx := 0, heap := [], locals := [.direct none, .direct (some (.bool false))] }
    runBody releaseCfg optOverflowAssertBody stFalse 10 = .returned (.bool false) ∧
    runBody releaseCfg optOverflowUnsafePropagatedBody stFalse 10 = .returned (.bool true) ∧
    runBody debugCfg optOverflowAssertBody stFalse 10 = .panicked :=
  ⟨rfl, rfl, rfl⟩

/-! ## Section 6: `EarlyOtherwiseBranch` and `Subtyper` (`CastKind::Subtype`) -/

def childExplicitArmsAfterUeb (enumVariants : Nat) : Nat :=
  if decide (enumVariants - 1 ≤ 1) then enumVariants else 1

def parentHasOnlyMatchedChildrenAndEmptyUnreach (enumVariants matchedArms : Nat) : Bool :=
  decide (matchedArms = enumVariants) && decide (enumVariants ≥ 2)

def uebThenEobCanFire (enumVariants matchedArms : Nat) : Bool :=
  parentHasOnlyMatchedChildrenAndEmptyUnreach enumVariants matchedArms &&
  decide (childExplicitArmsAfterUeb enumVariants = 1)

theorem ueb_eob_enum_fires_iff_exhaustive_at_least_three_variants
    (enumVariants matchedArms : Nat) :
    uebThenEobCanFire enumVariants matchedArms = true ↔
      (matchedArms = enumVariants ∧ enumVariants ≥ 3) := by
  unfold uebThenEobCanFire parentHasOnlyMatchedChildrenAndEmptyUnreach childExplicitArmsAfterUeb
  simp only [Bool.and_eq_true]
  constructor
  · intro ⟨⟨hmEq, hGe2⟩, hChild⟩
    have hm := of_decide_eq_true hmEq
    have h2 : enumVariants ≥ 2 := of_decide_eq_true hGe2
    have hCh : (if decide (enumVariants - 1 ≤ 1) then enumVariants else 1) = 1 :=
      of_decide_eq_true hChild
    cases hLe : decide (enumVariants - 1 ≤ 1) with
    | false =>
      have hn : ¬ (enumVariants - 1 ≤ 1) := of_decide_eq_false hLe
      have hGt1 : 2 ≤ enumVariants - 1 := Nat.gt_of_not_le hn
      refine ⟨hm, ?_⟩
      cases enumVariants with
      | zero => cases hGt1
      | succ k =>
        cases k with
        | zero => cases hGt1
        | succ m =>
          cases m with
          | zero => cases Nat.le_of_succ_le_succ (by exact hGt1)
          | succ r => exact Nat.le_add_left 3 r
    | true =>
      rw [hLe] at hCh
      simp only [↓reduceIte] at hCh
      subst hCh
      cases h2 with
      | step hh => cases hh
  · intro ⟨hm, hGe3⟩
    have hGe2 : enumVariants ≥ 2 := Nat.le_trans (by decide) hGe3
    have hGt1 : ¬ (enumVariants - 1 ≤ 1) := by
      cases enumVariants with
      | zero => cases hGe3
      | succ k =>
        cases k with
        | zero => cases Nat.le_of_succ_le_succ hGe3
        | succ m =>
          cases m with
          | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hGe3)
          | succ r => exact Nat.not_le_of_gt (Nat.succ_lt_succ (Nat.zero_lt_succ r))
    have hLeF : decide (enumVariants - 1 ≤ 1) = false := decide_eq_false hGt1
    refine ⟨⟨decide_eq_true hm, decide_eq_true hGe2⟩, ?_⟩
    rw [hLeF]; rfl

theorem eob_exhaustive_bidirectional_iff
    (cfg : EvalConfig) (vx vy : Int)
    (hvX : vx = 0 ∨ vx = 1 ∨ vx = 2)
    (hvY : vy = 0 ∨ vy = 1 ∨ vy = 2)
    (ret0 ret1 ret2 retOth : ConstVal) (fuel : Nat) (hFuel : fuel ≥ 10) :
    let tailSrc : List BasicBlock :=
      [ { stmts := [.assign 0 (.use (.const ret0))], term := .ret }
      , { stmts := [.assign 0 (.use (.const ret1))], term := .ret }
      , { stmts := [.assign 0 (.use (.const ret2))], term := .ret }
      , { stmts := [.assign 0 (.use (.const retOth))], term := .ret } ]
    let tailTgt : List BasicBlock :=
      [ { stmts := [.assign 0 (.use (.const ret0))], term := .ret }
      , { stmts := [.assign 0 (.use (.const ret1))], term := .ret }
      , { stmts := [.assign 0 (.use (.const ret2))], term := .ret }
      , { stmts := [.assign 0 (.use (.const retOth))], term := .ret } ]
    let bodySrc : Body :=
      { numLocals := 6, stackBackedLocals := []
        blocks :=
          [ { stmts := [.assign 3 (.discr 1)], term := .switchInt (.move 3) [(0, 1), (1, 2), (2, 3)] 4 }
          , { stmts := [.assign 4 (.discr 2)], term := .switchInt (.move 4) [(0, 5)] 8 }
          , { stmts := [.assign 4 (.discr 2)], term := .switchInt (.move 4) [(1, 6)] 8 }
          , { stmts := [.assign 4 (.discr 2)], term := .switchInt (.move 4) [(2, 7)] 8 }
          , { stmts := [], term := .unreachable }
          ] ++ tailSrc }
    let bodyTgt : Body :=
      { numLocals := 6, stackBackedLocals := []
        blocks :=
          [ { stmts := [.assign 3 (.discr 1), .assign 4 (.discr 2), .assign 5 (.binOp .ne (.copy 3) (.copy 4))]
              term := .switchInt (.copy 5) [(0, 5)] 9 }
          , { stmts := [], term := .unreachable }
          , { stmts := [], term := .unreachable }
          , { stmts := [], term := .unreachable }
          , { stmts := [], term := .unreachable }
          , { stmts := [], term := .switchInt (.copy 3) [(0, 6), (1, 7), (2, 8)] 4 }
          ] ++ tailTgt }
    let st : MachineState :=
      { pc := 0, stmtIdx := 0, heap := []
        locals := [.direct none, .direct (some (.int vx)), .direct (some (.int vy)),
                   .direct none, .direct none, .direct none] }
    runBody cfg bodyTgt st fuel = runBody cfg bodySrc st fuel := by
  intro tailSrc tailTgt bodySrc bodyTgt st
  cases fuel with
  | zero => cases hFuel
  | succ f1 => cases f1 with | zero => cases Nat.le_of_succ_le_succ hFuel | succ f2 =>
  cases f2 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel) | succ f3 =>
  cases f3 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel)) | succ f4 =>
  cases f4 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel))) | succ f5 =>
  cases f5 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel)))) | succ f6 =>
  cases f6 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel))))) | succ f7 =>
  cases f7 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel)))))) | succ f8 =>
  cases f8 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel))))))) | succ f9 =>
  cases f9 with | zero => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hFuel)))))))) | succ fRem =>
  rcases cfg with ⟨dmp, eoo⟩
  rcases hvX with rfl | rfl | rfl <;>
    rcases hvY with rfl | rfl | rfl <;>
    cases dmp <;>
    rfl

/-! ### `Subtyper` (`MirPhase::Runtime(Initial)`, `erase_and_anonymize_regions`, `CastKind::Subtype`) -/

inductive RegionTag where
  | rStatic
  | namedA
  | erased
  | anon
  deriving DecidableEq, Repr

inductive MirTy where
  | fnPtr (hrtb : Bool) (argReg : RegionTag)
  | refTy (reg : RegionTag)
  deriving DecidableEq, Repr

def eraseAndAnonymizeRegions : MirTy → MirTy
  | .fnPtr true _ => .fnPtr true .anon
  | .fnPtr false _ => .fnPtr false .erased
  | .refTy _ => .refTy .erased

def needsSubtyperCast (rhsTy lhsTy : MirTy) : Bool :=
  eraseAndAnonymizeRegions rhsTy != eraseAndAnonymizeRegions lhsTy

def subtyperRewriteBlock (tmp dst : LocalId) (op : Operand) (term : Term) : BasicBlock :=
  { stmts := [.assign tmp (.use op), .assign dst (.subtypeCast (.move tmp))], term := term }

private theorem sub_listGet2 {α : Type} (a b : α) : listGet [a, b] 2 = none := rfl
private theorem sub_listGet1 {α : Type} (a : α) : listGet [a] 1 = none := rfl

theorem writeLocalCell_stmtIdx_eq (st : MachineState) (dst : LocalId) (v : Val)
    {st' : MachineState} (h : writeLocalCell st dst v = .ok st') :
    st'.stmtIdx = st.stmtIdx := by
  dsimp only [writeLocalCell] at h
  cases hG : listGet st.locals dst with
  | none => rw [hG] at h; cases h
  | some s =>
    rw [hG] at h
    cases s with
    | dead => cases h
    | direct _ =>
      dsimp only at h
      cases hS : listSet st.locals dst (.direct (some v)) with
      | none => rw [hS] at h; cases h
      | some _ => rw [hS] at h; dsimp only at h; injection h with hs; subst hs; rfl
    | stack aid =>
      dsimp only at h
      cases hH : listGet st.heap aid with
      | none => rw [hH] at h; cases h
      | some e =>
        rw [hH] at h; rcases e with ⟨ea, ec⟩; dsimp only at h
        cases ea with
        | false => simp only [Bool.not_false, ↓reduceIte] at h; cases h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hS : listSet st.heap aid { alive := true, cell := some v } with
          | none => rw [hS] at h; dsimp only at h; cases h
          | some _ => rw [hS] at h; dsimp only at h; injection h with hs; subst hs; rfl

theorem writeLocalCell_with_stmtIdx (st : MachineState) (dst : LocalId) (v : Val) (k : Nat) :
    writeLocalCell { st with stmtIdx := k } dst v =
    match writeLocalCell st dst v with
    | .error u => .error u
    | .ok s => .ok { s with stmtIdx := k } := by
  dsimp only [writeLocalCell]
  cases listGet st.locals dst with
  | none => rfl
  | some s =>
    cases s with
    | dead => rfl
    | direct _ =>
      dsimp only
      cases listSet st.locals dst (.direct (some v)) <;> rfl
    | stack aid =>
      dsimp only
      cases listGet st.heap aid with
      | none => rfl
      | some e =>
        rcases e with ⟨ea, ec⟩
        dsimp only
        cases ea with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases listSet st.heap aid { alive := true, cell := some v } <;> rfl

theorem deinitLocalCell_stmtIdx_eq (st : MachineState) (loc : LocalId) :
    (deinitLocalCell st loc).stmtIdx = st.stmtIdx := by
  dsimp only [deinitLocalCell]
  cases listGet st.locals loc with
  | none => rfl
  | some s =>
    cases s with
    | dead => rfl
    | direct _ => dsimp only; cases listSet st.locals loc (.direct none) <;> rfl
    | stack aid =>
      dsimp only
      cases listGet st.heap aid with
      | none => rfl
      | some e => dsimp only; cases listSet st.heap aid { e with cell := none } <;> rfl

theorem evalOperand_stmtIdx_eq (cfg : EvalConfig) (st : MachineState) (op : Operand)
    {v : Val} {st' : MachineState} (h : evalOperand cfg st op = .ok (v, st')) :
    st'.stmtIdx = st.stmtIdx := by
  cases op with
  | const _ => injection h with h1; injection h1 with _ hs; subst hs; rfl
  | copy loc =>
    dsimp only [evalOperand] at h
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at h; cases h
    | ok _ => rw [hR] at h; injection h with h1; injection h1 with _ hs; subst hs; rfl
  | move loc =>
    dsimp only [evalOperand] at h
    cases hR : readLocalCell st loc with
    | error _ => rw [hR] at h; cases h
    | ok _ =>
      rw [hR] at h; injection h with h1; injection h1 with _ hs; subst hs
      cases cfg.deinitMovedPlace with
      | false => rfl
      | true => exact deinitLocalCell_stmtIdx_eq st loc

theorem stepTerm_stmtIdx_irrel (cfg : EvalConfig) (st : MachineState) (t : Term) (k : Nat) :
    stepTerm cfg { st with stmtIdx := k } t = stepTerm cfg st t := by
  cases t with
  | goto _ => rfl
  | unreachable => rfl
  | ret => rfl
  | switchInt discr arms oth =>
    dsimp only [stepTerm]
    cases discr with
    | const _ => rfl
    | copy loc =>
      dsimp only [evalOperand]
      have hRL : readLocalCell { st with stmtIdx := k } loc = readLocalCell st loc := rfl
      rw [hRL]
      cases readLocalCell st loc with
      | error _ => rfl
      | ok v => cases discrBits v <;> rfl
    | move loc =>
      dsimp only [evalOperand]
      have hRL : readLocalCell { st with stmtIdx := k } loc = readLocalCell st loc := rfl
      rw [hRL]
      cases readLocalCell st loc with
      | error _ => rfl
      | ok v =>
        dsimp only
        cases cfg.deinitMovedPlace with
        | false => rfl
        | true =>
          simp only [↓reduceIte]
          cases discrBits v with
          | error _ => rfl
          | ok bits =>
            dsimp only [deinitLocalCell]
            cases listGet st.locals loc with
            | none => rfl
            | some s =>
              cases s with
              | dead => rfl
              | direct _ => dsimp only; cases listSet st.locals loc (.direct none) <;> rfl
              | stack aid =>
                dsimp only
                cases listGet st.heap aid with
                | none => rfl
                | some e => dsimp only; cases listSet st.heap aid { e with cell := none } <;> rfl
  | assert cond exp tgt opt =>
    dsimp only [stepTerm]
    cases (opt && !cfg.enforceOptionalOverflow) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases cond with
      | const c =>
        dsimp only [evalOperand]
        cases constToVal c <;> rfl
      | copy loc =>
        dsimp only [evalOperand]
        have hRL : readLocalCell { st with stmtIdx := k } loc = readLocalCell st loc := rfl
        rw [hRL]
        cases readLocalCell st loc with
        | error _ => rfl
        | ok v => cases v <;> rfl
      | move loc =>
        dsimp only [evalOperand]
        have hRL : readLocalCell { st with stmtIdx := k } loc = readLocalCell st loc := rfl
        rw [hRL]
        cases readLocalCell st loc with
        | error _ => rfl
        | ok v =>
          dsimp only
          cases cfg.deinitMovedPlace with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases v <;> rfl
          | true =>
            simp only [↓reduceIte]
            cases v with
            | int _ | staticPtr _ | ptr _ => rfl
            | bool b =>
              dsimp only
              cases (b == exp) with
              | false => rfl
              | true =>
                simp only [↓reduceIte]
                dsimp only [deinitLocalCell]
                cases listGet st.locals loc with
                | none => rfl
                | some s =>
                  cases s with
                  | dead => rfl
                  | direct _ => dsimp only; cases listSet st.locals loc (.direct none) <;> rfl
                  | stack aid =>
                    dsimp only
                    cases listGet st.heap aid with
                    | none => rfl
                    | some e => dsimp only; cases listSet st.heap aid { e with cell := none } <;> rfl

theorem subtyper_region_erasure_and_operational_equiv
    (cfg : EvalConfig) (tmp dst : LocalId) (op : Operand)
    (hDistinct : tmp ≠ dst ∧ tmp ≠ 0 ∧ opMentionsLocal tmp op = false)
    (tailBlocks : List BasicBlock) (hSafe : bodyTailSafeForSciMove tmp tailBlocks = true)
    (hArm : Term) (hNoTmpTerm : termMentionsLocal tmp hArm = false) (hGe1 : termTargetsGe1 hArm = true)
    (st : MachineState) (fuel : Nat) (hFuel : fuel ≥ 2)
    (hpc0 : st.pc = 0) (hsi0 : st.stmtIdx = 0)
    (hTmpSlot : ∃ oT, listGet st.locals tmp = some (.direct oT)) :
    needsSubtyperCast (.fnPtr true .namedA) (.fnPtr false .rStatic) = true ∧
    needsSubtyperCast (.refTy .rStatic) (.refTy .namedA) = false ∧
    let bodySrc : Body := { numLocals := 0, stackBackedLocals := [], blocks := { stmts := [.assign dst (.use op)], term := hArm } :: tailBlocks }
    let bodyTgt : Body := { numLocals := 0, stackBackedLocals := [], blocks := subtyperRewriteBlock tmp dst op hArm :: tailBlocks }
    runBody cfg bodyTgt st (fuel + 1) = runBody cfg bodySrc st fuel := by
  refine ⟨rfl, rfl, ?_⟩
  rcases hDistinct with ⟨hTmpDst, hTmpZero, hNoOp⟩
  rcases hTmpSlot with ⟨oT, hGTmp⟩
  rcases st with ⟨spc, ssi, sloc, sheap⟩
  dsimp only at hpc0 hsi0
  subst hpc0; subst hsi0
  cases fuel with
  | zero => cases hFuel
  | succ f1 =>
    cases f1 with
    | zero => cases Nat.le_of_succ_le_succ hFuel
    | succ fRem =>
      dsimp only [runBody, listGet, stepStmt, subtyperRewriteBlock, evalRvalue]
      cases hOp : evalOperand cfg { pc := 0, stmtIdx := 0, locals := sloc, heap := sheap } op with
      | error u => rfl
      | ok po =>
        rcases po with ⟨vp, sp⟩
        dsimp only
        have hPre : opPreservesMoveX tmp op = true := by
          cases op with
          | const _ => rfl | copy _ => rfl
          | move l => dsimp [opMentionsLocal] at hNoOp; dsimp [opPreservesMoveX]; rw [hNoOp]; rfl
        have hXTmp := evalOperand_preserves_direct_x cfg tmp oT hGTmp hPre hOp
        rcases listSet_exists_of_get hXTmp (.direct (some vp)) with ⟨ls1, hS1⟩
        have hWTmp : writeLocalCell sp tmp vp = .ok { sp with locals := ls1 } := by
          dsimp only [writeLocalCell]; rw [hXTmp, hS1]
        rw [hWTmp]; dsimp only
        have hpcSp : sp.pc = 0 := evalOperand_pc_eq cfg _ op hOp
        have hsiSp : sp.stmtIdx = 0 := evalOperand_stmtIdx_eq cfg _ op hOp
        rw [hpcSp, hsiSp]
        dsimp only [stepStmt, evalRvalue, evalOperand, readLocalCell]
        rw [listGet_listSet_eq hS1]; dsimp only
        let spMid0 : MachineState :=
          if cfg.deinitMovedPlace then deinitLocalCell { sp with locals := ls1 } tmp
          else { sp with locals := ls1 }
        have hMidSim : StateAgreeExcept tmp sp spMid0 := by
          cases hD : cfg.deinitMovedPlace with
          | false =>
            dsimp [spMid0]; rw [hD]; simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨rfl, rfl, rfl, (listSet_length_eq hS1).symm, fun i hix => (listGet_listSet_ne hS1 hix).symm⟩
          | true =>
            dsimp [spMid0]; rw [hD]; simp only [↓reduceIte, deinitLocalCell]
            rw [listGet_listSet_eq hS1]; dsimp only
            rcases listSet_exists_of_get (listGet_listSet_eq hS1) (.direct none) with ⟨ls2, hS2⟩
            rw [hS2]; dsimp only
            refine ⟨rfl, rfl, rfl, (listSet_length_eq hS1).symm.trans (listSet_length_eq hS2).symm, ?_⟩
            intro i hix
            rw [listGet_listSet_ne hS2 hix, listGet_listSet_ne hS1 hix]
        have hMidStmtEq :
            (if cfg.deinitMovedPlace then deinitLocalCell { pc := 0, stmtIdx := 0 + 1, locals := ls1, heap := sp.heap } tmp
             else { pc := 0, stmtIdx := 0 + 1, locals := ls1, heap := sp.heap }) = { spMid0 with stmtIdx := 1 } := by
          cases hD : cfg.deinitMovedPlace with
          | false => dsimp [spMid0]; rw [hD]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hpcSp]
          | true =>
            dsimp [spMid0]; rw [hD]; simp only [↓reduceIte, deinitLocalCell]
            rw [listGet_listSet_eq hS1]; dsimp only
            rcases listSet_exists_of_get (listGet_listSet_eq hS1) (.direct none) with ⟨ls2, hS2⟩
            rw [hS2]; dsimp only; rw [hpcSp]
        rw [hMidStmtEq, writeLocalCell_with_stmtIdx]
        have hW := agree_writeLocalCell_not_mentioned hMidSim hTmpDst.symm vp
        cases hWSrc : writeLocalCell sp dst vp with
        | error u =>
          rw [hW.1 u hWSrc]
        | ok stS0 =>
          rcases hW.2 stS0 hWSrc with ⟨stT0, hWTgt, hAg0⟩
          rw [hWTgt]; dsimp only
          have hpcS0 : stS0.pc = 0 := (writeLocalCell_pc_eq _ _ _ hWSrc).trans hpcSp
          have hpcT0 : stT0.pc = 0 := hAg0.1.symm.trans hpcS0
          have hsiS0 : stS0.stmtIdx = 0 := (writeLocalCell_stmtIdx_eq _ _ _ hWSrc).trans hsiSp
          have hsiT0 : stT0.stmtIdx = 0 := hAg0.2.1.symm.trans hsiS0
          rw [hpcT0, hpcS0, hsiS0]
          dsimp only
          have hAdd2 : (1 + 1 : Nat) = 2 := rfl
          have hAdd1 : (0 + 1 : Nat) = 1 := rfl
          rw [hAdd2, hAdd1]
          have hStT := stepTerm_stmtIdx_irrel cfg stT0 hArm 2
          have hStS := stepTerm_stmtIdx_irrel cfg stS0 hArm 1
          rw [hpcT0] at hStT
          rw [hpcS0] at hStS
          rw [hStT, hStS]
          have hTerm := agree_stepTerm_not_mentioned (cfg := cfg) hTmpZero hAg0 hNoTmpTerm hGe1
          cases hT : stepTerm cfg stS0 hArm with
          | stop out => rw [hTerm.1 out hT]
          | cont stS1 =>
            rcases hTerm.2 stS1 hT with ⟨stT1, hTT, hGe, hAg1⟩
            rw [hTT]; dsimp only
            have hAgRev1 : StateAgreeExcept tmp stT1 stS1 :=
              ⟨hAg1.1.symm, hAg1.2.1.symm, hAg1.2.2.1.symm, hAg1.2.2.2.1.symm, fun i hix => (hAg1.2.2.2.2 i hix).symm⟩
            exact agree_runBody_tail
              (body1 := { numLocals := 0, stackBackedLocals := [], blocks := subtyperRewriteBlock tmp dst op hArm :: tailBlocks })
              (body2 := { numLocals := 0, stackBackedLocals := [], blocks := { stmts := [.assign dst (.use op)], term := hArm } :: tailBlocks })
              hTmpZero rfl (fun _ => rfl) (fun _ => rfl) hSafe fRem stT1 stS1 (hAg1.1 ▸ hGe) hAgRev1

namespace Examples

theorem ce1_remove_storage_markers_erases_dangling_stack_ptr_ub :
    evalWithMiriPipeline miriMir0Opt0 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    evalWithMiriPipeline miriMir2Opt0 miriDefaultCfg danglingStackPtrBody 20 = .returned (.int 42) ∧
    evalWithMiriPipeline miriMir2Opt1 miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    evalWithMiriPipeline miriMir1Opt0DisableRsm miriDefaultCfg danglingStackPtrBody 20 = .ub .danglingStackPtr ∧
    ¬ ReverseUbSound
        (evalWithMiriPipeline miriMir0Opt0 miriDefaultCfg danglingStackPtrBody 20)
        (evalWithMiriPipeline miriMir2Opt0 miriDefaultCfg danglingStackPtrBody 20) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro hRev
  rcases hRev .danglingStackPtr rfl with ⟨w, hw⟩
  have h42 : evalWithMiriPipeline miriMir2Opt0 miriDefaultCfg danglingStackPtrBody 20 = .returned (.int 42) := rfl
  rw [h42] at hw
  cases hw

def loopAliasBody : Body :=
  { numLocals := 3
    stackBackedLocals := [1]
    blocks :=
      [ { stmts :=
            [ .storageLive 1
            , .assign 1 (.use (.const (.int 10)))
            , .storageLive 2
            , .assign 2 (.addrOf 1)
            , .storageDead 1
            , .storageLive 1
            , .assign 1 (.use (.const (.int 11)))
            , .assign 0 (.derefPtr (.copy 2))
            , .storageDead 1
            , .storageDead 2
            ]
          term := .ret } ] }

theorem ce1b_loop_reallocation_merges_distinct_alloc_ids :
    evalWithMiriPipeline miriMir0Opt0 miriDefaultCfg loopAliasBody 30 = .ub .danglingStackPtr ∧
    evalWithMiriPipeline miriMir2Opt0 miriDefaultCfg loopAliasBody 30 = .returned (.int 11) ∧
    evalWithMiriPipeline miriMir2Opt1 miriDefaultCfg loopAliasBody 30 = .ub .danglingStackPtr ∧
    evalWithMiriPipeline miriMir1Opt0DisableRsm miriDefaultCfg loopAliasBody 30 = .ub .danglingStackPtr :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ce2_simplify_cmp_retaining_move_operand_deinits_switch_scrutinee_ub :
    let deinitCfg : EvalConfig := { deinitMovedPlace := true, enforceOptionalOverflow := true }
    let srcBody : Body :=
      { numLocals := 3, stackBackedLocals := []
        blocks :=
          [ { stmts := [.assign 2 (.binOp .eq (.move 1) (.const (.int 43)))]
              term := .switchInt (.copy 2) [(0, 2)] 1 }
          , { stmts := [.assign 0 (.use (.const (.int 10)))], term := .ret }
          , { stmts := [.assign 0 (.use (.const (.int 20)))], term := .ret } ] }
    let buggyNoDowngradeBody : Body :=
      { numLocals := 3, stackBackedLocals := []
        blocks :=
          [ { stmts := [.assign 2 (.binOp .eq (.move 1) (.const (.int 43)))]
              term := .switchInt (.copy 1) [(43, 1)] 2 }
          , { stmts := [.assign 0 (.use (.const (.int 10)))], term := .ret }
          , { stmts := [.assign 0 (.use (.const (.int 20)))], term := .ret } ] }
    let fixedBody : Body :=
      { numLocals := 3, stackBackedLocals := []
        blocks :=
          [ rewriteSciBlock 2 1 43 .eq (.move 1) (.const (.int 43)) 0 2 1
          , { stmts := [.assign 0 (.use (.const (.int 10)))], term := .ret }
          , { stmts := [.assign 0 (.use (.const (.int 20)))], term := .ret } ] }
    let st43 : MachineState :=
      { pc := 0, stmtIdx := 0, heap := [], locals := [.direct none, .direct (some (.int 43)), .direct none] }
    runBody deinitCfg srcBody st43 10 = .returned (.int 10) ∧
    runBody deinitCfg buggyNoDowngradeBody st43 10 = .ub .uninitRead ∧
    runBody deinitCfg fixedBody st43 10 = .returned (.int 10) :=
  ⟨rfl, rfl, rfl⟩

theorem ce3_ssa_range_multi_predecessor_join_unsound_without_intersection :
    let cfg : EvalConfig := { deinitMovedPlace := false, enforceOptionalOverflow := true }
    let joinBody : Body :=
      { numLocals := 2, stackBackedLocals := []
        blocks :=
          [ { stmts := [], term := .switchInt (.copy 1) [(7, 2)] 1 }
          , { stmts := [], term := .goto 2 }
          , { stmts := [.assign 0 (.use (.copy 1))], term := .ret } ] }
    let buggyPropagatedBody : Body :=
      { numLocals := 2, stackBackedLocals := []
        blocks :=
          [ { stmts := [], term := .switchInt (.copy 1) [(7, 2)] 1 }
          , { stmts := [], term := .goto 2 }
          , { stmts := [.assign 0 (.use (.const (.int 7)))], term := .ret } ] }
    let st9 : MachineState :=
      { pc := 0, stmtIdx := 0, heap := [], locals := [.direct none, .direct (some (.int 9))] }
    runBody cfg joinBody st9 10 = .returned (.int 9) ∧
    runBody cfg buggyPropagatedBody st9 10 = .returned (.int 7) :=
  ⟨rfl, rfl⟩

theorem ce4_eob_issue_95162_non_exhaustive_hoist_introduces_ub :
    let cfg : EvalConfig := { deinitMovedPlace := true, enforceOptionalOverflow := true }
    let eobNonExhaustiveSrc : Body :=
      { numLocals := 6, stackBackedLocals := []
        blocks :=
          [ { stmts := [.assign 3 (.discr 1)], term := .switchInt (.move 3) [(0, 2), (1, 3)] 1 }
          , { stmts := [.assign 0 (.use (.const (.int 100)))], term := .ret }
          , { stmts := [.assign 4 (.discr 2)], term := .switchInt (.move 4) [(0, 4)] 1 }
          , { stmts := [.assign 4 (.discr 2)], term := .switchInt (.move 4) [(1, 5)] 1 }
          , { stmts := [.assign 0 (.use (.const (.int 10)))], term := .ret }
          , { stmts := [.assign 0 (.use (.const (.int 20)))], term := .ret } ] }
    let buggyEobHoistTgt : Body :=
      { numLocals := 6, stackBackedLocals := []
        blocks :=
          [ { stmts := [.assign 3 (.discr 1), .assign 4 (.discr 2), .assign 5 (.binOp .ne (.copy 3) (.copy 4))]
              term := .switchInt (.copy 5) [(0, 6)] 1 }
          , { stmts := [.assign 0 (.use (.const (.int 100)))], term := .ret }
          , { stmts := [], term := .unreachable }
          , { stmts := [], term := .unreachable }
          , { stmts := [.assign 0 (.use (.const (.int 10)))], term := .ret }
          , { stmts := [.assign 0 (.use (.const (.int 20)))], term := .ret }
          , { stmts := [], term := .switchInt (.copy 3) [(0, 4), (1, 5)] 7 }
          , { stmts := [], term := .unreachable } ] }
    let st22 : MachineState :=
      { pc := 0, stmtIdx := 0, heap := []
        locals := [.direct none, .direct (some (.int 2)), .direct (some (.int 2)),
                   .direct none, .direct none, .direct none] }
    runBody cfg eobNonExhaustiveSrc st22 15 = .returned (.int 100) ∧
    runBody cfg buggyEobHoistTgt st22 15 = .ub .unreachableReached :=
  ⟨rfl, rfl⟩

end Examples

end StorageMarkersRangeSwitch
