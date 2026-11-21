import ToyCoalesce.Basic

/-!
# Copy-to-move upgrades under three `move` semantics

An upgrade replaces the operand `copy q` of one body statement by `move q`. Whether this
preserves behaviour depends on the `move` semantics (`MoveSem`), which is a parameter. The
conditions below are *dynamic*: they are stated over the access log of the source run.
-/

namespace Toy.Coalesce

/-- Replace a `copy q` operand by `move q` in the three upgradable statement shapes; every other
statement is unchanged. -/
def Stmt.upgradeCopy : Stmt → Stmt
  | .assign lhs [.copy q] => .assign lhs [.move q]
  | .call fn (.copy q) => .call fn (.move q)
  | .out (.copy q) => .out (.move q)
  | st => st

/-- Apply `f` to the list element at index `k` (no change if `k` is out of range). -/
def modifyAt (f : Stmt → Stmt) : List Stmt → Nat → List Stmt
  | [], _ => []
  | st :: sts, 0 => f st :: sts
  | st :: sts, k + 1 => st :: modifyAt f sts k

/-- Upgrade the body statement at index `k`. -/
def Prog.upgradeAt (P : Prog) (k : Nat) : Prog :=
  { P with body := modifyAt Stmt.upgradeCopy P.body k }

/-- Two places have disjoint cell windows: different locals, or non-overlapping windows
`[off, off + len)`. Edge case: a width-`0` window strictly inside another window of the same local
counts as overlapping it (for example `⟨0, 1, 0⟩` and `⟨0, 0, 2⟩`), although it has no cells; every
use of this predicate is then conservative. -/
def WindowsDisjoint (a b : Place) : Prop :=
  a.base ≠ b.base ∨ a.off + a.len ≤ b.off ∨ b.off + b.len ≤ a.off

instance (a b : Place) : Decidable (WindowsDisjoint a b) := by
  unfold WindowsDisjoint; infer_instance

/-- An *upgrade site* for place `q` at body index `k`: a one-operand assignment `lhs := copy q`
whose left side is disjoint from `q`, a call `call fn (copy q)` whose callee parameter is not
`q.base`, or `out (copy q)`. -/
def UpgradeSite (P : Prog) (k : Nat) (q : Place) : Prop :=
  (∃ lhs, P.body[k]? = some (.assign lhs [.copy q]) ∧ WindowsDisjoint lhs q) ∨
  (∃ fn, P.body[k]? = some (.call fn (.copy q)) ∧ (P.fn fn).prm ≠ q.base) ∨
  P.body[k]? = some (.out (.copy q))

/-- An upgrade site that is a call `call fn (copy q)` (callee `fn`). -/
def CallSite (P : Prog) (k fn : Nat) (q : Place) : Prop :=
  P.body[k]? = some (.call fn (.copy q)) ∧ (P.fn fn).prm ≠ q.base

/-- Log entries *after the use* at tick `k`: entries of later ticks, and, when `inclCall`, the
entries made inside the callee of the statement at tick `k`. -/
def afterUse (inclCall : Bool) (k : Nat) (e : Access) : Bool :=
  decide (k < e.tick) || (inclCall && decide (e.tick = k) && e.inCall)

/-- Scan a log: among the entries satisfying `after` that touch cell `(loc, off)`, the first one
(if any) is not a read. -/
def firstTouchNotRead (after : Access → Bool) (loc off : Nat) : List Access → Bool
  | [] => true
  | e :: es =>
    if after e && e.loc == loc && e.off == off then e.kind != .read
    else firstTouchNotRead after loc off es

/-- *No read before re-initialization*: for every cell of `q`, the first access after the use at
tick `k` (including accesses inside the callee at tick `k` when `inclCall`) is a write or an
allocation/deallocation reset, or there is none. Reads through pointers, inside callees and inside
the destructor block all count, because every cell access is logged. -/
def NoReadBeforeReinit (log : List Access) (k : Nat) (inclCall : Bool) (q : Place) : Prop :=
  ∀ j, j < q.len → firstTouchNotRead (afterUse inclCall k) q.base (q.off + j) log = true

instance (log : List Access) (k : Nat) (c : Bool) (q : Place) :
    Decidable (NoReadBeforeReinit log k c q) := by unfold NoReadBeforeReinit; infer_instance

/-- The callee at tick `k` does not access (read, write or reset) any cell of `q`: in particular
`q` is unreachable from the callee through escaped pointers during the call. -/
def CalleeAvoids (log : List Access) (k : Nat) (q : Place) : Prop :=
  log.all (fun e => !(decide (e.tick = k) && e.inCall && decide (e.loc = q.base) &&
    decide (q.off ≤ e.off) && decide (e.off < q.off + q.len))) = true

instance (log : List Access) (k : Nat) (q : Place) : Decidable (CalleeAvoids log k q) := by
  unfold CalleeAvoids; infer_instance

/-- Callee `fn` never takes the address of a place based at its own parameter. -/
def CalleeNoParamAddr (P : Prog) (fn : Nat) : Prop :=
  (P.fn fn).body.any (Stmt.takesAddr (P.fn fn).prm) = false

instance (P : Prog) (fn : Nat) : Decidable (CalleeNoParamAddr P fn) := by
  unfold CalleeNoParamAddr; infer_instance

/-- If the parameter local of callee `fn` is not address-taken anywhere in `P`, the callee never
takes the address of its parameter. -/
theorem calleeNoParamAddr_of_not_addrTaken_prm (P : Prog) (fn : Nat)
    (h : ¬ AddrTaken P (P.fn fn).prm) : CalleeNoParamAddr P fn := by
  unfold CalleeNoParamAddr
  cases hb : (P.fn fn).body.any (Stmt.takesAddr (P.fn fn).prm) with
  | false => rfl
  | true =>
    exfalso
    by_cases hfn : fn < P.fns.length
    · have hmem : P.fn fn ∈ P.fns := by
        simp only [Prog.fn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hfn,
          Option.getD_some]
        exact List.getElem_mem hfn
      apply h
      unfold AddrTaken
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inl (Or.inr ⟨P.fn fn, hmem, by simpa [List.any_eq_true] using hb⟩)
    · have he : P.fn fn = ⟨0, []⟩ := by
        simp only [Prog.fn, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [he] at hb; simp at hb

/-! ## The semantics depends on a program only through its local sizes and callee table -/

section Congr

variable {P P' : Prog} (hs : P.sizes = P'.sizes) (hf : P.fns = P'.fns)
include hs

theorem resolvePlace_congr (s : St) (q : Place) : resolvePlace P s q = resolvePlace P' s q := by
  simp [resolvePlace, Prog.size, hs]

theorem evalOp_congr (ms : MoveSem) (s : St) (o : Operand) : evalOp ms P s o = evalOp ms P' s o := by
  cases o <;> simp [evalOp, resolvePlace_congr hs, Prog.size, hs]

theorem evalOps_congr (ms : MoveSem) (s : St) (os : List Operand) :
    evalOps ms P s os = evalOps ms P' s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp [evalOps, evalOp_congr hs, ih]

theorem writeInOrder_congr (ms : MoveSem) (s : St) (loc off : Nat) (os : List Operand) :
    writeInOrder ms P s loc off os = writeInOrder ms P' s loc off os := by
  induction os generalizing s off with
  | nil => rfl
  | cons o os ih => simp [writeInOrder, evalOp_congr hs, ih]

theorem allocate_congr (s : St) (x : Nat) : allocate P s x = allocate P' s x := by
  simp [allocate, liveOthers, Prog.nloc, Prog.size, hs]

theorem deallocate_congr (s : St) (x : Nat) : deallocate P s x = deallocate P' s x := by
  simp [deallocate, Prog.size, hs]

theorem cmpOp_congr (ms : MoveSem) (A : Layout) (s : St) (a b : Operand) (f : Nat → Nat → Bool) :
    cmpOp ms P A s a b f = cmpOp ms P' A s a b f := by
  simp [cmpOp, evalOp_congr hs]

theorem execBasic_congr (sem : Sem) (A : Layout) : execBasic sem P A = execBasic sem P' A := by
  funext s st
  cases st <;> simp [execBasic, allocate_congr hs, deallocate_congr hs, resolvePlace_congr hs,
    evalOps_congr hs, writeInOrder_congr hs, evalOp_congr hs, cmpOp_congr hs, Prog.size, hs]

include hf in
theorem execTop_congr (sem : Sem) (A : Layout) : execTop sem P A = execTop sem P' A := by
  funext s st
  have hfn : ∀ fn, P.fn fn = P'.fn fn := fun fn => by simp [Prog.fn, hf]
  cases st <;> simp [execTop, execStmt, execBasic_congr hs, execCallee, hfn,
    allocate_congr hs, deallocate_congr hs, resolvePlace_congr hs, evalOp_congr hs, Prog.size, hs]

end Congr

/-- Folding over a list in which the element at index `k` is replaced by `g` of it gives the same
result when the step function does not distinguish that element from its replacement. -/
theorem foldl_modifyAt {α : Type} (f : α → Stmt → α) (g : Stmt → Stmt) (l : List Stmt) (k : Nat)
    (h : ∀ st, l[k]? = some st → ∀ a, f a (g st) = f a st) (a : α) :
    (modifyAt g l k).foldl f a = l.foldl f a := by
  induction l generalizing k a with
  | nil => rfl
  | cons st sts ih =>
    cases k with
    | zero => simp [modifyAt, h st rfl]
    | succ k => simpa [modifyAt] using ih k (fun st' h' => h st' (by simpa using h')) (f a st)

/-- Outside `MoveSem.deinit`, `move q` evaluates exactly like `copy q`. -/
theorem evalOp_move_eq_copy (ms : MoveSem) (h : ms ≠ .deinit) (P : Prog) (s : St) (q : Place) :
    evalOp ms P s (.move q) = evalOp ms P s (.copy q) := by
  simp only [evalOp]
  cases resolvePlace P s q with
  | none => rfl
  | some r =>
    simp only
    cases readCells s r.base r.off r.len with
    | mk s' vs => cases vs <;> simp [h]

/-- The run of an upgraded program, when the upgraded statement behaves like the original one. -/
theorem run_upgradeAt_eq (sem : Sem) (P : Prog) (k : Nat) (A : Layout)
    (h : ∀ st, P.body[k]? = some st → ∀ s, execTop sem P A s st.upgradeCopy = execTop sem P A s st) :
    run sem (P.upgradeAt k) A = run sem P A := by
  have hc : execTop sem (P.upgradeAt k) A = execTop sem P A := execTop_congr (P := P.upgradeAt k) (P' := P) rfl rfl sem A
  unfold run
  rw [hc]
  simp only [Prog.code, Prog.upgradeAt, List.foldl_append]
  rw [foldl_modifyAt _ _ _ _ h]

/-! ## Main statements -/

/-- Under `MoveSem.asCopy`, upgrading any body statement leaves the outcome unchanged on every
layout, for either assignment order. -/
theorem upgrade_outcome_eq_moveAsCopy (am : AssignMode) (P : Prog) (k : Nat) (A : Layout) :
    outcome ⟨.asCopy, am⟩ (P.upgradeAt k) A = outcome ⟨.asCopy, am⟩ P A := by
  have hr : run ⟨.asCopy, am⟩ (P.upgradeAt k) A = run ⟨.asCopy, am⟩ P A := by
    refine run_upgradeAt_eq _ P k A (fun st _ s => ?_)
    have hm := evalOp_move_eq_copy .asCopy (by decide) P
    unfold Stmt.upgradeCopy
    split <;> simp [execTop, execStmt, execBasic, evalOps, writeInOrder, hm, Operand.len]
  unfold outcome; rw [hr]; rfl

/-- Under `MoveSem.inPlaceCall`, upgrading a body statement that is not a call leaves the outcome
unchanged on every layout. -/
theorem upgrade_outcome_eq_moveInPlaceCall_of_not_call (am : AssignMode) (P : Prog) (k : Nat)
    (hnc : ∀ fn a, P.body[k]? ≠ some (.call fn a)) (A : Layout) :
    outcome ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A = outcome ⟨.inPlaceCall, am⟩ P A := by
  have hr : run ⟨.inPlaceCall, am⟩ (P.upgradeAt k) A = run ⟨.inPlaceCall, am⟩ P A := by
    refine run_upgradeAt_eq _ P k A (fun st hst s => ?_)
    have hm := evalOp_move_eq_copy .inPlaceCall (by decide) P
    unfold Stmt.upgradeCopy
    split
    · simp [execTop, execStmt, execBasic, evalOps, writeInOrder, hm, Operand.len]
    · exact absurd hst (hnc _ _)
    · simp [execTop, execStmt, execBasic, hm]
    · rfl
  unfold outcome; rw [hr]; rfl

end Toy.Coalesce
