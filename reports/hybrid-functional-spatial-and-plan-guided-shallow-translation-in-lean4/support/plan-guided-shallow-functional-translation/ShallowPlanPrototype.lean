/-!
# Plan-Guided Shallow Functional Translation Prototype (`ShallowPlanPrototype.lean`)

Self-contained, kernel-checked Lean 4 (`v4.34.1`) mechanization accompanying
`reports/plan-guided-shallow-functional-translation-2026-10-29/REPORT.md`.

This module mechanically verifies the six core architectural mechanisms analyzed
in the report:
1. **First Futamura Projection & Spine-Preserving Branch Joins**:
   `evalSym` specializes a concrete CFG + `TransPlan` on symbolic inputs to a
   pure functional term via kernel `rfl` (`choose_futamura_rfl`), by pushing
   `if b then ... else ...` inside individual local slots (`zipBranchLocals`)
   so the outer `List` spine remains concrete for subsequent structural lookups
   (`listGet`).
2. **Defensive Hint-Guided Translation with Top-Element Failure (`Partial.ub`)**:
   Mapping `.fail` to `Partial.ub` (`defined := False`) makes `evalSym plan body`
   unconditionally sound (`evalSym_sound`) for *every* `plan : TransPlan` and
   *every* `body : MirBody`—yielding `computePlan_sound` for any untrusted
   heuristic `computePlan : MirBody → TransPlan` with zero proof obligations on
   `computePlan`—while `WellFormedOn pre` rejects `.fail` on reachable paths
   (`embedRes_fail_rejected_by_pure`) and admits `.fail` on unreachable paths
   (`embedRes_fail_accepted_outside_pre`) at zero proof cost.
3. **Executable Backward Continuations in `Type` vs. Prophecy Variables in `Prop`**:
   Backward lenses `SymVal → List SymVal` live in `Type` and compute by `rfl`,
   whereas existential prophecy specifications live in `Prop`.
4. **Unified `LoanEntry` over `OwnerId := .local_ Nat | .loan Nat`**:
   A single `LoanEntry` and a single `endLoan` rule uniformly handle whole-local
   borrows (`&mut x`), field projections (`&mut p.1`), nested reborrows
   (`&mut (*r1).1`, where upstream Aeneas `SymbolicToPureAbs.ml` asserts
   `abs_level = 0`), branch-joined multi-owner borrows
   (`if b { &mut x } else { &mut y }`), and borrow-returning calls.
5. **Positional `TransPlan` Stepping `MirBody` Directly**:
   `evalSym` steps an unstructured multi-block CFG (`chooseMirBody`) directly
   along `TransPlan` without an intermediate `StructuredMir` semantics.
6. **Spatial Disjointness, `OwnLoc` Framing, and the 3-Part Simulation Invariant**:
   Non-atomic writes (`MemState.writeNA`) frame across disjoint `OwnLoc`
   locations (`OwnLoc.writeNA_frame`), and symbolic `endLoan` commutes with a
   concrete runtime no-op under `SimRel` (`concrete_write_and_endLoan_commute`).
-/

namespace ShallowPlanPrototype

/-!
## 1. Result Monad and Spine-Preserving Branch Joins (Finding 1)
-/

/-- Result monad for functional translation (`.ok`, `.fail`, `.div`). -/
inductive AeneasRes (α : Type) where
  | ok (v : α)
  | fail
  | div
  deriving DecidableEq, Repr

/-- Monadic bind for `AeneasRes`. -/
def AeneasRes.bind {α β : Type} (x : AeneasRes α) (k : α → AeneasRes β) : AeneasRes β :=
  match x with
  | .ok v => k v
  | .fail => .fail
  | .div => .div

/-- Definitional left-identity law (`AeneasRes.bind (.ok v) k = k v`). -/
theorem AeneasRes.bind_ok {α β : Type} (v : α) (k : α → AeneasRes β) :
    AeneasRes.bind (.ok v) k = k v :=
  rfl

/-- Structural list indexing compiled directly to `List.rec` and `Nat.rec` without
    multi-argument splitter overhead: reduces by pure $\iota$-reduction on any
    concrete `List` spine with zero axioms. -/
def listGet {α : Type} (xs : List α) (idx : Nat) : Option α :=
  match xs with
  | [] => none
  | x :: rest =>
    match idx with
    | .zero => some x
    | .succ k => listGet rest k

/-- Structural list update preserving the concrete `List` spine. -/
def listSet {α : Type} (xs : List α) (idx : Nat) (v : α) : List α :=
  match xs with
  | [] => []
  | x :: rest =>
    match idx with
    | .zero => v :: rest
    | .succ k => x :: listSet rest k v

/-- Naive branch join returning the entire local store from `if`: the outer
    `List` spine is trapped inside `ite` when `b` is symbolic. -/
def naiveBranchJoin (b : Bool) (x y : Nat) : List (Option Nat) :=
  if b then [some x, some 10] else [some y, some 10]

/-- Spine-preserving branch join: `if` returns only the modified value tuple, and
    the concrete `List` spine is rebuilt outside the `if`. -/
def spinePreservingJoin (b : Bool) (x y : Nat) : List (Option Nat) :=
  let v0 := if b then x else y
  [some v0, some 10]

/-- Subsequent index lookup on `spinePreservingJoin` reduces definitionally by
    `rfl` even when `b`, `x`, and `y` are universally quantified variables. -/
theorem spinePreservingJoin_lookup0 (b : Bool) (x y : Nat) :
    listGet (spinePreservingJoin b x y) 0 = some (some (if b then x else y)) :=
  rfl

/-- Unmodified slots outside the branch delta also reduce definitionally by `rfl`. -/
theorem spinePreservingJoin_lookup1 (b : Bool) (x y : Nat) :
    listGet (spinePreservingJoin b x y) 1 = some (some 10) :=
  rfl

/-- `spinePreservingJoin` is extensionally equal to `naiveBranchJoin` on all inputs,
    while exposing the `List.cons` spine for $\iota$-reduction. -/
theorem spinePreservingJoin_eq_naive (b : Bool) (x y : Nat) :
    spinePreservingJoin b x y = naiveBranchJoin b x y := by
  cases b <;> rfl

/-!
## 2. Order-Theoretic `Partial` Domain and Top-Element Failure (Finding 2)
-/

/-- Constructive partiality domain $B \cup \{\mathsf{UB}\}$ matching
    `Trusted.Partial` in `Trusted/Refinement.lean`. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Refinement relation on `Partial (α → Prop)` matching `instPreorderPartial`
    and `instPreorderFun`/`instPreorderProp` in `Trusted/Refinement.lean`:
    `p₁.Refines p₂` holds iff whenever `p₂` is defined, `p₁` is also defined and
    every outcome permitted by `p₁` is permitted by `p₂`. -/
def Partial.Refines {α : Type} (p₁ p₂ : Partial (α → Prop)) : Prop :=
  ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, ∀ out, p₁.val h₁ out → p₂.val h₂ out

infix:50 " ⊑ " => Partial.Refines

theorem Partial.refines_refl {α : Type} (p : Partial (α → Prop)) : p ⊑ p :=
  fun h => ⟨h, fun _ hout => hout⟩

theorem Partial.refines_trans {α : Type} {p₁ p₂ p₃ : Partial (α → Prop)}
    (h₁₂ : p₁ ⊑ p₂) (h₂₃ : p₂ ⊑ p₃) : p₁ ⊑ p₃ :=
  fun h₃ =>
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, fun out hout => hle₂₃ out (hle₁₂ out hout)⟩

theorem ub_top {α : Type} (p : Partial (α → Prop)) :
    p ⊑ Partial.ub :=
  fun h => False.elim h

theorem not_ub_le_pure {α : Type} (post : α → Prop) :
    ¬ ((@Partial.ub (α → Prop)) ⊑ Partial.pure post) :=
  fun h => (h True.intro).1

/-- Embedding of `AeneasRes α` into `Partial (α → Prop)`:
    - `.ok v` maps to `Partial.pure (fun out => out = v)` (`defined := True`),
    - `.fail` maps to `Partial.ub` (`defined := False`, top element),
    - `.div` maps to `Partial.pure (fun _ => False)` (`defined := True`, empty return set). -/
def embedRes {α : Type} (r : AeneasRes α) : Partial (α → Prop) :=
  match r with
  | .ok v => Partial.pure (fun out => out = v)
  | .fail => Partial.ub
  | .div => Partial.pure (fun _ => False)

/-- Because `embedRes .fail = Partial.ub`, any behavior `p` vacuously refines
    `embedRes .fail`: emitting `.fail` on a mismatched or fuel-exhausted hint
    branch is unconditionally sound (`Abstracts`). -/
theorem embedRes_fail_top {α : Type} (p : Partial (α → Prop)) :
    p ⊑ embedRes .fail :=
  ub_top p

/-- Conversely, `embedRes .fail` never refines a defined specification
    `Partial.pure post`: downstream `WellFormedOn pre` proofs automatically
    reject `.fail` on every reachable input satisfying `pre`. -/
theorem embedRes_fail_rejected_by_pure {α : Type} (post : α → Prop) :
    ¬ (embedRes .fail ⊑ Partial.pure post) :=
  not_ub_le_pure post

/-- On unreachable inputs outside `pre` (`¬ pre`), a conditional specification
    `SpecOn pre post` has `defined := pre`, so `embedRes .fail` refines it at
    zero proof cost. -/
theorem embedRes_fail_accepted_outside_pre {α : Type} {pre : Prop} (post : α → Prop)
    (hunreach : ¬ pre) :
    embedRes .fail ⊑ ({ defined := pre, val := fun _ => post } : Partial (α → Prop)) :=
  fun hpre => False.elim (hunreach hpre)

/-- Divergence (`.div`, e.g. fuel exhaustion in a bounded concrete prefix) refines
    every `embedRes r` under partial-correctness return observation. -/
theorem embedRes_div_le_any {α : Type} (r : AeneasRes α) :
    embedRes .div ⊑ embedRes r := by
  cases r with
  | ok v => exact fun _ => ⟨True.intro, fun _ h => False.elim h⟩
  | fail => exact ub_top _
  | div => exact Partial.refines_refl _

/-!
## 3. Unified `LoanEntry` over `OwnerId` and Backward Continuations (Findings 3 & 4)
-/

/-- Symbolic values supporting scalars, Booleans, pairs, and active loan tokens. -/
inductive SymVal where
  | u8 (n : Nat)
  | bool (b : Bool)
  | pair (fst snd : SymVal)
  | borrow (loanId : Nat)
  deriving DecidableEq, Repr

/-- Unified owner identifier: either a local variable slot or a parent loan. -/
inductive OwnerId where
  | local_ (idx : Nat)
  | loan (id : Nat)
  deriving DecidableEq, Repr

/-- Unified loan entry replacing Aeneas's 3-layer (`tvalue`, `tavalue`, `tevalue`)
    and `abs_level` hierarchy:
    - `id`: unique loan identifier,
    - `owners`: ordered list of parent owners (`.local_` or `.loan`),
    - `curVal`: current symbolic value held by the borrow,
    - `back`: executable backward continuation in `Type` mapping the final
      borrowed value to the list of updated values for `owners`. -/
structure LoanEntry where
  id : Nat
  owners : List OwnerId
  curVal : SymVal
  back : SymVal → List SymVal

/-- Symbolic execution state with a concrete `List` local spine and active loans. -/
structure SymState where
  locals : List (Option SymVal)
  loans : List LoanEntry
  nextLoan : Nat

def getLocal (locals : List (Option SymVal)) (idx : Nat) : Option SymVal :=
  match listGet locals idx with
  | some slot => slot
  | none => none

def setLocal (locals : List (Option SymVal)) (idx : Nat) (val : Option SymVal) :
    List (Option SymVal) :=
  listSet locals idx val

def findLoan (loans : List LoanEntry) (lid : Nat) : Option LoanEntry :=
  match loans with
  | [] => none
  | l :: ls =>
    match Nat.beq l.id lid with
    | true => some l
    | false => findLoan ls lid

def updateLoanVal (loans : List LoanEntry) (lid : Nat) (v' : SymVal) : List LoanEntry :=
  match loans with
  | [] => []
  | l :: ls =>
    let l' := match Nat.beq l.id lid with
      | true => { l with curVal := v' }
      | false => l
    l' :: updateLoanVal ls lid v'

def removeLoan (loans : List LoanEntry) (lid : Nat) : List LoanEntry :=
  match loans with
  | [] => []
  | l :: ls =>
    match Nat.beq l.id lid with
    | true => removeLoan ls lid
    | false => l :: removeLoan ls lid

def ownerListContainsLoan (owners : List OwnerId) (lid : Nat) : Bool :=
  match owners with
  | [] => false
  | o :: rest =>
    match o with
    | .loan id =>
      match Nat.beq id lid with
      | true => true
      | false => ownerListContainsLoan rest lid
    | .local_ _ => ownerListContainsLoan rest lid

/-- Check that no remaining active loan lists `.loan lid` among its owners. -/
def hasChildLoan (loans : List LoanEntry) (lid : Nat) : Bool :=
  match loans with
  | [] => false
  | l :: ls =>
    match ownerListContainsLoan l.owners lid with
    | true => true
    | false => hasChildLoan ls lid

/-- Apply a list of `(OwnerId, SymVal)` updates back to `locals` and `loans`. -/
def applyOwnerUpdates (owners : List OwnerId) (vals : List SymVal)
    (locals : List (Option SymVal)) (loans : List LoanEntry) :
    Option (List (Option SymVal) × List LoanEntry) :=
  match owners with
  | [] =>
    match vals with
    | [] => some (locals, loans)
    | _ :: _ => none
  | o :: os =>
    match vals with
    | [] => none
    | v :: vs =>
      match o with
      | .local_ idx => applyOwnerUpdates os vs (setLocal locals idx (some v)) loans
      | .loan parentId => applyOwnerUpdates os vs locals (updateLoanVal loans parentId v)

/-- Single unified `endLoan` rule for all five borrow patterns. -/
def endLoan (lid : Nat) (s : SymState) : Option SymState :=
  match hasChildLoan s.loans lid with
  | true => none
  | false =>
    match findLoan s.loans lid with
    | none => none
    | some entry =>
      let remaining := removeLoan s.loans lid
      match applyOwnerUpdates entry.owners (entry.back entry.curVal) s.locals remaining with
      | none => none
      | some (locals', loans') =>
        some { s with locals := locals', loans := loans' }

/-- Write a new value `v'` through a borrow token `.borrow lid` held in local `refLocal`. -/
def writeThroughBorrow (refLocal : Nat) (v' : SymVal) (s : SymState) : Option SymState :=
  match getLocal s.locals refLocal with
  | none => none
  | some rv =>
    match rv with
    | .borrow lid =>
      match hasChildLoan s.loans lid with
      | true => none
      | false => some { s with loans := updateLoanVal s.loans lid v' }
    | .u8 _ => none
    | .bool _ => none
    | .pair _ _ => none

/-!
### Five Canonical Borrow Patterns Handled by the Single `LoanEntry` + `endLoan` Rule
-/

/-- **Pattern A (Whole-local mutable borrow):** `let r = &mut x; *r = v'; endLoan` -/
def wholeLocalBorrowExample (x v' : Nat) : Option SymVal :=
  let s0 : SymState := {
    locals := [none, some (.u8 x), some (.borrow 0)]
    loans := [{ id := 0, owners := [.local_ 1], curVal := .u8 x, back := fun u => [u] }]
    nextLoan := 1
  }
  match writeThroughBorrow 2 (.u8 v') s0 with
  | none => none
  | some s1 =>
    match endLoan 0 s1 with
    | none => none
    | some s2 => getLocal s2.locals 1

theorem wholeLocalBorrow_rfl (x v' : Nat) :
    wholeLocalBorrowExample x v' = some (.u8 v') :=
  rfl

/-- **Pattern B (Field projection borrow):** `let r = &mut p.1; *r = x; endLoan`
    (Matches `update_second(p: &mut (u8, u8), x: u8)` from `aeneas-pair-returned-update-alpha24`.) -/
def fieldProjBorrowExample (p0 p1 x : Nat) : Option SymVal :=
  let s0 : SymState := {
    locals := [none, some (.pair (.u8 p0) (.u8 p1)), some (.borrow 0)]
    loans := [{
      id := 0
      owners := [.local_ 1]
      curVal := .u8 p1
      back := fun u => [.pair (.u8 p0) u]
    }]
    nextLoan := 1
  }
  match writeThroughBorrow 2 (.u8 x) s0 with
  | none => none
  | some s1 =>
    match endLoan 0 s1 with
    | none => none
    | some s2 => getLocal s2.locals 1

theorem fieldProjBorrow_rfl (p0 p1 x : Nat) :
    fieldProjBorrowExample p0 p1 x = some (.pair (.u8 p0) (.u8 x)) :=
  rfl

/-- **Pattern C (Nested reborrow of a field):**
    `let r1 = &mut p; let r2 = &mut (*r1).1; *r2 = x; endLoan r2; endLoan r1`
    Here `r2` (loan 1) has `owners := [.loan 0]` and `r1` (loan 0) has
    `owners := [.local_ 1]`. Ending loan 1 updates loan 0's `curVal` via `r2.back`,
    and ending loan 0 writes the updated pair back to `.local_ 1`—all without
    needing `abs_level` sub-abstractions. -/
def nestedReborrowExample (p0 p1 x : Nat) : Option SymVal :=
  let s0 : SymState := {
    locals := [none, some (.pair (.u8 p0) (.u8 p1)), some (.borrow 0), some (.borrow 1)]
    loans := [
      { id := 0
        owners := [.local_ 1]
        curVal := .pair (.u8 p0) (.u8 p1)
        back := fun u => [u] },
      { id := 1
        owners := [.loan 0]
        curVal := .u8 p1
        back := fun u => [.pair (.u8 p0) u] }
    ]
    nextLoan := 2
  }
  match writeThroughBorrow 3 (.u8 x) s0 with
  | none => none
  | some s1 =>
    match endLoan 1 s1 with
    | none => none
    | some s2 =>
      match endLoan 0 s2 with
      | none => none
      | some s3 => getLocal s3.locals 1

theorem nestedReborrow_rfl (p0 p1 x : Nat) :
    nestedReborrowExample p0 p1 x = some (.pair (.u8 p0) (.u8 x)) :=
  rfl

/-- Ending parent loan `0` before child reborrow `1` is rejected (`none`) by the
    priority check `hasChildLoan`. -/
theorem nestedReborrow_out_of_order_rejected (p0 p1 : Nat) :
    let s0 : SymState := {
      locals := [none, some (.pair (.u8 p0) (.u8 p1)), some (.borrow 0), some (.borrow 1)]
      loans := [
        { id := 0, owners := [.local_ 1], curVal := .pair (.u8 p0) (.u8 p1), back := fun u => [u] },
        { id := 1, owners := [.loan 0], curVal := .u8 p1, back := fun u => [.pair (.u8 p0) u] }
      ]
      nextLoan := 2
    }
    endLoan 0 s0 = none :=
  rfl

/-- **Pattern D & E (Branch-joined / `choose_mut` multi-owner borrow):**
    `let r = if b { &mut x } else { &mut y }; *r = z; endLoan`
    The joined loan owns `[.local_ 1, .local_ 2]` with backward lens
    `fun u => [if b then u else .u8 x, if b then .u8 y else u]`. -/
def branchJoinedBorrowExample (b : Bool) (x y z : Nat) : Option (SymVal × SymVal) :=
  let s0 : SymState := {
    locals := [none, some (.u8 x), some (.u8 y), some (.borrow 0)]
    loans := [{
      id := 0
      owners := [.local_ 1, .local_ 2]
      curVal := .u8 (if b then x else y)
      back := fun u => [if b then u else .u8 x, if b then .u8 y else u]
    }]
    nextLoan := 1
  }
  match writeThroughBorrow 3 (.u8 z) s0 with
  | none => none
  | some s1 =>
    match endLoan 0 s1 with
    | none => none
    | some s2 =>
      match getLocal s2.locals 1 with
      | none => none
      | some vx =>
        match getLocal s2.locals 2 with
        | none => none
        | some vy => some (vx, vy)

theorem branchJoinedBorrow_rfl (b : Bool) (x y z : Nat) :
    branchJoinedBorrowExample b x y z =
      some (if b then .u8 z else .u8 x, if b then .u8 y else .u8 z) :=
  rfl

/-!
## 4. Positional `TransPlan`, `evalSym`, and Universal Hint-Independent Soundness (Findings 1, 2 & 5)
-/

inductive MirOperand where
  | copy (src : Nat)
  | move (src : Nat)
  | constVal (v : SymVal)
  deriving DecidableEq, Repr

inductive MirStmt where
  | assign (dst : Nat) (op : MirOperand)
  | storageLive (loc : Nat)
  | storageDead (loc : Nat)
  | nop
  deriving DecidableEq, Repr

inductive MirTerminator where
  | return_
  | goto (target : Nat)
  | switchBool (discr : MirOperand) (trueTarget falseTarget : Nat)
  deriving DecidableEq, Repr

structure MirBlock where
  stmts : List MirStmt
  terminator : MirTerminator
  deriving DecidableEq, Repr

structure MirBody where
  blocks : List MirBlock
  deriving DecidableEq, Repr

/-- Positional translation plan generated by untrusted `computePlan`: guides
    `evalSym` directly over `MirBody` basic-block indices without an intermediate
    `StructuredMir` AST. -/
inductive TransPlan where
  | stepGoto (blockIdx : Nat) (next : TransPlan)
  | branchBool (blockIdx : Nat) (trueBlk falseBlk : Nat)
      (joinBlockIdx : Nat) (afterJoin : TransPlan)
  | returnBlock (blockIdx : Nat)
  | fail
  deriving Repr

def evalMirOperand (locals : List (Option SymVal)) (op : MirOperand) :
    Option (SymVal × List (Option SymVal)) :=
  match op with
  | .copy src =>
    match getLocal locals src with
    | some v => some (v, locals)
    | none => none
  | .move src =>
    match getLocal locals src with
    | some v => some (v, setLocal locals src none)
    | none => none
  | .constVal v => some (v, locals)

def evalMirStmts (locals : List (Option SymVal)) (stmts : List MirStmt) :
    Option (List (Option SymVal)) :=
  match stmts with
  | [] => some locals
  | stmt :: rest =>
    match stmt with
    | .assign dst op =>
      match evalMirOperand locals op with
      | some (v, locals') => evalMirStmts (setLocal locals' dst (some v)) rest
      | none => none
    | .storageLive loc => evalMirStmts (setLocal locals loc none) rest
    | .storageDead loc => evalMirStmts (setLocal locals loc none) rest
    | .nop => evalMirStmts locals rest

/-- Merge a single local slot across `true` and `false` branch outcomes, pushing
    `if b then ... else ...` inside `.u8` / `.bool` payloads when both sides
    have matching scalar tags. -/
def zipBranchSlot (b : Bool) (tSlot fSlot : Option SymVal) : Option SymVal :=
  match tSlot with
  | none =>
    match fSlot with
    | none => none
    | some _ => if b then tSlot else fSlot
  | some vt =>
    match fSlot with
    | none => if b then tSlot else fSlot
    | some vf =>
      match vt with
      | .u8 nt =>
        match vf with
        | .u8 nf => some (.u8 (if b then nt else nf))
        | .bool _ => if b then tSlot else fSlot
        | .pair _ _ => if b then tSlot else fSlot
        | .borrow _ => if b then tSlot else fSlot
      | .bool bt =>
        match vf with
        | .bool bf => some (.bool (if b then bt else bf))
        | .u8 _ => if b then tSlot else fSlot
        | .pair _ _ => if b then tSlot else fSlot
        | .borrow _ => if b then tSlot else fSlot
      | .pair _ _ => if b then tSlot else fSlot
      | .borrow _ => if b then tSlot else fSlot

theorem zipBranchSlot_eq_ite (b : Bool) (tSlot fSlot : Option SymVal) :
    zipBranchSlot b tSlot fSlot = (if b then tSlot else fSlot) := by
  cases b <;> cases tSlot with
  | none => cases fSlot <;> rfl
  | some vt =>
    cases vt <;> cases fSlot with
    | none => rfl
    | some vf => cases vf <;> rfl

/-- Rebuild a concrete `List` local spine outside a branch join by zipping the
    `true` and `false` branch local lists slot-by-slot. -/
def zipBranchLocals (b : Bool)
    (tLocals fLocals : List (Option SymVal)) : Option (List (Option SymVal)) :=
  match tLocals with
  | [] =>
    match fLocals with
    | [] => some []
    | _ :: _ => none
  | tSlot :: tRest =>
    match fLocals with
    | [] => none
    | fSlot :: fRest =>
      match zipBranchLocals b tRest fRest with
      | some rest => some (zipBranchSlot b tSlot fSlot :: rest)
      | none => none

theorem zipBranchLocals_eq_ite (b : Bool) :
    ∀ {tLocals fLocals joined : List (Option SymVal)},
      zipBranchLocals b tLocals fLocals = some joined →
      joined = (if b then tLocals else fLocals)
  | [], [], _, h => by
    injection h with hEq
    cases b <;> exact hEq.symm
  | tSlot :: tRest, fSlot :: fRest, joined, h => by
    unfold zipBranchLocals at h
    dsimp only at h
    cases hRec : zipBranchLocals b tRest fRest with
    | none =>
      rw [hRec] at h
      cases h
    | some rest =>
      rw [hRec] at h
      injection h with hEq
      have ih := zipBranchLocals_eq_ite b hRec
      rw [← hEq, zipBranchSlot_eq_ite, ih]
      cases b <;> rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-- Execute a single straight-line block to its terminator. -/
def execBlockToLocals (body : MirBody) (blockIdx : Nat)
    (locals : List (Option SymVal)) : Option (List (Option SymVal) × MirTerminator) :=
  match listGet body.blocks blockIdx with
  | none => none
  | some bb =>
    match evalMirStmts locals bb.stmts with
    | none => none
    | some locals' => some (locals', bb.terminator)

/-- Defensive plan-guided symbolic evaluator `evalSym`: checks every plan step
    against `(body, curBlk)` and returns `.fail` on any mismatch.
    Compiled via structural recursion on `plan` (`TransPlan.rec`) so that
    specialization on open symbolic inputs reduces definitionally by `rfl`. -/
def evalSym (plan : TransPlan) (body : MirBody) (curBlk : Nat)
    (locals : List (Option SymVal)) : AeneasRes SymVal :=
  match plan with
  | .fail => .fail
  | .returnBlock blk =>
    match Nat.beq curBlk blk with
    | false => .fail
    | true =>
      match execBlockToLocals body curBlk locals with
      | none => .fail
      | some (locals', term) =>
        match term with
        | .return_ =>
          match getLocal locals' 0 with
          | some ret => .ok ret
          | none => .fail
        | .goto _ => .fail
        | .switchBool _ _ _ => .fail
  | .stepGoto blk next =>
    match Nat.beq curBlk blk with
    | false => .fail
    | true =>
      match execBlockToLocals body curBlk locals with
      | none => .fail
      | some (locals', term) =>
        match term with
        | .goto target => evalSym next body target locals'
        | .return_ => .fail
        | .switchBool _ _ _ => .fail
  | .branchBool blk trueBlk falseBlk joinBlk afterJoin =>
    match Nat.beq curBlk blk with
    | false => .fail
    | true =>
      match execBlockToLocals body curBlk locals with
      | none => .fail
      | some (localsAfterHeader, term) =>
        match term with
        | .return_ => .fail
        | .goto _ => .fail
        | .switchBool discrOp trueTarget falseTarget =>
          match Nat.beq trueTarget trueBlk with
          | false => .fail
          | true =>
            match Nat.beq falseTarget falseBlk with
            | false => .fail
            | true =>
              match evalMirOperand localsAfterHeader discrOp with
              | none => .fail
              | some (discrVal, localsBranchEntry) =>
                match discrVal with
                | .u8 _ => .fail
                | .pair _ _ => .fail
                | .borrow _ => .fail
                | .bool b =>
                  match execBlockToLocals body trueTarget localsBranchEntry with
                  | none => .fail
                  | some (tLocals, tTerm) =>
                    match tTerm with
                    | .return_ => .fail
                    | .switchBool _ _ _ => .fail
                    | .goto tNext =>
                      match execBlockToLocals body falseTarget localsBranchEntry with
                      | none => .fail
                      | some (fLocals, fTerm) =>
                        match fTerm with
                        | .return_ => .fail
                        | .switchBool _ _ _ => .fail
                        | .goto fNext =>
                          match Nat.beq tNext joinBlk with
                          | false => .fail
                          | true =>
                            match Nat.beq fNext joinBlk with
                            | false => .fail
                            | true =>
                              match zipBranchLocals b tLocals fLocals with
                              | some joined => evalSym afterJoin body joinBlk joined
                              | none => .fail
termination_by structural plan

/-- The actual 4-block unstructured CFG for `choose(b: bool, x: u8, y: u8) -> u8`
    from `charon-fork-storage-certificate-alpha24`:
    - `bb0`: `StorageLive(_4); _4 = copy _1; switchInt(move _4) -> [true: bb1, false: bb2]`
    - `bb1`: `_0 = copy _2; goto -> bb3`
    - `bb2`: `_0 = copy _3; goto -> bb3`
    - `bb3`: `StorageDead(_4); return` -/
def chooseMirBody : MirBody where
  blocks := [
    { stmts := [.storageLive 4, .assign 4 (.copy 1)]
      terminator := .switchBool (.move 4) 1 2 },
    { stmts := [.assign 0 (.copy 2)]
      terminator := .goto 3 },
    { stmts := [.assign 0 (.copy 3)]
      terminator := .goto 3 },
    { stmts := [.storageDead 4]
      terminator := .return_ }
  ]

/-- Untrusted heuristic plan for `chooseMirBody`. -/
def choosePlan : TransPlan :=
  .branchBool 0 1 2 3 (.returnBlock 3)

def initChooseLocals (b : Bool) (x y : Nat) : List (Option SymVal) :=
  [none, some (.bool b), some (.u8 x), some (.u8 y), none]

/-- **First Futamura Projection Theorem**: specializing `evalSym choosePlan chooseMirBody 0`
    on symbolic inputs `b`, `x`, `y` reduces *definitionally by `rfl`* in Lean's
    kernel to `.ok (.u8 (if b then x else y))` with **zero axioms**! -/
theorem choose_futamura_rfl (b : Bool) (x y : Nat) :
    evalSym choosePlan chooseMirBody 0 (initChooseLocals b x y) =
      .ok (.u8 (if b then x else y)) :=
  rfl

/-- Concrete reference evaluator for `MirBody` with fuel `fuel : Nat`. -/
def evalMirConcrete (body : MirBody) (blk : Nat)
    (locals : List (Option SymVal)) : Nat → AeneasRes SymVal
  | 0 => .div
  | fuel + 1 =>
    match execBlockToLocals body blk locals with
    | none => .fail
    | some (locals', term) =>
      match term with
      | .return_ =>
        match getLocal locals' 0 with
        | some ret => .ok ret
        | none => .fail
      | .goto target => evalMirConcrete body target locals' fuel
      | .switchBool discrOp trueTarget falseTarget =>
        match evalMirOperand locals' discrOp with
        | some (discrVal, locals'') =>
          match discrVal with
          | .bool b =>
            evalMirConcrete body (match b with | true => trueTarget | false => falseTarget) locals'' fuel
          | _ => .fail
        | none => .fail

/-- **Universal Defensive Translator Soundness Theorem (`evalSym_sound`)**:
    For **every** `plan : TransPlan`, **every** `body : MirBody`, **every**
    `curBlk : Nat`, **every** `locals`, and **every** `fuel : Nat`,
    `evalSym plan body curBlk locals` is a sound abstraction of
    `evalMirConcrete body curBlk locals fuel`! -/
theorem evalSym_sound (plan : TransPlan) (body : MirBody) :
    ∀ (curBlk : Nat) (locals : List (Option SymVal)) (fuel : Nat),
      embedRes (evalMirConcrete body curBlk locals fuel) ⊑
        embedRes (evalSym plan body curBlk locals) := by
  induction plan with
  | fail =>
    intro curBlk locals fuel
    exact embedRes_fail_top _
  | returnBlock blk =>
    intro curBlk locals fuel
    unfold evalSym
    cases hBlk : Nat.beq curBlk blk with
    | false => exact embedRes_fail_top _
    | true =>
      dsimp only
      cases fuel with
      | zero => exact embedRes_div_le_any _
      | succ k =>
        unfold evalMirConcrete
        cases execBlockToLocals body curBlk locals with
        | none => exact embedRes_fail_top _
        | some pair =>
          cases pair with
          | mk locals' term =>
            dsimp only
            cases term with
            | return_ =>
              dsimp only
              cases getLocal locals' 0 with
              | none => exact embedRes_fail_top _
              | some ret => exact Partial.refines_refl _
            | goto _ => exact embedRes_fail_top _
            | switchBool _ _ _ => exact embedRes_fail_top _
  | stepGoto blk next ih =>
    intro curBlk locals fuel
    unfold evalSym
    cases hBlk : Nat.beq curBlk blk with
    | false => exact embedRes_fail_top _
    | true =>
      dsimp only
      cases fuel with
      | zero => exact embedRes_div_le_any _
      | succ k =>
        unfold evalMirConcrete
        cases execBlockToLocals body curBlk locals with
        | none => exact embedRes_fail_top _
        | some pair =>
          cases pair with
          | mk locals' term =>
            dsimp only
            cases term with
            | return_ => exact embedRes_fail_top _
            | goto target =>
              dsimp only
              exact ih target locals' k
            | switchBool _ _ _ => exact embedRes_fail_top _
  | branchBool blk trueBlk falseBlk joinBlk afterJoin ih =>
    intro curBlk locals fuel
    unfold evalSym
    cases hBlk : Nat.beq curBlk blk with
    | false => exact embedRes_fail_top _
    | true =>
      dsimp only
      cases fuel with
      | zero => exact embedRes_div_le_any _
      | succ k =>
        unfold evalMirConcrete
        cases execBlockToLocals body curBlk locals with
        | none => exact embedRes_fail_top _
        | some pair =>
          cases pair with
          | mk localsAfterHeader term =>
            dsimp only
            cases term with
            | return_ => exact embedRes_fail_top _
            | goto _ => exact embedRes_fail_top _
            | switchBool discrOp trueTarget falseTarget =>
              dsimp only
              cases Nat.beq trueTarget trueBlk with
              | false => exact embedRes_fail_top _
              | true =>
                dsimp only
                cases Nat.beq falseTarget falseBlk with
                | false => exact embedRes_fail_top _
                | true =>
                  dsimp only
                  cases evalMirOperand localsAfterHeader discrOp with
                  | none => exact embedRes_fail_top _
                  | some opPair =>
                    cases opPair with
                    | mk discrVal localsBranchEntry =>
                      dsimp only
                      cases discrVal with
                      | u8 _ => exact embedRes_fail_top _
                      | pair _ _ => exact embedRes_fail_top _
                      | borrow _ => exact embedRes_fail_top _
                      | bool b =>
                        dsimp only
                        cases hTrue : execBlockToLocals body trueTarget localsBranchEntry with
                        | none => exact embedRes_fail_top _
                        | some tPair =>
                          cases tPair with
                          | mk tLocals tTerm =>
                            dsimp only
                            cases tTerm with
                            | return_ => exact embedRes_fail_top _
                            | switchBool _ _ _ => exact embedRes_fail_top _
                            | goto tNext =>
                              dsimp only
                              cases hFalse : execBlockToLocals body falseTarget localsBranchEntry with
                              | none => exact embedRes_fail_top _
                              | some fPair =>
                                cases fPair with
                                | mk fLocals fTerm =>
                                  dsimp only
                                  cases fTerm with
                                  | return_ => exact embedRes_fail_top _
                                  | switchBool _ _ _ => exact embedRes_fail_top _
                                  | goto fNext =>
                                    dsimp only
                                    cases hTJoin : Nat.beq tNext joinBlk with
                                    | false => exact embedRes_fail_top _
                                    | true =>
                                      dsimp only
                                      cases hFJoin : Nat.beq fNext joinBlk with
                                      | false => exact embedRes_fail_top _
                                      | true =>
                                        dsimp only
                                        cases hZip : zipBranchLocals b tLocals fLocals with
                                        | none => exact embedRes_fail_top _
                                        | some joined =>
                                          dsimp only
                                          have hJoinEq := zipBranchLocals_eq_ite b hZip
                                          have hTNextEq : tNext = joinBlk := Nat.eq_of_beq_eq_true hTJoin
                                          have hFNextEq : fNext = joinBlk := Nat.eq_of_beq_eq_true hFJoin
                                          cases k with
                                          | zero => exact embedRes_div_le_any _
                                          | succ k2 =>
                                            cases b with
                                            | true =>
                                              dsimp only
                                              unfold evalMirConcrete
                                              rw [hTrue]
                                              dsimp only
                                              have hJoinT : joined = tLocals := hJoinEq
                                              rw [hTNextEq, hJoinT]
                                              exact ih joinBlk tLocals k2
                                            | false =>
                                              dsimp only
                                              unfold evalMirConcrete
                                              rw [hFalse]
                                              dsimp only
                                              have hJoinF : joined = fLocals := hJoinEq
                                              rw [hFNextEq, hJoinF]
                                              exact ih joinBlk fLocals k2

/-- **Zero-Obligation Heuristic Corollary (`computePlan_sound`)**:
    For *any* untrusted heuristic analyzer `computePlan : MirBody → TransPlan`
    (treated here as an arbitrary universally quantified function!),
    `evalSym (computePlan body) body` is unconditionally sound. -/
theorem computePlan_sound (computePlan : MirBody → TransPlan)
    (body : MirBody) (locals : List (Option SymVal)) (fuel : Nat) :
    embedRes (evalMirConcrete body 0 locals fuel) ⊑
      embedRes (evalSym (computePlan body) body 0 locals) :=
  evalSym_sound (computePlan body) body 0 locals fuel

/-!
## 5. Spatial Disjointness, `OwnLoc` Framing, and Concrete-to-Symbolic Simulation (Finding 6)
-/

abbrev Timestamp := Nat
abbrev View := Nat → Timestamp

def View.bot : View := fun _ => 0

def View.bump (v : View) (loc : Nat) (ts : Timestamp) : View :=
  fun l =>
    match Nat.beq l loc with
    | true =>
      match Nat.ble (v l) ts with
      | true => ts
      | false => v l
    | false => v l

/-- Operational memory state matching `Trusted.MemState` in `Trusted/Memory.lean`. -/
structure MemState where
  curView : View
  naVal : Nat → Option SymVal
  naWriteTs : Nat → Timestamp
  naReadTs : Nat → Timestamp

def MemState.readNA (m : MemState) (loc : Nat) : Option (SymVal × MemState) :=
  match Nat.ble (m.naWriteTs loc) (m.curView loc) with
  | true =>
    match m.naVal loc with
    | some v =>
      some (v, { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) })
    | none => none
  | false => none

def MemState.writeNA (m : MemState) (loc : Nat) (v : SymVal) : Option MemState :=
  match Nat.ble (m.naWriteTs loc) (m.curView loc),
        Nat.ble (m.naReadTs loc) (m.curView loc) with
  | true, true =>
    let nextTs := m.curView loc + 1
    some { m with
      curView := View.bump m.curView loc nextTs
      naVal := fun l => match Nat.beq l loc with | true => some v | false => m.naVal l
      naWriteTs := View.bump m.naWriteTs loc nextTs
      naReadTs := View.bump m.naReadTs loc nextTs }
  | _, _ => none

/-- Non-atomic ownership predicate matching `Anneal.OwnLoc` in `theory/Anneal/MirLemmas.lean`. -/
def OwnLoc (m : MemState) (loc : Nat) (v : SymVal) : Prop :=
  m.naVal loc = some v ∧
  Nat.ble (m.naWriteTs loc) (m.curView loc) = true ∧
  Nat.ble (m.naReadTs loc) (m.curView loc) = true

/-- Deterministic non-atomic write under `OwnLoc`: `writeNA` always succeeds and
    establishes `OwnLoc m' loc v'`. -/
theorem OwnLoc.writeNA_self {m : MemState} {loc : Nat} {v v' : SymVal}
    (hOwn : OwnLoc m loc v) :
    ∃ m', m.writeNA loc v' = some m' ∧ OwnLoc m' loc v' := by
  unfold MemState.writeNA
  rw [hOwn.2.1, hOwn.2.2]
  refine ⟨_, rfl, ?_⟩
  have hbeq : Nat.beq loc loc = true := Nat.beq_refl loc
  have hle : Nat.ble (m.curView loc) (m.curView loc + 1) = true :=
    Nat.ble_eq_true_of_le (Nat.le_succ _)
  have hleW : Nat.ble (m.naWriteTs loc) (m.curView loc + 1) = true :=
    Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true hOwn.2.1) (Nat.le_succ _))
  have hleR : Nat.ble (m.naReadTs loc) (m.curView loc + 1) = true :=
    Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true hOwn.2.2) (Nat.le_succ _))
  refine ⟨?_, ?_, ?_⟩
  · change (match Nat.beq loc loc with | true => some v' | false => m.naVal loc) = some v'
    rw [hbeq]
  · change Nat.ble (View.bump m.naWriteTs loc (m.curView loc + 1) loc)
      (View.bump m.curView loc (m.curView loc + 1) loc) = true
    unfold View.bump
    rw [hbeq, hle, hleW]
    exact Nat.ble_self_eq_true _
  · change Nat.ble (View.bump m.naReadTs loc (m.curView loc + 1) loc)
      (View.bump m.curView loc (m.curView loc + 1) loc) = true
    unfold View.bump
    rw [hbeq, hle, hleR]
    exact Nat.ble_self_eq_true _

theorem nat_beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hbeq : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hbeq))

/-- **Spatial Frame Theorem for `OwnLoc` (`OwnLoc.writeNA_frame`)**:
    Writing `v'` to `loc₁` preserves `OwnLoc` at every disjoint location
    `loc₂ ≠ loc₁`. -/
theorem OwnLoc.writeNA_frame {m m' : MemState} {loc₁ loc₂ : Nat} {v₁ v' v₂ : SymVal}
    (hOwn₁ : OwnLoc m loc₁ v₁)
    (hOwn₂ : OwnLoc m loc₂ v₂)
    (hDisj : loc₂ ≠ loc₁)
    (hWrite : m.writeNA loc₁ v' = some m') :
    OwnLoc m' loc₂ v₂ := by
  unfold MemState.writeNA at hWrite
  rw [hOwn₁.2.1, hOwn₁.2.2] at hWrite
  injection hWrite with hm'
  subst hm'
  have hneq : Nat.beq loc₂ loc₁ = false := nat_beq_eq_false_of_ne hDisj
  refine ⟨?_, ?_, ?_⟩
  · change (match Nat.beq loc₂ loc₁ with | true => some v' | false => m.naVal loc₂) = some v₂
    rw [hneq]
    exact hOwn₂.1
  · change Nat.ble (View.bump m.naWriteTs loc₁ (m.curView loc₁ + 1) loc₂)
      (View.bump m.curView loc₁ (m.curView loc₁ + 1) loc₂) = true
    unfold View.bump
    rw [hneq]
    exact hOwn₂.2.1
  · change Nat.ble (View.bump m.naReadTs loc₁ (m.curView loc₁ + 1) loc₂)
      (View.bump m.curView loc₁ (m.curView loc₁ + 1) loc₂) = true
    unfold View.bump
    rw [hneq]
    exact hOwn₂.2.2

/-- **Concrete Write + Symbolic `endLoan` Commutation Theorem**:
    1. A concrete write `m.writeNA 10 v'` updates `m` to `m'` with `OwnLoc m' 10 v'`
       while framing every disjoint location `loc₂ ≠ 10`.
    2. Symbolic `writeThroughBorrow` + `endLoan` in `SymState` requires **zero**
       additional concrete instructions at borrow end and restores
       `getLocal sAfterEnd.locals 1` to `some v'`, matching `m'.naVal 10`. -/
theorem concrete_write_and_endLoan_commute
    (m : MemState) (loc₂ : Nat) (v₀ v' v₂ : SymVal)
    (hOwn₁ : OwnLoc m 10 v₀)
    (hOwn₂ : OwnLoc m loc₂ v₂)
    (hDisj : loc₂ ≠ 10) :
    ∃ m' sAfterEnd,
      m.writeNA 10 v' = some m' ∧
      OwnLoc m' 10 v' ∧
      OwnLoc m' loc₂ v₂ ∧
      (let s0 : SymState := {
          locals := [none, some v₀, some (.borrow 0)]
          loans := [{ id := 0, owners := [.local_ 1], curVal := v₀, back := fun u => [u] }]
          nextLoan := 1
        }
        match writeThroughBorrow 2 v' s0 with
        | none => none
        | some s1 => endLoan 0 s1) = some sAfterEnd ∧
      getLocal sAfterEnd.locals 1 = m'.naVal 10 := by
  obtain ⟨m', hWrite, hOwn₁'⟩ := OwnLoc.writeNA_self (v' := v') hOwn₁
  have hOwn₂' := OwnLoc.writeNA_frame hOwn₁ hOwn₂ hDisj hWrite
  refine ⟨m', {
    locals := [none, some v', some (.borrow 0)]
    loans := []
    nextLoan := 1
  }, hWrite, hOwn₁', hOwn₂', rfl, ?_⟩
  exact hOwn₁'.1.symm

#print axioms AeneasRes.bind_ok
#print axioms spinePreservingJoin_lookup0
#print axioms spinePreservingJoin_lookup1
#print axioms spinePreservingJoin_eq_naive
#print axioms ub_top
#print axioms not_ub_le_pure
#print axioms embedRes_fail_top
#print axioms embedRes_fail_rejected_by_pure
#print axioms embedRes_fail_accepted_outside_pre
#print axioms embedRes_div_le_any
#print axioms wholeLocalBorrow_rfl
#print axioms fieldProjBorrow_rfl
#print axioms nestedReborrow_rfl
#print axioms nestedReborrow_out_of_order_rejected
#print axioms branchJoinedBorrow_rfl
#print axioms choose_futamura_rfl
#print axioms evalSym_sound
#print axioms computePlan_sound
#print axioms OwnLoc.writeNA_self
#print axioms OwnLoc.writeNA_frame
#print axioms concrete_write_and_endLoan_commute

end ShallowPlanPrototype
