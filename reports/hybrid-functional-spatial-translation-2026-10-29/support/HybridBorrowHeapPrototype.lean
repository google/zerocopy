/-
  HybridBorrowHeapPrototype.lean
  Self-contained Lean 4 (v4.34.1) mechanization for:
  "Hybrid Functional and Spatial Translation for Unsafe Rust, Interior
   Mutability, and Weak-Memory Atomics"

  What is mechanized here (zero `sorry`, zero `Classical.choice`, zero non-standard axioms):
  1. Layer 1A / Layer 1B Refinement & Weak-Memory Foundations (`Partial`, `Language`,
     `Abstracts`, `StepResult`, `ReachesPrefix`, `MemState`, `OwnLoc`, `ReadOwnLoc`,
     `ReleaseGuarded`, `visibleAtomicMsgs`, `applyAtomicLoad`), plus the core framing
     lemmas (`OwnLoc.readNA_preserves`, `OwnLoc.afterWriteNA_self`,
     `OwnLoc.afterWriteNA_other`, `OwnLoc.preserved_by_atomic_load`,
     `ReadOwnLoc.preserved_by_atomic_load`, `OwnLoc.transfer_acquire`).
  2. Core MIR Language with Safe Borrows (`&usize`, `&mut usize`), Unsafe Raw
     Pointers (`*const usize`, `*mut usize`), Raw-Pointer-to-Reference Reborrows
     (`&mut *raw_p`), and Weak-Memory Atomics (`AtomicUsize::load` with `Relaxed`
     and `Acquire` orderings).
  3. Unified Spatial Simulation Relation (`StateRel` = `LocalRel` + `LoanRel` +
     `RawRel` + `AtomRel`): proves that functional `&mut` loans (`LoanEntry`),
     shared references (`ReadOwnLoc`), owned raw pointers (`rawOwn`),
     release-guarded raw pointers (`relOwn`), and weak-memory atomics coexist in a
     single `MemState` with automatic disjointness framing.
  4. Technique A (`SymTree` — Hybrid Interaction Trees / Free Monad Partial
     Evaluation) & Technique B (`symWP` — Omnisemantics Predicate Transformer):
     `evalSymTree` reduces all safe local, control-flow, and `&mut` borrow
     operations by kernel `rfl` (First Futamura Projection) into a residual
     `SymTree RetSummary`, while `symWP` computes pure first-order verification
     conditions over `rawOwn`, `relOwn`, and `atomView`.
  5. Technique C (Untrusted `TransPlan` Hints for Raw-Pointer-to-Loan Reborrowing
     `reborrowRaw` / `endRawLoan`): promotes a raw pointer backed by `rawOwn` into
     a temporary tracked `LoanEntry` (`promoteRaw`) so safe borrow mutations run
     by pure `rfl`, then releases the loan back to `rawOwn` (`releaseRaw`).
  6. Universal Hint-Independent Soundness (`evalSymTree_sound`) and End-to-End
     Verified Examples:
     - Example 1 (`atomicMaxAssignBody`): safe `&mut usize` + `AtomicUsize::load(Relaxed)`
       + conditional branch + `&mut` write (`rfl` reduction to 1-node `SymTree`).
     - Example 2 (`rawAddAndZeroBody`): safe `&mut usize` + `*mut usize` raw read
       and write with automatic `LoanRel` framing (`rfl` reduction to 2-node `SymTree`).
     - Example 3 (`reborrowRawMaxAssignBody`): Technique C `&mut *raw_p` reborrow
       promoted via `TransPlan.reborrowRaw`, mutated across a branch by `rfl`, and
       released via `TransPlan.endRawLoan`.
     - Example 4 (`acquireReadRawBody`): C++20 Release/Acquire message-passing
       synchronization (`AtomicUsize::load(Acquire)` guarding a conditional
       `*const usize` dereference via `OwnLoc.transfer_acquire`).
-/

namespace HybridBorrowHeapPrototype

/-!
## 1. Refinement Lattice (`Partial`, `Language`, `Abstracts`) & Small-Step Prefixes (`StepResult`, `ReachesPrefix`)
-/

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h1 h2 hp := h2 (h1 hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] : Preorder (A → B) where
  le f g := ∀ x, f x ≤ g x
  le_refl f x := Preorder.le_refl (f x)
  le_trans h1 h2 x := Preorder.le_trans (h1 x) (h2 x)

def Monotone {A : Type u} {B : Type v} [Preorder A] [Preorder B] (f : A → B) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

namespace Partial

instance instPreorderPartial (B : Type u) [Preorder B] : Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

def pure {B : Type u} (x : B) : Partial B where
  defined := True
  val := fun _ => x

def ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

def map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) : Partial B₂ where
  defined := p.defined
  val := fun h => f (p.val h)

theorem monotone_map {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hle h₂
  have ⟨h₁, hval⟩ := hle h₂
  exact ⟨h₁, hf hval⟩

end Partial

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Query → Partial (Out → Prop)

namespace Language

abbrev Behavior (L : Language) : Type :=
  L.Query → Partial (L.Out → Prop)

def Spec (L : Language) (R : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => Partial.pure (R q)

def WellFormed (L : Language) : L.Behavior :=
  L.Spec (fun _ _ => True)

end Language

def Abstracts (L_hi L_lo : Language) (π : L_hi.Behavior → L_lo.Behavior)
    (p_hi : L_hi.Prog) (p_lo : L_lo.Prog) : Prop :=
  Monotone π ∧ L_lo.sem p_lo ≤ π (L_hi.sem p_hi)

inductive ChoiceKind where
  | demonic
  | angelic

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive FailureKind where
  | ub
  | contractViolation

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State) (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

/-!
## 2. Weak-Memory View Model, Non-Atomic Ownership (`OwnLoc`, `ReadOwnLoc`, `ReleaseGuarded`), and Framing Lemmas
-/

inductive AtomicOrdering where
  | relaxed
  | acquire
  deriving DecidableEq, Repr

inductive MirVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | refMutLoc (loc : Nat)
  | refSharedLoc (loc : Nat)
  | rawPtrLoc (loc : Nat)
  | atomicLoc (loc : Nat)
  deriving DecidableEq, Repr

abbrev Timestamp := Nat
abbrev View := Nat → Timestamp

instance instPreorderView : Preorder View where
  le v₁ v₂ := ∀ loc, v₁ loc ≤ v₂ loc
  le_refl _ _ := Nat.le_refl _
  le_trans h₁ h₂ loc := Nat.le_trans (h₁ loc) (h₂ loc)

def View.bot : View := fun _ => 0

def View.bump (v : View) (loc : Nat) (ts : Timestamp) : View :=
  fun l =>
    if l == loc then
      if decide (v l ≤ ts) then ts else v l
    else
      v l

def View.join (v₁ v₂ : View) : View :=
  fun loc => if decide (v₁ loc ≤ v₂ loc) then v₂ loc else v₁ loc

theorem View.le_bump_self (v : View) (loc : Nat) (ts : Timestamp) :
    v ≤ View.bump v loc ts := by
  intro l
  unfold View.bump
  cases l == loc with
  | false => exact Nat.le_refl (v l)
  | true =>
    cases h : decide (v l ≤ ts) with
    | true => exact of_decide_eq_true h
    | false => exact Nat.le_refl (v l)

theorem View.ts_le_bump (v : View) (loc : Nat) (ts : Timestamp) :
    ts ≤ View.bump v loc ts loc := by
  unfold View.bump
  have hbeq : (loc == loc) = true := decide_eq_true rfl
  rw [hbeq]
  cases h : decide (v loc ≤ ts) with
  | true => exact Nat.le_refl ts
  | false =>
    have hgt : ts < v loc := Nat.lt_of_not_le (of_decide_eq_false h)
    exact Nat.le_of_lt hgt

theorem View.le_join_left (v₁ v₂ : View) : v₁ ≤ View.join v₁ v₂ := by
  intro loc
  unfold View.join
  cases h : decide (v₁ loc ≤ v₂ loc) with
  | true => exact of_decide_eq_true h
  | false => exact Nat.le_refl (v₁ loc)

theorem View.le_join_right (v₁ v₂ : View) : v₂ ≤ View.join v₁ v₂ := by
  intro loc
  unfold View.join
  cases h : decide (v₁ loc ≤ v₂ loc) with
  | true => exact Nat.le_refl (v₂ loc)
  | false =>
    have hgt : v₂ loc < v₁ loc := Nat.lt_of_not_le (of_decide_eq_false h)
    exact Nat.le_of_lt hgt

structure AtomicMsg where
  loc : Nat
  ts : Timestamp
  bits : Nat
  relView : View

structure MemState where
  curView : View
  atomicMsgs : List AtomicMsg
  naVal : Nat → Option MirVal
  naWriteTs : Nat → Timestamp
  naReadTs : Nat → Timestamp

def MemState.empty : MemState where
  curView := View.bot
  atomicMsgs := []
  naVal := fun _ => none
  naWriteTs := fun _ => 0
  naReadTs := fun _ => 0

def afterReadNA (m : MemState) (loc : Nat) : MemState :=
  { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) }

def MemState.readNA (m : MemState) (loc : Nat) : Option (MirVal × MemState) :=
  if decide (m.naWriteTs loc ≤ m.curView loc) then
    match m.naVal loc with
    | some v => some (v, afterReadNA m loc)
    | none => none
  else
    none

def afterWriteNA (m : MemState) (loc : Nat) (v : MirVal) : MemState :=
  let nextTs := m.curView loc + 1
  { m with
    curView := View.bump m.curView loc nextTs
    naVal := fun l => if l == loc then some v else m.naVal l
    naWriteTs := View.bump m.naWriteTs loc nextTs
    naReadTs := View.bump m.naReadTs loc nextTs }

def MemState.writeNA (m : MemState) (loc : Nat) (v : MirVal) : Option MemState :=
  if decide (m.naWriteTs loc ≤ m.curView loc) && decide (m.naReadTs loc ≤ m.curView loc) then
    some (afterWriteNA m loc v)
  else
    none

def visibleMsgsAt (msgs : List AtomicMsg) (curTs : Timestamp) (loc : Nat) : List AtomicMsg :=
  msgs.foldr
    (fun msg acc =>
      if msg.loc == loc && decide (curTs ≤ msg.ts) then
        msg :: acc
      else
        acc)
    []

def MemState.visibleAtomicMsgs (m : MemState) (loc : Nat) : List AtomicMsg :=
  visibleMsgsAt m.atomicMsgs (m.curView loc) loc

def applyViewLoad (ord : AtomicOrdering) (v : View) (msg : AtomicMsg) : View :=
  let bumped := View.bump v msg.loc msg.ts
  match ord with
  | .relaxed => bumped
  | .acquire => View.join bumped msg.relView

def MemState.applyAtomicLoad (m : MemState) (ord : AtomicOrdering) (msg : AtomicMsg) : MemState :=
  { m with curView := applyViewLoad ord m.curView msg }

theorem applyViewLoad_mono (ord : AtomicOrdering) (v : View) (msg : AtomicMsg) :
    v ≤ applyViewLoad ord v msg := by
  have hbump := View.le_bump_self v msg.loc msg.ts
  cases ord with
  | relaxed => exact hbump
  | acquire =>
    exact Preorder.le_trans hbump (View.le_join_left (View.bump v msg.loc msg.ts) msg.relView)

/-- Exclusive non-atomic ownership of `loc` holding `v`. -/
def OwnLoc (m : MemState) (loc : Nat) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc ∧
  m.naReadTs loc ≤ m.curView loc

/-- Read-only non-atomic ownership of `loc` holding `v`. -/
def ReadOwnLoc (m : MemState) (loc : Nat) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc

/-- Release-guarded non-atomic ownership of `loc` at timestamp `reqTs`: once an
    Acquire load joins a release view `relView` with `reqTs ≤ relView loc`,
    `ReleaseGuarded` upgrades to full `OwnLoc` via `OwnLoc.transfer_acquire`. -/
def ReleaseGuarded (m : MemState) (loc : Nat) (reqTs : Timestamp) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ reqTs ∧
  m.naReadTs loc ≤ reqTs

theorem OwnLoc.toReadOwnLoc {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) : ReadOwnLoc m loc v :=
  ⟨hOwn.1, hOwn.2.1⟩

theorem ReadOwnLoc.readNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hRead : ReadOwnLoc m loc v) :
    m.readNA loc = some (v, afterReadNA m loc) := by
  unfold MemState.readNA
  have h1 : decide (m.naWriteTs loc ≤ m.curView loc) = true := decide_eq_true hRead.2
  rw [h1, hRead.1]
  rfl

theorem OwnLoc.readNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) :
    m.readNA loc = some (v, afterReadNA m loc) :=
  ReadOwnLoc.readNA_eq hOwn.toReadOwnLoc

theorem OwnLoc.readNA_preserves {m : MemState} {loc locRead : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) :
    OwnLoc (afterReadNA m locRead) loc v := by
  refine ⟨hOwn.1, hOwn.2.1, ?_⟩
  dsimp [afterReadNA]
  unfold View.bump
  cases h : (loc == locRead) with
  | false => exact hOwn.2.2
  | true =>
    have heq : loc = locRead := of_decide_eq_true h
    subst heq
    rw [decide_eq_true hOwn.2.2]
    exact Nat.le_refl (m.curView loc)

theorem ReadOwnLoc.readNA_preserves {m : MemState} {loc locRead : Nat} {v : MirVal}
    (hRead : ReadOwnLoc m loc v) :
    ReadOwnLoc (afterReadNA m locRead) loc v :=
  ⟨hRead.1, hRead.2⟩

theorem ReleaseGuarded.afterReadNA_other {m : MemState} {loc locRead : Nat}
    {reqTs : Timestamp} {v : MirVal}
    (hne : loc ≠ locRead) (hRel : ReleaseGuarded m loc reqTs v) :
    ReleaseGuarded (afterReadNA m locRead) loc reqTs v := by
  have hbeq : (loc == locRead) = false := decide_eq_false hne
  refine ⟨hRel.1, hRel.2.1, ?_⟩
  dsimp [afterReadNA]
  unfold View.bump
  rw [hbeq]
  exact hRel.2.2

theorem OwnLoc.writeNA_eq {m : MemState} {loc : Nat} {v vNew : MirVal}
    (hOwn : OwnLoc m loc v) :
    m.writeNA loc vNew = some (afterWriteNA m loc vNew) := by
  unfold MemState.writeNA
  have h1 : decide (m.naWriteTs loc ≤ m.curView loc) = true := decide_eq_true hOwn.2.1
  have h2 : decide (m.naReadTs loc ≤ m.curView loc) = true := decide_eq_true hOwn.2.2
  rw [h1, h2]
  rfl

theorem OwnLoc.afterWriteNA_self {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) (vNew : MirVal) :
    OwnLoc (afterWriteNA m loc vNew) loc vNew := by
  have hbeq : (loc == loc) = true := decide_eq_true rfl
  have hle_cur : m.curView loc ≤ m.curView loc + 1 := Nat.le_succ (m.curView loc)
  have hle_w : m.naWriteTs loc ≤ m.curView loc + 1 := Nat.le_trans hOwn.2.1 hle_cur
  have hle_r : m.naReadTs loc ≤ m.curView loc + 1 := Nat.le_trans hOwn.2.2 hle_cur
  unfold OwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq, decide_eq_true hle_cur, decide_eq_true hle_w, decide_eq_true hle_r]
  exact ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem OwnLoc.afterWriteNA_other {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hne : loc' ≠ loc) (hOwn' : OwnLoc m loc' v') (vNew : MirVal) :
    OwnLoc (afterWriteNA m loc vNew) loc' v' := by
  have hbeq : (loc' == loc) = false := decide_eq_false hne
  unfold OwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq]
  exact hOwn'

theorem ReadOwnLoc.afterWriteNA_other {m : MemState} {loc loc' : Nat} {v' : MirVal}
    (hne : loc' ≠ loc) (hRead' : ReadOwnLoc m loc' v') (vNew : MirVal) :
    ReadOwnLoc (afterWriteNA m loc vNew) loc' v' := by
  have hbeq : (loc' == loc) = false := decide_eq_false hne
  unfold ReadOwnLoc afterWriteNA View.bump
  dsimp
  rw [hbeq]
  exact hRead'

theorem ReleaseGuarded.afterWriteNA_other {m : MemState} {loc loc' : Nat}
    {reqTs : Timestamp} {v' : MirVal}
    (hne : loc' ≠ loc) (hRel' : ReleaseGuarded m loc' reqTs v') (vNew : MirVal) :
    ReleaseGuarded (afterWriteNA m loc vNew) loc' reqTs v' := by
  have hbeq : (loc' == loc) = false := decide_eq_false hne
  unfold ReleaseGuarded afterWriteNA View.bump
  dsimp
  rw [hbeq]
  exact hRel'

theorem OwnLoc.preserved_by_atomic_load {m : MemState} {loc : Nat} {v : MirVal}
    (ord : AtomicOrdering) (msg : AtomicMsg) (hOwn : OwnLoc m loc v) :
    OwnLoc (m.applyAtomicLoad ord msg) loc v := by
  have hmono := applyViewLoad_mono ord m.curView msg loc
  exact ⟨hOwn.1, Nat.le_trans hOwn.2.1 hmono, Nat.le_trans hOwn.2.2 hmono⟩

theorem ReadOwnLoc.preserved_by_atomic_load {m : MemState} {loc : Nat} {v : MirVal}
    (ord : AtomicOrdering) (msg : AtomicMsg) (hRead : ReadOwnLoc m loc v) :
    ReadOwnLoc (m.applyAtomicLoad ord msg) loc v := by
  have hmono := applyViewLoad_mono ord m.curView msg loc
  exact ⟨hRead.1, Nat.le_trans hRead.2 hmono⟩

theorem ReleaseGuarded.preserved_by_atomic_load {m : MemState} {loc : Nat}
    {reqTs : Timestamp} {v : MirVal}
    (ord : AtomicOrdering) (msg : AtomicMsg) (hRel : ReleaseGuarded m loc reqTs v) :
    ReleaseGuarded (m.applyAtomicLoad ord msg) loc reqTs v :=
  hRel

theorem OwnLoc.transfer_acquire {m : MemState} {loc : Nat} {reqTs : Timestamp} {v : MirVal}
    (msg : AtomicMsg)
    (hRel : ReleaseGuarded m loc reqTs v)
    (hSync : reqTs ≤ msg.relView loc) :
    OwnLoc (m.applyAtomicLoad .acquire msg) loc v := by
  have hjoin := View.le_join_right (View.bump m.curView msg.loc msg.ts) msg.relView loc
  have hle : reqTs ≤ (m.applyAtomicLoad .acquire msg).curView loc := Nat.le_trans hSync hjoin
  exact ⟨hRel.1, Nat.le_trans hRel.2.1 hle, Nat.le_trans hRel.2.2 hle⟩
/-!
## 3. Core MIR Language with Safe Borrows, Unsafe Raw Pointers, Pointer Reborrows, and Atomics
-/

inductive Operand where
  | copy (src : Nat)
  | constVal (v : MirVal)
  deriving DecidableEq, Repr

inductive BinOp where
  | add
  | lt
  | eq
  deriving DecidableEq, Repr

inductive Rvalue where
  | use (op : Operand)
  | deref (src : Nat)
  | binaryOp (op : BinOp) (lhs rhs : Operand)
  deriving DecidableEq, Repr

inductive Stmt where
  | assign (dst : Nat) (rv : Rvalue)
  | assignDeref (dst : Nat) (op : Operand)
  | derefRaw (dst : Nat) (ptrLocal : Nat)
  | assignDerefRaw (ptrLocal : Nat) (op : Operand)
  | reborrowRawToMut (dst : Nat) (ptrLocal : Nat)
  | nop
  deriving DecidableEq, Repr

inductive Terminator where
  | return_
  | goto (target : Nat)
  | switchInt (discr : Operand) (falseTarget trueTarget : Nat)
  | callAtomicLoad (dst : Nat) (ptr : Operand) (ord : AtomicOrdering) (target : Nat)
  deriving DecidableEq, Repr

structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator
  deriving DecidableEq, Repr

structure MirBody where
  blocks : List BasicBlock
  deriving DecidableEq, Repr

structure MirState where
  locals : Nat → Option MirVal
  mem : MemState
  block : Nat
  stmtIdx : Nat

structure TermOutcome where
  retVal : MirVal
  mem : MemState

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

def evalOperand (locals : Nat → Option MirVal) (op : Operand) : Option MirVal :=
  match op with
  | .copy src => locals src
  | .constVal v => some v

def evalBinOp (op : BinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.usize (n1 + n2))
    | .lt => some (.bool (decide (n1 < n2)))
    | .eq => some (.bool (decide (n1 = n2)))
  | _, _ => none

def evalMirStmt (s : MirState) (stmt : Stmt) : StepResult MirState Unit TermOutcome :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand s.locals op with
    | some v =>
      .step () { s with
        locals := updateLocal s.locals dst (some v)
        stmtIdx := s.stmtIdx + 1 }
    | none => .failed .ub
  | .assign dst (.deref src) =>
    match s.locals src with
    | some (.refMutLoc loc) =>
      match s.mem.readNA loc with
      | some (v, mem') =>
        .step () { s with
          locals := updateLocal s.locals dst (some v)
          mem := mem'
          stmtIdx := s.stmtIdx + 1 }
      | none => .failed .ub
    | some (.refSharedLoc loc) =>
      match s.mem.readNA loc with
      | some (v, mem') =>
        .step () { s with
          locals := updateLocal s.locals dst (some v)
          mem := mem'
          stmtIdx := s.stmtIdx + 1 }
      | none => .failed .ub
    | _ => .failed .ub
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand s.locals lhs, evalOperand s.locals rhs with
    | some v1, some v2 =>
      match evalBinOp op v1 v2 with
      | some res =>
        .step () { s with
          locals := updateLocal s.locals dst (some res)
          stmtIdx := s.stmtIdx + 1 }
      | none => .failed .ub
    | _, _ => .failed .ub
  | .assignDeref dst op =>
    match evalOperand s.locals op, s.locals dst with
    | some v, some (.refMutLoc loc) =>
      match s.mem.writeNA loc v with
      | some mem' =>
        .step () { s with
          mem := mem'
          stmtIdx := s.stmtIdx + 1 }
      | none => .failed .ub
    | _, _ => .failed .ub
  | .derefRaw dst ptrLocal =>
    match s.locals ptrLocal with
    | some (.rawPtrLoc loc) =>
      match s.mem.readNA loc with
      | some (v, mem') =>
        .step () { s with
          locals := updateLocal s.locals dst (some v)
          mem := mem'
          stmtIdx := s.stmtIdx + 1 }
      | none => .failed .ub
    | _ => .failed .ub
  | .assignDerefRaw ptrLocal op =>
    match evalOperand s.locals op, s.locals ptrLocal with
    | some v, some (.rawPtrLoc loc) =>
      match s.mem.writeNA loc v with
      | some mem' =>
        .step () { s with
          mem := mem'
          stmtIdx := s.stmtIdx + 1 }
      | none => .failed .ub
    | _, _ => .failed .ub
  | .reborrowRawToMut dst ptrLocal =>
    match s.locals ptrLocal with
    | some (.rawPtrLoc loc) =>
      .step () { s with
        locals := updateLocal s.locals dst (some (.refMutLoc loc))
        stmtIdx := s.stmtIdx + 1 }
    | _ => .failed .ub
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

def evalMirTerminator (s : MirState) (term : Terminator) :
    StepResult MirState Unit TermOutcome :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | some retVal => .terminated (.normal { retVal := retVal, mem := s.mem })
    | none => .failed .ub
  | .goto target =>
    .step () { s with block := target, stmtIdx := 0 }
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand s.locals discr with
    | some (.bool false) =>
      .step () { s with block := falseTarget, stmtIdx := 0 }
    | some (.bool true) =>
      .step () { s with block := trueTarget, stmtIdx := 0 }
    | _ => .failed .ub
  | .callAtomicLoad dst ptr ord target =>
    match evalOperand s.locals ptr with
    | some (.atomicLoc loc) =>
      match s.mem.visibleAtomicMsgs loc with
      | [] => .failed .ub
      | head :: tail =>
        .choice .demonic (fun s' =>
          ∃ msg, msg ∈ (head :: tail) ∧
            s' = {
              locals := updateLocal s.locals dst (some (.usize msg.bits))
              mem := s.mem.applyAtomicLoad ord msg
              block := target
              stmtIdx := 0
            })
    | _ => .failed .ub

def listGet : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet xs n

def evalMirStep (body : MirBody) (s : MirState) : StepResult MirState Unit TermOutcome :=
  match listGet body.blocks s.block with
  | none => .failed .ub
  | some bb =>
    match listGet bb.stmts s.stmtIdx with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator s bb.terminator

def MirMachine : SmallStepMachine MirBody MirState Unit TermOutcome where
  initState _ s := s.block = 0 ∧ s.stmtIdx = 0
  step body s r := r = evalMirStep body s

def MirLang : Language where
  Prog := MirBody
  Query := ExecQuery MirState
  Out := ExecOut Unit TermOutcome
  sem body q := {
    defined := True
    val := fun _ out =>
      MirMachine.initState body q.init ∧
      ReachesPrefix MirMachine body q.init q.steps q.init out.trace out.outcome
  }

/-- From current concrete machine state `s`, every finite execution prefix of
    `body` is safe (`out.isSafe`) and any normal termination satisfies `Post`. -/
def SafeAndSatisfies (body : MirBody) (s : MirState)
    (Post : TermOutcome → Prop) : Prop :=
  ∀ (init : MirState) (steps : Nat) (tr : List Unit) (out : PrefixOutcome TermOutcome),
    ReachesPrefix MirMachine body init steps s tr out →
    out.isSafe ∧ (∀ termOut, out = .terminated (.normal termOut) → Post termOut)

theorem SafeAndSatisfies.of_step {body : MirBody} {s s' : MirState}
    {Post : TermOutcome → Prop}
    (hstep : evalMirStep body s = .step () s')
    (hnext : SafeAndSatisfies body s' Post) :
    SafeAndSatisfies body s Post := by
  intro init steps tr out hreach
  cases hreach with
  | zero =>
    exact ⟨True.intro, fun _ h => by cases h⟩
  | step n _ s'' obs tr' out h1 h2 =>
    have h1' : StepResult.step obs s'' = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with _ hs''
    subst hs''
    exact hnext init n tr' out h2
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hstep.symm⟩)

theorem SafeAndSatisfies.of_terminated {body : MirBody} {s : MirState}
    {termOut : TermOutcome} {Post : TermOutcome → Prop}
    (hterm : evalMirStep body s = .terminated (.normal termOut))
    (hPost : Post termOut) :
    SafeAndSatisfies body s Post := by
  intro init steps tr out hreach
  cases hreach with
  | zero =>
    exact ⟨True.intro, fun _ h => by cases h⟩
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | terminated _ _ term h1 =>
    have h1' : StepResult.terminated term = evalMirStep body s := h1
    rw [hterm] at h1'
    injection h1' with hterm_eq
    subst hterm_eq
    refine ⟨True.intro, ?_⟩
    intro ret hret
    injection hret with hterm_ret
    injection hterm_ret with hret_eq
    subst hret_eq
    exact hPost
  | failed _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hterm.symm⟩)

theorem SafeAndSatisfies.of_demonic_choice {body : MirBody} {s : MirState}
    {branches : MirState → Prop} {Post : TermOutcome → Prop}
    (hstep : evalMirStep body s = .choice .demonic branches)
    (hnonempty : ∃ s', branches s')
    (hnext : ∀ s', branches s' → SafeAndSatisfies body s' Post) :
    SafeAndSatisfies body s Post := by
  intro init steps tr out hreach
  cases hreach with
  | zero =>
    exact ⟨True.intro, fun _ h => by cases h⟩
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | choice n _ _ s' brs _ _ h1 hbr h2 =>
    have h1' : StepResult.choice _ brs = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with _ hbrs
    subst hbrs
    exact hnext s' hbr init n tr out h2
  | emptyChoice _ _ _ brs h1 hempty =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with _ hbrs
    subst hbrs
    exact False.elim (hempty hnonempty)
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hstep.symm⟩)

/-!
## 4. Hybrid Symbolic Domain (`SymVal`, `LoanEntry`, `SymState`), Interaction Trees (`SymTree`), and Omnisemantics (`symWP`)
-/

inductive SymVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | refShared (n : Nat)
  | borrow (loanId : Nat)
  | rawPtr (rawId : Nat)
  | atomicRef (atomId : Nat)
  deriving DecidableEq, Repr

def SymVal.toScalarMirVal : SymVal → Option MirVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | .refShared _ => none
  | .borrow _ => none
  | .rawPtr _ => none
  | .atomicRef _ => none

def zipMirVal (b : Bool) (vt vf : MirVal) : Option MirVal :=
  match vt, vf with
  | .usize nt, .usize nf => some (.usize (if b then nt else nf))
  | .bool bt, .bool bf => some (.bool (if b then bt else bf))
  | .unit, .unit => some .unit
  | _, _ => none

/-- Terminal return summary recording both `_0` (`retVal`) and the final value
    of root `&mut` parameter loan `1` (`loan1Val`). -/
structure RetSummary where
  retVal : MirVal
  loan1Val : Option MirVal
  deriving DecidableEq, Repr

def zipOptionMirVal (b : Bool) (ot of_ : Option MirVal) : Option (Option MirVal) :=
  match ot, of_ with
  | none, none => some none
  | some vt, some vf =>
    match zipMirVal b vt vf with
    | some v => some (some v)
    | none => none
  | _, _ => none

def zipRetSummary (b : Bool) (st sf : RetSummary) : Option RetSummary :=
  match zipMirVal b st.retVal sf.retVal, zipOptionMirVal b st.loan1Val sf.loan1Val with
  | some r, some l1 => some { retVal := r, loan1Val := l1 }
  | _, _ => none

/-- Technique A (`SymTree` — Hybrid Interaction Trees / Free Monad Target):
    All safe local, control-flow, and `&` / `&mut` borrow operations reduce at
    translation time by `rfl`, leaving only residual raw-pointer and weak-memory
    atomic effect nodes. -/
inductive SymTree (Val : Type) where
  | ret (v : Val)
  | fail
  | readRaw (rawId : Nat) (k : Nat → SymTree Val)
  | writeRaw (rawId : Nat) (newVal : MirVal) (k : SymTree Val)
  | promoteRaw (rawId : Nat) (loanId : Nat) (k : Nat → SymTree Val)
  | releaseRaw (rawId : Nat) (loanId : Nat) (finalVal : MirVal) (k : SymTree Val)
  | atomicLoad (atomId : Nat) (ord : AtomicOrdering) (k : Nat → SymTree Val)

/-- Spine-preserving merge on `SymTree RetSummary`: folds conditional branches
    over pure `.ret` and `.releaseRaw ... (.ret ...)` outcomes into a single
    constructor spine with `if b then ... else ...` pushed inside scalar payloads. -/
def zipSymTree (b : Bool) (tTrue tFalse : SymTree RetSummary) : SymTree RetSummary :=
  match tTrue, tFalse with
  | .ret st, .ret sf =>
    match zipRetSummary b st sf with
    | some s => .ret s
    | none => if b then tTrue else tFalse
  | .releaseRaw r1 l1 vt (.ret st), .releaseRaw r2 l2 vf (.ret sf) =>
    if r1 == r2 && l1 == l2 then
      match zipMirVal b vt vf, zipRetSummary b st sf with
      | some v, some s => .releaseRaw r1 l1 v (.ret s)
      | _, _ => if b then tTrue else tFalse
    else
      if b then tTrue else tFalse
  | _, _ => if b then tTrue else tFalse

theorem zipMirVal_true (vt vf : MirVal) {v : MirVal}
    (h : zipMirVal true vt vf = some v) : v = vt := by
  cases vt <;> cases vf <;> cases h <;> rfl

theorem zipMirVal_false (vt vf : MirVal) {v : MirVal}
    (h : zipMirVal false vt vf = some v) : v = vf := by
  cases vt <;> cases vf <;> cases h <;> rfl

theorem zipOptionMirVal_true (ot of_ : Option MirVal) {o : Option MirVal}
    (h : zipOptionMirVal true ot of_ = some o) : o = ot := by
  cases ot with
  | none =>
    cases of_ with
    | none => injection h with heq; exact heq.symm
    | some _ => cases h
  | some vt =>
    cases of_ with
    | none => cases h
    | some vf =>
      dsimp [zipOptionMirVal] at h
      cases hzv : zipMirVal true vt vf with
      | none => rw [hzv] at h; cases h
      | some v =>
        rw [hzv] at h
        injection h with heq
        rw [← heq, zipMirVal_true vt vf hzv]

theorem zipOptionMirVal_false (ot of_ : Option MirVal) {o : Option MirVal}
    (h : zipOptionMirVal false ot of_ = some o) : o = of_ := by
  cases ot with
  | none =>
    cases of_ with
    | none => injection h with heq; exact heq.symm
    | some _ => cases h
  | some vt =>
    cases of_ with
    | none => cases h
    | some vf =>
      dsimp [zipOptionMirVal] at h
      cases hzv : zipMirVal false vt vf with
      | none => rw [hzv] at h; cases h
      | some v =>
        rw [hzv] at h
        injection h with heq
        rw [← heq, zipMirVal_false vt vf hzv]

theorem zipRetSummary_true (st sf : RetSummary) {s : RetSummary}
    (h : zipRetSummary true st sf = some s) : s = st := by
  cases st with
  | mk rt lt =>
    cases sf with
    | mk rf lf =>
      dsimp [zipRetSummary] at h
      cases hzr : zipMirVal true rt rf with
      | none => rw [hzr] at h; cases h
      | some r =>
        rw [hzr] at h
        cases hzl : zipOptionMirVal true lt lf with
        | none => rw [hzl] at h; cases h
        | some l1 =>
          rw [hzl] at h
          injection h with heq
          rw [← heq, zipMirVal_true rt rf hzr, zipOptionMirVal_true lt lf hzl]

theorem zipRetSummary_false (st sf : RetSummary) {s : RetSummary}
    (h : zipRetSummary false st sf = some s) : s = sf := by
  cases st with
  | mk rt lt =>
    cases sf with
    | mk rf lf =>
      dsimp [zipRetSummary] at h
      cases hzr : zipMirVal false rt rf with
      | none => rw [hzr] at h; cases h
      | some r =>
        rw [hzr] at h
        cases hzl : zipOptionMirVal false lt lf with
        | none => rw [hzl] at h; cases h
        | some l1 =>
          rw [hzl] at h
          injection h with heq
          rw [← heq, zipMirVal_false rt rf hzr, zipOptionMirVal_false lt lf hzl]

theorem zipSymTree_eq_ite (b : Bool) (tTrue tFalse : SymTree RetSummary) :
    zipSymTree b tTrue tFalse = (if b then tTrue else tFalse) := by
  cases b with
  | true =>
    unfold zipSymTree
    cases tTrue with
    | ret st =>
      cases tFalse with
      | ret sf =>
        dsimp
        cases h : zipRetSummary true st sf with
        | none => rfl
        | some s => rw [zipRetSummary_true st sf h]
      | _ => rfl
    | releaseRaw r1 l1 vt kt =>
      cases kt with
      | ret st =>
        cases tFalse with
        | releaseRaw r2 l2 vf kf =>
          cases kf with
          | ret sf =>
            dsimp
            cases hcond : (r1 == r2 && l1 == l2) with
            | false => rfl
            | true =>
              dsimp
              cases hzv : zipMirVal true vt vf with
              | none => rfl
              | some v =>
                cases hzs : zipRetSummary true st sf with
                | none => rfl
                | some s =>
                  rw [zipMirVal_true vt vf hzv, zipRetSummary_true st sf hzs]
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | false =>
    unfold zipSymTree
    cases tTrue with
    | ret st =>
      cases tFalse with
      | ret sf =>
        dsimp
        cases h : zipRetSummary false st sf with
        | none => rfl
        | some s => rw [zipRetSummary_false st sf h]
      | _ => rfl
    | releaseRaw r1 l1 vt kt =>
      cases kt with
      | ret st =>
        cases tFalse with
        | releaseRaw r2 l2 vf kf =>
          cases kf with
          | ret sf =>
            dsimp
            cases hcond : (r1 == r2 && l1 == l2) with
            | false => rfl
            | true =>
              dsimp
              have hr : r1 = r2 := of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).1
              have hl : l1 = l2 := of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).2
              subst hr hl
              cases hzv : zipMirVal false vt vf with
              | none => rfl
              | some v =>
                cases hzs : zipRetSummary false st sf with
                | none => rfl
                | some s =>
                  rw [zipMirVal_false vt vf hzv, zipRetSummary_false st sf hzs]
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl

/-- Loan entry in `SymState.loans`: tracks root `&mut` parameter loans
    (`rawSource = none`) as well as raw-pointer-promoted loans created by
    `TransPlan.reborrowRaw` (`rawSource = some rawId`). -/
structure LoanEntry where
  rawSource : Option Nat
  curVal : SymVal
  frozen : Bool
  active : Bool
  deriving DecidableEq, Repr

structure SymState where
  locals : Nat → Option SymVal
  loans : Nat → Option LoanEntry
  block : Nat
  stmtIdx : Nat

def updateSymLocal (locals : Nat → Option SymVal) (target : Nat)
    (val : Option SymVal) : Nat → Option SymVal :=
  fun i => if i == target then val else locals i

def updateLoan (loans : Nat → Option LoanEntry) (target : Nat)
    (val : Option LoanEntry) : Nat → Option LoanEntry :=
  fun i => if i == target then val else loans i

def updateRawOwn (rawOwn : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else rawOwn i

/-- Positional translation plan guiding `evalSymTree` over `MirBody`, extended
    with Technique C hints (`reborrowRaw` and `endRawLoan`) for promoting raw
    pointers into tracked functional loans and releasing them back. -/
inductive TransPlan where
  | ret
  | step (next : TransPlan)
  | branch (falsePlan : TransPlan) (truePlan : TransPlan)
  | reborrowRaw (loanId : Nat) (next : TransPlan)
  | endRawLoan (loanId : Nat) (next : TransPlan)
  | fail
  deriving Repr

def evalSymConst : MirVal → Option SymVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | _ => none

def evalSymOperand (locals : Nat → Option SymVal) (op : Operand) : Option SymVal :=
  match op with
  | .copy src => locals src
  | .constVal mv => evalSymConst mv

def evalSymBinOp (op : BinOp) (v1 v2 : SymVal) : Option SymVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.usize (n1 + n2))
    | .lt => some (.bool (decide (n1 < n2)))
    | .eq => some (.bool (decide (n1 = n2)))
  | _, _ => none

/-- Pure symbolic evaluation of safe MIR statements (including safe `&` and `&mut`
    dereference reads and writes). Returns `none` on unsafe raw-pointer statements,
    which are handled as residual effect nodes in `evalSymTree`. -/
def evalSafeSymStmt (sym : SymState) (stmt : Stmt) : Option SymState :=
  match stmt with
  | .assign dst (.use op) =>
    match evalSymOperand sym.locals op with
    | some sv =>
      some { sym with
        locals := updateSymLocal sym.locals dst (some sv)
        stmtIdx := sym.stmtIdx + 1 }
    | none => none
  | .assign dst (.deref src) =>
    match sym.locals src with
    | some (.refShared n) =>
      some { sym with
        locals := updateSymLocal sym.locals dst (some (.usize n))
        stmtIdx := sym.stmtIdx + 1 }
    | some (.borrow lid) =>
      match sym.loans lid with
      | some entry =>
        if entry.active && !entry.frozen then
          some { sym with
            locals := updateSymLocal sym.locals dst (some entry.curVal)
            stmtIdx := sym.stmtIdx + 1 }
        else
          none
      | none => none
    | _ => none
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalSymOperand sym.locals lhs, evalSymOperand sym.locals rhs with
    | some v1, some v2 =>
      match evalSymBinOp op v1 v2 with
      | some res =>
        some { sym with
          locals := updateSymLocal sym.locals dst (some res)
          stmtIdx := sym.stmtIdx + 1 }
      | none => none
    | _, _ => none
  | .assignDeref dst op =>
    match evalSymOperand sym.locals op, sym.locals dst with
    | some sv, some (.borrow lid) =>
      match sv.toScalarMirVal, sym.loans lid with
      | some _, some entry =>
        if entry.active && !entry.frozen then
          some { sym with
            loans := updateLoan sym.loans lid (some { entry with curVal := sv })
            stmtIdx := sym.stmtIdx + 1 }
        else
          none
      | _, _ => none
    | _, _ => none
  | .nop =>
    some { sym with stmtIdx := sym.stmtIdx + 1 }
  | .derefRaw _ _ | .assignDerefRaw _ _ | .reborrowRawToMut _ _ =>
    none

def extractLoan1Val (loans : Nat → Option LoanEntry) : Option MirVal :=
  match loans 1 with
  | some entry =>
    if entry.active && !entry.frozen then
      entry.curVal.toScalarMirVal
    else
      none
  | none => none

def evalReturnSummary (body : MirBody) (sym : SymState) : Option RetSummary :=
  match listGet body.blocks sym.block with
  | none => none
  | some bb =>
    match listGet bb.stmts sym.stmtIdx, bb.terminator with
    | none, .return_ =>
      match sym.locals 0 with
      | some sv =>
        match sv.toScalarMirVal with
        | some retMv =>
          some { retVal := retMv, loan1Val := extractLoan1Val sym.loans }
        | none => none
      | none => none
    | _, _ => none

def evalBranchStep (body : MirBody) (sym : SymState) :
    Option (Bool × SymState × SymState) :=
  match listGet body.blocks sym.block with
  | none => none
  | some bb =>
    match listGet bb.stmts sym.stmtIdx, bb.terminator with
    | none, .switchInt discr falseTarget trueTarget =>
      match evalSymOperand sym.locals discr with
      | some (.bool cond) =>
        let symFalse := { sym with block := falseTarget, stmtIdx := 0 }
        let symTrue := { sym with block := trueTarget, stmtIdx := 0 }
        some (cond, symFalse, symTrue)
      | _ => none
    | _, _ => none

def rawLoanEntry (rawId : Nat) (v0 : Nat) : LoanEntry where
  rawSource := some rawId
  curVal := .usize v0
  frozen := false
  active := true

/-- Plan-guided hybrid symbolic evaluator (`evalSymTree`):
    - Reduces all safe statements, `&` / `&mut` borrow operations, `goto`, and
      `switchInt` branches directly in Lean's kernel by `rfl`.
    - Emits residual `SymTree` nodes for `derefRaw`, `assignDerefRaw`,
      `callAtomicLoad`, `reborrowRaw`, and `endRawLoan`. -/
def evalSymTree (plan : TransPlan) (body : MirBody) (sym : SymState) : SymTree RetSummary :=
  match plan with
  | .ret =>
    match evalReturnSummary body sym with
    | some summary => .ret summary
    | none => .fail
  | .step next =>
    match listGet body.blocks sym.block with
    | none => .fail
    | some bb =>
      match listGet bb.stmts sym.stmtIdx with
      | some stmt =>
        match stmt with
        | .derefRaw dst ptrLocal =>
          match sym.locals ptrLocal with
          | some (.rawPtr rawId) =>
            .readRaw rawId (fun v =>
              evalSymTree next body { sym with
                locals := updateSymLocal sym.locals dst (some (.usize v))
                stmtIdx := sym.stmtIdx + 1 })
          | _ => .fail
        | .assignDerefRaw ptrLocal op =>
          match evalSymOperand sym.locals op, sym.locals ptrLocal with
          | some sv, some (.rawPtr rawId) =>
            match sv.toScalarMirVal with
            | some mvNew =>
              .writeRaw rawId mvNew
                (evalSymTree next body { sym with stmtIdx := sym.stmtIdx + 1 })
            | none => .fail
          | _, _ => .fail
        | .reborrowRawToMut _ _ => .fail
        | _ =>
          match evalSafeSymStmt sym stmt with
          | some sym' => evalSymTree next body sym'
          | none => .fail
      | none =>
        match bb.terminator with
        | .goto target =>
          evalSymTree next body { sym with block := target, stmtIdx := 0 }
        | .callAtomicLoad dst ptr ord target =>
          match evalSymOperand sym.locals ptr with
          | some (.atomicRef atomId) =>
            .atomicLoad atomId ord (fun v =>
              evalSymTree next body { sym with
                locals := updateSymLocal sym.locals dst (some (.usize v))
                block := target
                stmtIdx := 0 })
          | _ => .fail
        | _ => .fail
  | .branch falsePlan truePlan =>
    match evalBranchStep body sym with
    | some (cond, symFalse, symTrue) =>
      zipSymTree cond
        (evalSymTree truePlan body symTrue)
        (evalSymTree falsePlan body symFalse)
    | none => .fail
  | .reborrowRaw loanId next =>
    match listGet body.blocks sym.block with
    | none => .fail
    | some bb =>
      match listGet bb.stmts sym.stmtIdx with
      | some (.reborrowRawToMut dst ptrLocal) =>
        match sym.locals ptrLocal, sym.loans loanId with
        | some (.rawPtr rawId), none =>
          if !(loanId == 1) then
            .promoteRaw rawId loanId (fun v0 =>
              evalSymTree next body { sym with
                locals := updateSymLocal sym.locals dst (some (.borrow loanId))
                loans := updateLoan sym.loans loanId (some (rawLoanEntry rawId v0))
                stmtIdx := sym.stmtIdx + 1 })
          else
            .fail
        | _, _ => .fail
      | _ => .fail
  | .endRawLoan loanId next =>
    if !(loanId == 1) then
      match sym.loans loanId with
      | some entry =>
        if entry.active && !entry.frozen then
          match entry.rawSource, entry.curVal.toScalarMirVal with
          | some rawId, some mvFinal =>
            .releaseRaw rawId loanId mvFinal
              (evalSymTree next body { sym with
                loans := updateLoan sym.loans loanId (some { entry with active := false }) })
          | _, _ => .fail
        else
          .fail
      | none => .fail
    else
      .fail
  | .fail => .fail
/-!
## 5. Unified Spatial Simulation Relation (`StateRel`) and Omnisemantics (`symWP`)
-/

structure SpatialEnv where
  loanLoc : Nat → Option Nat
  sharedLoc : Nat → Nat → Prop
  rawLoc : Nat → Option Nat
  atomicLoc : Nat → Option Nat

def updateRelOwn (relOwn : Nat → Option (Timestamp × MirVal)) (target : Nat)
    (val : Option (Timestamp × MirVal)) : Nat → Option (Timestamp × MirVal) :=
  fun i => if i == target then val else relOwn i

/-- Release-Acquire ownership extension at an atomic load:
    - `refl`: preserves `rawOwn` and `relOwn` unchanged (any ordering).
    - `transfer`: when `ord = .acquire` and `msg.relView locAcq` dominates the
      release timestamp `reqTs` of `relOwn acqId = some (reqTs, mv)`, promotes
      `acqId` from `relOwn` into active `rawOwn`. -/
inductive AcquireExt (env : SpatialEnv) (ord : AtomicOrdering) (msg : AtomicMsg)
    (rawOwn : Nat → Option MirVal) (relOwn : Nat → Option (Timestamp × MirVal)) :
    (Nat → Option MirVal) → (Nat → Option (Timestamp × MirVal)) → Prop where
  | refl :
      AcquireExt env ord msg rawOwn relOwn rawOwn relOwn
  | transfer (acqId : Nat) (locAcq : Nat) (reqTs : Timestamp) (mv : MirVal) :
      ord = .acquire →
      env.rawLoc acqId = some locAcq →
      relOwn acqId = some (reqTs, mv) →
      reqTs ≤ msg.relView locAcq →
      AcquireExt env ord msg rawOwn relOwn
        (updateRawOwn rawOwn acqId (some mv))
        (updateRelOwn relOwn acqId none)

/-- Technique B (`symWP` — Plan-Guided Omnisemantics Predicate Transformer):
    Computes the verification condition `Prop` for a residual `SymTree RetSummary`
    to safely reach `Post` from spatial state `(rawOwn, relOwn, atomMsgs, atomView)`. -/
def symWP : SymTree RetSummary → SpatialEnv →
    (Nat → Option MirVal) →
    (Nat → Option (Timestamp × MirVal)) →
    List AtomicMsg → View →
    (RetSummary → (Nat → Option MirVal) → Prop) → Prop
  | .ret summary, _, rawOwn, _, _, _, Post =>
    Post summary rawOwn
  | .fail, _, _, _, _, _, _ =>
    False
  | .readRaw rawId k, env, rawOwn, relOwn, atomMsgs, atomView, Post =>
    ∃ v, rawOwn rawId = some (.usize v) ∧
      symWP (k v) env rawOwn relOwn atomMsgs atomView Post
  | .writeRaw rawId newVal k, env, rawOwn, relOwn, atomMsgs, atomView, Post =>
    (∃ mvOld, rawOwn rawId = some mvOld) ∧
      symWP k env (updateRawOwn rawOwn rawId (some newVal)) relOwn atomMsgs atomView Post
  | .promoteRaw rawId loanId k, env, rawOwn, relOwn, atomMsgs, atomView, Post =>
    ∃ v0, rawOwn rawId = some (.usize v0) ∧
      env.loanLoc loanId = env.rawLoc rawId ∧
      symWP (k v0) env (updateRawOwn rawOwn rawId none) relOwn atomMsgs atomView Post
  | .releaseRaw rawId loanId finalVal k, env, rawOwn, relOwn, atomMsgs, atomView, Post =>
    rawOwn rawId = none ∧
      relOwn rawId = none ∧
      env.loanLoc loanId = env.rawLoc rawId ∧
      symWP k env (updateRawOwn rawOwn rawId (some finalVal)) relOwn atomMsgs atomView Post
  | .atomicLoad atomId ord k, env, rawOwn, relOwn, atomMsgs, atomView, Post =>
    ∃ locAtom, env.atomicLoc atomId = some locAtom ∧
      visibleMsgsAt atomMsgs (atomView locAtom) locAtom ≠ [] ∧
      ∀ msg, msg ∈ visibleMsgsAt atomMsgs (atomView locAtom) locAtom →
        ∃ rawOwn' relOwn',
          AcquireExt env ord msg rawOwn relOwn rawOwn' relOwn' ∧
          symWP (k msg.bits) env rawOwn' relOwn' atomMsgs (applyViewLoad ord atomView msg) Post

def ValRel (env : SpatialEnv) (sv : SymVal) (mv : MirVal) : Prop :=
  match sv with
  | .usize n => mv = .usize n
  | .bool b => mv = .bool b
  | .unit => mv = .unit
  | .refShared n => ∃ loc, env.sharedLoc loc n ∧ mv = .refSharedLoc loc
  | .borrow lid => ∃ loc, env.loanLoc lid = some loc ∧ mv = .refMutLoc loc
  | .rawPtr rawId => ∃ loc, env.rawLoc rawId = some loc ∧ mv = .rawPtrLoc loc
  | .atomicRef atomId => ∃ loc, env.atomicLoc atomId = some loc ∧ mv = .atomicLoc loc

theorem ValRel.of_toScalarMirVal (env : SpatialEnv)
    {sv : SymVal} {mv : MirVal} (h : sv.toScalarMirVal = some mv) :
    ValRel env sv mv := by
  cases sv with
  | usize n => injection h with heq; exact heq.symm
  | bool b => injection h with heq; exact heq.symm
  | unit => injection h with heq; exact heq.symm
  | refShared _ | borrow _ | rawPtr _ | atomicRef _ => cases h

theorem ValRel.toScalarMirVal_eq {env : SpatialEnv}
    {sv : SymVal} {mv mv' : MirVal}
    (hRel : ValRel env sv mv)
    (hScalar : sv.toScalarMirVal = some mv') :
    mv = mv' := by
  cases sv with
  | usize n => injection hScalar with h1; exact Eq.trans hRel h1
  | bool b => injection hScalar with h1; exact Eq.trans hRel h1
  | unit => injection hScalar with h1; exact Eq.trans hRel h1
  | refShared _ | borrow _ | rawPtr _ | atomicRef _ => cases hScalar

def LocalRel (env : SpatialEnv) (symLocals : Nat → Option SymVal)
    (concLocals : Nat → Option MirVal) : Prop :=
  ∀ i sv, symLocals i = some sv → ∃ mv, concLocals i = some mv ∧ ValRel env sv mv

theorem LocalRel.update_some {env : SpatialEnv}
    {symLocals : Nat → Option SymVal} {concLocals : Nat → Option MirVal}
    (hRel : LocalRel env symLocals concLocals)
    (dst : Nat) {sv : SymVal} {mv : MirVal} (hVal : ValRel env sv mv) :
    LocalRel env (updateSymLocal symLocals dst (some sv))
      (updateLocal concLocals dst (some mv)) := by
  intro i sv' hlookup
  unfold updateSymLocal at hlookup
  unfold updateLocal
  cases h : (i == dst) with
  | false =>
    rw [h] at hlookup
    exact hRel i sv' hlookup
  | true =>
    rw [h] at hlookup
    injection hlookup with heq
    subst heq
    exact ⟨mv, rfl, hVal⟩

theorem evalSymOperand_sound {env : SpatialEnv}
    {symLocals : Nat → Option SymVal} {concLocals : Nat → Option MirVal}
    {op : Operand} {sv : SymVal}
    (hRel : LocalRel env symLocals concLocals)
    (hEval : evalSymOperand symLocals op = some sv) :
    ∃ mv, evalOperand concLocals op = some mv ∧ ValRel env sv mv := by
  cases op with
  | copy src =>
    dsimp [evalSymOperand] at hEval
    have ⟨mv, hconc, hval⟩ := hRel src sv hEval
    exact ⟨mv, hconc, hval⟩
  | constVal mv0 =>
    dsimp [evalSymOperand] at hEval
    cases mv0 with
    | usize n =>
      injection hEval with hsv; subst hsv
      exact ⟨.usize n, rfl, rfl⟩
    | bool b =>
      injection hEval with hsv; subst hsv
      exact ⟨.bool b, rfl, rfl⟩
    | unit =>
      injection hEval with hsv; subst hsv
      exact ⟨.unit, rfl, rfl⟩
    | refMutLoc _ | refSharedLoc _ | rawPtrLoc _ | atomicLoc _ =>
      cases hEval

theorem evalSymBinOp_sound {env : SpatialEnv}
    {op : BinOp} {sv1 sv2 res : SymVal} {mv1 mv2 : MirVal}
    (hVal1 : ValRel env sv1 mv1)
    (hVal2 : ValRel env sv2 mv2)
    (hBin : evalSymBinOp op sv1 sv2 = some res) :
    ∃ mres, evalBinOp op mv1 mv2 = some mres ∧ ValRel env res mres := by
  cases sv1 with
  | bool _ | unit | refShared _ | borrow _ | rawPtr _ | atomicRef _ => cases hBin
  | usize n1 =>
    cases sv2 with
    | bool _ | unit | refShared _ | borrow _ | rawPtr _ | atomicRef _ => cases hBin
    | usize n2 =>
      subst hVal1 hVal2
      cases op with
      | add =>
        injection hBin with hres; subst hres
        exact ⟨.usize (n1 + n2), rfl, rfl⟩
      | lt =>
        injection hBin with hres; subst hres
        exact ⟨.bool (decide (n1 < n2)), rfl, rfl⟩
      | eq =>
        injection hBin with hres; subst hres
        exact ⟨.bool (decide (n1 = n2)), rfl, rfl⟩

/-- Functional borrow invariant (`LoanRel`): active unfrozen `&mut` loans own
    their concrete locations (`OwnLoc`), and shared references satisfy
    `ReadOwnLoc`. -/
structure LoanRel (env : SpatialEnv) (loans : Nat → Option LoanEntry)
    (mem : MemState) : Prop where
  activeOwn :
    ∀ lid entry,
      loans lid = some entry →
      entry.active = true →
      entry.frozen = false →
      ∃ loc mv,
        env.loanLoc lid = some loc ∧
        entry.curVal.toScalarMirVal = some mv ∧
        OwnLoc mem loc mv
  disjointActive :
    ∀ lid₁ lid₂ e₁ e₂ loc₁ loc₂,
      lid₁ ≠ lid₂ →
      loans lid₁ = some e₁ → e₁.active = true → e₁.frozen = false →
      loans lid₂ = some e₂ → e₂.active = true → e₂.frozen = false →
      env.loanLoc lid₁ = some loc₁ →
      env.loanLoc lid₂ = some loc₂ →
      loc₁ ≠ loc₂
  sharedOwn :
    ∀ loc n, env.sharedLoc loc n → ReadOwnLoc mem loc (.usize n)
  disjointShared :
    ∀ lid entry locMut locShared n,
      loans lid = some entry →
      entry.active = true →
      entry.frozen = false →
      env.loanLoc lid = some locMut →
      env.sharedLoc locShared n →
      locMut ≠ locShared

/-- Spatial raw-pointer invariant (`RawRel`): tracks owned raw pointers
    (`rawOwn`) via `OwnLoc` and release-guarded raw pointers (`relOwn`) via
    `ReleaseGuarded`, enforcing pairwise disjointness from active `LoanEntry`s
    and shared references. -/
structure RawRel (env : SpatialEnv) (loans : Nat → Option LoanEntry)
    (rawOwn : Nat → Option MirVal)
    (relOwn : Nat → Option (Timestamp × MirVal))
    (mem : MemState) : Prop where
  rawOwnLoc :
    ∀ rawId mv,
      rawOwn rawId = some mv →
      ∃ locRaw,
        env.rawLoc rawId = some locRaw ∧
        OwnLoc mem locRaw mv
  relOwnLoc :
    ∀ rawId reqTs mv,
      relOwn rawId = some (reqTs, mv) →
      ∃ locRaw,
        env.rawLoc rawId = some locRaw ∧
        ReleaseGuarded mem locRaw reqTs mv
  disjointRaw :
    ∀ r₁ r₂ loc₁ loc₂,
      r₁ ≠ r₂ →
      env.rawLoc r₁ = some loc₁ →
      env.rawLoc r₂ = some loc₂ →
      loc₁ ≠ loc₂
  disjointRawShared :
    ∀ r locRaw locShared n,
      env.rawLoc r = some locRaw →
      env.sharedLoc locShared n →
      locRaw ≠ locShared
  disjointRawLoans :
    ∀ r mv lid entry locRaw locLoan,
      (rawOwn r = some mv ∨ ∃ ts, relOwn r = some (ts, mv)) →
      loans lid = some entry →
      entry.active = true →
      entry.frozen = false →
      env.rawLoc r = some locRaw →
      env.loanLoc lid = some locLoan →
      locRaw ≠ locLoan
  exclusiveRawRel :
    ∀ r mv p, rawOwn r = some mv → relOwn r = some p → False

def isNonPtrLoc (env : SpatialEnv) (loc : Nat) : Prop :=
  (∀ lid, env.loanLoc lid ≠ some loc) ∧
  (∀ r, env.rawLoc r ≠ some loc)

/-- Weak-memory atomic view invariant (`AtomRel`). -/
structure AtomRel (env : SpatialEnv) (atomMsgs : List AtomicMsg)
    (atomView : View) (mem : MemState) : Prop where
  msgs_eq : mem.atomicMsgs = atomMsgs
  view_eq : ∀ loc, isNonPtrLoc env loc → mem.curView loc = atomView loc
  atomDisj : ∀ atomId locAtom, env.atomicLoc atomId = some locAtom → isNonPtrLoc env locAtom

/-- Unified simulation relation (`StateRel`) combining local variables,
    functional `&mut` / `&` loans, raw pointers, and weak-memory atomics. -/
structure StateRel (env : SpatialEnv)
    (rawOwn : Nat → Option MirVal)
    (relOwn : Nat → Option (Timestamp × MirVal))
    (atomMsgs : List AtomicMsg)
    (atomView : View)
    (sym : SymState) (conc : MirState) : Prop where
  block_eq : conc.block = sym.block
  stmtIdx_eq : conc.stmtIdx = sym.stmtIdx
  localRel : LocalRel env sym.locals conc.locals
  loanRel : LoanRel env sym.loans conc.mem
  rawRel : RawRel env sym.loans rawOwn relOwn conc.mem
  atomRel : AtomRel env atomMsgs atomView conc.mem

/-!
### Coexistence and Automatic Framing Theorems Across `LoanRel`, `RawRel`, and `AtomRel`
-/

theorem LoanRel.of_readNA {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {mem : MemState} (locRead : Nat)
    (hLoan : LoanRel env loans mem) :
    LoanRel env loans (afterReadNA mem locRead) where
  activeOwn lid entry hlookup hact hfrz := by
    have ⟨loc, mv, hloc, hsc, hown⟩ := hLoan.activeOwn lid entry hlookup hact hfrz
    exact ⟨loc, mv, hloc, hsc, OwnLoc.readNA_preserves hown⟩
  disjointActive := hLoan.disjointActive
  sharedOwn loc n hsh := ReadOwnLoc.readNA_preserves (hLoan.sharedOwn loc n hsh)
  disjointShared := hLoan.disjointShared

theorem RawRel.of_readNA_loan {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {lid : Nat} {entry : LoanEntry} {locRead : Nat}
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hlookup : loans lid = some entry) (hact : entry.active = true) (hfrz : entry.frozen = false)
    (hloc : env.loanLoc lid = some locRead) :
    RawRel env loans rawOwn relOwn (afterReadNA mem locRead) where
  rawOwnLoc rawId mv h := by
    have ⟨locRaw, hrloc, hown⟩ := hRaw.rawOwnLoc rawId mv h
    exact ⟨locRaw, hrloc, OwnLoc.readNA_preserves hown⟩
  relOwnLoc rawId reqTs mv h := by
    have ⟨locRaw, hrloc, hrel⟩ := hRaw.relOwnLoc rawId reqTs mv h
    have hne : locRaw ≠ locRead :=
      hRaw.disjointRawLoans rawId mv lid entry locRaw locRead
        (Or.inr ⟨reqTs, h⟩) hlookup hact hfrz hrloc hloc
    exact ⟨locRaw, hrloc, ReleaseGuarded.afterReadNA_other hne hrel⟩
  disjointRaw := hRaw.disjointRaw
  disjointRawShared := hRaw.disjointRawShared
  disjointRawLoans := hRaw.disjointRawLoans
  exclusiveRawRel := hRaw.exclusiveRawRel

theorem RawRel.of_readNA_shared {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {locRead n : Nat}
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hsh : env.sharedLoc locRead n) :
    RawRel env loans rawOwn relOwn (afterReadNA mem locRead) where
  rawOwnLoc rawId mv h := by
    have ⟨locRaw, hrloc, hown⟩ := hRaw.rawOwnLoc rawId mv h
    exact ⟨locRaw, hrloc, OwnLoc.readNA_preserves hown⟩
  relOwnLoc rawId reqTs mv h := by
    have ⟨locRaw, hrloc, hrel⟩ := hRaw.relOwnLoc rawId reqTs mv h
    have hne : locRaw ≠ locRead := hRaw.disjointRawShared rawId locRaw locRead n hrloc hsh
    exact ⟨locRaw, hrloc, ReleaseGuarded.afterReadNA_other hne hrel⟩
  disjointRaw := hRaw.disjointRaw
  disjointRawShared := hRaw.disjointRawShared
  disjointRawLoans := hRaw.disjointRawLoans
  exclusiveRawRel := hRaw.exclusiveRawRel

theorem RawRel.of_readNA_raw {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {rawId : Nat} {mvRead : MirVal} {locRead : Nat}
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hownRead : rawOwn rawId = some mvRead)
    (hrlocRead : env.rawLoc rawId = some locRead) :
    RawRel env loans rawOwn relOwn (afterReadNA mem locRead) where
  rawOwnLoc r mv h := by
    have ⟨locRaw, hrloc, hown⟩ := hRaw.rawOwnLoc r mv h
    exact ⟨locRaw, hrloc, OwnLoc.readNA_preserves hown⟩
  relOwnLoc r reqTs mv h := by
    have ⟨locRaw, hrloc, hrel⟩ := hRaw.relOwnLoc r reqTs mv h
    have hr_ne : r ≠ rawId := by
      intro heq
      subst heq
      exact hRaw.exclusiveRawRel r mvRead (reqTs, mv) hownRead h
    have hne : locRaw ≠ locRead := hRaw.disjointRaw r rawId locRaw locRead hr_ne hrloc hrlocRead
    exact ⟨locRaw, hrloc, ReleaseGuarded.afterReadNA_other hne hrel⟩
  disjointRaw := hRaw.disjointRaw
  disjointRawShared := hRaw.disjointRawShared
  disjointRawLoans := hRaw.disjointRawLoans
  exclusiveRawRel := hRaw.exclusiveRawRel

theorem AtomRel.of_readNA {env : SpatialEnv} {atomMsgs : List AtomicMsg}
    {atomView : View} {mem : MemState} (locRead : Nat)
    (hAtom : AtomRel env atomMsgs atomView mem) :
    AtomRel env atomMsgs atomView (afterReadNA mem locRead) :=
  ⟨hAtom.msgs_eq, hAtom.view_eq, hAtom.atomDisj⟩

theorem LoanRel.update_curVal {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {mem : MemState} {lid loc : Nat} {entry : LoanEntry} {mvOld mvNew : MirVal} {sv : SymVal}
    (hLoan : LoanRel env loans mem)
    (hlookup : loans lid = some entry)
    (hact : entry.active = true)
    (hfrz : entry.frozen = false)
    (hloc : env.loanLoc lid = some loc)
    (hOwnOld : OwnLoc mem loc mvOld)
    (hScalarNew : sv.toScalarMirVal = some mvNew) :
    LoanRel env (updateLoan loans lid (some { entry with curVal := sv }))
      (afterWriteNA mem loc mvNew) where
  activeOwn lid' entry' hlookup' hact' hfrz' := by
    unfold updateLoan at hlookup'
    cases hbeq : (lid' == lid) with
    | true =>
      rw [hbeq] at hlookup'
      injection hlookup' with heq'
      have hlid_eq : lid' = lid := of_decide_eq_true hbeq
      subst hlid_eq heq'
      exact ⟨loc, mvNew, hloc, hScalarNew, OwnLoc.afterWriteNA_self hOwnOld mvNew⟩
    | false =>
      rw [hbeq] at hlookup'
      have hne : lid' ≠ lid := of_decide_eq_false hbeq
      have ⟨loc', mv', hloc', hsc', hown'⟩ := hLoan.activeOwn lid' entry' hlookup' hact' hfrz'
      have hneLoc : loc' ≠ loc :=
        hLoan.disjointActive lid' lid entry' entry loc' loc hne hlookup' hact' hfrz' hlookup hact hfrz hloc' hloc
      exact ⟨loc', mv', hloc', hsc', OwnLoc.afterWriteNA_other hneLoc hown' mvNew⟩
  disjointActive lid₁ lid₂ e₁ e₂ loc₁ loc₂ hne hl₁ ha₁ hf₁ hl₂ ha₂ hf₂ hloc₁ hloc₂ := by
    unfold updateLoan at hl₁ hl₂
    have h₁ : ∃ e₁₀, loans lid₁ = some e₁₀ ∧ e₁₀.active = true ∧ e₁₀.frozen = false := by
      cases hb₁ : (lid₁ == lid) with
      | true =>
        rw [of_decide_eq_true hb₁]
        exact ⟨entry, hlookup, hact, hfrz⟩
      | false =>
        rw [hb₁] at hl₁; exact ⟨e₁, hl₁, ha₁, hf₁⟩
    have h₂ : ∃ e₂₀, loans lid₂ = some e₂₀ ∧ e₂₀.active = true ∧ e₂₀.frozen = false := by
      cases hb₂ : (lid₂ == lid) with
      | true =>
        rw [of_decide_eq_true hb₂]
        exact ⟨entry, hlookup, hact, hfrz⟩
      | false =>
        rw [hb₂] at hl₂; exact ⟨e₂, hl₂, ha₂, hf₂⟩
    have ⟨e₁₀, hl₁₀, ha₁₀, hf₁₀⟩ := h₁
    have ⟨e₂₀, hl₂₀, ha₂₀, hf₂₀⟩ := h₂
    exact hLoan.disjointActive lid₁ lid₂ e₁₀ e₂₀ loc₁ loc₂ hne hl₁₀ ha₁₀ hf₁₀ hl₂₀ ha₂₀ hf₂₀ hloc₁ hloc₂
  sharedOwn locShared n hsh := by
    have hne : locShared ≠ loc :=
      (hLoan.disjointShared lid entry loc locShared n hlookup hact hfrz hloc hsh).symm
    exact ReadOwnLoc.afterWriteNA_other hne (hLoan.sharedOwn locShared n hsh) mvNew
  disjointShared lid' entry' locMut locShared n hl' ha' hf' hlocMut hsh := by
    unfold updateLoan at hl'
    cases hb : (lid' == lid) with
    | true =>
      rw [hb] at hl'
      have hlid_eq : lid' = lid := of_decide_eq_true hb
      subst hlid_eq
      exact hLoan.disjointShared lid' entry locMut locShared n hlookup hact hfrz hlocMut hsh
    | false =>
      rw [hb] at hl'
      exact hLoan.disjointShared lid' entry' locMut locShared n hl' ha' hf' hlocMut hsh

theorem RawRel.of_writeNA_loan {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {lid loc : Nat} {entry : LoanEntry} {mvNew : MirVal} {sv : SymVal}
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hlookup : loans lid = some entry)
    (hact : entry.active = true)
    (hfrz : entry.frozen = false)
    (hloc : env.loanLoc lid = some loc) :
    RawRel env (updateLoan loans lid (some { entry with curVal := sv }))
      rawOwn relOwn (afterWriteNA mem loc mvNew) where
  rawOwnLoc r mv hr := by
    have ⟨locRaw, hrloc, hown⟩ := hRaw.rawOwnLoc r mv hr
    have hne : locRaw ≠ loc :=
      hRaw.disjointRawLoans r mv lid entry locRaw loc (Or.inl hr) hlookup hact hfrz hrloc hloc
    exact ⟨locRaw, hrloc, OwnLoc.afterWriteNA_other hne hown mvNew⟩
  relOwnLoc r reqTs mv hr := by
    have ⟨locRaw, hrloc, hrel⟩ := hRaw.relOwnLoc r reqTs mv hr
    have hne : locRaw ≠ loc :=
      hRaw.disjointRawLoans r mv lid entry locRaw loc (Or.inr ⟨reqTs, hr⟩) hlookup hact hfrz hrloc hloc
    exact ⟨locRaw, hrloc, ReleaseGuarded.afterWriteNA_other hne hrel mvNew⟩
  disjointRaw := hRaw.disjointRaw
  disjointRawShared := hRaw.disjointRawShared
  disjointRawLoans r mv lid' entry' locRaw locLoan hown hl' ha' hf' hrloc hloc' := by
    unfold updateLoan at hl'
    cases hb : (lid' == lid) with
    | true =>
      have hlid_eq : lid' = lid := of_decide_eq_true hb
      subst hlid_eq
      exact hRaw.disjointRawLoans r mv lid' entry locRaw locLoan hown hlookup hact hfrz hrloc hloc'
    | false =>
      rw [hb] at hl'
      exact hRaw.disjointRawLoans r mv lid' entry' locRaw locLoan hown hl' ha' hf' hrloc hloc'
  exclusiveRawRel := hRaw.exclusiveRawRel

theorem AtomRel.of_writeNA_loan {env : SpatialEnv} {atomMsgs : List AtomicMsg}
    {atomView : View} {mem : MemState} {lid loc : Nat} (mvNew : MirVal)
    (hAtom : AtomRel env atomMsgs atomView mem)
    (hloc : env.loanLoc lid = some loc) :
    AtomRel env atomMsgs atomView (afterWriteNA mem loc mvNew) where
  msgs_eq := hAtom.msgs_eq
  view_eq l hnon := by
    have hne : l ≠ loc := by
      intro heq
      subst heq
      exact hnon.1 lid hloc
    have hbeq : (l == loc) = false := decide_eq_false hne
    dsimp [afterWriteNA, View.bump]
    rw [hbeq]
    exact hAtom.view_eq l hnon
  atomDisj := hAtom.atomDisj

/-- Coexistence Theorem 1 (`LoanRel.preserved_by_raw_write`):
    Writing a raw pointer at `locRaw` (`rawOwn rawId = some mvOld`) preserves
    `LoanRel` across all active `&mut` loans and `&` shared references automatically. -/
theorem LoanRel.preserved_by_raw_write {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {rawId locRaw : Nat} {mvOld mvNew : MirVal}
    (hLoan : LoanRel env loans mem)
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hownRaw : rawOwn rawId = some mvOld)
    (hrloc : env.rawLoc rawId = some locRaw) :
    LoanRel env loans (afterWriteNA mem locRaw mvNew) where
  activeOwn lid entry hlookup hact hfrz := by
    have ⟨locLoan, mvLoan, hlocLoan, hsc, hownLoan⟩ :=
      hLoan.activeOwn lid entry hlookup hact hfrz
    have hne : locLoan ≠ locRaw :=
      (hRaw.disjointRawLoans rawId mvOld lid entry locRaw locLoan
        (Or.inl hownRaw) hlookup hact hfrz hrloc hlocLoan).symm
    exact ⟨locLoan, mvLoan, hlocLoan, hsc, OwnLoc.afterWriteNA_other hne hownLoan mvNew⟩
  disjointActive := hLoan.disjointActive
  sharedOwn locShared n hsh := by
    have hne : locShared ≠ locRaw :=
      (hRaw.disjointRawShared rawId locRaw locShared n hrloc hsh).symm
    exact ReadOwnLoc.afterWriteNA_other hne (hLoan.sharedOwn locShared n hsh) mvNew
  disjointShared := hLoan.disjointShared

theorem RawRel.of_writeNA_raw {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {rawId locRaw : Nat} {mvOld mvNew : MirVal}
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hownRaw : rawOwn rawId = some mvOld)
    (hrloc : env.rawLoc rawId = some locRaw)
    (hOwnMem : OwnLoc mem locRaw mvOld) :
    RawRel env loans (updateRawOwn rawOwn rawId (some mvNew)) relOwn
      (afterWriteNA mem locRaw mvNew) where
  rawOwnLoc r mv hr := by
    unfold updateRawOwn at hr
    cases hb : (r == rawId) with
    | true =>
      rw [hb] at hr; injection hr with heq; subst heq
      have hr_eq : r = rawId := of_decide_eq_true hb
      subst hr_eq
      exact ⟨locRaw, hrloc, OwnLoc.afterWriteNA_self hOwnMem mvNew⟩
    | false =>
      rw [hb] at hr
      have hr_ne : r ≠ rawId := of_decide_eq_false hb
      have ⟨loc', hrloc', hown'⟩ := hRaw.rawOwnLoc r mv hr
      have hne : loc' ≠ locRaw := hRaw.disjointRaw r rawId loc' locRaw hr_ne hrloc' hrloc
      exact ⟨loc', hrloc', OwnLoc.afterWriteNA_other hne hown' mvNew⟩
  relOwnLoc r reqTs mv hr := by
    have ⟨loc', hrloc', hrel'⟩ := hRaw.relOwnLoc r reqTs mv hr
    have hr_ne : r ≠ rawId := by
      intro heq; subst heq
      exact hRaw.exclusiveRawRel r mvOld (reqTs, mv) hownRaw hr
    have hne : loc' ≠ locRaw := hRaw.disjointRaw r rawId loc' locRaw hr_ne hrloc' hrloc
    exact ⟨loc', hrloc', ReleaseGuarded.afterWriteNA_other hne hrel' mvNew⟩
  disjointRaw := hRaw.disjointRaw
  disjointRawShared := hRaw.disjointRawShared
  disjointRawLoans r mv lid entry loc' locLoan hown hl ha hf hrloc' hlocLoan := by
    cases hown with
    | inl hr =>
      unfold updateRawOwn at hr
      cases hb : (r == rawId) with
      | true =>
        have hr_eq : r = rawId := of_decide_eq_true hb
        subst hr_eq
        exact hRaw.disjointRawLoans r mvOld lid entry loc' locLoan (Or.inl hownRaw) hl ha hf hrloc' hlocLoan
      | false =>
        rw [hb] at hr
        exact hRaw.disjointRawLoans r mv lid entry loc' locLoan (Or.inl hr) hl ha hf hrloc' hlocLoan
    | inr hrel =>
      exact hRaw.disjointRawLoans r mv lid entry loc' locLoan (Or.inr hrel) hl ha hf hrloc' hlocLoan
  exclusiveRawRel r mv p hr hrel := by
    unfold updateRawOwn at hr
    cases hb : (r == rawId) with
    | true =>
      have hr_eq : r = rawId := of_decide_eq_true hb
      subst hr_eq
      exact hRaw.exclusiveRawRel r mvOld p hownRaw hrel
    | false =>
      rw [hb] at hr
      exact hRaw.exclusiveRawRel r mv p hr hrel

theorem AtomRel.of_writeNA_raw {env : SpatialEnv} {atomMsgs : List AtomicMsg}
    {atomView : View} {mem : MemState} {rawId locRaw : Nat} (mvNew : MirVal)
    (hAtom : AtomRel env atomMsgs atomView mem)
    (hrloc : env.rawLoc rawId = some locRaw) :
    AtomRel env atomMsgs atomView (afterWriteNA mem locRaw mvNew) where
  msgs_eq := hAtom.msgs_eq
  view_eq l hnon := by
    have hne : l ≠ locRaw := by
      intro heq
      subst heq
      exact hnon.2 rawId hrloc
    have hbeq : (l == locRaw) = false := decide_eq_false hne
    dsimp [afterWriteNA, View.bump]
    rw [hbeq]
    exact hAtom.view_eq l hnon
  atomDisj := hAtom.atomDisj

/-- Coexistence Theorem 2 (`LoanRel.preserved_by_atomic_load`):
    Any weak-memory atomic load (`Relaxed` or `Acquire`) automatically preserves
    `LoanRel` across all active `&mut` loans and `&` shared references with
    zero disjointness side-conditions. -/
theorem LoanRel.preserved_by_atomic_load {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {mem : MemState} (ord : AtomicOrdering) (msg : AtomicMsg)
    (hLoan : LoanRel env loans mem) :
    LoanRel env loans (mem.applyAtomicLoad ord msg) where
  activeOwn lid entry hlookup hact hfrz := by
    have ⟨loc, mv, hloc, hsc, hown⟩ := hLoan.activeOwn lid entry hlookup hact hfrz
    exact ⟨loc, mv, hloc, hsc, OwnLoc.preserved_by_atomic_load ord msg hown⟩
  disjointActive := hLoan.disjointActive
  sharedOwn loc n hsh := ReadOwnLoc.preserved_by_atomic_load ord msg (hLoan.sharedOwn loc n hsh)
  disjointShared := hLoan.disjointShared

theorem RawRel.of_atomicLoad {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn rawOwn' : Nat → Option MirVal}
    {relOwn relOwn' : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {ord : AtomicOrdering} {msg : AtomicMsg}
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hAcq : AcquireExt env ord msg rawOwn relOwn rawOwn' relOwn') :
    RawRel env loans rawOwn' relOwn' (mem.applyAtomicLoad ord msg) := by
  cases hAcq with
  | refl =>
    exact {
      rawOwnLoc := fun r mv hr => by
        have ⟨locRaw, hrloc, hown⟩ := hRaw.rawOwnLoc r mv hr
        exact ⟨locRaw, hrloc, OwnLoc.preserved_by_atomic_load ord msg hown⟩
      relOwnLoc := fun r reqTs mv hr => by
        have ⟨locRaw, hrloc, hrel⟩ := hRaw.relOwnLoc r reqTs mv hr
        exact ⟨locRaw, hrloc, ReleaseGuarded.preserved_by_atomic_load ord msg hrel⟩
      disjointRaw := hRaw.disjointRaw
      disjointRawShared := hRaw.disjointRawShared
      disjointRawLoans := hRaw.disjointRawLoans
      exclusiveRawRel := hRaw.exclusiveRawRel
    }
  | transfer acqId locAcq reqTs mvAcq hord hrlocAcq hrelAcq hsync =>
    subst hord
    exact {
      rawOwnLoc := fun r mv hr => by
        unfold updateRawOwn at hr
        cases hb : (r == acqId) with
        | true =>
          rw [hb] at hr; injection hr with heq; subst heq
          have hr_eq : r = acqId := of_decide_eq_true hb
          subst hr_eq
          have ⟨loc', hrloc', hrel'⟩ := hRaw.relOwnLoc r reqTs mvAcq hrelAcq
          rw [hrlocAcq] at hrloc'; injection hrloc' with hloc_eq
          rw [← hloc_eq] at hrel'
          exact ⟨locAcq, hrlocAcq, OwnLoc.transfer_acquire msg hrel' hsync⟩
        | false =>
          rw [hb] at hr
          have ⟨loc', hrloc', hown'⟩ := hRaw.rawOwnLoc r mv hr
          exact ⟨loc', hrloc', OwnLoc.preserved_by_atomic_load .acquire msg hown'⟩
      relOwnLoc := fun r ts mv hr => by
        unfold updateRelOwn at hr
        cases hb : (r == acqId) with
        | true => rw [hb] at hr; cases hr
        | false =>
          rw [hb] at hr
          have ⟨loc', hrloc', hrel'⟩ := hRaw.relOwnLoc r ts mv hr
          exact ⟨loc', hrloc', ReleaseGuarded.preserved_by_atomic_load .acquire msg hrel'⟩
      disjointRaw := hRaw.disjointRaw
      disjointRawShared := hRaw.disjointRawShared
      disjointRawLoans := fun r mv lid entry locRaw locLoan hown hl ha hf hrloc hlocLoan => by
        have hownOrig : rawOwn r = some mv ∨ ∃ ts, relOwn r = some (ts, mv) := by
          cases hown with
          | inl hr =>
            unfold updateRawOwn at hr
            cases hb : (r == acqId) with
            | true =>
              rw [hb] at hr; injection hr with heq; subst heq
              have hr_eq : r = acqId := of_decide_eq_true hb
              subst hr_eq
              exact Or.inr ⟨reqTs, hrelAcq⟩
            | false =>
              rw [hb] at hr
              exact Or.inl hr
          | inr hrel =>
            have ⟨ts, hts⟩ := hrel
            unfold updateRelOwn at hts
            cases hb : (r == acqId) with
            | true => rw [hb] at hts; cases hts
            | false =>
              rw [hb] at hts
              exact Or.inr ⟨ts, hts⟩
        exact hRaw.disjointRawLoans r mv lid entry locRaw locLoan hownOrig hl ha hf hrloc hlocLoan
      exclusiveRawRel := fun r mv p hr hrel => by
        unfold updateRawOwn at hr
        unfold updateRelOwn at hrel
        cases hb : (r == acqId) with
        | true => rw [hb] at hrel; cases hrel
        | false =>
          rw [hb] at hr hrel
          exact hRaw.exclusiveRawRel r mv p hr hrel
    }

theorem AtomRel.of_atomicLoad {env : SpatialEnv} {atomMsgs : List AtomicMsg}
    {atomView : View} {mem : MemState} (ord : AtomicOrdering) (msg : AtomicMsg)
    (hAtom : AtomRel env atomMsgs atomView mem) :
    AtomRel env atomMsgs (applyViewLoad ord atomView msg) (mem.applyAtomicLoad ord msg) where
  msgs_eq := hAtom.msgs_eq
  view_eq l hnon := by
    have hcur : mem.curView l = atomView l := hAtom.view_eq l hnon
    have hbump : View.bump mem.curView msg.loc msg.ts l = View.bump atomView msg.loc msg.ts l := by
      dsimp [View.bump]
      rw [hcur]
    cases ord with
    | relaxed =>
      exact hbump
    | acquire =>
      dsimp [MemState.applyAtomicLoad, applyViewLoad, View.join]
      rw [hbump]
  atomDisj := hAtom.atomDisj

/-- Coexistence Theorem 3 (`promoteRaw` / `reborrowRaw` conservation):
    Moving `rawId` (`locRaw`) out of `rawOwn` and activating `loanId` in `loans`
    preserves `LoanRel` and `RawRel`. -/
theorem promoteRaw_preserves_loanRel {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {rawId loanId locRaw v0 : Nat}
    (hLoan : LoanRel env loans mem)
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hownRaw : rawOwn rawId = some (.usize v0))
    (hrloc : env.rawLoc rawId = some locRaw)
    (hlloc : env.loanLoc loanId = some locRaw)
    (hOwnMem : OwnLoc mem locRaw (.usize v0)) :
    LoanRel env (updateLoan loans loanId (some (rawLoanEntry rawId v0))) mem where
  activeOwn lid entry hlookup hact hfrz := by
    unfold updateLoan at hlookup
    cases hb : (lid == loanId) with
    | true =>
      rw [hb] at hlookup; injection hlookup with heq; subst heq
      have hlid_eq : lid = loanId := of_decide_eq_true hb
      subst hlid_eq
      exact ⟨locRaw, .usize v0, hlloc, rfl, hOwnMem⟩
    | false =>
      rw [hb] at hlookup
      exact hLoan.activeOwn lid entry hlookup hact hfrz
  disjointActive lid₁ lid₂ e₁ e₂ loc₁ loc₂ hne hl₁ ha₁ hf₁ hl₂ ha₂ hf₂ hloc₁ hloc₂ := by
    unfold updateLoan at hl₁ hl₂
    cases hb₁ : (lid₁ == loanId) with
    | true =>
      have hlid₁ : lid₁ = loanId := of_decide_eq_true hb₁
      subst hlid₁
      cases hb₂ : (lid₂ == lid₁) with
      | true => exact False.elim (hne (of_decide_eq_true hb₂).symm)
      | false =>
        rw [hb₂] at hl₂
        rw [hlloc] at hloc₁; injection hloc₁ with h₁
        rw [← h₁]
        exact hRaw.disjointRawLoans rawId (.usize v0) lid₂ e₂ locRaw loc₂
          (Or.inl hownRaw) hl₂ ha₂ hf₂ hrloc hloc₂
    | false =>
      rw [hb₁] at hl₁
      cases hb₂ : (lid₂ == loanId) with
      | true =>
        have hlid₂ : lid₂ = loanId := of_decide_eq_true hb₂
        subst hlid₂
        rw [hlloc] at hloc₂; injection hloc₂ with h₂
        rw [← h₂]
        exact (hRaw.disjointRawLoans rawId (.usize v0) lid₁ e₁ locRaw loc₁
          (Or.inl hownRaw) hl₁ ha₁ hf₁ hrloc hloc₁).symm
      | false =>
        rw [hb₂] at hl₂
        exact hLoan.disjointActive lid₁ lid₂ e₁ e₂ loc₁ loc₂ hne hl₁ ha₁ hf₁ hl₂ ha₂ hf₂ hloc₁ hloc₂
  sharedOwn := hLoan.sharedOwn
  disjointShared lid entry locMut locShared n hl ha hf hlocMut hsh := by
    unfold updateLoan at hl
    cases hb : (lid == loanId) with
    | true =>
      have hlid : lid = loanId := of_decide_eq_true hb
      subst hlid
      rw [hlloc] at hlocMut; injection hlocMut with h₁
      rw [← h₁]
      exact hRaw.disjointRawShared rawId locRaw locShared n hrloc hsh
    | false =>
      rw [hb] at hl
      exact hLoan.disjointShared lid entry locMut locShared n hl ha hf hlocMut hsh

theorem promoteRaw_preserves_rawRel {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {rawId loanId locRaw v0 : Nat}
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hownRaw : rawOwn rawId = some (.usize v0))
    (hrloc : env.rawLoc rawId = some locRaw)
    (hlloc : env.loanLoc loanId = some locRaw) :
    RawRel env (updateLoan loans loanId (some (rawLoanEntry rawId v0)))
      (updateRawOwn rawOwn rawId none) relOwn mem where
  rawOwnLoc r mv hr := by
    unfold updateRawOwn at hr
    cases hb : (r == rawId) with
    | true => rw [hb] at hr; cases hr
    | false =>
      rw [hb] at hr
      exact hRaw.rawOwnLoc r mv hr
  relOwnLoc := hRaw.relOwnLoc
  disjointRaw := hRaw.disjointRaw
  disjointRawShared := hRaw.disjointRawShared
  disjointRawLoans r mv lid entry loc' locLoan hown hl ha hf hrloc' hlocLoan := by
    have hr_ne_rawId : r ≠ rawId ∧ (rawOwn r = some mv ∨ ∃ ts, relOwn r = some (ts, mv)) := by
      cases hown with
      | inl hr =>
        unfold updateRawOwn at hr
        cases hb : (r == rawId) with
        | true => rw [hb] at hr; cases hr
        | false =>
          rw [hb] at hr
          exact ⟨of_decide_eq_false hb, Or.inl hr⟩
      | inr hrel =>
        have ⟨ts, hts⟩ := hrel
        refine ⟨?_, Or.inr ⟨ts, hts⟩⟩
        intro heq; subst heq
        exact hRaw.exclusiveRawRel r (.usize v0) (ts, mv) hownRaw hts
    unfold updateLoan at hl
    cases hb : (lid == loanId) with
    | true =>
      have hlid : lid = loanId := of_decide_eq_true hb
      subst hlid
      rw [hlloc] at hlocLoan; injection hlocLoan with h₂; subst h₂
      exact hRaw.disjointRaw r rawId loc' locRaw hr_ne_rawId.1 hrloc' hrloc
    | false =>
      rw [hb] at hl
      exact hRaw.disjointRawLoans r mv lid entry loc' locLoan hr_ne_rawId.2 hl ha hf hrloc' hlocLoan
  exclusiveRawRel r mv p hr hrel := by
    unfold updateRawOwn at hr
    cases hb : (r == rawId) with
    | true => rw [hb] at hr; cases hr
    | false =>
      rw [hb] at hr
      exact hRaw.exclusiveRawRel r mv p hr hrel

/-- Coexistence Theorem 4 (`releaseRaw` / `endRawLoan` conservation):
    Deactivating `loanId` in `loans` and restoring `rawId` (`locRaw`) to `rawOwn`
    preserves `LoanRel` and `RawRel`. -/
theorem releaseRaw_preserves_loanRel {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {mem : MemState} {loanId : Nat} {entry : LoanEntry}
    (hLoan : LoanRel env loans mem) :
    LoanRel env (updateLoan loans loanId (some { entry with active := false })) mem where
  activeOwn lid e hl ha hf := by
    unfold updateLoan at hl
    cases hb : (lid == loanId) with
    | true => rw [hb] at hl; injection hl with he; subst he; cases ha
    | false => rw [hb] at hl; exact hLoan.activeOwn lid e hl ha hf
  disjointActive lid₁ lid₂ e₁ e₂ loc₁ loc₂ hne hl₁ ha₁ hf₁ hl₂ ha₂ hf₂ hloc₁ hloc₂ := by
    unfold updateLoan at hl₁ hl₂
    cases hb₁ : (lid₁ == loanId) with
    | true => rw [hb₁] at hl₁; injection hl₁ with he₁; subst he₁; cases ha₁
    | false =>
      rw [hb₁] at hl₁
      cases hb₂ : (lid₂ == loanId) with
      | true => rw [hb₂] at hl₂; injection hl₂ with he₂; subst he₂; cases ha₂
      | false =>
        rw [hb₂] at hl₂
        exact hLoan.disjointActive lid₁ lid₂ e₁ e₂ loc₁ loc₂ hne hl₁ ha₁ hf₁ hl₂ ha₂ hf₂ hloc₁ hloc₂
  sharedOwn := hLoan.sharedOwn
  disjointShared lid e locMut locShared n hl ha hf hlocMut hsh := by
    unfold updateLoan at hl
    cases hb : (lid == loanId) with
    | true => rw [hb] at hl; injection hl with he; subst he; cases ha
    | false => rw [hb] at hl; exact hLoan.disjointShared lid e locMut locShared n hl ha hf hlocMut hsh

theorem releaseRaw_preserves_rawRel {env : SpatialEnv} {loans : Nat → Option LoanEntry}
    {rawOwn : Nat → Option MirVal} {relOwn : Nat → Option (Timestamp × MirVal)}
    {mem : MemState} {rawId loanId locRaw : Nat} {entry : LoanEntry} {mvFinal : MirVal}
    (hLoan : LoanRel env loans mem)
    (hRaw : RawRel env loans rawOwn relOwn mem)
    (hlookup : loans loanId = some entry)
    (hact : entry.active = true)
    (hfrz : entry.frozen = false)
    (hrloc : env.rawLoc rawId = some locRaw)
    (hlloc : env.loanLoc loanId = some locRaw)
    (hrelNone : relOwn rawId = none)
    (hOwnFinal : OwnLoc mem locRaw mvFinal) :
    RawRel env (updateLoan loans loanId (some { entry with active := false }))
      (updateRawOwn rawOwn rawId (some mvFinal)) relOwn mem where
  rawOwnLoc r mv hr := by
    unfold updateRawOwn at hr
    cases hb : (r == rawId) with
    | true =>
      rw [hb] at hr; injection hr with heq; subst heq
      have hr_eq : r = rawId := of_decide_eq_true hb
      subst hr_eq
      exact ⟨locRaw, hrloc, hOwnFinal⟩
    | false =>
      rw [hb] at hr
      exact hRaw.rawOwnLoc r mv hr
  relOwnLoc := hRaw.relOwnLoc
  disjointRaw := hRaw.disjointRaw
  disjointRawShared := hRaw.disjointRawShared
  disjointRawLoans r mv lid e loc' locLoan hown hl ha hf hrloc' hlocLoan := by
    unfold updateLoan at hl
    cases hbl : (lid == loanId) with
    | true => rw [hbl] at hl; injection hl with he; subst he; cases ha
    | false =>
      rw [hbl] at hl
      have hlid_ne : lid ≠ loanId := of_decide_eq_false hbl
      cases hown with
      | inl hr =>
        unfold updateRawOwn at hr
        cases hbr : (r == rawId) with
        | true =>
          have hr_eq : r = rawId := of_decide_eq_true hbr
          subst hr_eq
          rw [hrloc] at hrloc'; injection hrloc' with h₁
          rw [← h₁]
          exact hLoan.disjointActive loanId lid entry e locRaw locLoan
            hlid_ne.symm hlookup hact hfrz hl ha hf hlloc hlocLoan
        | false =>
          rw [hbr] at hr
          exact hRaw.disjointRawLoans r mv lid e loc' locLoan (Or.inl hr) hl ha hf hrloc' hlocLoan
      | inr hrel =>
        exact hRaw.disjointRawLoans r mv lid e loc' locLoan (Or.inr hrel) hl ha hf hrloc' hlocLoan
  exclusiveRawRel r mv p hr hrel := by
    unfold updateRawOwn at hr
    cases hb : (r == rawId) with
    | true =>
      have hr_eq : r = rawId := of_decide_eq_true hb
      subst hr_eq
      rw [hrelNone] at hrel; cases hrel
    | false =>
      rw [hb] at hr
      exact hRaw.exclusiveRawRel r mv p hr hrel
/-!
## 6. Universal Hint-Independent Soundness (`evalSymTree_sound`) and `FuncTreeLang` Refinement Bridge
-/

theorem evalSafeSymStmt_sound {env : SpatialEnv}
    {rawOwn : Nat → Option MirVal}
    {relOwn : Nat → Option (Timestamp × MirVal)}
    {atomMsgs : List AtomicMsg}
    {atomView : View}
    {sym sym' : SymState} {conc : MirState} {stmt : Stmt}
    (hState : StateRel env rawOwn relOwn atomMsgs atomView sym conc)
    (hSafe : evalSafeSymStmt sym stmt = some sym') :
    ∃ conc',
      evalMirStmt conc stmt = .step () conc' ∧
      StateRel env rawOwn relOwn atomMsgs atomView sym' conc' := by
  cases stmt with
  | derefRaw _ _ | assignDerefRaw _ _ | reborrowRawToMut _ _ =>
    cases hSafe
  | nop =>
    dsimp [evalSafeSymStmt] at hSafe
    injection hSafe with hsym'
    subst hsym'
    refine ⟨{ conc with stmtIdx := conc.stmtIdx + 1 }, rfl, ?_⟩
    exact {
      block_eq := hState.block_eq
      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
      localRel := hState.localRel
      loanRel := hState.loanRel
      rawRel := hState.rawRel
      atomRel := hState.atomRel
    }
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalSafeSymStmt] at hSafe
      cases hOp : evalSymOperand sym.locals op with
      | none => rw [hOp] at hSafe; cases hSafe
      | some sv =>
        rw [hOp] at hSafe
        injection hSafe with hsym'
        subst hsym'
        have ⟨mv, hConcOp, hVal⟩ := evalSymOperand_sound hState.localRel hOp
        refine ⟨{ conc with
          locals := updateLocal conc.locals dst (some mv)
          stmtIdx := conc.stmtIdx + 1 }, ?_, ?_⟩
        · dsimp [evalMirStmt]; rw [hConcOp]
        · exact {
            block_eq := hState.block_eq
            stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
            localRel := LocalRel.update_some hState.localRel dst hVal
            loanRel := hState.loanRel
            rawRel := hState.rawRel
            atomRel := hState.atomRel
          }
    | deref src =>
      dsimp [evalSafeSymStmt] at hSafe
      cases hsrc : sym.locals src with
      | none => rw [hsrc] at hSafe; cases hSafe
      | some svSrc =>
        rw [hsrc] at hSafe
        cases svSrc with
        | usize _ | bool _ | unit | rawPtr _ | atomicRef _ => cases hSafe
        | refShared n =>
          injection hSafe with hsym'
          subst hsym'
          have ⟨mvSrc, hconcSrc, hvalSrc⟩ := hState.localRel src (.refShared n) hsrc
          have ⟨loc, hsh, hmvSrc⟩ := hvalSrc
          subst hmvSrc
          have hReadOwn := hState.loanRel.sharedOwn loc n hsh
          have hRead := ReadOwnLoc.readNA_eq hReadOwn
          refine ⟨{ conc with
            locals := updateLocal conc.locals dst (some (.usize n))
            mem := afterReadNA conc.mem loc
            stmtIdx := conc.stmtIdx + 1 }, ?_, ?_⟩
          · dsimp [evalMirStmt]; rw [hconcSrc]; dsimp; rw [hRead]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localRel := LocalRel.update_some hState.localRel dst rfl
              loanRel := LoanRel.of_readNA loc hState.loanRel
              rawRel := RawRel.of_readNA_shared hState.rawRel hsh
              atomRel := AtomRel.of_readNA loc hState.atomRel
            }
        | borrow lid =>
          dsimp at hSafe
          cases hloan : sym.loans lid with
          | none => rw [hloan] at hSafe; cases hSafe
          | some entry =>
            rw [hloan] at hSafe
            dsimp at hSafe
            cases hact : entry.active with
            | false => rw [hact] at hSafe; cases hSafe
            | true =>
              rw [hact] at hSafe
              cases hfrz : entry.frozen with
              | true => rw [hfrz] at hSafe; cases hSafe
              | false =>
                rw [hfrz] at hSafe
                dsimp at hSafe
                injection hSafe with hsym'
                subst hsym'
                have ⟨mvSrc, hconcSrc, hvalSrc⟩ := hState.localRel src (.borrow lid) hsrc
                have ⟨loc1, hloc1, hmvSrc⟩ := hvalSrc
                subst hmvSrc
                have ⟨loc, mv, hloc, hsc, hown⟩ := hState.loanRel.activeOwn lid entry hloan hact hfrz
                rw [hloc] at hloc1; injection hloc1 with hloc_eq; subst hloc_eq
                have hRead := OwnLoc.readNA_eq hown
                have hValCur : ValRel env entry.curVal mv := ValRel.of_toScalarMirVal env hsc
                refine ⟨{ conc with
                  locals := updateLocal conc.locals dst (some mv)
                  mem := afterReadNA conc.mem loc
                  stmtIdx := conc.stmtIdx + 1 }, ?_, ?_⟩
                · dsimp [evalMirStmt]; rw [hconcSrc]; dsimp; rw [hRead]
                · exact {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localRel := LocalRel.update_some hState.localRel dst hValCur
                    loanRel := LoanRel.of_readNA loc hState.loanRel
                    rawRel := RawRel.of_readNA_loan hState.rawRel hloan hact hfrz hloc
                    atomRel := AtomRel.of_readNA loc hState.atomRel
                  }
    | binaryOp op lhs rhs =>
      dsimp [evalSafeSymStmt] at hSafe
      cases hOp1 : evalSymOperand sym.locals lhs with
      | none => rw [hOp1] at hSafe; cases hSafe
      | some v1 =>
        rw [hOp1] at hSafe
        cases hOp2 : evalSymOperand sym.locals rhs with
        | none => rw [hOp2] at hSafe; cases hSafe
        | some v2 =>
          rw [hOp2] at hSafe
          dsimp at hSafe
          cases hBin : evalSymBinOp op v1 v2 with
          | none => rw [hBin] at hSafe; cases hSafe
          | some res =>
            rw [hBin] at hSafe
            injection hSafe with hsym'
            subst hsym'
            have ⟨mv1, hConcOp1, hVal1⟩ := evalSymOperand_sound hState.localRel hOp1
            have ⟨mv2, hConcOp2, hVal2⟩ := evalSymOperand_sound hState.localRel hOp2
            have ⟨mres, hConcBin, hValRes⟩ := evalSymBinOp_sound hVal1 hVal2 hBin
            refine ⟨{ conc with
              locals := updateLocal conc.locals dst (some mres)
              stmtIdx := conc.stmtIdx + 1 }, ?_, ?_⟩
            · dsimp [evalMirStmt]; rw [hConcOp1, hConcOp2]; dsimp; rw [hConcBin]
            · exact {
                block_eq := hState.block_eq
                stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                localRel := LocalRel.update_some hState.localRel dst hValRes
                loanRel := hState.loanRel
                rawRel := hState.rawRel
                atomRel := hState.atomRel
              }
  | assignDeref dst op =>
    dsimp [evalSafeSymStmt] at hSafe
    cases hOp : evalSymOperand sym.locals op with
    | none => rw [hOp] at hSafe; cases hSafe
    | some sv =>
      rw [hOp] at hSafe
      cases hdst : sym.locals dst with
      | none => rw [hdst] at hSafe; cases hSafe
      | some svDst =>
        rw [hdst] at hSafe
        cases svDst with
        | usize _ | bool _ | unit | refShared _ | rawPtr _ | atomicRef _ => cases hSafe
        | borrow lid =>
          dsimp at hSafe
          cases hsc : sv.toScalarMirVal with
          | none => rw [hsc] at hSafe; cases hSafe
          | some mvNew =>
            rw [hsc] at hSafe
            cases hloan : sym.loans lid with
            | none => rw [hloan] at hSafe; cases hSafe
            | some entry =>
              rw [hloan] at hSafe
              dsimp at hSafe
              cases hact : entry.active with
              | false => rw [hact] at hSafe; cases hSafe
              | true =>
                rw [hact] at hSafe
                cases hfrz : entry.frozen with
                | true => rw [hfrz] at hSafe; cases hSafe
                | false =>
                  rw [hfrz] at hSafe
                  dsimp at hSafe
                  injection hSafe with hsym'
                  subst hsym'
                  have ⟨mvOp, hConcOp, hValOp⟩ := evalSymOperand_sound hState.localRel hOp
                  have hmv_eq : mvOp = mvNew := ValRel.toScalarMirVal_eq hValOp hsc
                  subst hmv_eq
                  have ⟨mvDst, hconcDst, hvalDst⟩ := hState.localRel dst (.borrow lid) hdst
                  have ⟨loc1, hloc1, hmvDst⟩ := hvalDst
                  subst hmvDst
                  have ⟨loc, mvOld, hloc, _, hownOld⟩ := hState.loanRel.activeOwn lid entry hloan hact hfrz
                  rw [hloc] at hloc1; injection hloc1 with hloc_eq; subst hloc_eq
                  have hWrite := OwnLoc.writeNA_eq hownOld (vNew := mvOp)
                  have hentry_eq :
                      { entry with curVal := sv, frozen := false, active := true } =
                      { entry with curVal := sv } := by
                    cases entry; dsimp at hact hfrz ⊢; subst hact hfrz; rfl
                  refine ⟨{ conc with
                    mem := afterWriteNA conc.mem loc mvOp
                    stmtIdx := conc.stmtIdx + 1 }, ?_, ?_⟩
                  · dsimp [evalMirStmt]; rw [hConcOp, hconcDst]; dsimp; rw [hWrite]
                  · exact {
                      block_eq := hState.block_eq
                      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                      localRel := hState.localRel
                      loanRel := by
                        dsimp; rw [hentry_eq]
                        exact LoanRel.update_curVal hState.loanRel hloan hact hfrz hloc hownOld hsc
                      rawRel := by
                        dsimp; rw [hentry_eq]
                        exact RawRel.of_writeNA_loan hState.rawRel hloan hact hfrz hloc
                      atomRel := AtomRel.of_writeNA_loan mvOp hState.atomRel hloc
                    }

/-- Terminal postcondition lifting `Post : RetSummary → (Nat → Option MirVal) → Prop`
    to concrete `TermOutcome`: guarantees that `termOut.retVal` equals `summary.retVal`,
    parameter loan `1` satisfies `OwnLoc termOut.mem loc1 mv1`, and every owned raw
    pointer in `rawOwnFinal` satisfies `OwnLoc termOut.mem locRaw mv`. -/
def TerminalPost (env : SpatialEnv)
    (Post : RetSummary → (Nat → Option MirVal) → Prop)
    (termOut : TermOutcome) : Prop :=
  ∃ summary rawOwnFinal,
    Post summary rawOwnFinal ∧
    termOut.retVal = summary.retVal ∧
    (∀ loc1 mv1, env.loanLoc 1 = some loc1 → summary.loan1Val = some mv1 →
      OwnLoc termOut.mem loc1 mv1) ∧
    (∀ rawId locRaw mv, env.rawLoc rawId = some locRaw → rawOwnFinal rawId = some mv →
      OwnLoc termOut.mem locRaw mv)

theorem visibleAtomicMsgs_eq_visibleMsgsAt {env : SpatialEnv}
    {atomMsgs : List AtomicMsg} {atomView : View} {mem : MemState}
    {atomId locAtom : Nat}
    (hAtom : AtomRel env atomMsgs atomView mem)
    (haloc : env.atomicLoc atomId = some locAtom) :
    mem.visibleAtomicMsgs locAtom = visibleMsgsAt atomMsgs (atomView locAtom) locAtom := by
  have hnon := hAtom.atomDisj atomId locAtom haloc
  unfold MemState.visibleAtomicMsgs
  rw [hAtom.msgs_eq, hAtom.view_eq locAtom hnon]

/-- Universal Hint-Independent Soundness (`evalSymTree_sound`):
    For **every** untrusted translation plan `plan : TransPlan` and **every**
    `body : MirBody`, if `StateRel` holds at `(sym, conc)` and the residual
    verification condition `symWP (evalSymTree plan body sym)` holds, then
    `conc` safely executes `body` and satisfies `TerminalPost env Post`. -/
theorem evalSymTree_sound (plan : TransPlan) (body : MirBody) :
    ∀ {env : SpatialEnv}
      {rawOwn : Nat → Option MirVal}
      {relOwn : Nat → Option (Timestamp × MirVal)}
      {atomMsgs : List AtomicMsg}
      {atomView : View}
      {sym : SymState} {conc : MirState}
      {Post : RetSummary → (Nat → Option MirVal) → Prop},
      StateRel env rawOwn relOwn atomMsgs atomView sym conc →
      symWP (evalSymTree plan body sym) env rawOwn relOwn atomMsgs atomView Post →
      SafeAndSatisfies body conc (TerminalPost env Post) := by
  induction plan with
  | fail =>
    intro _ _ _ _ _ _ _ _ _ hWP
    exact False.elim hWP
  | ret =>
    intro env rawOwn relOwn atomMsgs atomView sym conc Post hState hWP
    dsimp [evalSymTree] at hWP
    cases hRet : evalReturnSummary body sym with
    | none => rw [hRet] at hWP; exact False.elim hWP
    | some summary =>
      rw [hRet] at hWP
      dsimp [symWP] at hWP
      unfold evalReturnSummary at hRet
      cases hbb : listGet body.blocks sym.block with
      | none => rw [hbb] at hRet; cases hRet
      | some bb =>
        rw [hbb] at hRet
        dsimp at hRet
        cases hstmt : listGet bb.stmts sym.stmtIdx with
        | some _ => rw [hstmt] at hRet; cases hRet
        | none =>
          rw [hstmt] at hRet
          cases hterm : bb.terminator with
          | goto _ | switchInt _ _ _ | callAtomicLoad _ _ _ _ =>
            rw [hterm] at hRet; cases hRet
          | return_ =>
            rw [hterm] at hRet
            dsimp at hRet
            cases h0 : sym.locals 0 with
            | none => rw [h0] at hRet; cases hRet
            | some sv0 =>
              rw [h0] at hRet
              dsimp at hRet
              cases hsc : sv0.toScalarMirVal with
              | none => rw [hsc] at hRet; cases hRet
              | some retMv =>
                rw [hsc] at hRet
                dsimp at hRet
                injection hRet with hsum
                subst hsum
                have ⟨mv0, hconc0, hval0⟩ := hState.localRel 0 sv0 h0
                have hmv0_eq : mv0 = retMv := ValRel.toScalarMirVal_eq hval0 hsc
                subst hmv0_eq
                have hStepTerm : evalMirStep body conc =
                    .terminated (.normal { retVal := mv0, mem := conc.mem }) := by
                  unfold evalMirStep
                  rw [hState.block_eq, hbb]
                  dsimp
                  rw [hState.stmtIdx_eq, hstmt]
                  dsimp [evalMirTerminator]
                  rw [hterm]
                  dsimp
                  rw [hconc0]
                refine SafeAndSatisfies.of_terminated hStepTerm ⟨_, rawOwn, hWP, rfl, ?_, ?_⟩
                · intro loc1 mv1 hloc1 hl1
                  dsimp [extractLoan1Val] at hl1
                  cases hl : sym.loans 1 with
                  | none => rw [hl] at hl1; cases hl1
                  | some e1 =>
                    rw [hl] at hl1
                    dsimp at hl1
                    cases ha : e1.active with
                    | false => rw [ha] at hl1; cases hl1
                    | true =>
                      rw [ha] at hl1
                      cases hf : e1.frozen with
                      | true => rw [hf] at hl1; cases hl1
                      | false =>
                        rw [hf] at hl1
                        dsimp at hl1
                        have ⟨loc', mv', hloc', hsc', hown'⟩ :=
                          hState.loanRel.activeOwn 1 e1 hl ha hf
                        rw [hloc1] at hloc'; injection hloc' with heq1
                        rw [hl1] at hsc'; injection hsc' with heq2
                        rw [heq1, heq2]
                        exact hown'
                · intro rawId locRaw mv hrloc hraw
                  have ⟨loc', hrloc', hown'⟩ := hState.rawRel.rawOwnLoc rawId mv hraw
                  rw [hrloc] at hrloc'; injection hrloc' with heq
                  rw [heq]
                  exact hown'
  | step next ih =>
    intro env rawOwn relOwn atomMsgs atomView sym conc Post hState hWP
    dsimp [evalSymTree] at hWP
    cases hbb : listGet body.blocks sym.block with
    | none => rw [hbb] at hWP; exact False.elim hWP
    | some bb =>
      rw [hbb] at hWP
      dsimp at hWP
      cases hstmt : listGet bb.stmts sym.stmtIdx with
      | some stmt =>
        rw [hstmt] at hWP
        dsimp at hWP
        cases stmt with
        | reborrowRawToMut _ _ => exact False.elim hWP
        | derefRaw dst ptrLocal =>
          dsimp at hWP
          cases hptr : sym.locals ptrLocal with
          | none => rw [hptr] at hWP; exact False.elim hWP
          | some svPtr =>
            rw [hptr] at hWP
            cases svPtr with
            | usize _ | bool _ | unit | refShared _ | borrow _ | atomicRef _ =>
              exact False.elim hWP
            | rawPtr rawId =>
              dsimp [symWP] at hWP
              have ⟨v, hrawOwn, hWPNext⟩ := hWP
              have ⟨mvPtr, hconcPtr, hvalPtr⟩ := hState.localRel ptrLocal (.rawPtr rawId) hptr
              have ⟨locRaw, hrloc, hmvPtr⟩ := hvalPtr
              subst hmvPtr
              have ⟨locRaw', hrloc', hOwnMem⟩ := hState.rawRel.rawOwnLoc rawId (.usize v) hrawOwn
              rw [hrloc] at hrloc'; injection hrloc' with hloc_eq; subst hloc_eq
              have hRead := OwnLoc.readNA_eq hOwnMem
              have hbb' : listGet body.blocks conc.block = some bb := by rw [hState.block_eq]; exact hbb
              have hstmt' : listGet bb.stmts conc.stmtIdx = some (.derefRaw dst ptrLocal) := by
                rw [hState.stmtIdx_eq]; exact hstmt
              have hStep : evalMirStep body conc = .step () { conc with
                  locals := updateLocal conc.locals dst (some (.usize v))
                  mem := afterReadNA conc.mem locRaw
                  stmtIdx := conc.stmtIdx + 1 } := by
                unfold evalMirStep
                rw [hbb']
                dsimp
                rw [hstmt']
                dsimp [evalMirStmt]
                rw [hconcPtr]; dsimp; rw [hRead]
              have hState' : StateRel env rawOwn relOwn atomMsgs atomView
                  { sym with
                    locals := updateSymLocal sym.locals dst (some (.usize v))
                    stmtIdx := sym.stmtIdx + 1 }
                  { conc with
                    locals := updateLocal conc.locals dst (some (.usize v))
                    mem := afterReadNA conc.mem locRaw
                    stmtIdx := conc.stmtIdx + 1 } := {
                block_eq := hState.block_eq
                stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                localRel := LocalRel.update_some hState.localRel dst rfl
                loanRel := LoanRel.of_readNA locRaw hState.loanRel
                rawRel := RawRel.of_readNA_raw hState.rawRel hrawOwn hrloc
                atomRel := AtomRel.of_readNA locRaw hState.atomRel
              }
              exact SafeAndSatisfies.of_step hStep (ih hState' hWPNext)
        | assignDerefRaw ptrLocal op =>
          dsimp at hWP
          cases hOp : evalSymOperand sym.locals op with
          | none => rw [hOp] at hWP; exact False.elim hWP
          | some sv =>
            rw [hOp] at hWP
            cases hptr : sym.locals ptrLocal with
            | none => rw [hptr] at hWP; exact False.elim hWP
            | some svPtr =>
              rw [hptr] at hWP
              cases svPtr with
              | usize _ | bool _ | unit | refShared _ | borrow _ | atomicRef _ =>
                exact False.elim hWP
              | rawPtr rawId =>
                dsimp at hWP
                cases hsc : sv.toScalarMirVal with
                | none => rw [hsc] at hWP; exact False.elim hWP
                | some mvNew =>
                  rw [hsc] at hWP
                  dsimp [symWP] at hWP
                  have ⟨⟨mvOld, hrawOwn⟩, hWPNext⟩ := hWP
                  have ⟨mvOp, hConcOp, hValOp⟩ := evalSymOperand_sound hState.localRel hOp
                  have hmv_eq : mvOp = mvNew := ValRel.toScalarMirVal_eq hValOp hsc
                  subst hmv_eq
                  have ⟨mvPtr, hconcPtr, hvalPtr⟩ := hState.localRel ptrLocal (.rawPtr rawId) hptr
                  have ⟨locRaw, hrloc, hmvPtr⟩ := hvalPtr
                  subst hmvPtr
                  have ⟨locRaw', hrloc', hOwnMem⟩ := hState.rawRel.rawOwnLoc rawId mvOld hrawOwn
                  rw [hrloc] at hrloc'; injection hrloc' with hloc_eq; subst hloc_eq
                  have hWrite := OwnLoc.writeNA_eq hOwnMem (vNew := mvOp)
                  have hbb' : listGet body.blocks conc.block = some bb := by rw [hState.block_eq]; exact hbb
                  have hstmt' : listGet bb.stmts conc.stmtIdx = some (.assignDerefRaw ptrLocal op) := by
                    rw [hState.stmtIdx_eq]; exact hstmt
                  have hStep : evalMirStep body conc = .step () { conc with
                      mem := afterWriteNA conc.mem locRaw mvOp
                      stmtIdx := conc.stmtIdx + 1 } := by
                    unfold evalMirStep
                    rw [hbb']
                    dsimp
                    rw [hstmt']
                    dsimp [evalMirStmt]
                    rw [hConcOp, hconcPtr]; dsimp; rw [hWrite]
                  have hState' : StateRel env (updateRawOwn rawOwn rawId (some mvOp))
                      relOwn atomMsgs atomView
                      { sym with stmtIdx := sym.stmtIdx + 1 }
                      { conc with
                        mem := afterWriteNA conc.mem locRaw mvOp
                        stmtIdx := conc.stmtIdx + 1 } := {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localRel := hState.localRel
                    loanRel := LoanRel.preserved_by_raw_write hState.loanRel hState.rawRel hrawOwn hrloc
                    rawRel := RawRel.of_writeNA_raw hState.rawRel hrawOwn hrloc hOwnMem
                    atomRel := AtomRel.of_writeNA_raw mvOp hState.atomRel hrloc
                  }
                  exact SafeAndSatisfies.of_step hStep (ih hState' hWPNext)
        | assign dst rv =>
          dsimp at hWP
          cases hSafe : evalSafeSymStmt sym (.assign dst rv) with
          | none => rw [hSafe] at hWP; exact False.elim hWP
          | some sym' =>
            rw [hSafe] at hWP
            have ⟨conc', hMirStmt, hState'⟩ := evalSafeSymStmt_sound hState hSafe
            have hStep : evalMirStep body conc = .step () conc' := by
              unfold evalMirStep
              rw [hState.block_eq, hbb]; dsimp
              rw [hState.stmtIdx_eq, hstmt]; exact hMirStmt
            exact SafeAndSatisfies.of_step hStep (ih hState' hWP)
        | assignDeref dst op =>
          dsimp at hWP
          cases hSafe : evalSafeSymStmt sym (.assignDeref dst op) with
          | none => rw [hSafe] at hWP; exact False.elim hWP
          | some sym' =>
            rw [hSafe] at hWP
            have ⟨conc', hMirStmt, hState'⟩ := evalSafeSymStmt_sound hState hSafe
            have hStep : evalMirStep body conc = .step () conc' := by
              unfold evalMirStep
              rw [hState.block_eq, hbb]; dsimp
              rw [hState.stmtIdx_eq, hstmt]; exact hMirStmt
            exact SafeAndSatisfies.of_step hStep (ih hState' hWP)
        | nop =>
          dsimp at hWP
          cases hSafe : evalSafeSymStmt sym .nop with
          | none => rw [hSafe] at hWP; exact False.elim hWP
          | some sym' =>
            rw [hSafe] at hWP
            have ⟨conc', hMirStmt, hState'⟩ := evalSafeSymStmt_sound hState hSafe
            have hStep : evalMirStep body conc = .step () conc' := by
              unfold evalMirStep
              rw [hState.block_eq, hbb]; dsimp
              rw [hState.stmtIdx_eq, hstmt]; exact hMirStmt
            exact SafeAndSatisfies.of_step hStep (ih hState' hWP)
      | none =>
        rw [hstmt] at hWP
        dsimp at hWP
        cases hterm : bb.terminator with
        | return_ | switchInt _ _ _ =>
          rw [hterm] at hWP; exact False.elim hWP
        | goto target =>
          rw [hterm] at hWP
          dsimp at hWP
          have hStep : evalMirStep body conc = .step () { conc with block := target, stmtIdx := 0 } := by
            unfold evalMirStep
            rw [hState.block_eq, hbb]; dsimp
            rw [hState.stmtIdx_eq, hstmt]
            dsimp [evalMirTerminator]; rw [hterm]
          have hState' : StateRel env rawOwn relOwn atomMsgs atomView
              { sym with block := target, stmtIdx := 0 }
              { conc with block := target, stmtIdx := 0 } := {
            block_eq := rfl
            stmtIdx_eq := rfl
            localRel := hState.localRel
            loanRel := hState.loanRel
            rawRel := hState.rawRel
            atomRel := hState.atomRel
          }
          exact SafeAndSatisfies.of_step hStep (ih hState' hWP)
        | callAtomicLoad dst ptr ord target =>
          rw [hterm] at hWP
          dsimp at hWP
          cases hOp : evalSymOperand sym.locals ptr with
          | none => rw [hOp] at hWP; exact False.elim hWP
          | some svPtr =>
            rw [hOp] at hWP
            cases svPtr with
            | usize _ | bool _ | unit | refShared _ | borrow _ | rawPtr _ =>
              exact False.elim hWP
            | atomicRef atomId =>
              dsimp [symWP] at hWP
              have ⟨locAtom, haloc, hneVis, hForallMsg⟩ := hWP
              have ⟨mvPtr, hConcOp, hValPtr⟩ := evalSymOperand_sound hState.localRel hOp
              have ⟨locAtom', haloc', hmvPtr⟩ := hValPtr
              subst hmvPtr
              rw [haloc] at haloc'; injection haloc' with hloc_eq; subst hloc_eq
              have hVisEq := visibleAtomicMsgs_eq_visibleMsgsAt hState.atomRel haloc
              cases hVisList : conc.mem.visibleAtomicMsgs locAtom with
              | nil =>
                rw [hVisEq] at hVisList
                exact False.elim (hneVis hVisList)
              | cons head tail =>
                have hStep : evalMirStep body conc = .choice .demonic (fun s' =>
                    ∃ msg, msg ∈ (head :: tail) ∧
                      s' = {
                        locals := updateLocal conc.locals dst (some (.usize msg.bits))
                        mem := conc.mem.applyAtomicLoad ord msg
                        block := target
                        stmtIdx := 0 }) := by
                  unfold evalMirStep
                  rw [hState.block_eq, hbb]; dsimp
                  rw [hState.stmtIdx_eq, hstmt]
                  dsimp [evalMirTerminator]
                  rw [hterm]; dsimp
                  rw [hConcOp]; dsimp
                  rw [hVisList]
                have hNonempty : ∃ s' : MirState, ∃ msg, msg ∈ (head :: tail) ∧
                    s' = {
                      locals := updateLocal conc.locals dst (some (.usize msg.bits))
                      mem := conc.mem.applyAtomicLoad ord msg
                      block := target
                      stmtIdx := 0 } :=
                  ⟨{ locals := updateLocal conc.locals dst (some (.usize head.bits))
                     mem := conc.mem.applyAtomicLoad ord head
                     block := target
                     stmtIdx := 0 }, head, List.Mem.head tail, rfl⟩
                refine SafeAndSatisfies.of_demonic_choice hStep hNonempty ?_
                intro s' ⟨msg, hmem, hs'⟩
                subst hs'
                have hmemVis : msg ∈ visibleMsgsAt atomMsgs (atomView locAtom) locAtom := by
                  rw [← hVisEq, hVisList]
                  exact hmem
                have ⟨rawOwn', relOwn', hAcq, hWPMsg⟩ := hForallMsg msg hmemVis
                have hState' : StateRel env rawOwn' relOwn' atomMsgs
                    (applyViewLoad ord atomView msg)
                    { sym with
                      locals := updateSymLocal sym.locals dst (some (.usize msg.bits))
                      block := target
                      stmtIdx := 0 }
                    { locals := updateLocal conc.locals dst (some (.usize msg.bits))
                      mem := conc.mem.applyAtomicLoad ord msg
                      block := target
                      stmtIdx := 0 } := {
                  block_eq := rfl
                  stmtIdx_eq := rfl
                  localRel := LocalRel.update_some hState.localRel dst rfl
                  loanRel := LoanRel.preserved_by_atomic_load ord msg hState.loanRel
                  rawRel := RawRel.of_atomicLoad hState.rawRel hAcq
                  atomRel := AtomRel.of_atomicLoad ord msg hState.atomRel
                }
                exact ih hState' hWPMsg
  | branch falsePlan truePlan ihFalse ihTrue =>
    intro env rawOwn relOwn atomMsgs atomView sym conc Post hState hWP
    dsimp [evalSymTree] at hWP
    cases hbr : evalBranchStep body sym with
    | none => rw [hbr] at hWP; exact False.elim hWP
    | some p =>
      cases p with
      | mk cond rest =>
        cases rest with
        | mk symFalse symTrue =>
          rw [hbr] at hWP
          dsimp at hWP
          rw [zipSymTree_eq_ite] at hWP
          unfold evalBranchStep at hbr
          cases hbb : listGet body.blocks sym.block with
          | none => rw [hbb] at hbr; cases hbr
          | some bb =>
            rw [hbb] at hbr
            dsimp at hbr
            cases hstmt : listGet bb.stmts sym.stmtIdx with
            | some _ => rw [hstmt] at hbr; cases hbr
            | none =>
              rw [hstmt] at hbr
              cases hterm : bb.terminator with
              | return_ | goto _ | callAtomicLoad _ _ _ _ =>
                rw [hterm] at hbr; cases hbr
              | switchInt discr falseTarget trueTarget =>
                rw [hterm] at hbr
                dsimp at hbr
                cases hOp : evalSymOperand sym.locals discr with
                | none => rw [hOp] at hbr; cases hbr
                | some svDiscr =>
                  rw [hOp] at hbr
                  cases svDiscr with
                  | usize _ | unit | refShared _ | borrow _ | rawPtr _ | atomicRef _ =>
                    cases hbr
                  | bool b =>
                    dsimp at hbr
                    injection hbr with htuple
                    injection htuple with hb hrest
                    injection hrest with hF hT
                    subst hb hF hT
                    have ⟨mvDiscr, hConcOp, hValDiscr⟩ := evalSymOperand_sound hState.localRel hOp
                    subst hValDiscr
                    cases b with
                    | false =>
                      dsimp at hWP
                      have hStep : evalMirStep body conc = .step () { conc with block := falseTarget, stmtIdx := 0 } := by
                        unfold evalMirStep
                        rw [hState.block_eq, hbb]; dsimp
                        rw [hState.stmtIdx_eq, hstmt]
                        dsimp [evalMirTerminator]; rw [hterm]; dsimp; rw [hConcOp]
                      have hStateF : StateRel env rawOwn relOwn atomMsgs atomView
                          { sym with block := falseTarget, stmtIdx := 0 }
                          { conc with block := falseTarget, stmtIdx := 0 } := {
                        block_eq := rfl
                        stmtIdx_eq := rfl
                        localRel := hState.localRel
                        loanRel := hState.loanRel
                        rawRel := hState.rawRel
                        atomRel := hState.atomRel
                      }
                      exact SafeAndSatisfies.of_step hStep (ihFalse hStateF hWP)
                    | true =>
                      dsimp at hWP
                      have hStep : evalMirStep body conc = .step () { conc with block := trueTarget, stmtIdx := 0 } := by
                        unfold evalMirStep
                        rw [hState.block_eq, hbb]; dsimp
                        rw [hState.stmtIdx_eq, hstmt]
                        dsimp [evalMirTerminator]; rw [hterm]; dsimp; rw [hConcOp]
                      have hStateT : StateRel env rawOwn relOwn atomMsgs atomView
                          { sym with block := trueTarget, stmtIdx := 0 }
                          { conc with block := trueTarget, stmtIdx := 0 } := {
                        block_eq := rfl
                        stmtIdx_eq := rfl
                        localRel := hState.localRel
                        loanRel := hState.loanRel
                        rawRel := hState.rawRel
                        atomRel := hState.atomRel
                      }
                      exact SafeAndSatisfies.of_step hStep (ihTrue hStateT hWP)
  | reborrowRaw loanId next ih =>
    intro env rawOwn relOwn atomMsgs atomView sym conc Post hState hWP
    dsimp [evalSymTree] at hWP
    cases hbb : listGet body.blocks sym.block with
    | none => rw [hbb] at hWP; exact False.elim hWP
    | some bb =>
      rw [hbb] at hWP
      dsimp at hWP
      cases hstmt : listGet bb.stmts sym.stmtIdx with
      | none => rw [hstmt] at hWP; exact False.elim hWP
      | some stmt =>
        rw [hstmt] at hWP
        cases stmt with
        | assign _ _ | assignDeref _ _ | derefRaw _ _ | assignDerefRaw _ _ | nop =>
          exact False.elim hWP
        | reborrowRawToMut dst ptrLocal =>
          dsimp at hWP
          cases hptr : sym.locals ptrLocal with
          | none => rw [hptr] at hWP; exact False.elim hWP
          | some svPtr =>
            rw [hptr] at hWP
            cases svPtr with
            | usize _ | bool _ | unit | refShared _ | borrow _ | atomicRef _ =>
              exact False.elim hWP
            | rawPtr rawId =>
              cases hloan : sym.loans loanId with
              | some _ => rw [hloan] at hWP; exact False.elim hWP
              | none =>
                rw [hloan] at hWP
                dsimp at hWP
                cases hne1 : !(loanId == 1) with
                | false => rw [hne1] at hWP; exact False.elim hWP
                | true =>
                  rw [hne1] at hWP
                  dsimp [symWP] at hWP
                  have ⟨v0, hrawOwn, hlocEq, hWPNext⟩ := hWP
                  have ⟨mvPtr, hconcPtr, hvalPtr⟩ := hState.localRel ptrLocal (.rawPtr rawId) hptr
                  have ⟨locRaw, hrloc, hmvPtr⟩ := hvalPtr
                  subst hmvPtr
                  have ⟨locRaw', hrloc', hOwnMem⟩ := hState.rawRel.rawOwnLoc rawId (.usize v0) hrawOwn
                  rw [hrloc] at hrloc'; injection hrloc' with hloc_eq; subst hloc_eq
                  have hlloc : env.loanLoc loanId = some locRaw := Eq.trans hlocEq hrloc
                  have hbb' : listGet body.blocks conc.block = some bb := by rw [hState.block_eq]; exact hbb
                  have hstmt' : listGet bb.stmts conc.stmtIdx = some (.reborrowRawToMut dst ptrLocal) := by
                    rw [hState.stmtIdx_eq]; exact hstmt
                  have hStep : evalMirStep body conc = .step () { conc with
                      locals := updateLocal conc.locals dst (some (.refMutLoc locRaw))
                      stmtIdx := conc.stmtIdx + 1 } := by
                    unfold evalMirStep
                    rw [hbb']; dsimp
                    rw [hstmt']
                    dsimp [evalMirStmt]; rw [hconcPtr]
                  have hState' : StateRel env (updateRawOwn rawOwn rawId none) relOwn
                      atomMsgs atomView
                      { sym with
                        locals := updateSymLocal sym.locals dst (some (.borrow loanId))
                        loans := updateLoan sym.loans loanId (some (rawLoanEntry rawId v0))
                        stmtIdx := sym.stmtIdx + 1 }
                      { conc with
                        locals := updateLocal conc.locals dst (some (.refMutLoc locRaw))
                        stmtIdx := conc.stmtIdx + 1 } := {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localRel := LocalRel.update_some hState.localRel dst ⟨locRaw, hlloc, rfl⟩
                    loanRel := promoteRaw_preserves_loanRel hState.loanRel hState.rawRel hrawOwn hrloc hlloc hOwnMem
                    rawRel := promoteRaw_preserves_rawRel hState.rawRel hrawOwn hrloc hlloc
                    atomRel := hState.atomRel
                  }
                  exact SafeAndSatisfies.of_step hStep (ih hState' hWPNext)
  | endRawLoan loanId next ih =>
    intro env rawOwn relOwn atomMsgs atomView sym conc Post hState hWP
    dsimp [evalSymTree] at hWP
    cases hne1 : !(loanId == 1) with
    | false => rw [hne1] at hWP; exact False.elim hWP
    | true =>
      rw [hne1] at hWP
      dsimp at hWP
      cases hloan : sym.loans loanId with
      | none => rw [hloan] at hWP; exact False.elim hWP
      | some entry =>
        rw [hloan] at hWP
        dsimp at hWP
        cases hact : entry.active with
        | false => rw [hact] at hWP; exact False.elim hWP
        | true =>
          rw [hact] at hWP
          cases hfrz : entry.frozen with
          | true => rw [hfrz] at hWP; exact False.elim hWP
          | false =>
            rw [hfrz] at hWP
            dsimp at hWP
            cases hsrc : entry.rawSource with
            | none => rw [hsrc] at hWP; exact False.elim hWP
            | some rawId =>
              rw [hsrc] at hWP
              cases hsc : entry.curVal.toScalarMirVal with
              | none => rw [hsc] at hWP; exact False.elim hWP
              | some mvFinal =>
                rw [hsc] at hWP
                dsimp [symWP] at hWP
                have ⟨_, hrelNone, hlocEq, hWPNext⟩ := hWP
                have hentry_eq :
                    { entry with rawSource := some rawId, frozen := false, active := false } =
                    { entry with active := false } := by
                  cases entry; dsimp at hsrc hfrz ⊢; subst hsrc hfrz; rfl
                rw [hentry_eq] at hWPNext
                have ⟨locRaw, mv', hlloc, hsc', hOwnFinal⟩ :=
                  hState.loanRel.activeOwn loanId entry hloan hact hfrz
                rw [hsc] at hsc'; injection hsc' with hmv_eq; subst hmv_eq
                have hrloc : env.rawLoc rawId = some locRaw := Eq.trans hlocEq.symm hlloc
                have hState' : StateRel env (updateRawOwn rawOwn rawId (some mvFinal)) relOwn
                    atomMsgs atomView
                    { sym with loans := updateLoan sym.loans loanId (some { entry with active := false }) }
                    conc := {
                  block_eq := hState.block_eq
                  stmtIdx_eq := hState.stmtIdx_eq
                  localRel := hState.localRel
                  loanRel := releaseRaw_preserves_loanRel hState.loanRel
                  rawRel := releaseRaw_preserves_rawRel hState.loanRel hState.rawRel
                    hloan hact hfrz hrloc hlloc hrelNone hOwnFinal
                  atomRel := hState.atomRel
                }
                exact ih hState' hWPNext
/-!
## 7. `FuncTreeLang` Refinement Bridge and End-to-End Verified Mixed Safe/Unsafe/Atomic Examples
-/

/-- Abstract language `FuncTreeLang` packaging `evalSymTree` + `symWP` within
    `Trusted.Language` / `Trusted.Abstracts`. -/
def FuncTreeLang : Language where
  Prog := SymState → SymTree RetSummary
  Query := MirState
  Out := TermOutcome
  sem p init := {
    defined :=
      ∃ env rawOwn relOwn atomMsgs atomView sym Post,
        MirMachine.initState { blocks := [] } init ∧
        StateRel env rawOwn relOwn atomMsgs atomView sym init ∧
        symWP (p sym) env rawOwn relOwn atomMsgs atomView Post
    val := fun _ termOut =>
      ∀ env rawOwn relOwn atomMsgs atomView sym Post,
        StateRel env rawOwn relOwn atomMsgs atomView sym init →
        symWP (p sym) env rawOwn relOwn atomMsgs atomView Post →
        TerminalPost env Post termOut
  }

def π_tree (b : FuncTreeLang.Behavior) : MirLang.Behavior :=
  fun q =>
    Partial.map
      (fun (post : TermOutcome → Prop) (out : ExecOut Unit TermOutcome) =>
        out.outcome.isSafe ∧
        ∀ termOut, out.outcome = .terminated (.normal termOut) → post termOut)
      (b q.init)

theorem monotone_π_tree : Monotone π_tree :=
  fun _ _ hb q =>
    Partial.monotone_map
      (by intro _ _ hle out ⟨hsafe, hret⟩; exact ⟨hsafe, fun r hr => hle r (hret r hr)⟩)
      (hb q.init)

/-- `evalSymTree plan body` abstracts `body` in `MirLang` under `π_tree` for
    **every** untrusted `plan : TransPlan` and **every** `body : MirBody`. -/
theorem evalSymTree_abstracts (plan : TransPlan) (body : MirBody) :
    Abstracts FuncTreeLang MirLang π_tree (evalSymTree plan body) body := by
  refine ⟨monotone_π_tree, ?_⟩
  intro q hdef
  refine ⟨True.intro, ?_⟩
  intro out ⟨_, hreach⟩
  have ⟨env, rawOwn, relOwn, atomMsgs, atomView, sym, Post, _, hState0, hWP0⟩ := hdef
  have hSafe0 := evalSymTree_sound plan body hState0 hWP0 q.init q.steps out.trace out.outcome hreach
  refine ⟨hSafe0.1, ?_⟩
  intro termOut hout env' rawOwn' relOwn' atomMsgs' atomView' sym' Post' hState' hWP'
  have hSafe' := evalSymTree_sound plan body hState' hWP' q.init q.steps out.trace out.outcome hreach
  exact hSafe'.2 termOut hout

/-!
### Shared Initial Symbolic State Builders for the 4 Verified Examples
-/

def emptySymLocals : Nat → Option SymVal := fun _ => none
def emptySymLoans : Nat → Option LoanEntry := fun _ => none
def emptyRawOwn : Nat → Option MirVal := fun _ => none
def emptyRelOwn : Nat → Option (Timestamp × MirVal) := fun _ => none

def rootLoanEntry (n : Nat) : LoanEntry where
  rawSource := none
  curVal := .usize n
  frozen := false
  active := true

/-!
### Example 1: Mixed Safe `&mut usize` Borrow + Weak-Memory `AtomicUsize::load(Relaxed)` (`atomic_max_assign`)

```rust
pub fn atomic_max_assign(x: &mut usize, a: &AtomicUsize) -> usize {
    let cur = *x;
    let loaded = a.load(Ordering::Relaxed);
    if cur < loaded {
        *x = loaded;
    }
    *x
}
```
-/

def atomicMaxAssignBody : MirBody where
  blocks := [
    -- bb0: _3 = *_1; _4 = AtomicUsize::load(_2, Relaxed) -> bb1
    { stmts := [.assign 3 (.deref 1)]
      terminator := .callAtomicLoad 4 (.copy 2) .relaxed 1 },
    -- bb1: _5 = Lt(_3, _4); switchInt(_5) -> [false: bb2, true: bb3]
    { stmts := [.assign 5 (.binaryOp .lt (.copy 3) (.copy 4))]
      terminator := .switchInt (.copy 5) 2 3 },
    -- bb2 (false): goto -> bb4
    { stmts := []
      terminator := .goto 4 },
    -- bb3 (true): *_1 = _4; goto -> bb4
    { stmts := [.assignDeref 1 (.copy 4)]
      terminator := .goto 4 },
    -- bb4 (join): _0 = *_1; return
    { stmts := [.assign 0 (.deref 1)]
      terminator := .return_ }
  ]

def atomicMaxAssignPlan : TransPlan :=
  .step (.step (.step (.branch
    (.step (.step .ret))
    (.step (.step (.step .ret))))))

def initAtomicMaxSym (x0 : Nat) : SymState where
  locals := updateSymLocal (updateSymLocal emptySymLocals 1 (some (.borrow 1))) 2 (some (.atomicRef 2))
  loans := updateLoan emptySymLoans 1 (some (rootLoanEntry x0))
  block := 0
  stmtIdx := 0

/-- First Futamura Projection (`rfl`) for `atomic_max_assign`:
    All safe `&mut` dereferences, arithmetic comparisons, and diamond branches
    reduce at translation time by kernel `rfl` into a single `.atomicLoad` node. -/
theorem atomicMaxAssign_evalSymTree_rfl (x0 : Nat) :
    evalSymTree atomicMaxAssignPlan atomicMaxAssignBody (initAtomicMaxSym x0) =
      .atomicLoad 2 .relaxed (fun v =>
        .ret {
          retVal := .usize (if decide (x0 < v) then v else x0)
          loan1Val := some (.usize (if decide (x0 < v) then v else x0))
        }) :=
  rfl

theorem atomicMaxAssign_satisfies_spec {conc : MirState}
    {locX locAtom x0 : Nat}
    (hState : StateRel
      { loanLoc := fun l => if l == 1 then some locX else none
        sharedLoc := fun _ _ => False
        rawLoc := fun _ => none
        atomicLoc := fun a => if a == 2 then some locAtom else none }
      emptyRawOwn emptyRelOwn conc.mem.atomicMsgs conc.mem.curView
      (initAtomicMaxSym x0) conc)
    (hVis : conc.mem.visibleAtomicMsgs locAtom ≠ []) :
    SafeAndSatisfies atomicMaxAssignBody conc (fun termOut =>
      ∃ msg, msg ∈ conc.mem.visibleAtomicMsgs locAtom ∧
        let expected := if decide (x0 < msg.bits) then msg.bits else x0
        termOut.retVal = .usize expected ∧
        OwnLoc termOut.mem locX (.usize expected)) := by
  let env : SpatialEnv := {
    loanLoc := fun l => if l == 1 then some locX else none
    sharedLoc := fun _ _ => False
    rawLoc := fun _ => none
    atomicLoc := fun a => if a == 2 then some locAtom else none
  }
  let Post : RetSummary → (Nat → Option MirVal) → Prop := fun summary _ =>
    ∃ msg, msg ∈ conc.mem.visibleAtomicMsgs locAtom ∧
      let expected := if decide (x0 < msg.bits) then msg.bits else x0
      summary.retVal = .usize expected ∧
      summary.loan1Val = some (.usize expected)
  have hWP : symWP (evalSymTree atomicMaxAssignPlan atomicMaxAssignBody (initAtomicMaxSym x0))
      env emptyRawOwn emptyRelOwn conc.mem.atomicMsgs conc.mem.curView Post := by
    rw [atomicMaxAssign_evalSymTree_rfl x0]
    dsimp [symWP]
    refine ⟨locAtom, rfl, hVis, ?_⟩
    intro msg hmsg
    exact ⟨emptyRawOwn, emptyRelOwn, .refl, ⟨msg, hmsg, rfl, rfl⟩⟩
  have hSafe := evalSymTree_sound atomicMaxAssignPlan atomicMaxAssignBody hState hWP
  intro init steps tr out hreach
  have ⟨hsafe, hterm⟩ := hSafe init steps tr out hreach
  refine ⟨hsafe, ?_⟩
  intro termOut hout
  have ⟨summary, _, ⟨msg, hmsg, hretSum, hloan1Sum⟩, hretEq, hloan1Own, _⟩ := hterm termOut hout
  refine ⟨msg, hmsg, Eq.trans hretEq hretSum, ?_⟩
  exact hloan1Own locX (.usize (if decide (x0 < msg.bits) then msg.bits else x0)) rfl hloan1Sum

/-!
### Example 2: Mixed Safe `&mut usize` Borrow + Unsafe `*mut usize` Raw Pointer Read & Write (`raw_add_and_zero`)

```rust
pub unsafe fn raw_add_and_zero(x: &mut usize, raw_p: *mut usize) -> usize {
    let cur_x = *x;
    let raw_v = *raw_p;
    *x = cur_x + raw_v;
    *raw_p = 0;
    *x
}
```
-/

def rawAddAndZeroBody : MirBody where
  blocks := [
    { stmts := [
        .assign 3 (.deref 1),
        .derefRaw 4 2,
        .assign 5 (.binaryOp .add (.copy 3) (.copy 4)),
        .assignDeref 1 (.copy 5),
        .assignDerefRaw 2 (.constVal (.usize 0)),
        .assign 0 (.deref 1)
      ]
      terminator := .return_ }
  ]

def rawAddAndZeroPlan : TransPlan :=
  .step (.step (.step (.step (.step (.step .ret)))))

def initRawPtrSym (x0 : Nat) : SymState where
  locals := updateSymLocal (updateSymLocal emptySymLocals 1 (some (.borrow 1))) 2 (some (.rawPtr 2))
  loans := updateLoan emptySymLoans 1 (some (rootLoanEntry x0))
  block := 0
  stmtIdx := 0

/-- First Futamura Projection (`rfl`) for `raw_add_and_zero`:
    All safe `&mut x` reads/writes and arithmetic reduce by kernel `rfl`,
    leaving only the 2 residual `.readRaw` and `.writeRaw` nodes on `raw_p`. -/
theorem rawAddAndZero_evalSymTree_rfl (x0 : Nat) :
    evalSymTree rawAddAndZeroPlan rawAddAndZeroBody (initRawPtrSym x0) =
      .readRaw 2 (fun raw_v =>
        .writeRaw 2 (.usize 0)
          (.ret {
            retVal := .usize (x0 + raw_v)
            loan1Val := some (.usize (x0 + raw_v))
          })) :=
  rfl

theorem rawAddAndZero_satisfies_spec {conc : MirState}
    {locX locRaw x0 vRaw : Nat}
    (hState : StateRel
      { loanLoc := fun l => if l == 1 then some locX else none
        sharedLoc := fun _ _ => False
        rawLoc := fun r => if r == 2 then some locRaw else none
        atomicLoc := fun _ => none }
      (updateRawOwn emptyRawOwn 2 (some (.usize vRaw)))
      emptyRelOwn conc.mem.atomicMsgs conc.mem.curView
      (initRawPtrSym x0) conc) :
    SafeAndSatisfies rawAddAndZeroBody conc (fun termOut =>
      termOut.retVal = .usize (x0 + vRaw) ∧
      OwnLoc termOut.mem locX (.usize (x0 + vRaw)) ∧
      OwnLoc termOut.mem locRaw (.usize 0)) := by
  let env : SpatialEnv := {
    loanLoc := fun l => if l == 1 then some locX else none
    sharedLoc := fun _ _ => False
    rawLoc := fun r => if r == 2 then some locRaw else none
    atomicLoc := fun _ => none
  }
  let rawOwn0 := updateRawOwn emptyRawOwn 2 (some (.usize vRaw))
  let Post : RetSummary → (Nat → Option MirVal) → Prop := fun summary rawOwnFinal =>
    summary.retVal = .usize (x0 + vRaw) ∧
    summary.loan1Val = some (.usize (x0 + vRaw)) ∧
    rawOwnFinal 2 = some (.usize 0)
  have hWP : symWP (evalSymTree rawAddAndZeroPlan rawAddAndZeroBody (initRawPtrSym x0))
      env rawOwn0 emptyRelOwn conc.mem.atomicMsgs conc.mem.curView Post := by
    rw [rawAddAndZero_evalSymTree_rfl x0]
    dsimp [symWP]
    exact ⟨vRaw, rfl, ⟨.usize vRaw, rfl⟩, rfl, rfl, rfl⟩
  have hSafe := evalSymTree_sound rawAddAndZeroPlan rawAddAndZeroBody hState hWP
  intro init steps tr out hreach
  have ⟨hsafe, hterm⟩ := hSafe init steps tr out hreach
  refine ⟨hsafe, ?_⟩
  intro termOut hout
  have ⟨summary, rawOwnFinal, ⟨hretSum, hloan1Sum, hrawFinal⟩, hretEq, hloan1Own, hrawOwn⟩ :=
    hterm termOut hout
  refine ⟨Eq.trans hretEq hretSum, ?_, ?_⟩
  · exact hloan1Own locX (.usize (x0 + vRaw)) rfl hloan1Sum
  · exact hrawOwn 2 locRaw (.usize 0) rfl hrawFinal

/-!
### Example 3: Technique C — Plan-Guided Raw-Pointer-to-Loan Reborrowing (`reborrow_raw_max_assign`)

```rust
pub unsafe fn reborrow_raw_max_assign(x: &mut usize, raw_p: *mut usize) -> usize {
    let cur_x = *x;
    let r: &mut usize = &mut *raw_p; // promoted to LoanEntry 10 via TransPlan.reborrowRaw
    let cur_r = *r;                  // safe &mut deref!
    if cur_r < cur_x {
        *r = cur_x;                  // safe &mut assignDeref!
    }
    let res = *r;                    // safe &mut deref!
    // released back to rawOwn 2 via TransPlan.endRawLoan
    res
}
```
-/

def reborrowRawMaxAssignBody : MirBody where
  blocks := [
    -- bb0: _3 = *_1; _4 = &mut *_2; _5 = *_4; _6 = Lt(_5, _3); switchInt(_6) -> [false: bb1, true: bb2]
    { stmts := [
        .assign 3 (.deref 1),
        .reborrowRawToMut 4 2,
        .assign 5 (.deref 4),
        .assign 6 (.binaryOp .lt (.copy 5) (.copy 3))
      ]
      terminator := .switchInt (.copy 6) 1 2 },
    -- bb1 (false): goto -> bb3
    { stmts := []
      terminator := .goto 3 },
    -- bb2 (true): *_4 = _3; goto -> bb3
    { stmts := [.assignDeref 4 (.copy 3)]
      terminator := .goto 3 },
    -- bb3 (join): _0 = *_4; return
    { stmts := [.assign 0 (.deref 4)]
      terminator := .return_ }
  ]

def reborrowRawMaxAssignPlan : TransPlan :=
  .step (.reborrowRaw 10 (.step (.step (.branch
    (.step (.step (.endRawLoan 10 .ret)))
    (.step (.step (.step (.endRawLoan 10 .ret))))))))

/-- First Futamura Projection (`rfl`) for `reborrow_raw_max_assign` (Technique C):
    After `reborrowRaw 10` promotes `raw_p` into tracked loan `10`, all subsequent
    reads (`*r`), branches (`if *r < *x`), and mutations (`*r = *x`) on the
    reborrowed pointer execute as pure functional borrow operations and collapse
    via `zipSymTree` by kernel `rfl`! -/
theorem reborrowRawMaxAssign_evalSymTree_rfl (x0 : Nat) :
    evalSymTree reborrowRawMaxAssignPlan reborrowRawMaxAssignBody (initRawPtrSym x0) =
      .promoteRaw 2 10 (fun v0 =>
        .releaseRaw 2 10 (.usize (if decide (v0 < x0) then x0 else v0))
          (.ret {
            retVal := .usize (if decide (v0 < x0) then x0 else v0)
            loan1Val := some (.usize (if decide (v0 < x0) then x0 else x0))
          })) :=
  rfl

theorem reborrowRawMaxAssign_satisfies_spec {conc : MirState}
    {locX locRaw x0 vRaw : Nat}
    (hState : StateRel
      { loanLoc := fun l => if l == 1 then some locX else if l == 10 then some locRaw else none
        sharedLoc := fun _ _ => False
        rawLoc := fun r => if r == 2 then some locRaw else none
        atomicLoc := fun _ => none }
      (updateRawOwn emptyRawOwn 2 (some (.usize vRaw)))
      emptyRelOwn conc.mem.atomicMsgs conc.mem.curView
      (initRawPtrSym x0) conc) :
    SafeAndSatisfies reborrowRawMaxAssignBody conc (fun termOut =>
      let expected := if decide (vRaw < x0) then x0 else vRaw
      termOut.retVal = .usize expected ∧
      OwnLoc termOut.mem locX (.usize x0) ∧
      OwnLoc termOut.mem locRaw (.usize expected)) := by
  let env : SpatialEnv := {
    loanLoc := fun l => if l == 1 then some locX else if l == 10 then some locRaw else none
    sharedLoc := fun _ _ => False
    rawLoc := fun r => if r == 2 then some locRaw else none
    atomicLoc := fun _ => none
  }
  let rawOwn0 := updateRawOwn emptyRawOwn 2 (some (.usize vRaw))
  let expected := if decide (vRaw < x0) then x0 else vRaw
  let Post : RetSummary → (Nat → Option MirVal) → Prop := fun summary rawOwnFinal =>
    summary.retVal = .usize expected ∧
    summary.loan1Val = some (.usize (if decide (vRaw < x0) then x0 else x0)) ∧
    rawOwnFinal 2 = some (.usize expected)
  have hWP : symWP (evalSymTree reborrowRawMaxAssignPlan reborrowRawMaxAssignBody (initRawPtrSym x0))
      env rawOwn0 emptyRelOwn conc.mem.atomicMsgs conc.mem.curView Post := by
    rw [reborrowRawMaxAssign_evalSymTree_rfl x0]
    dsimp [symWP]
    exact ⟨vRaw, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hSafe := evalSymTree_sound reborrowRawMaxAssignPlan reborrowRawMaxAssignBody hState hWP
  intro init steps tr out hreach
  have ⟨hsafe, hterm⟩ := hSafe init steps tr out hreach
  refine ⟨hsafe, ?_⟩
  intro termOut hout
  have ⟨summary, rawOwnFinal, ⟨hretSum, hloan1Sum, hrawFinal⟩, hretEq, hloan1Own, hrawOwn⟩ :=
    hterm termOut hout
  have hx0 : (if decide (vRaw < x0) then x0 else x0) = x0 := by
    cases decide (vRaw < x0) <;> rfl
  refine ⟨Eq.trans hretEq hretSum, ?_, ?_⟩
  · rw [hx0] at hloan1Sum
    exact hloan1Own locX (.usize x0) rfl hloan1Sum
  · exact hrawOwn 2 locRaw (.usize expected) rfl hrawFinal

/-!
### Example 4: C++20 Release/Acquire Message-Passing Ownership Transfer (`acquire_read_raw`)

```rust
pub unsafe fn acquire_read_raw(flag: &AtomicUsize, data: *const usize) -> usize {
    let f = flag.load(Ordering::Acquire);
    if f == 1 {
        *data
    } else {
        0
    }
}
```
-/

def acquireReadRawBody : MirBody where
  blocks := [
    -- bb0: _3 = AtomicUsize::load(_1, Acquire) -> bb1
    { stmts := []
      terminator := .callAtomicLoad 3 (.copy 1) .acquire 1 },
    -- bb1: _4 = Eq(_3, 1); switchInt(_4) -> [false: bb2, true: bb3]
    { stmts := [.assign 4 (.binaryOp .eq (.copy 3) (.constVal (.usize 1)))]
      terminator := .switchInt (.copy 4) 2 3 },
    -- bb2 (false): _0 = 0; return
    { stmts := [.assign 0 (.use (.constVal (.usize 0)))]
      terminator := .return_ },
    -- bb3 (true): _0 = *_2 (derefRaw); return
    { stmts := [.derefRaw 0 2]
      terminator := .return_ }
  ]

def acquireReadRawPlan : TransPlan :=
  .step (.step (.branch
    (.step .ret)
    (.step .ret)))

def initAcquireReadSym : SymState where
  locals := updateSymLocal (updateSymLocal emptySymLocals 1 (some (.atomicRef 1))) 2 (some (.rawPtr 2))
  loans := emptySymLoans
  block := 0
  stmtIdx := 0

/-- First Futamura Projection (`rfl`) for `acquire_read_raw`:
    `evalSymTree` reduces the post-load equality comparison and branch dispatch
    by kernel `rfl`, isolating `.readRaw 2` strictly inside the `f = 1` branch of
    the `.atomicLoad 1 .acquire` continuation. -/
theorem acquireReadRaw_evalSymTree_rfl :
    evalSymTree acquireReadRawPlan acquireReadRawBody initAcquireReadSym =
      .atomicLoad 1 .acquire (fun f =>
        if decide (f = 1) then
          .readRaw 2 (fun d =>
            .ret { retVal := .usize d, loan1Val := none })
        else
          .ret { retVal := .usize 0, loan1Val := none }) :=
  rfl

/-- End-to-End Verification of C++20 Release/Acquire Message Passing (`acquire_read_raw`):
    At entry, `locData` is **not** in `rawOwn` (`rawOwn = emptyRawOwn`); it is only
    release-guarded (`relOwn 2 = some (reqTs, .usize dVal)`). Whenever the Acquire
    load of `flag` observes a message with `msg.bits = 1`, `hReleaseSync` guarantees
    `reqTs ≤ msg.relView locData`, allowing `AcquireExt.transfer` (backed by
    `OwnLoc.transfer_acquire`) to dynamically materialize `rawOwn 2 = some (.usize dVal)`
    for the `.readRaw 2` dereference in the `then` branch! -/
theorem acquireReadRaw_satisfies_spec {conc : MirState}
    {locFlag locData reqTs dVal : Nat}
    (hState : StateRel
      { loanLoc := fun _ => none
        sharedLoc := fun _ _ => False
        rawLoc := fun r => if r == 2 then some locData else none
        atomicLoc := fun a => if a == 1 then some locFlag else none }
      emptyRawOwn
      (updateRelOwn emptyRelOwn 2 (some (reqTs, .usize dVal)))
      conc.mem.atomicMsgs conc.mem.curView
      initAcquireReadSym conc)
    (hVis : conc.mem.visibleAtomicMsgs locFlag ≠ [])
    (hReleaseSync : ∀ msg, msg ∈ conc.mem.visibleAtomicMsgs locFlag →
      msg.bits = 1 → reqTs ≤ msg.relView locData) :
    SafeAndSatisfies acquireReadRawBody conc (fun termOut =>
      ∃ msg, msg ∈ conc.mem.visibleAtomicMsgs locFlag ∧
        termOut.retVal = .usize (if decide (msg.bits = 1) then dVal else 0)) := by
  let env : SpatialEnv := {
    loanLoc := fun _ => none
    sharedLoc := fun _ _ => False
    rawLoc := fun r => if r == 2 then some locData else none
    atomicLoc := fun a => if a == 1 then some locFlag else none
  }
  let relOwn0 := updateRelOwn emptyRelOwn 2 (some (reqTs, .usize dVal))
  let Post : RetSummary → (Nat → Option MirVal) → Prop := fun summary _ =>
    ∃ msg, msg ∈ conc.mem.visibleAtomicMsgs locFlag ∧
      summary.retVal = .usize (if decide (msg.bits = 1) then dVal else 0)
  have hWP : symWP (evalSymTree acquireReadRawPlan acquireReadRawBody initAcquireReadSym)
      env emptyRawOwn relOwn0 conc.mem.atomicMsgs conc.mem.curView Post := by
    rw [acquireReadRaw_evalSymTree_rfl]
    dsimp [symWP]
    refine ⟨locFlag, rfl, hVis, ?_⟩
    intro msg hmsg
    cases hbits : decide (msg.bits = 1) with
    | true =>
      have hsync : reqTs ≤ msg.relView locData :=
        hReleaseSync msg hmsg (of_decide_eq_true hbits)
      refine ⟨updateRawOwn emptyRawOwn 2 (some (.usize dVal)),
              updateRelOwn relOwn0 2 none,
              .transfer 2 locData reqTs (.usize dVal) rfl rfl rfl hsync, ?_⟩
      dsimp [symWP]
      refine ⟨dVal, rfl, ⟨msg, hmsg, ?_⟩⟩
      rw [hbits]; rfl
    | false =>
      refine ⟨emptyRawOwn, relOwn0, .refl, ?_⟩
      dsimp [symWP]
      refine ⟨msg, hmsg, ?_⟩
      rw [hbits]; rfl
  have hSafe := evalSymTree_sound acquireReadRawPlan acquireReadRawBody hState hWP
  intro init steps tr out hreach
  have ⟨hsafe, hterm⟩ := hSafe init steps tr out hreach
  refine ⟨hsafe, ?_⟩
  intro termOut hout
  have ⟨summary, _, ⟨msg, hmsg, hretSum⟩, hretEq, _, _⟩ := hterm termOut hout
  exact ⟨msg, hmsg, Eq.trans hretEq hretSum⟩

/-!
## 8. Axiom Footprint Audit (`#print axioms`)
-/

#print axioms OwnLoc.readNA_preserves
#print axioms OwnLoc.afterWriteNA_self
#print axioms OwnLoc.afterWriteNA_other
#print axioms OwnLoc.preserved_by_atomic_load
#print axioms ReadOwnLoc.preserved_by_atomic_load
#print axioms OwnLoc.transfer_acquire
#print axioms SafeAndSatisfies.of_step
#print axioms SafeAndSatisfies.of_terminated
#print axioms SafeAndSatisfies.of_demonic_choice
#print axioms LoanRel.preserved_by_raw_write
#print axioms LoanRel.preserved_by_atomic_load
#print axioms promoteRaw_preserves_loanRel
#print axioms releaseRaw_preserves_rawRel
#print axioms zipSymTree_eq_ite
#print axioms evalSymTree_sound
#print axioms evalSymTree_abstracts
#print axioms atomicMaxAssign_evalSymTree_rfl
#print axioms atomicMaxAssign_satisfies_spec
#print axioms rawAddAndZero_evalSymTree_rfl
#print axioms rawAddAndZero_satisfies_spec
#print axioms reborrowRawMaxAssign_evalSymTree_rfl
#print axioms reborrowRawMaxAssign_satisfies_spec
#print axioms acquireReadRaw_evalSymTree_rfl
#print axioms acquireReadRaw_satisfies_spec

end HybridBorrowHeapPrototype
