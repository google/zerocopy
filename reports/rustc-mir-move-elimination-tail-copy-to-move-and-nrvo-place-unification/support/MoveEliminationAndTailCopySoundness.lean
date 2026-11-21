/-!
# MoveEliminationAndTailCopySoundness

Self-contained Lean 4 (core library only) mechanization of four small models of
the rustc MIR passes `TailCopyToMove` and `MoveElimination`
(`compiler/rustc_mir_transform/src/{tail_copy_to_move,move_elimination}.rs`,
`compiler/rustc_mir_dataflow/src/impls/precise_liveness.rs`).

* `Tail`   -- the backward return-tail scan (`backwardReturnTailScan`) that
  rewrites a final-use `Copy(x)` into `Move(x)`, with exact outcome equivalence
  and the sharpness counterexample `ce1`.
* `Unify`  -- whole-local place unification in a store where every allocation
  has an address picked by an explicit allocator choice, `AllocationInterval`
  rows, `DisjointLiveRanges`, the value and address-observation bisimulation,
  and the sharpness counterexample `ce2`.
* `Places` -- the transitive `Local -> Place` substitution (`unifyPlaces`).
* `Fixup`  -- the aggregate aliasing fixup (`aliasFixup`) and the sharpness
  counterexample `ce3`.

Every model is a deliberate abstraction; the accompanying report states what
each one does and does not capture.
-/

namespace MoveEliminationAndTailCopySoundness

/-! ## 0. Lockstep relation on optional outcomes (`none` models undefined behaviour) -/

/-- Two optional outcomes are related when both are undefined, or both are
defined and related by `R`. -/
def OptRel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | some a, some b => R a b
  | none, none => True
  | some _, none => False
  | none, some _ => False

theorem OptRel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {a : Option α} {b : Option β} {f : α → Option γ} {g : β → Option δ}
    (h : OptRel R a b) (hfg : ∀ x y, R x y → OptRel S (f x) (g y)) :
    OptRel S (a.bind f) (b.bind g) := by
  cases a with
  | none =>
    cases b with
    | none => exact True.intro
    | some y => exact False.elim h
  | some x =>
    cases b with
    | none => exact False.elim h
    | some y => exact hfg x y h

theorem OptRel.refl {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) (x : Option α) :
    OptRel R x x := by
  cases x with
  | none => exact True.intro
  | some a => exact hR a

theorem OptRel.mono {α β : Type} {R S : α → β → Prop} {x : Option α} {y : Option β}
    (hRS : ∀ a b, R a b → S a b) (h : OptRel R x y) : OptRel S x y := by
  cases x with
  | none =>
    cases y with
    | none => exact True.intro
    | some b => exact False.elim h
  | some a =>
    cases y with
    | none => exact False.elim h
    | some b => exact hRS a b h

theorem OptRel.none_iff {α β : Type} {R : α → β → Prop} {x : Option α} {y : Option β}
    (h : OptRel R x y) : y = none ↔ x = none := by
  cases x with
  | none =>
    cases y with
    | none => exact Iff.intro (fun _ => rfl) (fun _ => rfl)
    | some b => exact False.elim h
  | some a =>
    cases y with
    | none => exact False.elim h
    | some b => exact Iff.intro (fun hy => by cases hy) (fun hx => by cases hx)

theorem OptRel.exists_of_some {α β : Type} {R : α → β → Prop} {x : Option α} {y : Option β}
    {a : α} (h : OptRel R x y) (hx : x = some a) : ∃ b, y = some b ∧ R a b := by
  subst hx
  cases y with
  | none => exact False.elim h
  | some b => exact ⟨b, rfl, h⟩

/-! ## 1. `TailCopyToMove`: backward return-tail scan -/

namespace Tail

/-- A memory cell: the allocation of a MIR local, or a cell outside the frame
(caller-visible memory reachable only through pointers). -/
inductive Cell where
  | loc (l : Nat)
  | heap (a : Nat)
  deriving DecidableEq, Repr

/-- Values are flat; `opaque n` stands for any value whose structure the model
does not look into (aggregates are built by the uninterpreted `Interp.aggregate`). -/
inductive Val where
  | int (n : Nat)
  | ptr (c : Cell)
  | opaque (n : Nat)
  deriving DecidableEq, Repr

/-- The three local states of the proposed local-lifetime semantics: `dead`
(outside its storage scope), `live` (in scope, no allocation) and `alloc v`
(allocated, holding `v`). -/
inductive LState where
  | dead
  | live
  | alloc (v : Val)
  deriving DecidableEq, Repr

abbrev Store := Cell → LState

def Store.put (s : Store) (c : Cell) (x : LState) : Store := fun k => if k = c then x else s k

/-- `direct base proj idx`: a place whose first projection is not `Deref`.
`proj = none` is the bare local; `proj = some k` is an abstract stable
projection number `k`; `idx` lists the locals read by `Index` projections.
`deref p`: a place whose first projection dereferences local `p`. -/
inductive Place where
  | direct (base : Nat) (proj : Option Nat) (idx : List Nat)
  | deref (p : Nat)
  deriving DecidableEq, Repr

inductive Operand where
  | copy (p : Place)
  | move (p : Place)
  | const (n : Nat)
  deriving DecidableEq, Repr

inductive Rvalue where
  | use (op : Operand)
  | aggregate (ops : List Operand)
  | other
  deriving DecidableEq, Repr

inductive Stmt where
  | storageLive (l : Nat)
  | storageDead (l : Nat)
  | nop
  | assign (dst : Place) (rv : Rvalue)
  | setDiscriminant (dst : Place)
  | other
  deriving DecidableEq, Repr

/-- Uninterpreted parts of the semantics. The equivalence theorem holds for
every interpretation. -/
structure Interp where
  project : Nat → Val → Val
  inject : Nat → Option Val → Val → Val
  discr : Val → Val
  aggregate : List Val → Val
  otherRv : Store → Option (Val × Store)
  otherStmt : Store → Option Store

def LState.isAlloc : LState → Bool
  | .alloc _ => true
  | .dead => false
  | .live => false

noncomputable def allAlloc (s : Store) : List Nat → Bool
  | [] => true
  | i :: rest => (s (.loc i)).isAlloc && allAlloc s rest

noncomputable def readPlace (I : Interp) (s : Store) : Place → Option Val
  | .direct b pr idx =>
    if allAlloc s idx then
      match s (.loc b) with
      | .alloc v => some (match pr with | none => v | some k => I.project k v)
      | .live => none
      | .dead => none
    else none
  | .deref p =>
    match s (.loc p) with
    | .alloc (.ptr c) =>
      match s c with
      | .alloc v => some v
      | .live => none
      | .dead => none
    | _ => none

noncomputable def writePlace (I : Interp) (s : Store) (v : Val) : Place → Option Store
  | .direct b pr idx =>
    if allAlloc s idx then
      match s (.loc b) with
      | .dead => none
      | .live =>
        some (s.put (.loc b) (.alloc (match pr with | none => v | some k => I.inject k none v)))
      | .alloc w =>
        some (s.put (.loc b) (.alloc (match pr with | none => v | some k => I.inject k (some w) v)))
    else none
  | .deref p =>
    match s (.loc p) with
    | .alloc (.ptr c) =>
      match s c with
      | .alloc _ => some (s.put c (.alloc v))
      | .live => none
      | .dead => none
    | _ => none

/-- A whole-local move operand ends the allocation of that local (it becomes
`live`); a move through a projection behaves like a copy. -/
def afterMove (s : Store) : Place → Store
  | .direct b none _ => s.put (.loc b) .live
  | .direct _ (some _) _ => s
  | .deref _ => s

noncomputable def evalOperand (I : Interp) (s : Store) : Operand → Option (Val × Store)
  | .const n => some (.int n, s)
  | .copy pl => (readPlace I s pl).bind fun v => some (v, s)
  | .move pl => (readPlace I s pl).bind fun v => some (v, afterMove s pl)

noncomputable def evalOperands (I : Interp) : List Operand → Store → Option (List Val × Store)
  | [], s => some ([], s)
  | op :: rest, s =>
    (evalOperand I s op).bind fun r =>
      (evalOperands I rest r.2).bind fun rs => some (r.1 :: rs.1, rs.2)

noncomputable def evalRvalue (I : Interp) (s : Store) : Rvalue → Option (Val × Store)
  | .use op => evalOperand I s op
  | .aggregate ops => (evalOperands I ops s).bind fun r => some (I.aggregate r.1, r.2)
  | .other => I.otherRv s

noncomputable def exec (I : Interp) (s : Store) : Stmt → Option Store
  | .storageLive l => some (s.put (.loc l) .live)
  | .storageDead l => some (s.put (.loc l) .dead)
  | .nop => some s
  | .assign dst rv => (evalRvalue I s rv).bind fun r => writePlace I r.2 r.1 dst
  | .setDiscriminant dst => (readPlace I s dst).bind fun v => writePlace I s (I.discr v) dst
  | .other => I.otherStmt s

noncomputable def run (I : Interp) : List Stmt → Store → Option Store
  | [], s => some s
  | st :: rest, s => (exec I s st).bind (run I rest)

/-- Which of the two scan stops are enabled. The upstream pass enables both. -/
structure ScanCfg where
  stopIndirect : Bool
  stopBorrowedWrite : Bool

def upstreamCfg : ScanCfg := ⟨true, true⟩

/-- `process_operand`: the second component is `none` for `ControlFlow::Break`. -/
def scanOperand (cfg : ScanCfg) (used : List Nat) : Operand → Operand × Option (List Nat)
  | .const n => (.const n, some used)
  | .copy (.direct b pr idx) =>
    (if b ∈ used then .copy (.direct b pr idx) else .move (.direct b pr idx),
      some (b :: (idx ++ used)))
  | .move (.direct b pr idx) => (.move (.direct b pr idx), some (b :: (idx ++ used)))
  | .copy (.deref p) =>
    if cfg.stopIndirect then (.copy (.deref p), none) else (.copy (.deref p), some (p :: used))
  | .move (.deref p) =>
    if cfg.stopIndirect then (.move (.deref p), none) else (.move (.deref p), some (p :: used))

/-- Aggregate operands are scanned right to left; rewrites made before a
`Break` persist. -/
noncomputable def scanOperands (cfg : ScanCfg) : List Operand → List Nat → List Operand × Option (List Nat)
  | [], used => ([], some used)
  | op :: rest, used =>
    match (scanOperands cfg rest used).2 with
    | none => (op :: (scanOperands cfg rest used).1, none)
    | some used₁ =>
      ((scanOperand cfg used₁ op).1 :: (scanOperands cfg rest used).1,
        (scanOperand cfg used₁ op).2)

/-- `process_rvalue`. -/
noncomputable def scanRvalue (cfg : ScanCfg) (used : List Nat) : Rvalue → Rvalue × Option (List Nat)
  | .use op => (.use (scanOperand cfg used op).1, (scanOperand cfg used op).2)
  | .aggregate ops => (.aggregate (scanOperands cfg ops used).1, (scanOperands cfg ops used).2)
  | .other => (.other, none)

/-- One iteration of the `scan_block` loop. -/
noncomputable def scanStmt (cfg : ScanCfg) (borrowed : Nat → Bool) (used : List Nat) :
    Stmt → Stmt × Option (List Nat)
  | .storageLive l => (.storageLive l, some used)
  | .storageDead l => (.storageDead l, some used)
  | .nop => (.nop, some used)
  | .other => (.other, none)
  | .setDiscriminant (.deref p) =>
    if cfg.stopIndirect then (.setDiscriminant (.deref p), none)
    else (.setDiscriminant (.deref p), some (p :: used))
  | .setDiscriminant (.direct b pr idx) =>
    if cfg.stopBorrowedWrite && borrowed b then (.setDiscriminant (.direct b pr idx), none)
    else (.setDiscriminant (.direct b pr idx), some (b :: (idx ++ used)))
  | .assign (.deref p) rv =>
    if cfg.stopIndirect then (.assign (.deref p) rv, none)
    else (.assign (.deref p) (scanRvalue cfg (p :: used) rv).1, (scanRvalue cfg (p :: used) rv).2)
  | .assign (.direct b pr idx) rv =>
    if cfg.stopBorrowedWrite && borrowed b then (.assign (.direct b pr idx) rv, none)
    else
      (.assign (.direct b pr idx) (scanRvalue cfg (b :: (idx ++ used)) rv).1,
        (scanRvalue cfg (b :: (idx ++ used)) rv).2)

/-- `backwardReturnTailScan` on the reversed statement list (last statement first). -/
noncomputable def scanRev (cfg : ScanCfg) (borrowed : Nat → Bool) : List Stmt → List Nat → List Stmt
  | [], _ => []
  | st :: before, used =>
    match (scanStmt cfg borrowed used st).2 with
    | none => (scanStmt cfg borrowed used st).1 :: before
    | some used' => (scanStmt cfg borrowed used st).1 :: scanRev cfg borrowed before used'

/-- The pass on one straight-line return tail. `used_after` starts as `{_0}`. -/
noncomputable def tailCopyToMoveWith (cfg : ScanCfg) (borrowed : Nat → Bool) (tail : List Stmt) : List Stmt :=
  (scanRev cfg borrowed tail.reverse [0]).reverse

noncomputable def tailCopyToMove (borrowed : Nat → Bool) (tail : List Stmt) : List Stmt :=
  tailCopyToMoveWith upstreamCfg borrowed tail

/-- `s'` is `s` except that some locals outside `U` have already lost their
allocation (they are `live` instead). -/
def Rel (U : List Nat) (s s' : Store) : Prop :=
  ∀ c, s' c = s c ∨ (s' c = LState.live ∧ ∃ x, c = Cell.loc x ∧ ¬ x ∈ U)

theorem Rel.refl (U : List Nat) (s : Store) : Rel U s s := fun _ => Or.inl rfl

theorem Rel.mono {U U' : List Nat} {s s' : Store} (hsub : ∀ x, x ∈ U → x ∈ U')
    (h : Rel U' s s') : Rel U s s' := by
  intro c
  cases h c with
  | inl heq => exact Or.inl heq
  | inr hfree =>
    cases hfree with
    | intro hnone hx =>
      cases hx with
      | intro x hx =>
        exact Or.inr ⟨hnone, x, hx.1, fun hmem => hx.2 (hsub x hmem)⟩

theorem Rel.agree {U : List Nat} {s s' : Store} (h : Rel U s s') {x : Nat} (hx : x ∈ U) :
    s' (.loc x) = s (.loc x) := by
  cases h (.loc x) with
  | inl heq => exact heq
  | inr hfree =>
    cases hfree with
    | intro _ hy =>
      cases hy with
      | intro y hy =>
        have hxy : x = y := Cell.loc.inj hy.1
        exact False.elim (hy.2 (hxy ▸ hx))

theorem Rel.put {U : List Nat} {s s' : Store} (h : Rel U s s') (c : Cell) (x : LState) :
    Rel U (s.put c x) (s'.put c x) := by
  intro k
  by_cases hk : k = c
  · exact Or.inl (by simp [Store.put, hk])
  · cases h k with
    | inl heq => exact Or.inl (by simp [Store.put, hk, heq])
    | inr hfree => exact Or.inr ⟨by simp [Store.put, hk, hfree.1], hfree.2⟩

theorem Rel.liveRight {U : List Nat} {s s' : Store} (h : Rel U s s') {x : Nat}
    (hx : ¬ x ∈ U) : Rel U s (s'.put (.loc x) .live) := by
  intro k
  by_cases hk : k = Cell.loc x
  · exact Or.inr ⟨by simp [Store.put, hk], x, hk, hx⟩
  · cases h k with
    | inl heq => exact Or.inl (by simp [Store.put, hk, heq])
    | inr hfree => exact Or.inr ⟨by simp [Store.put, hk, hfree.1], hfree.2⟩

theorem allAlloc_congr {s s' : Store} :
    ∀ (idx : List Nat), (∀ i, i ∈ idx → s' (.loc i) = s (.loc i)) → allAlloc s' idx = allAlloc s idx
  | [], _ => rfl
  | i :: rest, h => by
    have hi : s' (.loc i) = s (.loc i) := h i (List.mem_cons_self ..)
    have hrest : allAlloc s' rest = allAlloc s rest :=
      allAlloc_congr rest (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp [allAlloc, hi, hrest]

theorem readPlace_agree (I : Interp) {U : List Nat} {s s' : Store} (h : Rel U s s')
    {b : Nat} (pr : Option Nat) {idx : List Nat} (hb : b ∈ U) (hidx : ∀ i, i ∈ idx → i ∈ U) :
    readPlace I s' (.direct b pr idx) = readPlace I s (.direct b pr idx) := by
  have h1 : allAlloc s' idx = allAlloc s idx :=
    allAlloc_congr idx (fun i hi => h.agree (hidx i hi))
  have h2 : s' (.loc b) = s (.loc b) := h.agree hb
  simp [readPlace, h1, h2]

theorem writePlace_rel (I : Interp) {U : List Nat} {s s' : Store} (h : Rel U s s')
    {b : Nat} (pr : Option Nat) {idx : List Nat} (v : Val)
    (hb : b ∈ U) (hidx : ∀ i, i ∈ idx → i ∈ U) :
    OptRel (Rel U) (writePlace I s v (.direct b pr idx)) (writePlace I s' v (.direct b pr idx)) := by
  have h1 : allAlloc s' idx = allAlloc s idx :=
    allAlloc_congr idx (fun i hi => h.agree (hidx i hi))
  have h2 : s' (.loc b) = s (.loc b) := h.agree hb
  cases hall : allAlloc s idx with
  | false => simp [writePlace, h1, hall, OptRel]
  | true =>
    cases hbase : s (.loc b) with
    | dead => simp [writePlace, h1, hall, h2, hbase, OptRel]
    | live =>
      simp only [writePlace, h1, hall, h2, hbase, ↓reduceIte, OptRel]
      exact h.put _ _
    | alloc w =>
      simp only [writePlace, h1, hall, h2, hbase, ↓reduceIte, OptRel]
      exact h.put _ _

/-- Hypothesis shape shared by all scan lemmas: after a successful scan step the
two stores are related at the enlarged `used` set; after a `Break` the stores
are still identical. -/
def Pre : Option (List Nat) → Store → Store → Prop
  | some U₂, s, s' => Rel U₂ s s'
  | none, s, s' => s' = s

/-- Result relation for operand and rvalue evaluation. -/
def ValRel (U : List Nat) (x y : Val × Store) : Prop := x.1 = y.1 ∧ Rel U x.2 y.2

def ValsRel (U : List Nat) (x y : List Val × Store) : Prop := x.1 = y.1 ∧ Rel U x.2 y.2

theorem ValRel.refl (U : List Nat) (x : Val × Store) : ValRel U x x := ⟨rfl, Rel.refl U x.2⟩

theorem ValsRel.refl (U : List Nat) (x : List Val × Store) : ValsRel U x x :=
  ⟨rfl, Rel.refl U x.2⟩

theorem mem_cons_append_right {x b : Nat} {idx U : List Nat} (h : x ∈ U) :
    x ∈ b :: (idx ++ U) :=
  List.mem_cons_of_mem _ (List.mem_append_right _ h)

theorem mem_cons_append_idx {x b : Nat} {idx U : List Nat} (h : x ∈ idx) :
    x ∈ b :: (idx ++ U) :=
  List.mem_cons_of_mem _ (List.mem_append_left _ h)

theorem scanOperand_sound (cfg : ScanCfg) (hcfg : cfg.stopIndirect = true) (I : Interp)
    (U : List Nat) (op : Operand) (s s' : Store)
    (hpre : Pre (scanOperand cfg U op).2 s s') :
    OptRel (ValRel U) (evalOperand I s op) (evalOperand I s' (scanOperand cfg U op).1) := by
  cases op with
  | const n =>
    exact ⟨rfl, hpre⟩
  | copy pl =>
    cases pl with
    | deref p =>
      simp only [scanOperand, ite_eq_left hcfg, Pre] at hpre ⊢
      subst hpre
      exact OptRel.refl (ValRel.refl U) _
    | direct b pr idx =>
      have hR : Rel (b :: (idx ++ U)) s s' := hpre
      have hread : readPlace I s' (.direct b pr idx) = readPlace I s (.direct b pr idx) :=
        readPlace_agree I hR pr (List.mem_cons_self ..) (fun i hi => mem_cons_append_idx hi)
      have hRU : Rel U s s' := hR.mono (fun x hx => mem_cons_append_right hx)
      by_cases hb : b ∈ U
      · simp only [scanOperand, ite_eq_left hb, evalOperand, hread]
        exact OptRel.bind (OptRel.refl (R := fun a b => a = b) (fun _ => rfl) _)
          (fun x y hxy => by subst hxy; exact ⟨rfl, hRU⟩)
      · simp only [scanOperand, ite_eq_right hb, evalOperand, hread]
        refine OptRel.bind (OptRel.refl (R := fun a b => a = b) (fun _ => rfl) _) ?_
        intro x y hxy
        subst hxy
        refine ⟨rfl, ?_⟩
        cases pr with
        | none => exact hRU.liveRight hb
        | some k => exact hRU
  | move pl =>
    cases pl with
    | deref p =>
      simp only [scanOperand, ite_eq_left hcfg, Pre] at hpre ⊢
      subst hpre
      exact OptRel.refl (ValRel.refl U) _
    | direct b pr idx =>
      have hR : Rel (b :: (idx ++ U)) s s' := hpre
      have hread : readPlace I s' (.direct b pr idx) = readPlace I s (.direct b pr idx) :=
        readPlace_agree I hR pr (List.mem_cons_self ..) (fun i hi => mem_cons_append_idx hi)
      have hRU : Rel U s s' := hR.mono (fun x hx => mem_cons_append_right hx)
      simp only [scanOperand, evalOperand, hread]
      refine OptRel.bind (OptRel.refl (R := fun a b => a = b) (fun _ => rfl) _) ?_
      intro x y hxy
      subst hxy
      refine ⟨rfl, ?_⟩
      cases pr with
      | none => exact hRU.put _ _
      | some k => exact hRU

theorem scanOperands_sound (cfg : ScanCfg) (hcfg : cfg.stopIndirect = true) (I : Interp) :
    ∀ (ops : List Operand) (U : List Nat) (s s' : Store),
      Pre (scanOperands cfg ops U).2 s s' →
      OptRel (ValsRel U) (evalOperands I ops s) (evalOperands I (scanOperands cfg ops U).1 s')
  | [], U, s, s', hpre => ⟨rfl, hpre⟩
  | op :: rest, U, s, s', hpre => by
    cases hrest : (scanOperands cfg rest U).2 with
    | none =>
      simp only [scanOperands, hrest, Pre] at hpre ⊢
      subst hpre
      simp only [evalOperands]
      refine OptRel.bind (OptRel.refl (R := fun a b => a = b) (fun _ => rfl) _) ?_
      intro x y hxy
      subst hxy
      have ih := scanOperands_sound cfg hcfg I rest U x.2 x.2 (by rw [hrest]; rfl)
      exact OptRel.bind ih (fun a b hab => ⟨by rw [hab.1], hab.2⟩)
    | some U₁ =>
      simp only [scanOperands, hrest] at hpre ⊢
      simp only [evalOperands]
      refine OptRel.bind (scanOperand_sound cfg hcfg I U₁ op s s' hpre) ?_
      intro x y hxy
      have ih := scanOperands_sound cfg hcfg I rest U x.2 y.2 (by rw [hrest]; exact hxy.2)
      exact OptRel.bind ih (fun a b hab => ⟨by rw [hxy.1, hab.1], hab.2⟩)

theorem scanRvalue_sound (cfg : ScanCfg) (hcfg : cfg.stopIndirect = true) (I : Interp)
    (U : List Nat) (rv : Rvalue) (s s' : Store)
    (hpre : Pre (scanRvalue cfg U rv).2 s s') :
    OptRel (ValRel U) (evalRvalue I s rv) (evalRvalue I s' (scanRvalue cfg U rv).1) := by
  cases rv with
  | use op => exact scanOperand_sound cfg hcfg I U op s s' hpre
  | aggregate ops =>
    simp only [scanRvalue, evalRvalue]
    exact OptRel.bind (scanOperands_sound cfg hcfg I ops U s s' hpre)
      (fun a b hab => ⟨by rw [hab.1], hab.2⟩)
  | other =>
    simp only [scanRvalue, Pre] at hpre ⊢
    subst hpre
    exact OptRel.refl (ValRel.refl U) _

theorem scanStmt_sound (cfg : ScanCfg) (hcfg : cfg.stopIndirect = true) (I : Interp)
    (borrowed : Nat → Bool) (U : List Nat) (st : Stmt) (s s' : Store)
    (hpre : Pre (scanStmt cfg borrowed U st).2 s s') :
    OptRel (Rel U) (exec I s st) (exec I s' (scanStmt cfg borrowed U st).1) := by
  cases st with
  | storageLive l => exact Rel.put hpre _ _
  | storageDead l => exact Rel.put hpre _ _
  | nop => exact hpre
  | other =>
    simp only [scanStmt, Pre] at hpre ⊢
    subst hpre
    exact OptRel.refl (Rel.refl U) _
  | setDiscriminant dst =>
    cases dst with
    | deref p =>
      simp only [scanStmt, ite_eq_left hcfg, Pre] at hpre ⊢
      subst hpre
      exact OptRel.refl (Rel.refl U) _
    | direct b pr idx =>
      by_cases hstop : (cfg.stopBorrowedWrite && borrowed b) = true
      · simp only [scanStmt, ite_eq_left hstop, Pre] at hpre ⊢
        subst hpre
        exact OptRel.refl (Rel.refl U) _
      · simp only [scanStmt, ite_eq_right hstop, Pre] at hpre ⊢
        have hread : readPlace I s' (.direct b pr idx) = readPlace I s (.direct b pr idx) :=
          readPlace_agree I hpre pr (List.mem_cons_self ..) (fun i hi => mem_cons_append_idx hi)
        simp only [exec, hread]
        refine OptRel.bind (OptRel.refl (R := fun a b => a = b) (fun _ => rfl) _) ?_
        intro x y hxy
        subst hxy
        exact OptRel.mono (fun a b hab => Rel.mono (fun z hz => mem_cons_append_right hz) hab)
          (writePlace_rel I hpre pr (I.discr x) (List.mem_cons_self ..)
            (fun i hi => mem_cons_append_idx hi))
  | assign dst rv =>
    cases dst with
    | deref p =>
      simp only [scanStmt, ite_eq_left hcfg, Pre] at hpre ⊢
      subst hpre
      exact OptRel.refl (Rel.refl U) _
    | direct b pr idx =>
      by_cases hstop : (cfg.stopBorrowedWrite && borrowed b) = true
      · simp only [scanStmt, ite_eq_left hstop, Pre] at hpre ⊢
        subst hpre
        exact OptRel.refl (Rel.refl U) _
      · simp only [scanStmt, ite_eq_right hstop] at hpre ⊢
        simp only [exec]
        refine OptRel.bind (scanRvalue_sound cfg hcfg I (b :: (idx ++ U)) rv s s' hpre) ?_
        intro x y hxy
        rw [hxy.1]
        exact OptRel.mono (fun a b hab => Rel.mono (fun z hz => mem_cons_append_right hz) hab)
          (writePlace_rel I hxy.2 pr y.1 (List.mem_cons_self ..)
            (fun i hi => mem_cons_append_idx hi))

theorem run_append_single (I : Interp) :
    ∀ (xs : List Stmt) (st : Stmt) (s : Store),
      run I (xs ++ [st]) s = (run I xs s).bind (fun m => exec I m st)
  | [], st, s => by
    simp only [List.nil_append, run, Option.bind]
    cases exec I s st <;> rfl
  | x :: xs, st, s => by
    simp only [List.cons_append, run]
    cases hx : exec I s x with
    | none => rfl
    | some m => simpa [Option.bind] using run_append_single I xs st m

theorem scanRev_sound (cfg : ScanCfg) (hcfg : cfg.stopIndirect = true) (I : Interp)
    (borrowed : Nat → Bool) :
    ∀ (rev : List Stmt) (U : List Nat) (s : Store),
      OptRel (Rel U) (run I rev.reverse s) (run I (scanRev cfg borrowed rev U).reverse s)
  | [], U, s => Rel.refl U s
  | st :: before, U, s => by
    cases hst : (scanStmt cfg borrowed U st).2 with
    | none =>
      simp only [scanRev, hst, List.reverse_cons, run_append_single]
      refine OptRel.bind (OptRel.refl (R := fun a b => a = b) (fun _ => rfl) _) ?_
      intro m m' hm
      subst hm
      exact scanStmt_sound cfg hcfg I borrowed U st m m (by rw [hst]; rfl)
    | some U' =>
      simp only [scanRev, hst, List.reverse_cons, run_append_single]
      refine OptRel.bind (scanRev_sound cfg hcfg I borrowed before U' s) ?_
      intro m m' hm
      exact scanStmt_sound cfg hcfg I borrowed U st m m' (by rw [hst]; exact hm)

/-- What survives the `Return`: the return place `_0` and every cell outside
the frame. All other locals are deallocated by the return itself. -/
def exitStore (t : Store) : Cell → LState
  | .loc 0 => t (.loc 0)
  | .loc (_ + 1) => .dead
  | .heap a => t (.heap a)

theorem exitStore_eq_of_rel {t t' : Store} (h : Rel [0] t t') :
    ∀ c, exitStore t' c = exitStore t c := by
  intro c
  cases c with
  | heap a =>
    cases h (.heap a) with
    | inl heq => exact heq
    | inr hfree =>
      cases hfree.2 with
      | intro x hx => exact Cell.noConfusion hx.1
  | loc l =>
    cases l with
    | zero => exact h.agree (List.mem_cons_self ..)
    | succ n => rfl

/-- **Theorem 1 (exact return-value and memory equivalence of `TailCopyToMove`).**
For every interpretation of the unmodelled constructs, every borrowed-local set,
every straight-line return tail and every initial store, the original tail and
the rewritten tail are either both undefined or both defined with the same
return value in `_0` and the same contents of every cell outside the frame.
Only the indirect-access stop is needed in this allocation-identity model. -/
theorem tailCopyToMove_exact_return_value_and_memory_equivalence
    (cfg : ScanCfg) (hcfg : cfg.stopIndirect = true) (I : Interp)
    (borrowed : Nat → Bool) (tail : List Stmt) (s : Store) :
    OptRel (fun t t' => ∀ c, exitStore t' c = exitStore t c)
      (run I tail s) (run I (tailCopyToMoveWith cfg borrowed tail) s) := by
  have h := scanRev_sound cfg hcfg I borrowed tail.reverse [0] s
  rw [List.reverse_reverse] at h
  exact OptRel.mono (fun t t' hrel => exitStore_eq_of_rel hrel) h

/-- The rewritten tail has undefined behaviour exactly when the original has. -/
theorem tailCopyToMove_ub_iff (I : Interp) (borrowed : Nat → Bool) (tail : List Stmt)
    (s : Store) :
    run I (tailCopyToMove borrowed tail) s = none ↔ run I tail s = none :=
  OptRel.none_iff
    (tailCopyToMove_exact_return_value_and_memory_equivalence upstreamCfg rfl I borrowed tail s)

/-- Defined executions return the same value and leave the same outside memory. -/
theorem tailCopyToMove_preserves_return_and_heap (I : Interp) (borrowed : Nat → Bool)
    (tail : List Stmt) (s t : Store) (hrun : run I tail s = some t) :
    ∃ t', run I (tailCopyToMove borrowed tail) s = some t' ∧
      t' (.loc 0) = t (.loc 0) ∧ ∀ a, t' (.heap a) = t (.heap a) := by
  have h := tailCopyToMove_exact_return_value_and_memory_equivalence
    upstreamCfg rfl I borrowed tail s
  cases OptRel.exists_of_some h hrun with
  | intro t' ht' => exact ⟨t', ht'.1, ht'.2 (.loc 0), fun a => ht'.2 (.heap a)⟩

/-- The same equivalence with the borrowed-destination stop switched off: in
this allocation-identity model that stop is not what makes the rewrite sound
(its upstream justification concerns address overlap, which this model does not
represent). -/
theorem tailCopyToMove_equivalence_without_borrowed_write_stop (I : Interp)
    (borrowed : Nat → Bool) (tail : List Stmt) (s : Store) :
    OptRel (fun t t' => ∀ c, exitStore t' c = exitStore t c)
      (run I tail s) (run I (tailCopyToMoveWith ⟨true, false⟩ borrowed tail) s) :=
  tailCopyToMove_exact_return_value_and_memory_equivalence ⟨true, false⟩ rfl I borrowed tail s

/-! ### Sharpness counterexample 1: scanning past an indirect read -/

def ceInterp : Interp :=
  { project := fun _ v => v
    inject := fun _ _ v => v
    discr := fun v => v
    aggregate := fun _ => .opaque 0
    otherRv := fun _ => none
    otherStmt := fun _ => none }

/-- `_2 = copy _1; _0 = copy (*_3)` with `_3 = &_1`. -/
def ce1Tail : List Stmt :=
  [ .assign (.direct 2 none []) (.use (.copy (.direct 1 none []))),
    .assign (.direct 0 none []) (.use (.copy (.deref 3))) ]

def ce1Borrowed : Nat → Bool := fun l => l == 1

def ce1Store : Store := fun c =>
  match c with
  | .loc 1 => .alloc (.int 7)
  | .loc 3 => .alloc (.ptr (.loc 1))
  | _ => .live

/-- The scan with the indirect-access stop disabled. -/
def noIndirectStopCfg : ScanCfg := ⟨false, true⟩

/-- **Counterexample 1.** Without the indirect-access stop the scan rewrites
`_2 = copy _1` into `_2 = move _1` although the later read `*_3` still reaches
`_1`; the original tail returns `7`, the rewritten tail is undefined. The
upstream configuration leaves the tail unchanged. -/
theorem ce1_tail_copy_to_move_past_indirect_borrow_read_unsound :
    (run ceInterp ce1Tail ce1Store).map (fun t => t (.loc 0)) = some (.alloc (.int 7)) ∧
    tailCopyToMoveWith noIndirectStopCfg ce1Borrowed ce1Tail =
      [ .assign (.direct 2 none []) (.use (.move (.direct 1 none []))),
        .assign (.direct 0 none []) (.use (.copy (.deref 3))) ] ∧
    (run ceInterp (tailCopyToMoveWith noIndirectStopCfg ce1Borrowed ce1Tail) ce1Store).isNone
      = true ∧
    tailCopyToMove ce1Borrowed ce1Tail = ce1Tail := by
  decide

/-- A positive instance: the borrowed-local return `_0 = copy _2` (the
`buf`-returning shape) is rewritten to a move by the upstream configuration,
because the return place is not borrowed and nothing later touches `_2`. -/
theorem tail_rewrites_borrowed_local_return :
    tailCopyToMove (fun l => l == 2)
      [ .storageDead 4,
        .assign (.direct 0 none []) (.use (.copy (.direct 2 none []))),
        .storageDead 2 ] =
      [ .storageDead 4,
        .assign (.direct 0 none []) (.use (.move (.direct 2 none []))),
        .storageDead 2 ] := by
  decide

/-- A write to a borrowed destination stops the upstream scan before the
operand is examined. -/
theorem tail_stops_at_borrowed_destination :
    tailCopyToMove (fun l => l == 0 || l == 2)
      [ .assign (.direct 0 none []) (.use (.copy (.direct 2 none []))) ] =
      [ .assign (.direct 0 none []) (.use (.copy (.direct 2 none []))) ] := by
  decide

end Tail

/-! ## 2. `MoveElimination`: whole-local unification with observable addresses -/

namespace Unify

theorem bind_some_inv {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : x.bind f = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

/-- A pointer carries the local it was derived from and the numeric address of
that local's allocation at the time. Only the address is compared by `ptrEq`. -/
inductive Val where
  | int (n : Nat)
  | ptr (l : Nat) (a : Nat)
  deriving DecidableEq, Repr

/-- A live allocation: its address and its contents. -/
structure Slot where
  addr : Nat
  val : Val
  deriving DecidableEq, Repr

/-- `none`: the local currently has no allocation. -/
abbrev Store := Nat → Option Slot

def emptyStore : Store := fun _ => none

def Store.free (s : Store) (l : Nat) : Store := fun k => if k = l then none else s k

/-- Address used by a write to `d`: the current one if `d` is allocated,
otherwise the allocator's choice `c` for a fresh allocation. -/
def Store.addrFor (s : Store) (d c : Nat) : Nat :=
  match s d with
  | some sl => sl.addr
  | none => c

def Store.write (s : Store) (d c : Nat) (v : Val) : Store :=
  fun k => if k = d then some ⟨s.addrFor d c, v⟩ else s k

def Store.ptrAt (s : Store) (p : Nat) : Option (Nat × Nat) :=
  match s p with
  | some ⟨_, .ptr l a⟩ => some (l, a)
  | some ⟨_, .int _⟩ => none
  | none => none

/-- Dereference: the pointee local must be allocated at the pointer's address. -/
def Store.deref (s : Store) (l a : Nat) : Option Val :=
  match s l with
  | some sl => if sl.addr = a then some sl.val else none
  | none => none

inductive Stmt where
  | const (d n : Nat)
  | copy (d x : Nat)
  | move (d x : Nat)
  | addrOf (d x : Nat)
  | ptrEq (d p q : Nat)
  | load (d p : Nat)
  | store (p x : Nat)
  | storageDead (l : Nat)
  | nop
  deriving DecidableEq, Repr

/-- One statement. `c` is the address the allocator would hand out if this
statement has to create an allocation for its destination. Operands are
evaluated (and a moved-from local freed) before the destination is allocated. -/
def step (c : Nat) (s : Store) : Stmt → Option Store
  | .const d n => some (s.write d c (.int n))
  | .copy d x => (s x).bind fun sx => some (s.write d c sx.val)
  | .move d x => (s x).bind fun sx => some ((s.free x).write d c sx.val)
  | .addrOf d x => (s x).bind fun sx => some (s.write d c (.ptr x sx.addr))
  | .ptrEq d p q =>
    (s.ptrAt p).bind fun pa =>
      (s.ptrAt q).bind fun qa => some (s.write d c (.int (if pa.2 = qa.2 then 1 else 0)))
  | .load d p =>
    (s.ptrAt p).bind fun pa => (s.deref pa.1 pa.2).bind fun v => some (s.write d c v)
  | .store p x =>
    (s.ptrAt p).bind fun pa =>
      (s x).bind fun sx => (s.deref pa.1 pa.2).bind fun _ => some (s.write pa.1 c sx.val)
  | .storageDead l => some (s.free l)
  | .nop => some s

/-- A program annotated with the allocator choice available to each statement. -/
noncomputable def run : List (Nat × Stmt) → Store → Option Store
  | [], s => some s
  | x :: rest, s => (step x.1 s x.2).bind (run rest)

def renVal (σ : Nat → Nat) : Val → Val
  | .int n => .int n
  | .ptr l a => .ptr (σ l) a

/-- Rewrite of one statement under the unification map `σ`: uses are renamed,
assignments that became self-assignments are deleted, storage markers are
erased (the real pass rebuilds them afterwards from the merged matrix). -/
def unifyStmt (σ : Nat → Nat) : Stmt → Stmt
  | .const d n => .const (σ d) n
  | .copy d x => if σ d = σ x then .nop else .copy (σ d) (σ x)
  | .move d x => if σ d = σ x then .nop else .move (σ d) (σ x)
  | .addrOf d x => .addrOf (σ d) (σ x)
  | .ptrEq d p q => .ptrEq (σ d) (σ p) (σ q)
  | .load d p => .load (σ d) (σ p)
  | .store p x => .store (σ p) (σ x)
  | .storageDead _ => .nop
  | .nop => .nop

def unifyProg (σ : Nat → Nat) (ap : List (Nat × Stmt)) : List (Nat × Stmt) :=
  ap.map fun x => (x.1, unifyStmt σ x.2)

/-- Every allocated original local is allocated in the unified store under its
representative, at the same address, with the renamed value. -/
def Rel (σ : Nat → Nat) (s s' : Store) : Prop :=
  ∀ l sl, s l = some sl → s' (σ l) = some ⟨sl.addr, renVal σ sl.val⟩

/-- Semantic content of `DisjointLiveRanges`: two different locals of the same
unification class are never allocated at the same time. -/
def ClassDisjoint (σ : Nat → Nat) (s : Store) : Prop :=
  ∀ l₁ l₂ sl₁ sl₂, s l₁ = some sl₁ → s l₂ = some sl₂ → σ l₁ = σ l₂ → l₁ = l₂

/-- The allocator invariant: simultaneously live allocations have distinct addresses. -/
def Valid (s : Store) : Prop :=
  ∀ l₁ l₂ sl₁ sl₂, s l₁ = some sl₁ → s l₂ = some sl₂ → sl₁.addr = sl₂.addr → l₁ = l₂

def Stmt.dest : Stmt → Option Nat
  | .const d _ => some d
  | .copy d _ => some d
  | .move d _ => some d
  | .addrOf d _ => some d
  | .ptrEq d _ _ => some d
  | .load d _ => some d
  | .store _ _ => none
  | .storageDead _ => none
  | .nop => none

/-- The allocator choice the *original* program is given: whatever address the
unified execution has (or is about to pick) for the destination's representative. -/
def origChoice (σ : Nat → Nat) (s' : Store) (c' : Nat) (st : Stmt) : Nat :=
  match st.dest with
  | some d => s'.addrFor (σ d) c'
  | none => c'

theorem write_same (s : Store) (d c : Nat) (v : Val) :
    (s.write d c v) d = some ⟨s.addrFor d c, v⟩ := by
  simp [Store.write]

theorem write_other (s : Store) {d k : Nat} (c : Nat) (v : Val) (h : ¬ k = d) :
    (s.write d c v) k = s k := by
  simp [Store.write, h]

theorem free_same (s : Store) (l : Nat) : (s.free l) l = none := by
  simp [Store.free]

theorem free_other (s : Store) {l k : Nat} (h : ¬ k = l) : (s.free l) k = s k := by
  simp [Store.free, h]

theorem addrFor_rel {σ : Nat → Nat} {s s' : Store} (hR : Rel σ s s') (d c' : Nat) :
    s.addrFor d (s'.addrFor (σ d) c') = s'.addrFor (σ d) c' := by
  cases hs : s d with
  | none => simp [Store.addrFor, hs]
  | some sl =>
    have h := hR d sl hs
    simp [Store.addrFor, hs, h]

theorem rel_write {σ : Nat → Nat} {s s' : Store} (hR : Rel σ s s') (d c' : Nat) (v : Val)
    (hpost : ClassDisjoint σ (s.write d (s'.addrFor (σ d) c') v)) :
    Rel σ (s.write d (s'.addrFor (σ d) c') v) (s'.write (σ d) c' (renVal σ v)) := by
  intro l sl hl
  by_cases hld : l = d
  · subst hld
    rw [write_same] at hl
    have hsl : sl = ⟨s.addrFor l (s'.addrFor (σ l) c'), v⟩ := (Option.some.inj hl).symm
    subst hsl
    rw [write_same, addrFor_rel hR]
  · rw [write_other _ _ _ hld] at hl
    by_cases hσ : σ l = σ d
    · exact absurd
        (hpost l d sl _ (by rw [write_other _ _ _ hld]; exact hl) (write_same _ _ _ _) hσ) hld
    · rw [write_other _ _ _ hσ]
      exact hR l sl hl

theorem rel_free {σ : Nat → Nat} {s s' : Store} (hR : Rel σ s s') (hpre : ClassDisjoint σ s)
    {x : Nat} {sx : Slot} (hx : s x = some sx) : Rel σ (s.free x) (s'.free (σ x)) := by
  intro l sl hl
  by_cases hlx : l = x
  · rw [hlx, free_same] at hl
    cases hl
  · rw [free_other _ hlx] at hl
    by_cases hσ : σ l = σ x
    · exact absurd (hpre l x sl sx hl hx hσ) hlx
    · rw [free_other _ hσ]
      exact hR l sl hl

theorem write_alloc_choice {s : Store} {l : Nat} {sl : Slot} (h : s l = some sl)
    (c₁ c₂ : Nat) (v : Val) : s.write l c₁ v = s.write l c₂ v := by
  funext k
  simp [Store.write, Store.addrFor, h]

theorem ptrAt_rel {σ : Nat → Nat} {s s' : Store} (hR : Rel σ s s') {p : Nat} {pa : Nat × Nat}
    (h : s.ptrAt p = some pa) : s'.ptrAt (σ p) = some (σ pa.1, pa.2) := by
  cases hs : s p with
  | none => simp [Store.ptrAt, hs] at h
  | some sl =>
    cases sl with
    | mk a v =>
      cases v with
      | int n => simp [Store.ptrAt, hs] at h
      | ptr l b =>
        have hpa : pa = (l, b) := by
          simp [Store.ptrAt, hs] at h
          exact h.symm
        have h' := hR p ⟨a, .ptr l b⟩ hs
        simp [Store.ptrAt, h', renVal, hpa]

theorem deref_rel {σ : Nat → Nat} {s s' : Store} (hR : Rel σ s s') {l a : Nat} {v : Val}
    (h : s.deref l a = some v) : s'.deref (σ l) a = some (renVal σ v) := by
  cases hs : s l with
  | none => simp [Store.deref, hs] at h
  | some sl =>
    have h' := hR l sl hs
    by_cases ha : sl.addr = a
    · simp [Store.deref, hs, ha] at h
      simp [Store.deref, h', ha, h]
    · simp [Store.deref, hs, ha] at h

theorem deref_alloc {s : Store} {l a : Nat} {v : Val} (h : s.deref l a = some v) :
    ∃ sl, s l = some sl := by
  cases hs : s l with
  | none => simp [Store.deref, hs] at h
  | some sl => exact ⟨sl, rfl⟩

/-- **One-step refinement.** If the original statement is defined when its
allocator choice is read off the unified execution, and no two locals of one
class are allocated together before or after it, then the unified statement is
defined and the stores stay related (same addresses, renamed values). -/
theorem step_refines (σ : Nat → Nat) (c' : Nat) (st : Stmt) (s s' t : Store)
    (hR : Rel σ s s') (hpre : ClassDisjoint σ s) (hpost : ClassDisjoint σ t)
    (hstep : step (origChoice σ s' c' st) s st = some t) :
    ∃ t', step c' s' (unifyStmt σ st) = some t' ∧ Rel σ t t' := by
  cases st with
  | const d n =>
    have ht : t = s.write d (s'.addrFor (σ d) c') (.int n) := (Option.some.inj hstep).symm
    subst ht
    exact ⟨_, rfl, rel_write hR d c' (.int n) hpost⟩
  | copy d x =>
    cases bind_some_inv hstep with
    | intro sx hsx =>
      have hx : s x = some sx := hsx.1
      have ht : t = s.write d (s'.addrFor (σ d) c') sx.val := (Option.some.inj hsx.2).symm
      subst ht
      have hx' : s' (σ x) = some ⟨sx.addr, renVal σ sx.val⟩ := hR x sx hx
      by_cases hσ : σ d = σ x
      · refine ⟨s', ?_, ?_⟩
        · simp [unifyStmt, hσ, step]
        · intro l sl hl
          by_cases hld : l = d
          · subst hld
            rw [write_same] at hl
            have hsl : sl = ⟨s.addrFor l (s'.addrFor (σ l) c'), sx.val⟩ :=
              (Option.some.inj hl).symm
            subst hsl
            show s' (σ l) = some ⟨s.addrFor l (s'.addrFor (σ l) c'), renVal σ sx.val⟩
            rw [addrFor_rel hR]
            simp [Store.addrFor, hσ, hx']
          · rw [write_other _ _ _ hld] at hl
            exact hR l sl hl
      · refine ⟨s'.write (σ d) c' (renVal σ sx.val), ?_, rel_write hR d c' sx.val hpost⟩
        simp [unifyStmt, hσ, step, hx']
  | move d x =>
    cases bind_some_inv hstep with
    | intro sx hsx =>
      have hx : s x = some sx := hsx.1
      have ht : t = (s.free x).write d (s'.addrFor (σ d) c') sx.val :=
        (Option.some.inj hsx.2).symm
      subst ht
      have hx' : s' (σ x) = some ⟨sx.addr, renVal σ sx.val⟩ := hR x sx hx
      by_cases hσ : σ d = σ x
      · refine ⟨s', ?_, ?_⟩
        · simp [unifyStmt, hσ, step]
        · intro l sl hl
          by_cases hld : l = d
          · subst hld
            rw [write_same] at hl
            have hsl : sl = ⟨(s.free x).addrFor l (s'.addrFor (σ l) c'), sx.val⟩ :=
              (Option.some.inj hl).symm
            subst hsl
            show s' (σ l) = some ⟨(s.free x).addrFor l (s'.addrFor (σ l) c'), renVal σ sx.val⟩
            have hnone : (s.free x) l = none := by
              by_cases hlx : l = x
              · rw [hlx]
                exact free_same s x
              · rw [free_other _ hlx]
                cases hsd : s l with
                | none => rfl
                | some sd => exact absurd (hpre l x sd sx hsd hx hσ) hlx
            simp [Store.addrFor, hnone, hσ, hx']
          · rw [write_other _ _ _ hld] at hl
            by_cases hlx : l = x
            · rw [hlx, free_same] at hl
              cases hl
            · rw [free_other _ hlx] at hl
              exact hR l sl hl
      · have hRf : Rel σ (s.free x) (s'.free (σ x)) := rel_free hR hpre hx
        have haddr : (s'.free (σ x)).addrFor (σ d) c' = s'.addrFor (σ d) c' := by
          simp [Store.addrFor, Store.free, hσ]
        have hpost' :
            ClassDisjoint σ ((s.free x).write d ((s'.free (σ x)).addrFor (σ d) c') sx.val) := by
          rw [haddr]
          exact hpost
        have hrel := rel_write hRf d c' sx.val hpost'
        rw [haddr] at hrel
        refine ⟨(s'.free (σ x)).write (σ d) c' (renVal σ sx.val), ?_, hrel⟩
        simp [unifyStmt, hσ, step, hx']
  | addrOf d x =>
    cases bind_some_inv hstep with
    | intro sx hsx =>
      have hx : s x = some sx := hsx.1
      have ht : t = s.write d (s'.addrFor (σ d) c') (.ptr x sx.addr) :=
        (Option.some.inj hsx.2).symm
      subst ht
      have hx' : s' (σ x) = some ⟨sx.addr, renVal σ sx.val⟩ := hR x sx hx
      refine ⟨s'.write (σ d) c' (renVal σ (.ptr x sx.addr)), ?_, rel_write hR d c' _ hpost⟩
      simp [unifyStmt, step, hx', renVal]
  | ptrEq d p q =>
    cases bind_some_inv hstep with
    | intro pa hpa =>
      cases bind_some_inv hpa.2 with
      | intro qa hqa =>
        have ht : t = s.write d (s'.addrFor (σ d) c') (.int (if pa.2 = qa.2 then 1 else 0)) :=
          (Option.some.inj hqa.2).symm
        subst ht
        have hp' := ptrAt_rel hR hpa.1
        have hq' := ptrAt_rel hR hqa.1
        refine ⟨s'.write (σ d) c' (renVal σ (.int (if pa.2 = qa.2 then 1 else 0))), ?_,
          rel_write hR d c' _ hpost⟩
        simp [unifyStmt, step, hp', hq', renVal]
  | load d p =>
    cases bind_some_inv hstep with
    | intro pa hpa =>
      cases bind_some_inv hpa.2 with
      | intro v hv =>
        have ht : t = s.write d (s'.addrFor (σ d) c') v := (Option.some.inj hv.2).symm
        subst ht
        have hp' := ptrAt_rel hR hpa.1
        have hv' := deref_rel hR hv.1
        refine ⟨s'.write (σ d) c' (renVal σ v), ?_, rel_write hR d c' v hpost⟩
        simp [unifyStmt, step, hp', hv']
  | store p x =>
    cases bind_some_inv hstep with
    | intro pa hpa =>
      cases bind_some_inv hpa.2 with
      | intro sx hsx =>
        cases bind_some_inv hsx.2 with
        | intro w hw =>
          have ht : t = s.write pa.1 c' sx.val := (Option.some.inj hw.2).symm
          subst ht
          cases deref_alloc hw.1 with
          | intro sl hsl =>
            have hp' := ptrAt_rel hR hpa.1
            have hx' : s' (σ x) = some ⟨sx.addr, renVal σ sx.val⟩ := hR x sx hsx.1
            have hw' := deref_rel hR hw.1
            have hch : s.write pa.1 c' sx.val
                = s.write pa.1 (s'.addrFor (σ pa.1) c') sx.val :=
              write_alloc_choice hsl _ _ _
            rw [hch] at hpost ⊢
            refine ⟨s'.write (σ pa.1) c' (renVal σ sx.val), ?_,
              rel_write hR pa.1 c' sx.val hpost⟩
            simp [unifyStmt, step, hp', hx', hw']
  | storageDead l =>
    have ht : t = s.free l := (Option.some.inj hstep).symm
    subst ht
    refine ⟨s', rfl, ?_⟩
    intro k sk hk
    by_cases hkl : k = l
    · rw [hkl, free_same] at hk
      cases hk
    · rw [free_other _ hkl] at hk
      exact hR k sk hk
  | nop =>
    have ht : t = s := (Option.some.inj hstep).symm
    subst ht
    exact ⟨s', rfl, hR⟩

/-- `P` holds at every state the annotated program passes through. -/
noncomputable def AllAlong (P : Store → Prop) : List (Nat × Stmt) → Store → Prop
  | [], s => P s
  | x :: rest, s => P s ∧ ∀ s₁, step x.1 s x.2 = some s₁ → AllAlong P rest s₁

theorem AllAlong.head {P : Store → Prop} :
    ∀ {ap : List (Nat × Stmt)} {s : Store}, AllAlong P ap s → P s
  | [], _, h => h
  | _ :: _, _, h => h.1

/-- The original program's allocator choices, read off a lockstep run against
the unified program whose own choices are the annotations in `ap`. -/
noncomputable def origAnnot (σ : Nat → Nat) : List (Nat × Stmt) → Store → Store → List (Nat × Stmt)
  | [], _, _ => []
  | x :: rest, s, s' =>
    (origChoice σ s' x.1 x.2, x.2) ::
      (match step (origChoice σ s' x.1 x.2) s x.2, step x.1 s' (unifyStmt σ x.2) with
        | some s₁, some s₁' => origAnnot σ rest s₁ s₁'
        | some _, none => rest
        | none, _ => rest)

/-- **Theorem 2a (value and address-observation bisimulation of whole-local
unification).** Take any execution of the unified program (allocator choices
`ap`). Run the original program with the allocator choices `origAnnot` reads off
that execution. If the original run is defined and never has two locals of one
unification class allocated at once, then the unified run is defined and the
final stores are related: every allocated original local sits at the same
address as its representative and holds the renamed value. -/
theorem moveElimination_value_and_address_bisimulation (σ : Nat → Nat) :
    ∀ (ap : List (Nat × Stmt)) (s s' t : Store), Rel σ s s' →
      AllAlong (ClassDisjoint σ) (origAnnot σ ap s s') s →
      run (origAnnot σ ap s s') s = some t →
      ∃ t', run (unifyProg σ ap) s' = some t' ∧ Rel σ t t'
  | [], s, s', t, hR, _, hrun => by
    have ht : t = s := (Option.some.inj hrun).symm
    subst ht
    exact ⟨s', rfl, hR⟩
  | x :: rest, s, s', t, hR, hD, hrun => by
    simp only [origAnnot, run, AllAlong] at hD hrun
    cases hs : step (origChoice σ s' x.1 x.2) s x.2 with
    | none =>
      rw [hs] at hrun
      simp at hrun
    | some s₁ =>
      have hpost : ClassDisjoint σ s₁ := AllAlong.head (hD.2 s₁ hs)
      cases step_refines σ x.1 x.2 s s' s₁ hR hD.1 hpost hs with
      | intro s₁' hs' =>
        have hD₁ := hD.2 s₁ hs
        rw [hs, hs'.1] at hD₁ hrun
        simp only [Option.bind] at hrun
        cases moveElimination_value_and_address_bisimulation σ rest s₁ s₁' t hs'.2 hD₁ hrun with
        | intro t' ht' =>
          refine ⟨t', ?_, ht'.2⟩
          simp only [unifyProg, List.map, run, hs'.1, Option.bind]
          exact ht'.1

theorem valid_of_rel {σ : Nat → Nat} {s s' : Store} (hR : Rel σ s s')
    (hD : ClassDisjoint σ s) (hV : Valid s') : Valid s := by
  intro l₁ l₂ sl₁ sl₂ h₁ h₂ haddr
  have h₁' := hR l₁ sl₁ h₁
  have h₂' := hR l₂ sl₂ h₂
  exact hD l₁ l₂ sl₁ sl₂ h₁ h₂ (hV (σ l₁) (σ l₂) _ _ h₁' h₂' haddr)

/-- **Theorem 2b (the original allocator choices are legal).** If the unified
execution keeps simultaneously live allocations at distinct addresses, so does
the original execution driven by `origAnnot`. Together with Theorem 2a: every
behaviour of the unified program is a behaviour the original program can
exhibit under a legal allocator. -/
theorem moveElimination_original_choices_valid (σ : Nat → Nat) :
    ∀ (ap : List (Nat × Stmt)) (s s' : Store), Rel σ s s' →
      AllAlong (ClassDisjoint σ) (origAnnot σ ap s s') s →
      AllAlong Valid (unifyProg σ ap) s' →
      AllAlong Valid (origAnnot σ ap s s') s
  | [], _, _, hR, hD, hV => valid_of_rel hR hD hV
  | x :: rest, s, s', hR, hD, hV => by
    simp only [origAnnot, AllAlong] at hD ⊢
    simp only [unifyProg, List.map, AllAlong] at hV
    refine ⟨valid_of_rel hR hD.1 hV.1, ?_⟩
    intro s₁ hs
    have hpost : ClassDisjoint σ s₁ := AllAlong.head (hD.2 s₁ hs)
    cases step_refines σ x.1 x.2 s s' s₁ hR hD.1 hpost hs with
    | intro s₁' hs' =>
      have hD₁ := hD.2 s₁ hs
      rw [hs, hs'.1] at hD₁ ⊢
      exact moveElimination_original_choices_valid σ rest s₁ s₁' hs'.2 hD₁ (hV.2 s₁' hs'.1)

/-- What an observer can see of a value: integers, and the numeric address of a
pointer (its provenance is not observable). -/
def obsVal : Val → Nat × Nat
  | .int n => (0, n)
  | .ptr _ a => (1, a)

theorem obsVal_renVal (σ : Nat → Nat) (v : Val) : obsVal (renVal σ v) = obsVal v := by
  cases v <;> rfl

/-- **Theorem 2c.** With the return place kept as its own representative, the
returned value is observably identical and lives at the same address. -/
theorem moveElimination_return_observation (σ : Nat → Nat) (hσ0 : σ 0 = 0)
    (ap : List (Nat × Stmt)) (s s' t : Store) (ret : Slot) (hR : Rel σ s s')
    (hD : AllAlong (ClassDisjoint σ) (origAnnot σ ap s s') s)
    (hrun : run (origAnnot σ ap s s') s = some t) (hret : t 0 = some ret) :
    ∃ t' ret', run (unifyProg σ ap) s' = some t' ∧ t' 0 = some ret' ∧
      ret'.addr = ret.addr ∧ obsVal ret'.val = obsVal ret.val := by
  cases moveElimination_value_and_address_bisimulation σ ap s s' t hR hD hrun with
  | intro t' ht' =>
    have h := ht'.2 0 ret hret
    rw [hσ0] at h
    exact ⟨t', _, ht'.1, h, rfl, obsVal_renVal σ ret.val⟩

/-! ### `AllocationInterval` rows and `DisjointLiveRanges` -/

/-- An inclusive range of split points. -/
structure AllocationInterval where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

def AllocationInterval.contains (i : AllocationInterval) (t : Nat) : Bool :=
  decide (i.start ≤ t) && decide (t ≤ i.stop)

def AllocationInterval.overlaps (a b : AllocationInterval) : Bool :=
  decide (a.start ≤ b.stop) && decide (b.start ≤ a.stop)

/-- One row of the liveness matrix. -/
abbrev Row := List AllocationInterval

def Row.contains (r : Row) (t : Nat) : Bool := r.any fun i => i.contains t

/-- `SparseIntervalMatrix::disjoint_rows`. -/
def Row.disjoint (r₁ r₂ : Row) : Bool := r₁.all fun a => r₂.all fun b => !(a.overlaps b)

/-- Each statement `i` has an early split point (operands are read, moved-from
locals die) and a late split point (the destination is written). -/
def earlyPoint (i : Nat) : Nat := 2 * i

def latePoint (i : Nat) : Nat := 2 * i + 1

theorem AllocationInterval.overlaps_of_common_point {a b : AllocationInterval} {t : Nat}
    (ha : a.contains t = true) (hb : b.contains t = true) : a.overlaps b = true := by
  simp only [AllocationInterval.contains, Bool.and_eq_true, decide_eq_true_eq] at ha hb
  simp only [AllocationInterval.overlaps, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Nat.le_trans ha.1 hb.2, Nat.le_trans hb.1 ha.2⟩

theorem Row.disjoint_sound {r₁ r₂ : Row} {t : Nat} (hd : r₁.disjoint r₂ = true)
    (h₁ : r₁.contains t = true) (h₂ : r₂.contains t = true) : False := by
  simp only [Row.contains, List.any_eq_true] at h₁ h₂
  simp only [Row.disjoint, List.all_eq_true] at hd
  cases h₁ with
  | intro a ha =>
    cases h₂ with
    | intro b hb =>
      have hov := AllocationInterval.overlaps_of_common_point ha.2 hb.2
      have hno := hd a ha.1 b hb.1
      rw [hov] at hno
      cases hno

/-- A range that ends at the early point of a statement never overlaps a range
that starts at the late point of the same statement: this is what lets
`dst = move src` unify `src` with `dst`. -/
theorem early_end_late_start_disjoint (a b i : Nat) :
    (AllocationInterval.mk a (earlyPoint i)).overlaps ⟨latePoint i, b⟩ = false := by
  have h : ¬ (2 * i + 1 ≤ 2 * i) := Nat.not_succ_le_self (2 * i)
  simp [AllocationInterval.overlaps, earlyPoint, latePoint, h]

abbrev LivenessMatrix := Nat → Row

/-- The static check performed before a mapping is added: different locals that
are mapped to the same representative have disjoint rows. -/
def DisjointLiveRanges (σ : Nat → Nat) (m : LivenessMatrix) : Prop :=
  ∀ l₁ l₂, ¬ l₁ = l₂ → σ l₁ = σ l₂ → (m l₁).disjoint (m l₂) = true

/-- The matrix over-approximates allocation: whenever a local is allocated in
the state before statement `k`, its row contains the early point of `k`. -/
noncomputable def CoversFrom (m : LivenessMatrix) : Nat → List (Nat × Stmt) → Store → Prop
  | k, [], s => ∀ l sl, s l = some sl → (m l).contains (earlyPoint k) = true
  | k, x :: rest, s =>
    (∀ l sl, s l = some sl → (m l).contains (earlyPoint k) = true) ∧
      ∀ s₁, step x.1 s x.2 = some s₁ → CoversFrom m (k + 1) rest s₁

theorem classDisjoint_of_cover {σ : Nat → Nat} {m : LivenessMatrix}
    (hm : DisjointLiveRanges σ m) {k : Nat} {s : Store}
    (hc : ∀ l sl, s l = some sl → (m l).contains (earlyPoint k) = true) :
    ClassDisjoint σ s := by
  intro l₁ l₂ sl₁ sl₂ h₁ h₂ hσ
  by_cases hne : l₁ = l₂
  · exact hne
  · exact False.elim (Row.disjoint_sound (hm l₁ l₂ hne hσ) (hc l₁ sl₁ h₁) (hc l₂ sl₂ h₂))

/-- **Theorem 2d (`DisjointLiveRanges` is sufficient).** Row disjointness of a
matrix that covers the execution implies the semantic hypothesis of Theorems
2a-2c. -/
theorem disjointLiveRanges_sound (σ : Nat → Nat) (m : LivenessMatrix)
    (hm : DisjointLiveRanges σ m) :
    ∀ (ap : List (Nat × Stmt)) (k : Nat) (s : Store),
      CoversFrom m k ap s → AllAlong (ClassDisjoint σ) ap s
  | [], _, _, hc => classDisjoint_of_cover hm hc
  | _ :: rest, k, _, hc =>
    ⟨classDisjoint_of_cover hm hc.1,
      fun s₁ hs => disjointLiveRanges_sound σ m hm rest (k + 1) s₁ (hc.2 s₁ hs)⟩

/-! ### The borrowed-local return shape in the model -/

/-- `_2 = 0; _4 = &mut _2; *_4 = copy _1; StorageDead(_4); _0 = move _2`,
annotated with the unified program's allocator choices. -/
def nrvoProg (c2 c4 c5 c6 c0 : Nat) : List (Nat × Stmt) :=
  [(c2, .const 2 0), (c4, .addrOf 4 2), (c5, .store 4 1), (c6, .storageDead 4), (c0, .move 0 2)]

/-- `buf` (`_2`) is unified into the return place `_0`. -/
def nrvoσ : Nat → Nat := fun l => if l = 2 then 0 else l

def nrvoInit (a1 : Nat) : Store := fun l => if l = 1 then some ⟨a1, .int 7⟩ else none

/-- In the unified program the buffer is built directly in `_0`; the original
program, given the same addresses, returns the same value at the same address,
and the pointer handed out for `buf` is the address of the return place. -/
theorem nrvo_model_instance (a1 c2 c4 c5 c6 c0 : Nat) :
    unifyProg nrvoσ (nrvoProg c2 c4 c5 c6 c0) =
      [(c2, .const 0 0), (c4, .addrOf 4 0), (c5, .store 4 1), (c6, .nop), (c0, .nop)] ∧
    origAnnot nrvoσ (nrvoProg c2 c4 c5 c6 c0) (nrvoInit a1) (nrvoInit a1) =
      [(c2, .const 2 0), (c4, .addrOf 4 2), (c5, .store 4 1), (c6, .storageDead 4),
        (c2, .move 0 2)] ∧
    (run (unifyProg nrvoσ (nrvoProg c2 c4 c5 c6 c0)) (nrvoInit a1)).bind (fun t => t 0)
      = some ⟨c2, .int 7⟩ ∧
    (run (origAnnot nrvoσ (nrvoProg c2 c4 c5 c6 c0) (nrvoInit a1) (nrvoInit a1))
        (nrvoInit a1)).bind (fun t => t 0) = some ⟨c2, .int 7⟩ ∧
    (run (unifyProg nrvoσ (nrvoProg c2 c4 c5 c6 c0)) (nrvoInit a1)).bind (fun t => t 4)
      = some ⟨c4, .ptr 0 c2⟩ := by
  have hu : unifyProg nrvoσ (nrvoProg c2 c4 c5 c6 c0) =
      [(c2, .const 0 0), (c4, .addrOf 4 0), (c5, .store 4 1), (c6, .nop), (c0, .nop)] := rfl
  have ho : origAnnot nrvoσ (nrvoProg c2 c4 c5 c6 c0) (nrvoInit a1) (nrvoInit a1) =
      [(c2, .const 2 0), (c4, .addrOf 4 2), (c5, .store 4 1), (c6, .storageDead 4),
        (c2, .move 0 2)] := by
    simp [origAnnot, nrvoProg, nrvoσ, nrvoInit, origChoice, Stmt.dest, unifyStmt, step,
      Store.write, Store.addrFor, Store.ptrAt, Store.deref, Store.free]
  refine ⟨hu, ho, ?_, ?_, ?_⟩
  · rw [hu]
    simp [run, step, nrvoInit, Store.write, Store.addrFor, Store.ptrAt, Store.deref]
  · rw [ho]
    simp [run, step, nrvoInit, Store.write, Store.addrFor, Store.ptrAt, Store.deref, Store.free]
  · rw [hu]
    simp [run, step, nrvoInit, Store.write, Store.addrFor, Store.ptrAt, Store.deref]

/-- Rows of the model instance: `buf` is live from the late point of statement 0
to the early point of the final move (statement 4); `_0` starts at its late point. -/
theorem nrvo_model_rows_disjoint :
    Row.disjoint [⟨latePoint 0, earlyPoint 4⟩] [⟨latePoint 4, earlyPoint 5⟩] = true := by
  decide

/-! ### Sharpness counterexample 2: unifying overlapping address-observed locals -/

/-- `_1 = 5; _2 = 5; _3 = &_1; _4 = &_2; _0 = (_3 == _4)`. -/
def ce2Prog (c1 c2 c3 c4 c0 : Nat) : List (Nat × Stmt) :=
  [(c1, .const 1 5), (c2, .const 2 5), (c3, .addrOf 3 1), (c4, .addrOf 4 2), (c0, .ptrEq 0 3 4)]

/-- The illegal unification `_2 ↦ _1`. -/
def ce2σ : Nat → Nat := fun l => if l = 2 then 1 else l

/-- **Counterexample 2.** `_1` and `_2` are allocated at the same time and both
addresses are observed. Under every legal allocator the original program
returns `0` (the pointers differ); after unifying `_2` into `_1` the program
returns `1` under every allocator. The semantic hypothesis of Theorem 2a fails
for this program, and so does the row check on its liveness rows. -/
theorem ce2_unifying_overlapping_address_observed_locals_breaks_ptr_inequality :
    (∀ (c1 c2 c3 c4 c0 : Nat) (t : Store),
        run (ce2Prog c1 c2 c3 c4 c0) emptyStore = some t → Valid t →
        (t 0).map (fun sl => sl.val) = some (.int 0)) ∧
    (∀ (c1 c2 c3 c4 c0 : Nat),
        (run (unifyProg ce2σ (ce2Prog c1 c2 c3 c4 c0)) emptyStore).bind
          (fun t => (t 0).map (fun sl => sl.val)) = some (.int 1)) ∧
    (∀ (c1 c2 c3 c4 c0 : Nat),
        ¬ AllAlong (ClassDisjoint ce2σ) (ce2Prog c1 c2 c3 c4 c0) emptyStore) ∧
    Row.disjoint [⟨latePoint 0, earlyPoint 5⟩] [⟨latePoint 1, earlyPoint 5⟩] = false := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro c1 c2 c3 c4 c0 t hrun hvalid
    have h0 : (run (ce2Prog c1 c2 c3 c4 c0) emptyStore).bind
        (fun t => (t 0).map (fun sl => sl.val)) = some (.int (if c1 = c2 then 1 else 0)) := rfl
    have h1 : (run (ce2Prog c1 c2 c3 c4 c0) emptyStore).bind (fun t => t 1)
        = some ⟨c1, .int 5⟩ := rfl
    have h2 : (run (ce2Prog c1 c2 c3 c4 c0) emptyStore).bind (fun t => t 2)
        = some ⟨c2, .int 5⟩ := rfl
    rw [hrun] at h0 h1 h2
    have hne : ¬ c1 = c2 := fun heq => by
      have h12 : (1 : Nat) = 2 := hvalid 1 2 _ _ h1 h2 heq
      cases h12
    have h0' : (t 0).map (fun sl => sl.val) = some (.int (if c1 = c2 then 1 else 0)) := h0
    rw [h0']
    simp [hne]
  · intro c1 c2 c3 c4 c0
    have h : (run (unifyProg ce2σ (ce2Prog c1 c2 c3 c4 c0)) emptyStore).bind
        (fun t => (t 0).map (fun sl => sl.val)) = some (.int (if c1 = c1 then 1 else 0)) := rfl
    rw [h]
    simp
  · intro c1 c2 c3 c4 c0 hD
    have hstate : ClassDisjoint ce2σ
        ((emptyStore.write 1 c1 (.int 5)).write 2 c2 (.int 5)) :=
      AllAlong.head ((hD.2 _ rfl).2 _ rfl)
    have h12 : (1 : Nat) = 2 := hstate 1 2 ⟨c1, .int 5⟩ ⟨c2, .int 5⟩ rfl rfl rfl
    cases h12

end Unify

/-! ## 3. `unifyPlaces`: the transitive `Local -> Place` substitution -/

namespace Places

/-- A place: a base local and a path of stable projections (field numbers). -/
structure Place where
  base : Nat
  path : List Nat
  deriving DecidableEq, Repr

/-- `Place::project_deeper`. -/
def Place.projectDeeper (p : Place) (suffix : List Nat) : Place := ⟨p.base, p.path ++ suffix⟩

/-- `remapped_locals`: each local is either unmapped or mapped to a place. -/
abbrev Mapping := Nat → Option Place

/-- `resolve_place`, with the `while let` loop bounded by explicit fuel. -/
noncomputable def resolve (m : Mapping) : Nat → Place → Place
  | 0, p => p
  | fuel + 1, p =>
    match m p.base with
    | none => p
    | some q => resolve m fuel (q.projectDeeper p.path)

/-- One rewrite of a place with a (finalized) mapping, as in `PlaceUpdater::visit_place`. -/
def substPlace (m : Mapping) (p : Place) : Place :=
  match m p.base with
  | none => p
  | some q => q.projectDeeper p.path

/-- The finalization loop at the end of `PlaceUnification::run`. -/
noncomputable def finalize (m : Mapping) (fuel : Nat) : Mapping := fun l => (m l).map (resolve m fuel)

/-- `unifyPlaces`: rewrite a place with the transitively resolved mapping. -/
noncomputable def unifyPlaces (m : Mapping) (fuel : Nat) (p : Place) : Place := substPlace (finalize m fuel) p

theorem projectDeeper_assoc (p : Place) (a b : List Nat) :
    (p.projectDeeper a).projectDeeper b = p.projectDeeper (a ++ b) := by
  simp [Place.projectDeeper, List.append_assoc]

/-- Resolution commutes with projecting deeper: a mapped local can be replaced
underneath any projection suffix. -/
theorem resolve_projectDeeper (m : Mapping) :
    ∀ (fuel : Nat) (p : Place) (sfx : List Nat),
      resolve m fuel (p.projectDeeper sfx) = (resolve m fuel p).projectDeeper sfx
  | 0, _, _ => rfl
  | fuel + 1, p, sfx => by
    cases hm : m p.base with
    | none =>
      have hb : (p.projectDeeper sfx).base = p.base := rfl
      simp only [resolve, hb, hm]
    | some q =>
      have hb : (p.projectDeeper sfx).base = p.base := rfl
      have hp : (p.projectDeeper sfx).path = p.path ++ sfx := rfl
      simp only [resolve, hb, hp, hm]
      rw [← projectDeeper_assoc, resolve_projectDeeper m fuel (q.projectDeeper p.path) sfx]

/-- With an acyclicity witness `rank` (every mapping step strictly decreases the
rank of the base local) and enough fuel, resolution ends at an unmapped local. -/
theorem resolve_reaches_unmapped (m : Mapping) (rank : Nat → Nat)
    (hrank : ∀ l q, m l = some q → rank q.base < rank l) :
    ∀ (fuel : Nat) (p : Place), rank p.base ≤ fuel → m (resolve m fuel p).base = none
  | 0, p, hle => by
    cases hm : m p.base with
    | none => exact hm
    | some q =>
      have h1 : rank q.base < rank p.base := hrank p.base q hm
      have h2 : rank q.base < 0 := Nat.lt_of_lt_of_le h1 hle
      exact absurd h2 (Nat.not_lt_zero _)
  | fuel + 1, p, hle => by
    cases hm : m p.base with
    | none =>
      simp only [resolve, hm]
    | some q =>
      have h1 : rank q.base < rank p.base := hrank p.base q hm
      have h2 : rank q.base ≤ fuel := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h1 hle)
      simp only [resolve, hm]
      exact resolve_reaches_unmapped m rank hrank fuel (q.projectDeeper p.path) h2

/-- **Theorem (finalized mappings are fixed points).** After finalization with
enough fuel, every mapped local points at a place whose base is unmapped, so
applying the substitution twice is the same as applying it once: one rewrite
pass over the body suffices. -/
theorem unifyPlaces_idempotent (m : Mapping) (rank : Nat → Nat) (fuel : Nat)
    (hrank : ∀ l q, m l = some q → rank q.base < rank l)
    (hfuel : ∀ l, rank l ≤ fuel) (p : Place) :
    unifyPlaces m fuel (unifyPlaces m fuel p) = unifyPlaces m fuel p := by
  cases hm : m p.base with
  | none =>
    have h1 : unifyPlaces m fuel p = p := by
      simp [unifyPlaces, substPlace, finalize, hm]
    rw [h1, h1]
  | some q =>
    have h1 : unifyPlaces m fuel p = (resolve m fuel q).projectDeeper p.path := by
      simp [unifyPlaces, substPlace, finalize, hm]
    have hbase : ((resolve m fuel q).projectDeeper p.path).base = (resolve m fuel q).base := rfl
    have hnone : m (resolve m fuel q).base = none :=
      resolve_reaches_unmapped m rank hrank fuel q (hfuel q.base)
    rw [h1]
    simp [unifyPlaces, substPlace, finalize, hbase, hnone]

/-- The transitivity example from the pass documentation: with `_3 ↦ _2.1` and
`_2 ↦ _1.0`, local `_3` resolves to `_1.0.1`, and a use `_3.7` becomes `_1.0.1.7`. -/
def exampleMapping : Mapping := fun l =>
  match l with
  | 3 => some ⟨2, [1]⟩
  | 2 => some ⟨1, [0]⟩
  | _ => none

theorem unifyPlaces_transitive_example :
    unifyPlaces exampleMapping 4 ⟨3, []⟩ = ⟨1, [0, 1]⟩ ∧
    unifyPlaces exampleMapping 4 ⟨3, [7]⟩ = ⟨1, [0, 1, 7]⟩ ∧
    unifyPlaces exampleMapping 4 ⟨2, []⟩ = ⟨1, [0]⟩ ∧
    unifyPlaces exampleMapping 4 ⟨1, [5]⟩ = ⟨1, [5]⟩ := by
  decide

end Places

/-! ## 4. `aliasFixup`: restoring non-overlapping aggregate assignments -/

namespace Fixup

/-- `local → field → scalar`. Each field is a scalar-backend leaf. -/
abbrev Store := Nat → Nat → Nat

inductive Operand where
  | place (l f : Nat)
  | const (n : Nat)
  deriving DecidableEq, Repr

/-- A simple field assignment `dl.df = src`. -/
structure Assign where
  dl : Nat
  df : Nat
  src : Operand
  deriving DecidableEq, Repr

def evalOp (s : Store) : Operand → Nat
  | .place l f => s l f
  | .const n => n

def Store.write (s : Store) (l f v : Nat) : Store :=
  fun l' f' => if l' = l ∧ f' = f then v else s l' f'

def execAssign (s : Store) (a : Assign) : Store := s.write a.dl a.df (evalOp s a.src)

/-- Sequential execution: each assignment reads its source when it runs. -/
noncomputable def execAssigns : List Assign → Store → Store
  | [], s => s
  | a :: rest, s => execAssigns rest (execAssign s a)

noncomputable def writeFields (d : Nat) : Nat → List Nat → Store → Store
  | _, [], s => s
  | i, v :: vs, s => writeFields d (i + 1) vs (s.write d i v)

/-- Specification of `d = Aggregate(ops)`: every operand is read first, then
the fields of `d` are written. -/
noncomputable def specAggregate (s : Store) (d : Nat) (ops : List Operand) : Store :=
  writeFields d 0 (ops.map (evalOp s)) s

noncomputable def lowerFrom (d : Nat) : Nat → List Operand → List Assign
  | _, [] => []
  | i, op :: rest => ⟨d, i, op⟩ :: lowerFrom d (i + 1) rest

/-- Field-by-field lowering without any fixup: field `i` is written before
operand `i + 1` is read. -/
noncomputable def naiveLower (d : Nat) (ops : List Operand) : List Assign := lowerFrom d 0 ops

/-- `places_directly_alias(dest, src)` for a whole-local destination. -/
def aliasesDest (d : Nat) : Operand → Bool
  | .place l _ => decide (l = d)
  | .const _ => false

/-- `*src == dest_field`. -/
def isIdentity (d i : Nat) : Operand → Bool
  | .place l f => decide (l = d) && decide (f = i)
  | .const _ => false

/-- First pass: aliasing, non-identity operands are read into fresh temporaries. -/
noncomputable def hoistsFrom (fresh : Nat → Nat) (d : Nat) : Nat → List Operand → List Assign
  | _, [] => []
  | i, op :: rest =>
    if aliasesDest d op && !isIdentity d i op then
      ⟨fresh i, 0, op⟩ :: hoistsFrom fresh d (i + 1) rest
    else hoistsFrom fresh d (i + 1) rest

/-- Second pass: the destination fields are written; identity fields are skipped. -/
noncomputable def writesFrom (fresh : Nat → Nat) (d : Nat) : Nat → List Operand → List Assign
  | _, [] => []
  | i, op :: rest =>
    if isIdentity d i op then writesFrom fresh d (i + 1) rest
    else if aliasesDest d op then
      ⟨d, i, .place (fresh i) 0⟩ :: writesFrom fresh d (i + 1) rest
    else ⟨d, i, op⟩ :: writesFrom fresh d (i + 1) rest

/-- `AliasFixup::visit_aggregate_assign`: untouched when no operand aliases the
destination, otherwise hoists followed by per-field writes. -/
noncomputable def aliasFixup (fresh : Nat → Nat) (d : Nat) (ops : List Operand) : List Assign :=
  if ops.any (aliasesDest d) then hoistsFrom fresh d 0 ops ++ writesFrom fresh d 0 ops
  else naiveLower d ops

/-- No emitted assignment reads the local it writes. -/
def NonOverlapping (a : Assign) : Prop := ∀ l f, a.src = .place l f → ¬ l = a.dl

theorem hoistsFrom_nonoverlapping (fresh : Nat → Nat) (d : Nat) (hfresh : ∀ i, ¬ fresh i = d) :
    ∀ (ops : List Operand) (i : Nat) (a : Assign), a ∈ hoistsFrom fresh d i ops → NonOverlapping a
  | [], _, a, h => by cases h
  | op :: rest, i, a, h => by
    by_cases hc : (aliasesDest d op && !isIdentity d i op) = true
    · simp only [hoistsFrom, hc, ↓reduceIte] at h
      cases List.mem_cons.mp h with
      | inl heq =>
        subst heq
        intro l f hsrc hl
        have hsrc' : op = .place l f := hsrc
        subst hsrc'
        have hal : aliasesDest d (.place l f) = true := by
          simp only [Bool.and_eq_true] at hc
          exact hc.1
        have hld : l = d := of_decide_eq_true hal
        have hl' : l = fresh i := hl
        exact hfresh i (hl'.symm.trans hld)
      | inr hmem => exact hoistsFrom_nonoverlapping fresh d hfresh rest (i + 1) a hmem
    · simp only [hoistsFrom, hc] at h
      exact hoistsFrom_nonoverlapping fresh d hfresh rest (i + 1) a h

theorem writesFrom_nonoverlapping (fresh : Nat → Nat) (d : Nat) (hfresh : ∀ i, ¬ fresh i = d) :
    ∀ (ops : List Operand) (i : Nat) (a : Assign), a ∈ writesFrom fresh d i ops → NonOverlapping a
  | [], _, a, h => by cases h
  | op :: rest, i, a, h => by
    by_cases hid : isIdentity d i op = true
    · simp only [writesFrom, hid, ↓reduceIte] at h
      exact writesFrom_nonoverlapping fresh d hfresh rest (i + 1) a h
    · by_cases hal : aliasesDest d op = true
      · simp only [writesFrom, hid, hal, ↓reduceIte] at h
        cases List.mem_cons.mp h with
        | inl heq =>
          subst heq
          intro l f hsrc hl
          have hlf : l = fresh i := by
            have h1 : Operand.place (fresh i) 0 = Operand.place l f := hsrc
            cases h1
            rfl
          exact hfresh i (hlf ▸ hl)
        | inr hmem => exact writesFrom_nonoverlapping fresh d hfresh rest (i + 1) a hmem
      · simp only [writesFrom, hid, hal] at h
        cases List.mem_cons.mp h with
        | inl heq =>
          subst heq
          intro l f hsrc hl
          have hsrc' : op = .place l f := hsrc
          subst hsrc'
          have hld : l = d := hl
          exact hal (decide_eq_true hld)
        | inr hmem => exact writesFrom_nonoverlapping fresh d hfresh rest (i + 1) a hmem

theorem lowerFrom_nonoverlapping (d : Nat) :
    ∀ (ops : List Operand) (i : Nat), (∀ op, op ∈ ops → aliasesDest d op = false) →
      ∀ a, a ∈ lowerFrom d i ops → NonOverlapping a
  | [], _, _, a, h => by cases h
  | op :: rest, i, hno, a, h => by
    simp only [lowerFrom] at h
    cases List.mem_cons.mp h with
    | inl heq =>
      subst heq
      intro l f hsrc hl
      have hsrc' : op = .place l f := hsrc
      subst hsrc'
      have hld : l = d := hl
      have hfalse : decide (l = d) = false := hno (.place l f) (List.mem_cons_self ..)
      rw [decide_eq_true hld] at hfalse
      cases hfalse
    | inr hmem =>
      exact lowerFrom_nonoverlapping d rest (i + 1)
        (fun o ho => hno o (List.mem_cons_of_mem _ ho)) a hmem

/-- **Theorem 3a (non-overlapping copies, any arity).** Every assignment the
fixup emits has a source local different from its destination local, so each
one satisfies the no-overlap requirement of a MIR `Use` assignment. -/
theorem aliasFixup_emits_nonoverlapping_copies (fresh : Nat → Nat) (d : Nat)
    (hfresh : ∀ i, ¬ fresh i = d) (ops : List Operand) :
    ∀ a, a ∈ aliasFixup fresh d ops → NonOverlapping a := by
  intro a ha
  by_cases hany : ops.any (aliasesDest d) = true
  · simp only [aliasFixup, hany, ↓reduceIte] at ha
    cases List.mem_append.mp ha with
    | inl h => exact hoistsFrom_nonoverlapping fresh d hfresh ops 0 a h
    | inr h => exact writesFrom_nonoverlapping fresh d hfresh ops 0 a h
  · simp only [aliasFixup, hany] at ha
    refine lowerFrom_nonoverlapping d ops 0 ?_ a ha
    intro op hop
    cases hal : aliasesDest d op with
    | false => rfl
    | true => exact absurd (List.any_eq_true.mpr ⟨op, hop, hal⟩) hany

/-- Every operand is, relative to destination `d` and field index `i`, a
constant, a field of another local, the identity field `d.i`, or another field
of `d`. -/
theorem classify (d i : Nat) (op : Operand) :
    (∃ n, op = .const n) ∨ (∃ l f, op = .place l f ∧ ¬ l = d) ∨ op = .place d i ∨
      (∃ j, op = .place d j ∧ ¬ j = i) := by
  cases op with
  | const n => exact Or.inl ⟨n, rfl⟩
  | place l f =>
    by_cases hl : l = d
    · subst hl
      by_cases hf : f = i
      · subst hf
        exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr ⟨f, rfl, hf⟩))
    · exact Or.inr (Or.inl ⟨l, f, rfl, hl⟩)

set_option linter.unusedSimpArgs false in
/-- **Theorem 3b (the fixup implements the aggregate, every operand shape,
two fields).** For a two-field aggregate `d = Aggregate(op0, op1)` with arbitrary
operands (constants, fields of other locals, identity fields, or aliasing fields
of `d` itself) and temporaries that are fresh (different from `d`, from each
other, and not read by the operands), running the fixup output sequentially
gives exactly the read-all-operands-first result on every local other than the
temporaries. -/
theorem aliasFixup_pair_matches_specification (fresh : Nat → Nat) (d : Nat) (op0 op1 : Operand)
    (hd0 : ¬ fresh 0 = d) (hd1 : ¬ fresh 1 = d) (h01 : ¬ fresh 0 = fresh 1)
    (ht00 : aliasesDest (fresh 0) op0 = false) (ht01 : aliasesDest (fresh 1) op0 = false)
    (ht10 : aliasesDest (fresh 0) op1 = false) (ht11 : aliasesDest (fresh 1) op1 = false)
    (s : Store) (l f : Nat) (hl0 : ¬ l = fresh 0) (hl1 : ¬ l = fresh 1) :
    execAssigns (aliasFixup fresh d [op0, op1]) s l f = specAggregate s d [op0, op1] l f := by
  have hd0' : ¬ d = fresh 0 := fun h => hd0 h.symm
  have hd1' : ¬ d = fresh 1 := fun h => hd1 h.symm
  have h10 : ¬ fresh 1 = fresh 0 := fun h => h01 h.symm
  rcases classify d 0 op0 with ⟨n0, rfl⟩ | ⟨l0, f0, rfl, hl0d⟩ | rfl | ⟨j0, rfl, hj0⟩ <;>
  rcases classify d 1 op1 with ⟨n1, rfl⟩ | ⟨l1, f1, rfl, hl1d⟩ | rfl | ⟨j1, rfl, hj1⟩ <;>
  simp [aliasesDest] at ht00 ht01 ht10 ht11 <;>
  (by_cases hld : l = d
   · subst hld
     by_cases hf0 : f = 0
     · subst hf0
       simp [aliasFixup, hoistsFrom, writesFrom, naiveLower, lowerFrom, aliasesDest,
         isIdentity, execAssigns, execAssign, evalOp, Store.write, specAggregate,
         writeFields, *]
     · by_cases hf1 : f = 1
       · subst hf1
         simp [aliasFixup, hoistsFrom, writesFrom, naiveLower, lowerFrom, aliasesDest,
           isIdentity, execAssigns, execAssign, evalOp, Store.write, specAggregate,
           writeFields, *]
       · simp [aliasFixup, hoistsFrom, writesFrom, naiveLower, lowerFrom, aliasesDest,
           isIdentity, execAssigns, execAssign, evalOp, Store.write, specAggregate,
           writeFields, *]
   · simp [aliasFixup, hoistsFrom, writesFrom, naiveLower, lowerFrom, aliasesDest,
       isIdentity, execAssigns, execAssign, evalOp, Store.write, specAggregate,
       writeFields, *])

/-- **Theorem 3c (self-swap).** `d = Aggregate(move d.1, move d.0)` is rewritten
into two hoists and two writes, and the result is the swapped pair. -/
theorem aliasFixup_self_swap_correct (fresh : Nat → Nat) (d : Nat) (s : Store)
    (hd0 : ¬ fresh 0 = d) (hd1 : ¬ fresh 1 = d) (h01 : ¬ fresh 0 = fresh 1) :
    aliasFixup fresh d [.place d 1, .place d 0] =
      [⟨fresh 0, 0, .place d 1⟩, ⟨fresh 1, 0, .place d 0⟩,
        ⟨d, 0, .place (fresh 0) 0⟩, ⟨d, 1, .place (fresh 1) 0⟩] ∧
    execAssigns (aliasFixup fresh d [.place d 1, .place d 0]) s d 0 = s d 1 ∧
    execAssigns (aliasFixup fresh d [.place d 1, .place d 0]) s d 1 = s d 0 := by
  have hd0' : ¬ d = fresh 0 := fun h => hd0 h.symm
  have hd1' : ¬ d = fresh 1 := fun h => hd1 h.symm
  have h10 : ¬ fresh 1 = fresh 0 := fun h => h01 h.symm
  have hprog : aliasFixup fresh d [.place d 1, .place d 0] =
      [⟨fresh 0, 0, .place d 1⟩, ⟨fresh 1, 0, .place d 0⟩,
        ⟨d, 0, .place (fresh 0) 0⟩, ⟨d, 1, .place (fresh 1) 0⟩] := by
    simp [aliasFixup, hoistsFrom, writesFrom, aliasesDest, isIdentity]
  refine ⟨hprog, ?_, ?_⟩
  · rw [hprog]
    simp [execAssigns, execAssign, evalOp, Store.write, *]
  · rw [hprog]
    simp [execAssigns, execAssign, evalOp, Store.write, *]

/-- **Counterexample 3.** Lowering the self-swap field by field without the
fixup overwrites `d.0` before `d.0` is read as the second operand: field `1`
ends up holding the old `d.1` instead of the old `d.0`. -/
theorem ce3_aggregate_self_swap_without_aliasing_fixup_clobbers_field (d : Nat) (s : Store)
    (hne : ¬ s d 0 = s d 1) :
    execAssigns (naiveLower d [.place d 1, .place d 0]) s d 0 = s d 1 ∧
    execAssigns (naiveLower d [.place d 1, .place d 0]) s d 1 = s d 1 ∧
    specAggregate s d [.place d 1, .place d 0] d 1 = s d 0 ∧
    ¬ execAssigns (naiveLower d [.place d 1, .place d 0]) s d 1
        = specAggregate s d [.place d 1, .place d 0] d 1 := by
  have h1 : execAssigns (naiveLower d [.place d 1, .place d 0]) s d 1 = s d 1 := by
    simp [naiveLower, lowerFrom, execAssigns, execAssign, evalOp, Store.write]
  have h2 : specAggregate s d [.place d 1, .place d 0] d 1 = s d 0 := by
    simp [specAggregate, writeFields, evalOp, Store.write]
  refine ⟨?_, h1, h2, ?_⟩
  · simp [naiveLower, lowerFrom, execAssigns, execAssign, evalOp, Store.write]
  · rw [h1, h2]
    exact fun h => hne h.symm

def rotStore : Store := fun l f => if l = 1 then 10 * (f + 1) else 0

def rotFresh : Nat → Nat := fun i => 100 + i

/-- A three-field rotation `_1 = Aggregate(_1.1, _1.2, _1.0)` on a concrete
store: the fixup output computes the rotation, the unfixed lowering does not. -/
theorem aliasFixup_three_field_rotation_instance :
    (execAssigns (aliasFixup rotFresh 1 [.place 1 1, .place 1 2, .place 1 0]) rotStore 1 0,
      execAssigns (aliasFixup rotFresh 1 [.place 1 1, .place 1 2, .place 1 0]) rotStore 1 1,
      execAssigns (aliasFixup rotFresh 1 [.place 1 1, .place 1 2, .place 1 0]) rotStore 1 2)
      = (20, 30, 10) ∧
    (specAggregate rotStore 1 [.place 1 1, .place 1 2, .place 1 0] 1 0,
      specAggregate rotStore 1 [.place 1 1, .place 1 2, .place 1 0] 1 1,
      specAggregate rotStore 1 [.place 1 1, .place 1 2, .place 1 0] 1 2) = (20, 30, 10) ∧
    (execAssigns (naiveLower 1 [.place 1 1, .place 1 2, .place 1 0]) rotStore 1 0,
      execAssigns (naiveLower 1 [.place 1 1, .place 1 2, .place 1 0]) rotStore 1 1,
      execAssigns (naiveLower 1 [.place 1 1, .place 1 2, .place 1 0]) rotStore 1 2)
      = (20, 30, 20) := by
  decide

/-- The shape observed in the captured optimized MIR of the pair-swap probe:
after unification the aggregate is `_2 = Aggregate(move _2.0, move _1.0)`; the
fixup drops the identity field and keeps one plain field write, no temporary. -/
theorem aliasFixup_identity_field_dropped_instance (fresh : Nat → Nat) :
    aliasFixup fresh 2 [.place 2 0, .place 1 0] = [⟨2, 1, .place 1 0⟩] := by
  rfl

end Fixup

end MoveEliminationAndTailCopySoundness
