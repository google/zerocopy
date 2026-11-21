/-!
# Drop elaboration as a certified refinement

A self-contained model (only `Init`, no imports) of what `rustc`'s `ElaborateDrops` pass does to
`Drop` terminators.

* **Reference (pre-elaboration) semantics.** A body is a control-flow graph whose `drop p`
  terminator runs the destructors of exactly those move-path leaves of `p` that are initialized
  when control reaches it. Initialization is recorded at run time in an `InitTree`: one bit per
  move-path leaf of the frame. A destructor may panic (an oracle decides). The first panic starts
  unwinding: the remaining leaves of the place are still dropped, then control follows the
  terminator's unwind action. A panic raised while the terminator is already on the unwind path
  (`UnwindAction.terminate`), or a second panic inside the same place, aborts.

* **Lowered (post-elaboration) semantics.** `drop p` is unconditional: it runs the destructor of
  every leaf of `p`. Whether to drop is decided by tests of explicit boolean drop flags
  (`DropFlagEnv`), written next to every initialization and move-out, where `ElaborateDrops`
  places them. A lowered drop is a `Ladder`: the tree of fresh basic blocks the pass creates for
  one `Drop` terminator. As in the pass, an elaborated drop does not clear the flags it tested.

* **Certificate.** Every block carries dataflow facts: which leaves may be initialized, which are
  definitely initialized, and which flags may be stale. `check` validates the facts and the side
  conditions that the lowering relies on; `elaborate` produces the lowered body.

Main results

* `elaborate_refines`, `elaborate_refines_blind`: for a body whose certificate checks, the
  elaborated body has the same outcome and the same trace as the reference semantics, for every
  fuel bound and every oracle; on an aborting run the elaborated trace extends the reference
  trace (destructors that the real drop glue still runs between the fatal panic and the abort).
* `elaborate_no_double_drop`, `elaborate_no_leak`: no unconditional drop ever reaches an
  uninitialized leaf; the leaves live at exit are those of the reference run.
* `double_panic_aborts`: under the cleanup discipline of the MIR validator, a run that returns saw
  no panic and a run that unwinds out of the frame saw exactly one.
* `no_flagFree_ladder_is_conditional` and the bodies in `DropElab.Example`: the drop flag, the
  "terminate" unwind action on the unwind half of a ladder, and the stale-flag side condition are
  each necessary.
-/

namespace DropElab

/-! ## 1. Move paths, places and run-time ownership -/

/-- Index of a move-path leaf: an atomic unit of initialization bookkeeping. -/
abbrev MovePath := Nat

/-- The move-path tree below a place. A `node` is an aggregate whose two parts can be moved
independently (n-ary aggregates nest); a `leaf` is a part that is only moved as a whole. -/
inductive PlaceTree where
  | leaf (mp : MovePath)
  | node (l r : PlaceTree)

/-- Leaves of a place in drop order (declaration order of the fields). -/
noncomputable def PlaceTree.leaves : PlaceTree → List MovePath
  | .leaf mp => [mp]
  | .node l r => l.leaves ++ r.leaves

/-- No move path occurs twice below the place. -/
noncomputable def PlaceTree.wf : PlaceTree → Bool
  | .leaf _ => true
  | .node l r => l.wf && r.wf && l.leaves.all (fun a => !r.leaves.contains a)

/-- Run-time ownership state of a frame: its move-path tree with one initialization bit per leaf. -/
inductive InitTree where
  | leaf (mp : MovePath) (init : Bool)
  | node (l r : InitTree)

/-- The frame at function entry: nothing is initialized. -/
noncomputable def InitTree.ofPlace : PlaceTree → InitTree
  | .leaf mp => .leaf mp false
  | .node l r => .node (ofPlace l) (ofPlace r)

noncomputable def InitTree.ids : InitTree → List MovePath
  | .leaf mp _ => [mp]
  | .node l r => l.ids ++ r.ids

/-- Is leaf `x` initialized? -/
noncomputable def InitTree.get : InitTree → MovePath → Bool
  | .leaf mp b, x => decide (mp = x) && b
  | .node l r, x => l.get x || r.get x

/-- Set the bit of every leaf in `s` to `b`. -/
noncomputable def InitTree.setAll (s : List MovePath) (b : Bool) : InitTree → InitTree
  | .leaf mp b0 => .leaf mp (if mp ∈ s then b else b0)
  | .node l r => .node (setAll s b l) (setAll s b r)

/-- The initialized leaves, in tree order. -/
noncomputable def InitTree.live : InitTree → List MovePath
  | .leaf mp b => if b then [mp] else []
  | .node l r => l.live ++ r.live

theorem InitTree.ids_setAll (s : List MovePath) (b : Bool) (t : InitTree) :
    (t.setAll s b).ids = t.ids := by
  induction t with
  | leaf mp b0 => rfl
  | node l r ihl ihr => simp [InitTree.setAll, InitTree.ids, ihl, ihr]

theorem InitTree.get_setAll (s : List MovePath) (b : Bool) (t : InitTree) (x : MovePath) :
    (t.setAll s b).get x = if x ∈ s then (b && decide (x ∈ t.ids)) else t.get x := by
  induction t with
  | leaf mp b0 =>
    show (decide (mp = x) && (if mp ∈ s then b else b0)) =
      if x ∈ s then (b && decide (x ∈ [mp])) else (decide (mp = x) && b0)
    by_cases hx : mp = x
    · subst hx
      have h1 : decide (mp = mp) = true := decide_eq_true rfl
      have h2 : decide (mp ∈ [mp]) = true := decide_eq_true List.mem_cons_self
      by_cases hs : mp ∈ s
      · rw [ite_eq_left hs, ite_eq_left hs, h1, h2, Bool.true_and, Bool.and_true]
      · rw [ite_eq_right hs, ite_eq_right hs]
    · have h1 : decide (mp = x) = false := decide_eq_false hx
      have h2 : decide (x ∈ [mp]) = false :=
        decide_eq_false (fun h => hx (List.mem_singleton.mp h).symm)
      rw [h1, h2, Bool.false_and, Bool.false_and, Bool.and_false]
      by_cases hs : x ∈ s
      · rw [ite_eq_left hs]
      · rw [ite_eq_right hs]
  | node l r ihl ihr =>
    show ((l.setAll s b).get x || (r.setAll s b).get x) =
      if x ∈ s then (b && decide (x ∈ l.ids ++ r.ids)) else (l.get x || r.get x)
    rw [ihl, ihr]
    by_cases hs : x ∈ s
    · rw [ite_eq_left hs, ite_eq_left hs, ite_eq_left hs]
      have h : decide (x ∈ l.ids ++ r.ids) = (decide (x ∈ l.ids) || decide (x ∈ r.ids)) := by
        by_cases h1 : x ∈ l.ids
        · rw [decide_eq_true h1, decide_eq_true (List.mem_append_left _ h1), Bool.true_or]
        · by_cases h2 : x ∈ r.ids
          · rw [decide_eq_true h2, decide_eq_true (List.mem_append_right _ h2), Bool.or_true]
          · rw [decide_eq_false h1, decide_eq_false h2,
              decide_eq_false (fun h => (List.mem_append.mp h).elim h1 h2), Bool.false_or]
      rw [h, Bool.and_or_distrib_left]
    · rw [ite_eq_right hs, ite_eq_right hs, ite_eq_right hs]

theorem InitTree.ids_ofPlace (p : PlaceTree) : (InitTree.ofPlace p).ids = p.leaves := by
  induction p with
  | leaf mp => rfl
  | node l r ihl ihr => simp [InitTree.ofPlace, InitTree.ids, PlaceTree.leaves, ihl, ihr]

theorem InitTree.get_ofPlace (p : PlaceTree) (x : MovePath) : (InitTree.ofPlace p).get x = false := by
  induction p with
  | leaf mp => simp [InitTree.ofPlace, InitTree.get]
  | node l r ihl ihr => simp [InitTree.ofPlace, InitTree.get, ihl, ihr]

/-! ## 2. Observations -/

inductive Event where
  /-- a fresh value was written into the leaf -/
  | init (mp : MovePath)
  /-- ownership of the leaf's value left the frame (operand move, `StorageDead`) -/
  | moved (mp : MovePath)
  /-- the destructor of the leaf's value ran -/
  | drop (mp : MovePath)
  /-- a panic started unwinding (from a call or from a destructor) -/
  | panic
  deriving DecidableEq

inductive Outcome where
  /-- `return`; `live` lists the leaves that are still initialized -/
  | returned (live : List MovePath)
  /-- unwinding left the frame (`resume` or `UnwindAction::Continue`) -/
  | unwound (live : List MovePath)
  /-- the process aborted (`UnwindAction::Terminate`, `UnwindTerminate`) -/
  | aborted
  /-- an `unreachable` terminator or an `UnwindAction::Unreachable` edge was executed -/
  | unreachable
  /-- control was transferred to a block that does not exist -/
  | badJump
  /-- an unconditional drop was executed on an uninitialized leaf -/
  | doubleDrop (mp : MovePath)
  | outOfFuel
  deriving DecidableEq

structure Result where
  trace : List Event
  outcome : Outcome
  deriving DecidableEq

/-- Environment choices, consumed in execution order: branch directions, whether a call panics,
whether a destructor panics. An exhausted oracle answers `false`. -/
abbrev Oracle := List Bool

noncomputable def Oracle.next : Oracle → Bool × Oracle
  | [] => (false, [])
  | b :: o => (b, o)

/-! ## 3. Drop glue -/

inductive GlueMode where
  /-- pre-elaboration `Drop`: a leaf's destructor runs only if the leaf is initialized -/
  | conditional
  /-- post-elaboration `Drop`: unconditional; executing it on an uninitialized leaf is reported -/
  | checked
  /-- post-elaboration `Drop` as a machine executes it: unconditional, nothing is checked -/
  | blind

inductive GlueExit where
  | ok
  /-- a destructor panicked (or the glue was entered while unwinding) and unwinding continues -/
  | panicked
  /-- a destructor panicked while unwinding -/
  | aborted
  | doubleDrop (mp : MovePath)

structure GlueRes where
  events : List Event
  init : InitTree
  oracle : Oracle
  exit : GlueExit

noncomputable def GlueRes.prepend (es : List Event) (r : GlueRes) : GlueRes :=
  ⟨es ++ r.events, r.init, r.oracle, r.exit⟩

/-- Drop the leaves `ls` in order. `unw` says whether a panic is already in flight. After the
first destructor panic the remaining leaves are still dropped; a panic while one is already in
flight aborts. -/
noncomputable def glue (m : GlueMode) : List MovePath → Bool → InitTree → Oracle → GlueRes
  | [], unw, i, o => ⟨[], i, o, if unw then .panicked else .ok⟩
  | l :: ls, unw, i, o =>
    if i.get l then
      if o.next.1 then
        if unw then ⟨[.drop l, .panic], i.setAll [l] false, o.next.2, .aborted⟩
        else (glue m ls true (i.setAll [l] false) o.next.2).prepend [.drop l, .panic]
      else (glue m ls unw (i.setAll [l] false) o.next.2).prepend [.drop l]
    else
      match m with
      | .conditional => glue m ls unw i o
      | .checked => ⟨[], i, o, .doubleDrop l⟩
      | .blind =>
        if o.next.1 then
          if unw then ⟨[.drop l, .panic], i.setAll [l] false, o.next.2, .aborted⟩
          else (glue m ls true (i.setAll [l] false) o.next.2).prepend [.drop l, .panic]
        else (glue m ls unw (i.setAll [l] false) o.next.2).prepend [.drop l]

/-- Sequential composition of glue runs: `k` receives whether a panic is in flight. -/
noncomputable def GlueRes.andThen (g : GlueRes) (k : Bool → InitTree → Oracle → GlueRes) : GlueRes :=
  match g.exit with
  | .ok => (k false g.init g.oracle).prepend g.events
  | .panicked => (k true g.init g.oracle).prepend g.events
  | .aborted => g
  | .doubleDrop _ => g

theorem GlueRes.prepend_nil (r : GlueRes) : r.prepend [] = r := by
  cases r; rfl

theorem GlueRes.prepend_prepend (a b : List Event) (r : GlueRes) :
    (r.prepend a).prepend b = r.prepend (b ++ a) := by
  simp [GlueRes.prepend, List.append_assoc]

theorem GlueRes.prepend_andThen (es : List Event) (g : GlueRes)
    (k : Bool → InitTree → Oracle → GlueRes) :
    (g.prepend es).andThen k = (g.andThen k).prepend es := by
  cases g with
  | mk ev i o ex =>
    cases ex <;> simp [GlueRes.prepend, GlueRes.andThen, List.append_assoc]

theorem InitTree.get_clear (i : InitTree) (l x : MovePath) :
    (i.setAll [l] false).get x = if x = l then false else i.get x := by
  rw [InitTree.get_setAll]
  by_cases h : x = l
  · rw [ite_eq_left h, ite_eq_left (List.mem_singleton.mpr h), Bool.false_and]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (List.mem_singleton.mp h'))]

theorem glue_nil (m : GlueMode) (unw : Bool) (i : InitTree) (o : Oracle) :
    glue m [] unw i o = ⟨[], i, o, if unw then .panicked else .ok⟩ := by
  simp [glue]

/-- One step of the glue when the destructor of `l` actually runs. -/
noncomputable def glueStep (m : GlueMode) (l : MovePath) (ls : List MovePath) (unw : Bool)
    (i : InitTree) (o : Oracle) : GlueRes :=
  if o.next.1 then
    if unw then ⟨[.drop l, .panic], i.setAll [l] false, o.next.2, .aborted⟩
    else (glue m ls true (i.setAll [l] false) o.next.2).prepend [.drop l, .panic]
  else (glue m ls unw (i.setAll [l] false) o.next.2).prepend [.drop l]

theorem glue_cons_init (m : GlueMode) (l : MovePath) (ls : List MovePath) (unw : Bool)
    (i : InitTree) (o : Oracle) (h : i.get l = true) :
    glue m (l :: ls) unw i o = glueStep m l ls unw i o := by
  simp [glue, glueStep, h]

theorem glue_cons_uninit_conditional (l : MovePath) (ls : List MovePath) (unw : Bool)
    (i : InitTree) (o : Oracle) (h : i.get l = false) :
    glue .conditional (l :: ls) unw i o = glue .conditional ls unw i o := by
  simp [glue, h]

theorem glue_cons_uninit_checked (l : MovePath) (ls : List MovePath) (unw : Bool)
    (i : InitTree) (o : Oracle) (h : i.get l = false) :
    glue .checked (l :: ls) unw i o = ⟨[], i, o, .doubleDrop l⟩ := by
  simp [glue, h]

theorem glue_cons_uninit_blind (l : MovePath) (ls : List MovePath) (unw : Bool)
    (i : InitTree) (o : Oracle) (h : i.get l = false) :
    glue .blind (l :: ls) unw i o = glueStep .blind l ls unw i o := by
  simp [glue, glueStep, h]

/-- The glue never changes which leaves exist. -/
theorem glue_ids (m : GlueMode) (ls : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle), (glue m ls unw i o).init.ids = i.ids := by
  induction ls with
  | nil => intro unw i o; simp [glue]
  | cons l ls ih =>
    intro unw i o
    have step : (glueStep m l ls unw i o).init.ids = i.ids := by
      unfold glueStep
      split
      · split
        · simp [InitTree.ids_setAll]
        · simp [GlueRes.prepend, ih, InitTree.ids_setAll]
      · simp [GlueRes.prepend, ih, InitTree.ids_setAll]
    by_cases hg : i.get l = true
    · rw [glue_cons_init m l ls unw i o hg]; exact step
    · have hg' : i.get l = false := by simpa using hg
      cases m with
      | conditional => rw [glue_cons_uninit_conditional l ls unw i o hg']; exact ih unw i o
      | checked => rw [glue_cons_uninit_checked l ls unw i o hg']
      | blind => rw [glue_cons_uninit_blind l ls unw i o hg']; exact step

/-- The glue only touches the leaves it is asked to drop. -/
theorem glue_frame (m : GlueMode) (ls : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle) (x : MovePath), x ∉ ls →
      (glue m ls unw i o).init.get x = i.get x := by
  induction ls with
  | nil => intro unw i o x _; simp [glue]
  | cons l ls ih =>
    intro unw i o x hx
    have hxl : x ≠ l := fun h => hx (h ▸ List.mem_cons_self)
    have hxls : x ∉ ls := fun h => hx (List.mem_cons_of_mem _ h)
    have hc : (i.setAll [l] false).get x = i.get x := by
      rw [InitTree.get_clear]; simp [hxl]
    have step : (glueStep m l ls unw i o).init.get x = i.get x := by
      unfold glueStep
      split
      · split
        · exact hc
        · simp [GlueRes.prepend, ih _ _ _ x hxls, hc]
      · simp [GlueRes.prepend, ih _ _ _ x hxls, hc]
    by_cases hg : i.get l = true
    · rw [glue_cons_init m l ls unw i o hg]; exact step
    · have hg' : i.get l = false := by simpa using hg
      cases m with
      | conditional =>
        rw [glue_cons_uninit_conditional l ls unw i o hg']; exact ih unw i o x hxls
      | checked => rw [glue_cons_uninit_checked l ls unw i o hg']
      | blind => rw [glue_cons_uninit_blind l ls unw i o hg']; exact step

/-- If the glue completes (normally or unwinding), every leaf it was asked to drop is
uninitialized afterwards. -/
theorem glue_cleared (m : GlueMode) (ls : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle) (x : MovePath), x ∈ ls →
      ((glue m ls unw i o).exit = .ok ∨ (glue m ls unw i o).exit = .panicked) →
      (glue m ls unw i o).init.get x = false := by
  induction ls with
  | nil => intro unw i o x hx; cases hx
  | cons l ls ih =>
    intro unw i o x hx
    have hc : (i.setAll [l] false).get l = false := by
      rw [InitTree.get_clear]; simp
    have step : ((glueStep m l ls unw i o).exit = .ok ∨ (glueStep m l ls unw i o).exit = .panicked) →
        (glueStep m l ls unw i o).init.get x = false := by
      unfold glueStep
      split
      · split
        · intro h; cases h <;> rename_i h <;> cases h
        · intro h
          by_cases hxls : x ∈ ls
          · exact ih _ _ _ x hxls h
          · have hxl : x = l := by
              cases hx with
              | head => rfl
              | tail _ h' => exact absurd h' hxls
            subst hxl
            simp [GlueRes.prepend, glue_frame m ls _ _ _ x hxls, hc]
      · intro h
        by_cases hxls : x ∈ ls
        · exact ih _ _ _ x hxls h
        · have hxl : x = l := by
            cases hx with
            | head => rfl
            | tail _ h' => exact absurd h' hxls
          subst hxl
          simp [GlueRes.prepend, glue_frame m ls _ _ _ x hxls, hc]
    by_cases hg : i.get l = true
    · rw [glue_cons_init m l ls unw i o hg]; exact step
    · have hg' : i.get l = false := by simpa using hg
      cases m with
      | conditional =>
        rw [glue_cons_uninit_conditional l ls unw i o hg']
        intro h
        by_cases hxls : x ∈ ls
        · exact ih _ _ _ x hxls h
        · have hxl : x = l := by
            cases hx with
            | head => rfl
            | tail _ h' => exact absurd h' hxls
          subst hxl
          rw [glue_frame .conditional ls _ _ _ x hxls]; exact hg'
      | checked =>
        rw [glue_cons_uninit_checked l ls unw i o hg']
        intro h; cases h <;> rename_i h <;> cases h
      | blind => rw [glue_cons_uninit_blind l ls unw i o hg']; exact step

/-- Conditional glue never reports a double drop: it only runs destructors of initialized leaves. -/
theorem glue_conditional_no_doubleDrop (ls : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle) (mp : MovePath),
      (glue .conditional ls unw i o).exit ≠ .doubleDrop mp := by
  induction ls with
  | nil => intro unw i o mp; cases unw <;> simp [glue]
  | cons l ls ih =>
    intro unw i o mp
    by_cases hg : i.get l = true
    · rw [glue_cons_init .conditional l ls unw i o hg]
      unfold glueStep
      split
      · split
        · simp
        · simpa [GlueRes.prepend] using ih _ _ _ mp
      · simpa [GlueRes.prepend] using ih _ _ _ mp
    · have hg' : i.get l = false := by simpa using hg
      rw [glue_cons_uninit_conditional l ls unw i o hg']; exact ih unw i o mp

/-- Glue entered while a panic is in flight either completes still unwinding or aborts. -/
theorem glue_conditional_unwinding_exit (ls : List MovePath) :
    ∀ (i : InitTree) (o : Oracle),
      (glue .conditional ls true i o).exit = .panicked ∨
      (glue .conditional ls true i o).exit = .aborted := by
  induction ls with
  | nil => intro i o; simp [glue]
  | cons l ls ih =>
    intro i o
    by_cases hg : i.get l = true
    · rw [glue_cons_init .conditional l ls true i o hg]
      unfold glueStep
      split
      · simp
      · simpa [GlueRes.prepend] using ih _ _
    · have hg' : i.get l = false := by simpa using hg
      rw [glue_cons_uninit_conditional l ls true i o hg']; exact ih i o

/-- If no leaf is initialized, conditional glue does nothing. -/
theorem glue_conditional_all_uninit (ls : List MovePath) (unw : Bool) (i : InitTree) (o : Oracle)
    (h : ∀ x, x ∈ ls → i.get x = false) :
    glue .conditional ls unw i o = ⟨[], i, o, if unw then .panicked else .ok⟩ := by
  induction ls with
  | nil => simp [glue]
  | cons l ls ih =>
    rw [glue_cons_uninit_conditional l ls unw i o (h l List.mem_cons_self)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- No repeated element. -/
noncomputable def distinct : List MovePath → Bool
  | [] => true
  | a :: l => !l.contains a && distinct l

theorem distinct_append (l1 l2 : List MovePath) (h1 : distinct l1 = true) (h2 : distinct l2 = true)
    (hd : ∀ a, a ∈ l1 → a ∉ l2) : distinct (l1 ++ l2) = true := by
  induction l1 with
  | nil => simpa using h2
  | cons a l ih =>
    simp [distinct] at h1
    have ha : a ∉ l2 := hd a List.mem_cons_self
    have ih' := ih h1.2 (fun b hb => hd b (List.mem_cons_of_mem _ hb))
    simp [distinct, h1.1, ha, ih']

theorem PlaceTree.wf_node (l r : PlaceTree) (h : (PlaceTree.node l r).wf = true) :
    l.wf = true ∧ r.wf = true ∧ ∀ a, a ∈ l.leaves → a ∉ r.leaves := by
  simp [PlaceTree.wf] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem PlaceTree.wf_distinct (p : PlaceTree) (h : p.wf = true) : distinct p.leaves = true := by
  induction p with
  | leaf mp => simp [PlaceTree.leaves, distinct]
  | node l r ihl ihr =>
    have hw := PlaceTree.wf_node l r h
    exact distinct_append _ _ (ihl hw.1) (ihr hw.2.1) hw.2.2

/-- On distinct, initialized leaves the unconditional (checked) glue coincides with the
conditional one: this is what justifies a `Static` drop. -/
theorem glue_checked_eq_conditional (ls : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle), distinct ls = true →
      (∀ x, x ∈ ls → i.get x = true) →
      glue .checked ls unw i o = glue .conditional ls unw i o := by
  induction ls with
  | nil => intro unw i o _ _; simp [glue]
  | cons l ls ih =>
    intro unw i o hd hall
    simp [distinct] at hd
    have hl : i.get l = true := hall l List.mem_cons_self
    have hrest : ∀ x, x ∈ ls → (i.setAll [l] false).get x = true := by
      intro x hx
      rw [InitTree.get_clear]
      have hxl : x ≠ l := fun h => hd.1 (h ▸ hx)
      simp [hxl, hall x (List.mem_cons_of_mem _ hx)]
    rw [glue_cons_init .checked l ls unw i o hl, glue_cons_init .conditional l ls unw i o hl]
    unfold glueStep
    rw [ih true _ _ hd.2 hrest, ih unw _ _ hd.2 hrest]

/-- Where the checked glue reports no double drop, a machine that checks nothing behaves the
same. -/
theorem glue_blind_eq_checked (ls : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle),
      (∀ mp, (glue .checked ls unw i o).exit ≠ .doubleDrop mp) →
      glue .blind ls unw i o = glue .checked ls unw i o := by
  induction ls with
  | nil => intro unw i o _; simp [glue]
  | cons l ls ih =>
    intro unw i o h
    by_cases hg : i.get l = true
    · rw [glue_cons_init .checked l ls unw i o hg] at h
      rw [glue_cons_init .blind l ls unw i o hg, glue_cons_init .checked l ls unw i o hg]
      unfold glueStep at h ⊢
      split
      · rename_i hp
        split
        · rfl
        · rename_i hu
          simp [hp, hu, GlueRes.prepend] at h
          rw [ih true _ _ h]
      · rename_i hp
        simp [hp, GlueRes.prepend] at h
        rw [ih unw _ _ h]
    · have hg' : i.get l = false := by simpa using hg
      rw [glue_cons_uninit_checked l ls unw i o hg'] at h
      exact absurd rfl (h l)

/-- Dropping `l1 ++ l2` is dropping `l1` and then `l2`, carrying the "panic in flight" bit. -/
theorem glue_append (m : GlueMode) (l1 l2 : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle),
      glue m (l1 ++ l2) unw i o = (glue m l1 unw i o).andThen (glue m l2) := by
  induction l1 with
  | nil =>
    intro unw i o
    cases unw <;> simp [glue, GlueRes.andThen, GlueRes.prepend_nil]
  | cons l ls ih =>
    intro unw i o
    have step : glueStep m l (ls ++ l2) unw i o = (glueStep m l ls unw i o).andThen (glue m l2) := by
      unfold glueStep
      split
      · split
        · simp [GlueRes.andThen]
        · rw [ih, GlueRes.prepend_andThen]
      · rw [ih, GlueRes.prepend_andThen]
    by_cases hg : i.get l = true
    · rw [List.cons_append, glue_cons_init m l (ls ++ l2) unw i o hg,
        glue_cons_init m l ls unw i o hg]
      exact step
    · have hg' : i.get l = false := by simpa using hg
      cases m with
      | conditional =>
        rw [List.cons_append, glue_cons_uninit_conditional l (ls ++ l2) unw i o hg',
          glue_cons_uninit_conditional l ls unw i o hg']
        exact ih unw i o
      | checked =>
        rw [List.cons_append, glue_cons_uninit_checked l (ls ++ l2) unw i o hg',
          glue_cons_uninit_checked l ls unw i o hg']
        simp [GlueRes.andThen]
      | blind =>
        rw [List.cons_append, glue_cons_uninit_blind l (ls ++ l2) unw i o hg',
          glue_cons_uninit_blind l ls unw i o hg']
        exact step

/-- Conditional glue entered while unwinding, when it completes, did exactly what the same glue
does when entered normally. -/
theorem glue_conditional_unwinding_panicked (ls : List MovePath) :
    ∀ (i : InitTree) (o : Oracle), (glue .conditional ls true i o).exit = .panicked →
      glue .conditional ls false i o =
        ⟨(glue .conditional ls true i o).events, (glue .conditional ls true i o).init,
          (glue .conditional ls true i o).oracle, .ok⟩ := by
  induction ls with
  | nil => intro i o _; simp [glue]
  | cons l ls ih =>
    intro i o h
    by_cases hg : i.get l = true
    · rw [glue_cons_init .conditional l ls true i o hg] at h ⊢
      rw [glue_cons_init .conditional l ls false i o hg]
      unfold glueStep at h ⊢
      split
      · rename_i hp
        simp [hp] at h
      · rename_i hp
        simp [hp, GlueRes.prepend] at h
        rw [ih _ _ h]
        simp [GlueRes.prepend]
    · have hg' : i.get l = false := by simpa using hg
      rw [glue_cons_uninit_conditional l ls true i o hg'] at h ⊢
      rw [glue_cons_uninit_conditional l ls false i o hg']
      exact ih i o h

/-- Conditional glue entered while unwinding, when it aborts, has run a prefix of what the same
glue runs when entered normally; and the latter does not complete normally either. -/
theorem glue_conditional_unwinding_aborted (ls : List MovePath) :
    ∀ (i : InitTree) (o : Oracle), (glue .conditional ls true i o).exit = .aborted →
      (∃ extra, (glue .conditional ls false i o).events =
          (glue .conditional ls true i o).events ++ extra) ∧
      ((glue .conditional ls false i o).exit = .panicked ∨
        (glue .conditional ls false i o).exit = .aborted) := by
  induction ls with
  | nil => intro i o h; simp [glue] at h
  | cons l ls ih =>
    intro i o h
    by_cases hg : i.get l = true
    · rw [glue_cons_init .conditional l ls true i o hg] at h ⊢
      rw [glue_cons_init .conditional l ls false i o hg]
      unfold glueStep at h ⊢
      split
      · rename_i hp
        simp only [GlueRes.prepend]
        refine ⟨⟨(glue .conditional ls true (i.setAll [l] false) o.next.2).events, ?_⟩, ?_⟩
        · simp
        · exact glue_conditional_unwinding_exit ls _ _
      · rename_i hp
        simp [hp, GlueRes.prepend] at h
        obtain ⟨⟨extra, he⟩, hx⟩ := ih _ _ h
        refine ⟨⟨extra, ?_⟩, ?_⟩
        · simp [GlueRes.prepend, he]
        · simpa [GlueRes.prepend] using hx
    · have hg' : i.get l = false := by simpa using hg
      rw [glue_cons_uninit_conditional l ls true i o hg'] at h ⊢
      rw [glue_cons_uninit_conditional l ls false i o hg']
      exact ih i o h

/-! ## 4. Bodies before elaboration and their reference semantics -/

/-- `rustc_middle::mir::UnwindAction`. `terminate` is `Terminate(InCleanup)`: the terminator
already sits on the unwind path. -/
inductive UnwindAction where
  | continue_
  | cleanup (b : Nat)
  | terminate
  | unreachable

inductive Stmt where
  /-- assignment of a fresh value to the place (initializes every leaf below it) -/
  | init (p : PlaceTree)
  /-- move out of the place (operand `move p`, or `StorageDead`) -/
  | move (p : PlaceTree)
  | nop

inductive Term where
  | goto (t : Nat)
  /-- `SwitchInt` on program data: the oracle picks the successor -/
  | branch (t e : Nat)
  /-- a call that may panic (the oracle decides) -/
  | call (ret : Nat) (unw : UnwindAction)
  /-- `Drop(p) -> [return: ret, unwind: unw]` before elaboration: drops what is initialized -/
  | drop (p : PlaceTree) (ret : Nat) (unw : UnwindAction)
  | ret
  | resume
  /-- `UnwindTerminate` -/
  | abort
  | unreachable

/-- Dataflow facts at a program point (the certificate).
* `mi`: leaves that may be initialized (`MaybeInitializedPlaces`);
* `di`: leaves that are definitely initialized (the complement of `MaybeUninitializedPlaces`);
* `st`: leaves whose drop flag may be stale, i.e. still set although the leaf was dropped. -/
structure Facts where
  mi : List MovePath
  di : List MovePath
  st : List MovePath

structure Block where
  facts : Facts
  cleanup : Bool
  stmts : List Stmt
  term : Term

structure Body where
  /-- move-path tree of the whole frame -/
  frame : PlaceTree
  /-- move paths that own a drop flag -/
  flagged : List MovePath
  blocks : List Block

noncomputable def execStmt : Stmt → InitTree → List Event × InitTree
  | .init p, i => (p.leaves.map Event.init, i.setAll p.leaves true)
  | .move p, i => ((p.leaves.filter i.get).map Event.moved, i.setAll p.leaves false)
  | .nop, i => ([], i)

noncomputable def execStmts : List Stmt → InitTree → List Event × InitTree
  | [], i => ([], i)
  | s :: ss, i =>
    ((execStmt s i).1 ++ (execStmts ss (execStmt s i).2).1, (execStmts ss (execStmt s i).2).2)

inductive Next where
  | jump (b : Nat)
  | exit (o : Outcome)

structure StepRes where
  events : List Event
  init : InitTree
  oracle : Oracle
  next : Next

/-- Where an elaborated drop, or an unwind edge, leaves to. -/
inductive Kont where
  | goto (b : Nat)
  | resume
  | abort
  | unreachable

noncomputable def kontOf : UnwindAction → Kont
  | .continue_ => .resume
  | .cleanup b => .goto b
  | .terminate => .abort
  | .unreachable => .unreachable

noncomputable def kontNext (i : InitTree) : Kont → Next
  | .goto b => .jump b
  | .resume => .exit (.unwound i.live)
  | .abort => .exit .aborted
  | .unreachable => .exit .unreachable

noncomputable def UnwindAction.isTerminate : UnwindAction → Bool
  | .terminate => true
  | _ => false

/-- Reference meaning of `Drop(p) -> [return: ret, unwind: unw]`. -/
noncomputable def srcDrop (p : PlaceTree) (ret : Nat) (unw : UnwindAction) (i : InitTree)
    (o : Oracle) : StepRes :=
  match (glue .conditional p.leaves unw.isTerminate i o).exit with
  | .ok =>
    ⟨(glue .conditional p.leaves unw.isTerminate i o).events,
      (glue .conditional p.leaves unw.isTerminate i o).init,
      (glue .conditional p.leaves unw.isTerminate i o).oracle, .jump ret⟩
  | .panicked =>
    ⟨(glue .conditional p.leaves unw.isTerminate i o).events,
      (glue .conditional p.leaves unw.isTerminate i o).init,
      (glue .conditional p.leaves unw.isTerminate i o).oracle,
      if unw.isTerminate then .jump ret
      else kontNext (glue .conditional p.leaves unw.isTerminate i o).init (kontOf unw)⟩
  | .aborted =>
    ⟨(glue .conditional p.leaves unw.isTerminate i o).events,
      (glue .conditional p.leaves unw.isTerminate i o).init,
      (glue .conditional p.leaves unw.isTerminate i o).oracle, .exit .aborted⟩
  | .doubleDrop mp =>
    ⟨(glue .conditional p.leaves unw.isTerminate i o).events,
      (glue .conditional p.leaves unw.isTerminate i o).init,
      (glue .conditional p.leaves unw.isTerminate i o).oracle, .exit (.doubleDrop mp)⟩

noncomputable def srcTerm (t : Term) (i : InitTree) (o : Oracle) : StepRes :=
  match t with
  | .goto b => ⟨[], i, o, .jump b⟩
  | .branch a b => ⟨[], i, o.next.2, .jump (if o.next.1 then a else b)⟩
  | .call r u =>
    if o.next.1 then ⟨[.panic], i, o.next.2, kontNext i (kontOf u)⟩ else ⟨[], i, o.next.2, .jump r⟩
  | .drop p r u => srcDrop p r u i o
  | .ret => ⟨[], i, o, .exit (.returned i.live)⟩
  | .resume => ⟨[], i, o, .exit (.unwound i.live)⟩
  | .abort => ⟨[], i, o, .exit .aborted⟩
  | .unreachable => ⟨[], i, o, .exit .unreachable⟩

/-- One block of the reference semantics: its statements, then its terminator. -/
noncomputable def srcBlock (blk : Block) (i : InitTree) (o : Oracle) : StepRes :=
  ⟨(execStmts blk.stmts i).1 ++ (srcTerm blk.term (execStmts blk.stmts i).2 o).events,
    (srcTerm blk.term (execStmts blk.stmts i).2 o).init,
    (srcTerm blk.term (execStmts blk.stmts i).2 o).oracle,
    (srcTerm blk.term (execStmts blk.stmts i).2 o).next⟩

/-- Finish a block step: stop with its outcome, or continue with `k` at the block jumped to. -/
noncomputable def Result.ofStep (s : StepRes) (k : Nat → Result) : Result :=
  match s.next with
  | .jump t => ⟨s.events ++ (k t).trace, (k t).outcome⟩
  | .exit oc => ⟨s.events, oc⟩

/-- Fuel-bounded execution of the reference semantics from block `pc`. -/
noncomputable def runSrc (b : Body) : Nat → Nat → InitTree → Oracle → Result
  | 0, _, _, _ => ⟨[], .outOfFuel⟩
  | n + 1, pc, i, o =>
    match b.blocks[pc]? with
    | none => ⟨[], .badJump⟩
    | some blk =>
      Result.ofStep (srcBlock blk i o)
        (fun t => runSrc b n t (srcBlock blk i o).init (srcBlock blk i o).oracle)

theorem Result.ofStep_jump (s : StepRes) (k : Nat → Result) (t : Nat) (h : s.next = .jump t) :
    Result.ofStep s k = ⟨s.events ++ (k t).trace, (k t).outcome⟩ := by
  unfold Result.ofStep; rw [h]

theorem Result.ofStep_exit (s : StepRes) (k : Nat → Result) (oc : Outcome)
    (h : s.next = .exit oc) : Result.ofStep s k = ⟨s.events, oc⟩ := by
  unfold Result.ofStep; rw [h]

theorem runSrc_succ_some (b : Body) (n pc : Nat) (i : InitTree) (o : Oracle) (blk : Block)
    (hb : b.blocks[pc]? = some blk) :
    runSrc b (n + 1) pc i o =
      Result.ofStep (srcBlock blk i o)
        (fun t => runSrc b n t (srcBlock blk i o).init (srcBlock blk i o).oracle) := by
  rw [runSrc, hb]

theorem runSrc_succ_none (b : Body) (n pc : Nat) (i : InitTree) (o : Oracle)
    (hb : b.blocks[pc]? = none) : runSrc b (n + 1) pc i o = ⟨[], .badJump⟩ := by
  rw [runSrc, hb]

/-! ## 5. Elaborated bodies and their semantics -/

/-- Values of the drop-flag locals, indexed by the move path they guard. -/
abbrev DropFlagEnv := MovePath → Bool

noncomputable def DropFlagEnv.set (f : DropFlagEnv) (mp : MovePath) (b : Bool) : DropFlagEnv :=
  fun x => if x = mp then b else f x

inductive TStmt where
  | init (p : PlaceTree)
  | move (p : PlaceTree)
  | nop
  /-- `_flag = const b` -/
  | setFlag (mp : MovePath) (b : Bool)

/-- The blocks created for one elaborated drop, as a tree. -/
inductive Ladder where
  | exit (k : Kont)
  /-- `switchInt(copy flag) -> [0: unset, otherwise: set]` -/
  | test (flag : MovePath) (set unset : Ladder)
  /-- `drop(p) -> [return: ret, unwind: unw]`, unconditional -/
  | drop (p : PlaceTree) (ret unw : Ladder)

inductive TTerm where
  | goto (t : Nat)
  | branch (t e : Nat)
  | call (ret : Nat) (unw : UnwindAction)
  | ladder (l : Ladder)
  | ret
  | resume
  | abort
  | unreachable

structure TBlock where
  stmts : List TStmt
  term : TTerm

structure TBody where
  blocks : List TBlock

noncomputable def texecStmt : TStmt → DropFlagEnv → InitTree → List Event × DropFlagEnv × InitTree
  | .init p, f, i => (p.leaves.map Event.init, f, i.setAll p.leaves true)
  | .move p, f, i => ((p.leaves.filter i.get).map Event.moved, f, i.setAll p.leaves false)
  | .nop, f, i => ([], f, i)
  | .setFlag mp b, f, i => ([], f.set mp b, i)

noncomputable def texecStmts :
    List TStmt → DropFlagEnv → InitTree → List Event × DropFlagEnv × InitTree
  | [], f, i => ([], f, i)
  | s :: ss, f, i =>
    ((texecStmt s f i).1 ++ (texecStmts ss (texecStmt s f i).2.1 (texecStmt s f i).2.2).1,
      (texecStmts ss (texecStmt s f i).2.1 (texecStmt s f i).2.2).2)

inductive LExit where
  | kont (k : Kont)
  | doubleDrop (mp : MovePath)

structure LadderRes where
  events : List Event
  init : InitTree
  oracle : Oracle
  exit : LExit

noncomputable def LadderRes.prepend (es : List Event) (r : LadderRes) : LadderRes :=
  ⟨es ++ r.events, r.init, r.oracle, r.exit⟩

/-- Continue a glue run as a ladder: `onOk` after normal completion, `onPanicked` when a
destructor panicked and unwinding continues. -/
noncomputable def GlueRes.toLadder (g : GlueRes) (onOk onPanicked : InitTree → Oracle → LadderRes) :
    LadderRes :=
  match g.exit with
  | .ok => (onOk g.init g.oracle).prepend g.events
  | .panicked => (onPanicked g.init g.oracle).prepend g.events
  | .aborted => ⟨g.events, g.init, g.oracle, .kont .abort⟩
  | .doubleDrop mp => ⟨g.events, g.init, g.oracle, .doubleDrop mp⟩

/-- Execute a ladder. `m` is `.checked` (report drops of uninitialized leaves) or `.blind`. -/
noncomputable def Ladder.eval (m : GlueMode) (f : DropFlagEnv) :
    Ladder → InitTree → Oracle → LadderRes
  | .exit k, i, o => ⟨[], i, o, .kont k⟩
  | .test flag s u, i, o => if f flag then s.eval m f i o else u.eval m f i o
  | .drop p ret unw, i, o =>
    (glue m p.leaves false i o).toLadder (fun i' o' => ret.eval m f i' o')
      (fun i' o' => unw.eval m f i' o')

noncomputable def stepOfLadder (r : LadderRes) : StepRes :=
  match r.exit with
  | .kont k => ⟨r.events, r.init, r.oracle, kontNext r.init k⟩
  | .doubleDrop mp => ⟨r.events, r.init, r.oracle, .exit (.doubleDrop mp)⟩

noncomputable def tgtTerm (m : GlueMode) (t : TTerm) (f : DropFlagEnv) (i : InitTree)
    (o : Oracle) : StepRes :=
  match t with
  | .goto b => ⟨[], i, o, .jump b⟩
  | .branch a b => ⟨[], i, o.next.2, .jump (if o.next.1 then a else b)⟩
  | .call r u =>
    if o.next.1 then ⟨[.panic], i, o.next.2, kontNext i (kontOf u)⟩ else ⟨[], i, o.next.2, .jump r⟩
  | .ladder l => stepOfLadder (l.eval m f i o)
  | .ret => ⟨[], i, o, .exit (.returned i.live)⟩
  | .resume => ⟨[], i, o, .exit (.unwound i.live)⟩
  | .abort => ⟨[], i, o, .exit .aborted⟩
  | .unreachable => ⟨[], i, o, .exit .unreachable⟩

/-- One block of an elaborated body: the drop flags after its statements, and its step. -/
noncomputable def tgtBlock (m : GlueMode) (blk : TBlock) (f : DropFlagEnv) (i : InitTree)
    (o : Oracle) : DropFlagEnv × StepRes :=
  ((texecStmts blk.stmts f i).2.1,
    ⟨(texecStmts blk.stmts f i).1 ++
        (tgtTerm m blk.term (texecStmts blk.stmts f i).2.1 (texecStmts blk.stmts f i).2.2 o).events,
      (tgtTerm m blk.term (texecStmts blk.stmts f i).2.1 (texecStmts blk.stmts f i).2.2 o).init,
      (tgtTerm m blk.term (texecStmts blk.stmts f i).2.1 (texecStmts blk.stmts f i).2.2 o).oracle,
      (tgtTerm m blk.term (texecStmts blk.stmts f i).2.1 (texecStmts blk.stmts f i).2.2 o).next⟩)

/-- Fuel-bounded execution of an elaborated body from block `pc`. The `InitTree` is ghost state:
no elaborated instruction reads it; it only decides whether a drop is reported as a double drop
(in `.checked` mode) and which leaves are live at exit. -/
noncomputable def runTgt (m : GlueMode) (b : TBody) :
    Nat → Nat → DropFlagEnv → InitTree → Oracle → Result
  | 0, _, _, _, _ => ⟨[], .outOfFuel⟩
  | n + 1, pc, f, i, o =>
    match b.blocks[pc]? with
    | none => ⟨[], .badJump⟩
    | some blk =>
      Result.ofStep (tgtBlock m blk f i o).2
        (fun t => runTgt m b n t (tgtBlock m blk f i o).1 (tgtBlock m blk f i o).2.init
          (tgtBlock m blk f i o).2.oracle)

/-! ## 6. The elaboration -/

/-- Elaborate a drop that sits on the unwind path (`Unwind::InCleanup`): any panic aborts. -/
noncomputable def elabCleanup (f : Facts) : PlaceTree → Ladder → Ladder
  | .leaf l, k =>
    if !f.mi.contains l then k
    else if f.di.contains l then .drop (.leaf l) k (.exit .abort)
    else .test l (.drop (.leaf l) k (.exit .abort)) k
  | .node a b, k =>
    if (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) then k
    else if (a.leaves ++ b.leaves).all (fun l => f.di.contains l) then
      .drop (.node a b) k (.exit .abort)
    else elabCleanup f a (elabCleanup f b k)

/-- Elaborate `drop p` with return continuation `ret` and unwind continuation `unw`.
* no leaf may be initialized: `DropStyle::Dead`, the drop disappears;
* every leaf is definitely initialized: `DropStyle::Static`, one unconditional drop;
* a single leaf in doubt: `DropStyle::Conditional`, test its flag;
* an aggregate in doubt: `DropStyle::Open`, a ladder over the parts; if dropping the first part
  panics, the second part is dropped on the unwind path before following `unw`. -/
noncomputable def elabDrop (f : Facts) : PlaceTree → Ladder → Ladder → Ladder
  | .leaf l, ret, unw =>
    if !f.mi.contains l then ret
    else if f.di.contains l then .drop (.leaf l) ret unw
    else .test l (.drop (.leaf l) ret unw) ret
  | .node a b, ret, unw =>
    if (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) then ret
    else if (a.leaves ++ b.leaves).all (fun l => f.di.contains l) then .drop (.node a b) ret unw
    else elabDrop f a (elabDrop f b ret unw) (elabCleanup f b unw)

noncomputable def xferStmt (f : Facts) : Stmt → Facts
  | .init p =>
    ⟨p.leaves ++ f.mi, p.leaves ++ f.di, f.st.filter (fun x => !p.leaves.contains x)⟩
  | .move p =>
    ⟨f.mi.filter (fun x => !p.leaves.contains x), f.di.filter (fun x => !p.leaves.contains x),
      f.st.filter (fun x => !p.leaves.contains x)⟩
  | .nop => f

noncomputable def xferStmts : Facts → List Stmt → Facts
  | f, [] => f
  | f, s :: ss => xferStmts (xferStmt f s) ss

/-- Facts after a drop of `p`: its leaves are uninitialized; the flags of those that may have been
initialized are now possibly stale, because the elaborated drop does not clear them. -/
noncomputable def xferDrop (f : Facts) (p : PlaceTree) : Facts :=
  ⟨f.mi.filter (fun x => !p.leaves.contains x), f.di.filter (fun x => !p.leaves.contains x),
    p.leaves.filter (fun x => f.mi.contains x) ++ f.st⟩

noncomputable def flagWrites (flagged : List MovePath) (ls : List MovePath) (b : Bool) : List TStmt :=
  (ls.filter (fun x => flagged.contains x)).map (fun x => TStmt.setFlag x b)

noncomputable def elabStmt (flagged : List MovePath) : Stmt → List TStmt
  | .init p => flagWrites flagged p.leaves true ++ [.init p]
  | .move p => flagWrites flagged p.leaves false ++ [.move p]
  | .nop => [.nop]

noncomputable def elabStmts (flagged : List MovePath) : List Stmt → List TStmt
  | [] => []
  | s :: ss => elabStmt flagged s ++ elabStmts flagged ss

noncomputable def elabTerm (f : Facts) : Term → TTerm
  | .goto t => .goto t
  | .branch t e => .branch t e
  | .call r u => .call r u
  | .drop p r u =>
    if u.isTerminate then .ladder (elabCleanup f p (.exit (.goto r)))
    else .ladder (elabDrop f p (.exit (.goto r)) (.exit (kontOf u)))
  | .ret => .ret
  | .resume => .resume
  | .abort => .abort
  | .unreachable => .unreachable

noncomputable def elabBlock (flagged : List MovePath) (b : Block) : TBlock :=
  ⟨elabStmts flagged b.stmts, elabTerm (xferStmts b.facts b.stmts) b.term⟩

/-- The lowered body. All drop flags start out `false` (see `runElab`). -/
noncomputable def elaborate (b : Body) : TBody :=
  ⟨b.blocks.map (elabBlock b.flagged)⟩

/-! ## 7. The certificate checker -/

noncomputable def Facts.le (f g : Facts) : Bool :=
  f.mi.all (fun x => g.mi.contains x) && g.di.all (fun x => f.di.contains x) &&
    f.st.all (fun x => g.st.contains x)

/-- The facts `f` flowing along an edge are subsumed by the facts recorded at its target. -/
noncomputable def edgeOk (b : Body) (f : Facts) (t : Nat) : Bool :=
  match b.blocks[t]? with
  | some blk => f.le blk.facts
  | none => true

noncomputable def unwindOk (b : Body) (f : Facts) : UnwindAction → Bool
  | .cleanup t => edgeOk b f t
  | _ => true

noncomputable def stmtOk (b : Body) : Stmt → Bool
  | .init p => p.leaves.all (fun x => b.frame.leaves.contains x)
  | _ => true

/-- Side conditions of an elaborated drop: the place has no repeated move path, and every leaf
that is in doubt owns a drop flag which is not stale. -/
noncomputable def dropOk (b : Body) (f : Facts) (p : PlaceTree) : Bool :=
  p.wf && p.leaves.all (fun l =>
    !f.mi.contains l || f.di.contains l || (b.flagged.contains l && !f.st.contains l))

noncomputable def termOk (b : Body) (f : Facts) : Term → Bool
  | .goto t => edgeOk b f t
  | .branch t e => edgeOk b f t && edgeOk b f e
  | .call r u => edgeOk b f r && unwindOk b f u
  | .drop p r u => dropOk b f p && edgeOk b (xferDrop f p) r && unwindOk b (xferDrop f p) u
  | _ => true

noncomputable def blockOk (b : Body) (blk : Block) : Bool :=
  blk.stmts.all (stmtOk b) && termOk b (xferStmts blk.facts blk.stmts) blk.term

noncomputable def entryOk (b : Body) : Bool :=
  match b.blocks[0]? with
  | some blk => blk.facts.di.isEmpty
  | none => true

/-- The whole certificate is valid. -/
noncomputable def check (b : Body) : Bool :=
  b.blocks.all (blockOk b) && entryOk b

/-- Run the reference semantics from function entry. -/
noncomputable def runRef (b : Body) (fuel : Nat) (o : Oracle) : Result :=
  runSrc b fuel 0 (InitTree.ofPlace b.frame) o

/-- Run the elaborated body from function entry, all drop flags cleared. -/
noncomputable def runElab (m : GlueMode) (b : Body) (fuel : Nat) (o : Oracle) : Result :=
  runTgt m (elaborate b) fuel 0 (fun _ => false) (InitTree.ofPlace b.frame) o

/-! ## 8. Correctness of the elaboration -/

/-- An elaborated ladder run `t` against its reference `s`: identical, or both abort and the
elaborated run ran additional destructors after the fatal panic. -/
def LRel (t s : LadderRes) : Prop :=
  t = s ∨ (s.exit = .kont .abort ∧ t.exit = .kont .abort ∧ ∃ extra, t.events = s.events ++ extra)

theorem LRel.refl (t : LadderRes) : LRel t t := Or.inl rfl

theorem LRel.trans {a b c : LadderRes} (h1 : LRel a b) (h2 : LRel b c) : LRel a c := by
  rcases h1 with h1 | ⟨hb, ha, e1, he1⟩
  · subst h1; exact h2
  · rcases h2 with h2 | ⟨hc, _, e2, he2⟩
    · subst h2; exact Or.inr ⟨hb, ha, e1, he1⟩
    · exact Or.inr ⟨hc, ha, e2 ++ e1, by rw [he1, he2, List.append_assoc]⟩

theorem LadderRes.prepend_nil (r : LadderRes) : r.prepend [] = r := by
  cases r; rfl

theorem LRel.prepend (es : List Event) {t s : LadderRes} (h : LRel t s) :
    LRel (t.prepend es) (s.prepend es) := by
  rcases h with h | ⟨hs, ht, e, he⟩
  · subst h; exact Or.inl rfl
  · refine Or.inr ⟨hs, ht, e, ?_⟩
    simp [LadderRes.prepend, he, List.append_assoc]

theorem GlueRes.toLadder_prepend (es : List Event) (g : GlueRes)
    (A B : InitTree → Oracle → LadderRes) :
    (g.prepend es).toLadder A B = (g.toLadder A B).prepend es := by
  cases g with
  | mk ev i o ex =>
    cases ex <;>
      simp [GlueRes.prepend, GlueRes.toLadder, LadderRes.prepend, List.append_assoc]

theorem GlueRes.andThen_toLadder (g : GlueRes) (k : Bool → InitTree → Oracle → GlueRes)
    (A B : InitTree → Oracle → LadderRes) :
    (g.andThen k).toLadder A B =
      g.toLadder (fun i o => (k false i o).toLadder A B) (fun i o => (k true i o).toLadder A B) := by
  cases g with
  | mk ev i o ex =>
    cases ex with
    | ok =>
      show ((k false i o).prepend ev).toLadder A B = _
      rw [GlueRes.toLadder_prepend]; rfl
    | panicked =>
      show ((k true i o).prepend ev).toLadder A B = _
      rw [GlueRes.toLadder_prepend]; rfl
    | aborted => rfl
    | doubleDrop mp => rfl

theorem GlueRes.toLadder_congr_ok (g : GlueRes) (A A' B : InitTree → Oracle → LadderRes)
    (h : g.exit ≠ .ok) : g.toLadder A B = g.toLadder A' B := by
  cases g with
  | mk ev i o ex =>
    cases ex with
    | ok => exact absurd rfl h
    | panicked => rfl
    | aborted => rfl
    | doubleDrop mp => rfl

theorem LRel.toLadder (g : GlueRes) (A A' B B' : InitTree → Oracle → LadderRes)
    (hA : g.exit = .ok → LRel (A g.init g.oracle) (A' g.init g.oracle))
    (hB : g.exit = .panicked → LRel (B g.init g.oracle) (B' g.init g.oracle)) :
    LRel (g.toLadder A B) (g.toLadder A' B') := by
  cases g with
  | mk ev i o ex =>
    cases ex with
    | ok => exact LRel.prepend ev (hA rfl)
    | panicked => exact LRel.prepend ev (hB rfl)
    | aborted => exact Or.inl rfl
    | doubleDrop mp => exact Or.inl rfl

/-- Reference behaviour of a drop of the leaves `ls` that is not on the unwind path, continued by
the ladders `ret` and `unw`. -/
noncomputable def refDrop (fl : DropFlagEnv) (ls : List MovePath) (ret unw : Ladder)
    (i : InitTree) (o : Oracle) : LadderRes :=
  (glue .conditional ls false i o).toLadder (fun i' o' => ret.eval .checked fl i' o')
    (fun i' o' => unw.eval .checked fl i' o')

/-- Reference behaviour of a drop of the leaves `ls` on the unwind path, continued by `k`. -/
noncomputable def refCleanup (fl : DropFlagEnv) (ls : List MovePath) (k : Ladder)
    (i : InitTree) (o : Oracle) : LadderRes :=
  (glue .conditional ls true i o).toLadder (fun i' o' => k.eval .checked fl i' o')
    (fun i' o' => k.eval .checked fl i' o')

theorem glue_conditional_unwinding_not_ok (ls : List MovePath) (i : InitTree) (o : Oracle) :
    (glue .conditional ls true i o).exit ≠ .ok := by
  intro h
  rcases glue_conditional_unwinding_exit ls i o with h' | h' <;> rw [h] at h' <;> cases h'

theorem refDrop_append (fl : DropFlagEnv) (l1 l2 : List MovePath) (ret unw : Ladder)
    (i : InitTree) (o : Oracle) :
    refDrop fl (l1 ++ l2) ret unw i o =
      (glue .conditional l1 false i o).toLadder (fun i' o' => refDrop fl l2 ret unw i' o')
        (fun i' o' => refCleanup fl l2 unw i' o') := by
  have hU : ∀ i' o', refCleanup fl l2 unw i' o' =
      (glue .conditional l2 true i' o').toLadder (fun i'' o'' => ret.eval .checked fl i'' o'')
        (fun i'' o'' => unw.eval .checked fl i'' o'') := by
    intro i' o'
    exact GlueRes.toLadder_congr_ok _ _ _ _ (glue_conditional_unwinding_not_ok l2 i' o')
  simp only [refDrop, hU, glue_append, GlueRes.andThen_toLadder]

theorem refCleanup_append (fl : DropFlagEnv) (l1 l2 : List MovePath) (k : Ladder)
    (i : InitTree) (o : Oracle) :
    refCleanup fl (l1 ++ l2) k i o =
      (glue .conditional l1 true i o).toLadder (fun i' o' => refCleanup fl l2 k i' o')
        (fun i' o' => refCleanup fl l2 k i' o') := by
  simp only [refCleanup, glue_append, GlueRes.andThen_toLadder]
  exact GlueRes.toLadder_congr_ok _ _ _ _ (glue_conditional_unwinding_not_ok l1 i o)

theorem refDrop_dead (fl : DropFlagEnv) (ls : List MovePath) (ret unw : Ladder) (i : InitTree)
    (o : Oracle) (h : ∀ x, x ∈ ls → i.get x = false) :
    refDrop fl ls ret unw i o = ret.eval .checked fl i o := by
  unfold refDrop
  rw [glue_conditional_all_uninit ls false i o h]
  exact LadderRes.prepend_nil _

theorem refCleanup_dead (fl : DropFlagEnv) (ls : List MovePath) (k : Ladder) (i : InitTree)
    (o : Oracle) (h : ∀ x, x ∈ ls → i.get x = false) :
    refCleanup fl ls k i o = k.eval .checked fl i o := by
  unfold refCleanup
  rw [glue_conditional_all_uninit ls true i o h]
  exact LadderRes.prepend_nil _

theorem Ladder.eval_drop (m : GlueMode) (fl : DropFlagEnv) (p : PlaceTree) (ret unw : Ladder)
    (i : InitTree) (o : Oracle) :
    (Ladder.drop p ret unw).eval m fl i o =
      (glue m p.leaves false i o).toLadder (fun i' o' => ret.eval m fl i' o')
        (fun i' o' => unw.eval m fl i' o') := by
  rw [Ladder.eval]

theorem Ladder.eval_test (m : GlueMode) (fl : DropFlagEnv) (flag : MovePath) (s u : Ladder)
    (i : InitTree) (o : Oracle) :
    (Ladder.test flag s u).eval m fl i o = if fl flag then s.eval m fl i o else u.eval m fl i o := by
  rw [Ladder.eval]

theorem Ladder.eval_exit (m : GlueMode) (fl : DropFlagEnv) (k : Kont) (i : InitTree) (o : Oracle) :
    (Ladder.exit k).eval m fl i o = ⟨[], i, o, .kont k⟩ := by
  rw [Ladder.eval]

/-- `DropStyle::Static`, not on the unwind path: one unconditional drop is exactly the reference. -/
theorem eval_drop_static (fl : DropFlagEnv) (p : PlaceTree) (ret unw : Ladder) (i : InitTree)
    (o : Oracle) (hw : p.wf = true) (h : ∀ x, x ∈ p.leaves → i.get x = true) :
    (Ladder.drop p ret unw).eval .checked fl i o = refDrop fl p.leaves ret unw i o := by
  rw [Ladder.eval_drop, glue_checked_eq_conditional p.leaves false i o (PlaceTree.wf_distinct p hw) h]
  rfl

/-- On the unwind path, drop glue called for a whole place keeps dropping its remaining leaves
after the fatal panic, whereas the reference stops at that panic. -/
theorem cleanup_static (K : InitTree → Oracle → LadderRes) (ls : List MovePath) (i : InitTree)
    (o : Oracle) :
    LRel ((glue .conditional ls false i o).toLadder K (fun i' o' => ⟨[], i', o', .kont .abort⟩))
      ((glue .conditional ls true i o).toLadder K K) := by
  rcases glue_conditional_unwinding_exit ls i o with hx | hx
  · rw [glue_conditional_unwinding_panicked ls i o hx]
    apply Or.inl
    generalize glue .conditional ls true i o = g at hx
    cases g with
    | mk ev i' o' ex =>
      simp at hx
      subst hx
      rfl
  · obtain ⟨⟨extra, he⟩, hx'⟩ := glue_conditional_unwinding_aborted ls i o hx
    apply Or.inr
    generalize glue .conditional ls true i o = g at hx he
    generalize glue .conditional ls false i o = g' at he hx'
    cases g with
    | mk ev i1 o1 ex =>
      cases g' with
      | mk ev' i2 o2 ex' =>
        simp at hx he hx'
        subst hx
        rcases hx' with h | h <;> subst h <;>
          simp [GlueRes.toLadder, LadderRes.prepend, he]

/-- `DropStyle::Static` on the unwind path. -/
theorem eval_drop_static_cleanup (fl : DropFlagEnv) (p : PlaceTree) (k : Ladder) (i : InitTree)
    (o : Oracle) (hw : p.wf = true) (h : ∀ x, x ∈ p.leaves → i.get x = true) :
    LRel ((Ladder.drop p k (.exit .abort)).eval .checked fl i o) (refCleanup fl p.leaves k i o) := by
  rw [Ladder.eval_drop, glue_checked_eq_conditional p.leaves false i o (PlaceTree.wf_distinct p hw) h]
  have e : (fun i' o' => (Ladder.exit Kont.abort).eval .checked fl i' o') =
      (fun i' o' => (⟨[], i', o', .kont .abort⟩ : LadderRes)) := by
    funext i' o'; rw [Ladder.eval_exit]
  rw [e]
  exact cleanup_static _ p.leaves i o

/-- What the elaboration needs to know about one leaf of a dropped place. -/
def LeafOK (f : Facts) (fl : DropFlagEnv) (i : InitTree) (l : MovePath) : Prop :=
  (l ∈ f.di → i.get l = true) ∧ (i.get l = true → l ∈ f.mi) ∧
    (l ∈ f.mi → l ∉ f.di → fl l = i.get l)

theorem elabDrop_leaf (f : Facts) (l : MovePath) (ret unw : Ladder) :
    elabDrop f (.leaf l) ret unw =
      if !f.mi.contains l then ret
      else if f.di.contains l then .drop (.leaf l) ret unw
      else .test l (.drop (.leaf l) ret unw) ret := by
  rw [elabDrop]

theorem elabDrop_node (f : Facts) (a b : PlaceTree) (ret unw : Ladder) :
    elabDrop f (.node a b) ret unw =
      if (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) then ret
      else if (a.leaves ++ b.leaves).all (fun l => f.di.contains l) then .drop (.node a b) ret unw
      else elabDrop f a (elabDrop f b ret unw) (elabCleanup f b unw) := by
  rw [elabDrop]

theorem elabCleanup_leaf (f : Facts) (l : MovePath) (k : Ladder) :
    elabCleanup f (.leaf l) k =
      if !f.mi.contains l then k
      else if f.di.contains l then .drop (.leaf l) k (.exit .abort)
      else .test l (.drop (.leaf l) k (.exit .abort)) k := by
  rw [elabCleanup]

theorem elabCleanup_node (f : Facts) (a b : PlaceTree) (k : Ladder) :
    elabCleanup f (.node a b) k =
      if (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) then k
      else if (a.leaves ++ b.leaves).all (fun l => f.di.contains l) then
        .drop (.node a b) k (.exit .abort)
      else elabCleanup f a (elabCleanup f b k) := by
  rw [elabCleanup]

/-- The elaborated ladder of a drop agrees with the reference behaviour of that drop. -/
theorem elab_ladder (f : Facts) (fl : DropFlagEnv) (p : PlaceTree) :
    p.wf = true → ∀ (i : InitTree) (o : Oracle), (∀ l, l ∈ p.leaves → LeafOK f fl i l) →
      (∀ ret unw, LRel ((elabDrop f p ret unw).eval .checked fl i o)
          (refDrop fl p.leaves ret unw i o)) ∧
      (∀ k, LRel ((elabCleanup f p k).eval .checked fl i o) (refCleanup fl p.leaves k i o)) := by
  induction p with
  | leaf l =>
    intro hw i o hok
    have hl : LeafOK f fl i l := hok l (by simp [PlaceTree.leaves])
    have hall : ∀ (v : Bool), i.get l = v → ∀ x, x ∈ (PlaceTree.leaf l).leaves → i.get x = v := by
      intro v hv x hx
      simp [PlaceTree.leaves] at hx
      subst hx; exact hv
    by_cases hmi : l ∈ f.mi
    · have cmi : (!f.mi.contains l) = false := by simpa using hmi
      by_cases hdi : l ∈ f.di
      · have cdi : f.di.contains l = true := by simpa using hdi
        have hg := hall true (hl.1 hdi)
        constructor
        · intro ret unw
          rw [elabDrop_leaf, cmi, cdi]
          simp only [Bool.false_eq_true, ite_false, ite_true]
          rw [eval_drop_static fl _ ret unw i o hw hg]
          exact LRel.refl _
        · intro k
          rw [elabCleanup_leaf, cmi, cdi]
          simp only [Bool.false_eq_true, ite_false, ite_true]
          exact eval_drop_static_cleanup fl _ k i o hw hg
      · have cdi : f.di.contains l = false := by simpa using hdi
        have hfl : fl l = i.get l := hl.2.2 hmi hdi
        cases hgl : i.get l with
        | true =>
          have hg := hall true hgl
          rw [hgl] at hfl
          constructor
          · intro ret unw
            rw [elabDrop_leaf, cmi, cdi]
            simp only [Bool.false_eq_true, ite_false]
            rw [Ladder.eval_test, hfl]
            simp only [ite_true]
            rw [eval_drop_static fl _ ret unw i o hw hg]
            exact LRel.refl _
          · intro k
            rw [elabCleanup_leaf, cmi, cdi]
            simp only [Bool.false_eq_true, ite_false]
            rw [Ladder.eval_test, hfl]
            simp only [ite_true]
            exact eval_drop_static_cleanup fl _ k i o hw hg
        | false =>
          have hg := hall false hgl
          rw [hgl] at hfl
          constructor
          · intro ret unw
            rw [elabDrop_leaf, cmi, cdi]
            simp only [Bool.false_eq_true, ite_false]
            rw [Ladder.eval_test, hfl]
            simp only [Bool.false_eq_true, ite_false]
            rw [refDrop_dead fl _ ret unw i o hg]
            exact LRel.refl _
          · intro k
            rw [elabCleanup_leaf, cmi, cdi]
            simp only [Bool.false_eq_true, ite_false]
            rw [Ladder.eval_test, hfl]
            simp only [Bool.false_eq_true, ite_false]
            rw [refCleanup_dead fl _ k i o hg]
            exact LRel.refl _
    · have cmi : (!f.mi.contains l) = true := by simpa using hmi
      have hgl : i.get l = false := by
        cases h : i.get l with
        | false => rfl
        | true => exact absurd (hl.2.1 h) hmi
      have hg := hall false hgl
      constructor
      · intro ret unw
        rw [elabDrop_leaf, cmi]
        simp only [ite_true]
        rw [refDrop_dead fl _ ret unw i o hg]
        exact LRel.refl _
      · intro k
        rw [elabCleanup_leaf, cmi]
        simp only [ite_true]
        rw [refCleanup_dead fl _ k i o hg]
        exact LRel.refl _
  | node a b iha ihb =>
    intro hw i o hok
    obtain ⟨hwa, hwb, hdisj⟩ := PlaceTree.wf_node a b hw
    have hleaves : (PlaceTree.node a b).leaves = a.leaves ++ b.leaves := rfl
    by_cases hdead : (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) = true
    · have hg : ∀ x, x ∈ (PlaceTree.node a b).leaves → i.get x = false := by
        intro x hx
        have hx' : x ∉ f.mi := by
          have := List.all_eq_true.mp hdead x hx
          simpa using this
        cases h : i.get x with
        | false => rfl
        | true => exact absurd ((hok x hx).2.1 h) hx'
      constructor
      · intro ret unw
        rw [elabDrop_node, ite_eq_left hdead, refDrop_dead fl _ ret unw i o hg]
        exact LRel.refl _
      · intro k
        rw [elabCleanup_node, ite_eq_left hdead, refCleanup_dead fl _ k i o hg]
        exact LRel.refl _
    · by_cases hstat : (a.leaves ++ b.leaves).all (fun l => f.di.contains l) = true
      · have hg : ∀ x, x ∈ (PlaceTree.node a b).leaves → i.get x = true := by
          intro x hx
          have hx' : x ∈ f.di := by
            have := List.all_eq_true.mp hstat x hx
            simpa using this
          exact (hok x hx).1 hx'
        constructor
        · intro ret unw
          rw [elabDrop_node, ite_eq_right hdead, ite_eq_left hstat, eval_drop_static fl _ ret unw i o hw hg]
          exact LRel.refl _
        · intro k
          rw [elabCleanup_node, ite_eq_right hdead, ite_eq_left hstat]
          exact eval_drop_static_cleanup fl _ k i o hw hg
      · have hoka : ∀ l, l ∈ a.leaves → LeafOK f fl i l :=
          fun l hl => hok l (by rw [hleaves]; exact List.mem_append_left _ hl)
        have hokb : ∀ (i' : InitTree), (∀ x, x ∈ b.leaves → i'.get x = i.get x) →
            ∀ l, l ∈ b.leaves → LeafOK f fl i' l := by
          intro i' hi' l hl
          have h0 := hok l (by rw [hleaves]; exact List.mem_append_right _ hl)
          unfold LeafOK at h0 ⊢
          rw [hi' l hl]; exact h0
        have hframe : ∀ (u : Bool) (x : MovePath), x ∈ b.leaves →
            (glue .conditional a.leaves u i o).init.get x = i.get x :=
          fun u x hx => glue_frame .conditional a.leaves u i o x (fun hxa => hdisj x hxa hx)
        constructor
        · intro ret unw
          rw [elabDrop_node, ite_eq_right hdead, ite_eq_right hstat, hleaves, refDrop_append]
          refine LRel.trans ((iha hwa i o hoka).1 _ _) ?_
          exact LRel.toLadder _ _ _ _ _
            (fun _ => (ihb hwb _ _ (hokb _ (hframe false))).1 ret unw)
            (fun _ => (ihb hwb _ _ (hokb _ (hframe false))).2 unw)
        · intro k
          rw [elabCleanup_node, ite_eq_right hdead, ite_eq_right hstat, hleaves, refCleanup_append]
          refine LRel.trans ((iha hwa i o hoka).2 _) ?_
          exact LRel.toLadder _ _ _ _ _
            (fun _ => (ihb hwb _ _ (hokb _ (hframe true))).2 k)
            (fun _ => (ihb hwb _ _ (hokb _ (hframe true))).2 k)

/-- The simulation invariant between a reference state and an elaborated state at a program
point with facts `f`: the facts are sound, and every flag that is not possibly stale mirrors the
initialization bit of its leaf. -/
structure Inv (b : Body) (f : Facts) (fl : DropFlagEnv) (i : InitTree) : Prop where
  ids : i.ids = b.frame.leaves
  di : ∀ l, l ∈ f.di → i.get l = true
  mi : ∀ l, i.get l = true → l ∈ f.mi
  flag : ∀ l, l ∈ b.flagged → l ∉ f.st → fl l = i.get l

theorem Inv.mono {b : Body} {f g : Facts} {fl : DropFlagEnv} {i : InitTree}
    (h : f.le g = true) (hinv : Inv b f fl i) : Inv b g fl i := by
  unfold Facts.le at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1' : ∀ x, x ∈ f.mi → x ∈ g.mi := fun x hx => by
    have := List.all_eq_true.mp h1 x hx; simpa using this
  have h2' : ∀ x, x ∈ g.di → x ∈ f.di := fun x hx => by
    have := List.all_eq_true.mp h2 x hx; simpa using this
  have h3' : ∀ x, x ∈ f.st → x ∈ g.st := fun x hx => by
    have := List.all_eq_true.mp h3 x hx; simpa using this
  exact ⟨hinv.ids, fun l hl => hinv.di l (h2' l hl), fun l hl => h1' l (hinv.mi l hl),
    fun l hf hs => hinv.flag l hf (fun hs' => hs (h3' l hs'))⟩

theorem edge_inv {b : Body} {f : Facts} {fl : DropFlagEnv} {i : InitTree} {t : Nat} {blk : Block}
    (he : edgeOk b f t = true) (hb : b.blocks[t]? = some blk) (hinv : Inv b f fl i) :
    Inv b blk.facts fl i := by
  unfold edgeOk at he
  rw [hb] at he
  exact Inv.mono he hinv

theorem texecStmts_append (a b : List TStmt) : ∀ (f : DropFlagEnv) (i : InitTree),
    texecStmts (a ++ b) f i =
      ((texecStmts a f i).1 ++ (texecStmts b (texecStmts a f i).2.1 (texecStmts a f i).2.2).1,
        (texecStmts b (texecStmts a f i).2.1 (texecStmts a f i).2.2).2) := by
  induction a with
  | nil => intro f i; simp [texecStmts]
  | cons s ss ih => intro f i; simp [texecStmts, ih, List.append_assoc]

theorem texec_setFlags (v : Bool) (ls : List MovePath) : ∀ (f : DropFlagEnv) (i : InitTree),
    texecStmts (ls.map (fun x => TStmt.setFlag x v)) f i =
      ([], (fun x => if x ∈ ls then v else f x), i) := by
  induction ls with
  | nil => intro f i; simp [texecStmts]
  | cons a ls ih =>
    intro f i
    have hfun : (fun x => if x ∈ ls then v else DropFlagEnv.set f a v x) =
        (fun x => if x ∈ a :: ls then v else f x) := by
      funext x
      by_cases h1 : x ∈ ls <;> by_cases h2 : x = a <;> simp [DropFlagEnv.set, h1, h2]
    simp [texecStmts, texecStmt, ih, hfun]

/-- One statement: same events, same ownership state, invariant preserved. -/
theorem sim_stmt (b : Body) (f : Facts) (s : Stmt) (fl : DropFlagEnv) (i : InitTree)
    (hok : stmtOk b s = true) (hinv : Inv b f fl i) :
    (texecStmts (elabStmt b.flagged s) fl i).1 = (execStmt s i).1 ∧
    (texecStmts (elabStmt b.flagged s) fl i).2.2 = (execStmt s i).2 ∧
    Inv b (xferStmt f s) (texecStmts (elabStmt b.flagged s) fl i).2.1 (execStmt s i).2 := by
  cases s with
  | init p =>
    have hfr : ∀ x, x ∈ p.leaves → x ∈ i.ids := by
      intro x hx
      rw [hinv.ids]
      have := List.all_eq_true.mp hok x hx
      simpa using this
    have e : texecStmts (elabStmt b.flagged (.init p)) fl i =
        (p.leaves.map Event.init,
          (fun x => if x ∈ p.leaves.filter (fun y => b.flagged.contains y) then true else fl x),
          i.setAll p.leaves true) := by
      simp [elabStmt, flagWrites, texecStmts_append, texec_setFlags, texecStmts, texecStmt]
    rw [e]
    refine ⟨rfl, rfl, ?_⟩
    show Inv b (xferStmt f (.init p)) _ (i.setAll p.leaves true)
    constructor
    · rw [InitTree.ids_setAll]; exact hinv.ids
    · intro l hl
      have hl' : l ∈ p.leaves ∨ l ∈ f.di := by simpa [xferStmt] using hl
      rw [InitTree.get_setAll]
      by_cases h : l ∈ p.leaves
      · simp [h, hfr l h]
      · simp [h]; exact hinv.di l (hl'.resolve_left h)
    · intro l hl
      rw [InitTree.get_setAll] at hl
      show l ∈ p.leaves ++ f.mi
      by_cases h : l ∈ p.leaves
      · exact List.mem_append_left _ h
      · simp [h] at hl; exact List.mem_append_right _ (hinv.mi l hl)
    · intro l hf hs
      have hs' : l ∈ f.st → l ∈ p.leaves := by
        intro h1
        cases Decidable.em (l ∈ p.leaves) with
        | inl h2 => exact h2
        | inr h2 => exact absurd (by simp [xferStmt, List.mem_filter, h1, h2]) hs
      rw [InitTree.get_setAll]
      by_cases h : l ∈ p.leaves
      · simp [h, hf, hfr l h, List.mem_filter]
      · have hst : l ∉ f.st := fun h' => h (hs' h')
        simp [h, List.mem_filter]; exact hinv.flag l hf hst
  | move p =>
    have e : texecStmts (elabStmt b.flagged (.move p)) fl i =
        ((p.leaves.filter i.get).map Event.moved,
          (fun x => if x ∈ p.leaves.filter (fun y => b.flagged.contains y) then false else fl x),
          i.setAll p.leaves false) := by
      simp [elabStmt, flagWrites, texecStmts_append, texec_setFlags, texecStmts, texecStmt]
    rw [e]
    refine ⟨rfl, rfl, ?_⟩
    show Inv b (xferStmt f (.move p)) _ (i.setAll p.leaves false)
    constructor
    · rw [InitTree.ids_setAll]; exact hinv.ids
    · intro l hl
      have hl' : l ∈ f.di ∧ l ∉ p.leaves := by simpa [xferStmt, List.mem_filter] using hl
      rw [InitTree.get_setAll]
      simp [hl'.2]; exact hinv.di l hl'.1
    · intro l hl
      rw [InitTree.get_setAll] at hl
      by_cases h : l ∈ p.leaves
      · simp [h] at hl
      · simp [h] at hl
        show l ∈ f.mi.filter (fun x => !p.leaves.contains x)
        simp [List.mem_filter, h]; exact hinv.mi l hl
    · intro l hf hs
      have hs' : l ∈ f.st → l ∈ p.leaves := by
        intro h1
        cases Decidable.em (l ∈ p.leaves) with
        | inl h2 => exact h2
        | inr h2 => exact absurd (by simp [xferStmt, List.mem_filter, h1, h2]) hs
      rw [InitTree.get_setAll]
      by_cases h : l ∈ p.leaves
      · simp [h, hf, List.mem_filter]
      · have hst : l ∉ f.st := fun h' => h (hs' h')
        simp [h, List.mem_filter]; exact hinv.flag l hf hst
  | nop =>
    exact ⟨by simp [elabStmt, texecStmts, texecStmt, execStmt],
      by simp [elabStmt, texecStmts, texecStmt, execStmt],
      by simpa [elabStmt, texecStmts, texecStmt, execStmt, xferStmt] using hinv⟩

theorem sim_stmts (b : Body) : ∀ (ss : List Stmt) (f : Facts) (fl : DropFlagEnv) (i : InitTree),
    ss.all (stmtOk b) = true → Inv b f fl i →
    (texecStmts (elabStmts b.flagged ss) fl i).1 = (execStmts ss i).1 ∧
    (texecStmts (elabStmts b.flagged ss) fl i).2.2 = (execStmts ss i).2 ∧
    Inv b (xferStmts f ss) (texecStmts (elabStmts b.flagged ss) fl i).2.1 (execStmts ss i).2 := by
  intro ss
  induction ss with
  | nil =>
    intro f fl i _ hinv
    exact ⟨rfl, rfl, hinv⟩
  | cons s ss ih =>
    intro f fl i hok hinv
    rw [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨h1, h2, h3⟩ := sim_stmt b f s fl i hok.1 hinv
    have e : elabStmts b.flagged (s :: ss) = elabStmt b.flagged s ++ elabStmts b.flagged ss := rfl
    rw [e, texecStmts_append]
    rw [← h2] at h3
    obtain ⟨g1, g2, g3⟩ := ih _ _ _ hok.2 h3
    rw [h2] at g1 g2 g3
    refine ⟨?_, ?_, ?_⟩
    · show (texecStmts (elabStmt b.flagged s) fl i).1 ++ _ = (execStmt s i).1 ++ _
      rw [h1, h2, g1]
    · show (texecStmts (elabStmts b.flagged ss) _ _).2.2 = (execStmts ss (execStmt s i).2).2
      rw [h2, g2]
    · show Inv b (xferStmts (xferStmt f s) ss) (texecStmts (elabStmts b.flagged ss) _ _).2.1
        (execStmts ss (execStmt s i).2).2
      rw [h2]; exact g3

/-- A block step of the elaborated body `t` against the reference step `s`. -/
def SRel (t s : StepRes) : Prop :=
  t = s ∨ (s.next = .exit .aborted ∧ t.next = .exit .aborted ∧ ∃ extra, t.events = s.events ++ extra)

theorem SRel.ofLadder {t s : LadderRes} (h : LRel t s) : SRel (stepOfLadder t) (stepOfLadder s) := by
  rcases h with h | ⟨hs, ht, e, he⟩
  · subst h; exact Or.inl rfl
  · refine Or.inr ⟨?_, ?_, e, ?_⟩
    · simp [stepOfLadder, hs, kontNext]
    · simp [stepOfLadder, ht, kontNext]
    · simp [stepOfLadder, hs, ht, he]

theorem srcDrop_cleanup (fl : DropFlagEnv) (p : PlaceTree) (r : Nat) (i : InitTree) (o : Oracle) :
    srcDrop p r .terminate i o = stepOfLadder (refCleanup fl p.leaves (.exit (.goto r)) i o) := by
  unfold srcDrop refCleanup
  simp only [UnwindAction.isTerminate]
  generalize glue .conditional p.leaves true i o = g
  cases g with
  | mk ev i' o' ex =>
    cases ex <;>
      simp [GlueRes.toLadder, stepOfLadder, LadderRes.prepend, Ladder.eval_exit, kontNext]

theorem srcDrop_normal (fl : DropFlagEnv) (p : PlaceTree) (r : Nat) (u : UnwindAction)
    (i : InitTree) (o : Oracle) (hu : u.isTerminate = false) :
    srcDrop p r u i o =
      stepOfLadder (refDrop fl p.leaves (.exit (.goto r)) (.exit (kontOf u)) i o) := by
  unfold srcDrop refDrop
  rw [hu]
  generalize glue .conditional p.leaves false i o = g
  cases g with
  | mk ev i' o' ex =>
    cases ex <;>
      simp [GlueRes.toLadder, stepOfLadder, LadderRes.prepend, Ladder.eval_exit, kontNext]

theorem dropOk_spec (b : Body) (f : Facts) (p : PlaceTree) (h : dropOk b f p = true) :
    p.wf = true ∧ ∀ l, l ∈ p.leaves → l ∈ f.mi → l ∉ f.di → (l ∈ b.flagged ∧ l ∉ f.st) := by
  unfold dropOk at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro l hl hmi hdi
  have h0 := List.all_eq_true.mp h.2 l hl
  have e1 : f.mi.contains l = true := by simpa using hmi
  have e2 : f.di.contains l = false := by simpa using hdi
  rw [e1, e2] at h0
  simpa using h0

/-- The terminator of a block: elaborated versus reference. -/
theorem sim_term (b : Body) (f : Facts) (t : Term) (fl : DropFlagEnv) (i : InitTree) (o : Oracle)
    (hok : termOk b f t = true) (hinv : Inv b f fl i) :
    SRel (tgtTerm .checked (elabTerm f t) fl i o) (srcTerm t i o) := by
  cases t with
  | drop p r u =>
    have h1 : dropOk b f p = true := by
      simp only [termOk, Bool.and_eq_true] at hok; exact hok.1.1
    obtain ⟨hw, hfl⟩ := dropOk_spec b f p h1
    have hleaf : ∀ l, l ∈ p.leaves → LeafOK f fl i l := by
      intro l hl
      refine ⟨hinv.di l, hinv.mi l, fun hmi hdi => ?_⟩
      obtain ⟨h2, h3⟩ := hfl l hl hmi hdi
      exact hinv.flag l h2 h3
    cases hu : u.isTerminate with
    | false =>
      have e : tgtTerm .checked (elabTerm f (.drop p r u)) fl i o =
          stepOfLadder ((elabDrop f p (.exit (.goto r)) (.exit (kontOf u))).eval .checked fl i o) := by
        simp [elabTerm, hu, tgtTerm]
      rw [e]
      show SRel _ (srcDrop p r u i o)
      rw [srcDrop_normal fl p r u i o hu]
      exact SRel.ofLadder ((elab_ladder f fl p hw i o hleaf).1 _ _)
    | true =>
      have hut : u = .terminate := by
        cases u <;> simp [UnwindAction.isTerminate] at hu ⊢
      subst hut
      have e : tgtTerm .checked (elabTerm f (.drop p r .terminate)) fl i o =
          stepOfLadder ((elabCleanup f p (.exit (.goto r))).eval .checked fl i o) := by
        simp [elabTerm, UnwindAction.isTerminate, tgtTerm]
      rw [e]
      show SRel _ (srcDrop p r .terminate i o)
      rw [srcDrop_cleanup fl]
      exact SRel.ofLadder ((elab_ladder f fl p hw i o hleaf).2 _)
  | goto t => exact Or.inl rfl
  | branch t e => exact Or.inl rfl
  | call r u => exact Or.inl rfl
  | ret => exact Or.inl rfl
  | resume => exact Or.inl rfl
  | abort => exact Or.inl rfl
  | unreachable => exact Or.inl rfl

/-- Facts after a drop are sound for the state the reference drop leaves behind. -/
theorem inv_after_glue (b : Body) (f : Facts) (fl : DropFlagEnv) (i : InitTree) (p : PlaceTree)
    (u : Bool) (o : Oracle) (hinv : Inv b f fl i)
    (hx : (glue .conditional p.leaves u i o).exit = .ok ∨
      (glue .conditional p.leaves u i o).exit = .panicked) :
    Inv b (xferDrop f p) fl (glue .conditional p.leaves u i o).init := by
  have hfr := glue_frame .conditional p.leaves u i o
  have hcl := fun x hx' => glue_cleared .conditional p.leaves u i o x hx' hx
  constructor
  · rw [glue_ids]; exact hinv.ids
  · intro l hl
    have hl' : l ∈ f.di ∧ l ∉ p.leaves := by simpa [xferDrop, List.mem_filter] using hl
    rw [hfr l hl'.2]; exact hinv.di l hl'.1
  · intro l hl
    by_cases h : l ∈ p.leaves
    · rw [hcl l h] at hl; cases hl
    · rw [hfr l h] at hl
      show l ∈ f.mi.filter (fun x => !p.leaves.contains x)
      simp [List.mem_filter, h]; exact hinv.mi l hl
  · intro l hf hs
    have hs1 : l ∉ f.st := fun h1 => hs (by simp [xferDrop, h1])
    by_cases h : l ∈ p.leaves
    · have hmi : l ∉ f.mi := fun h1 => hs (by simp [xferDrop, List.mem_filter, h, h1])
      have hi : i.get l = false := by
        cases h' : i.get l with
        | false => rfl
        | true => exact absurd (hinv.mi l h') hmi
      rw [hcl l h, hinv.flag l hf hs1, hi]
    · rw [hfr l h]; exact hinv.flag l hf hs1

theorem srcDrop_jump (p : PlaceTree) (r : Nat) (u : UnwindAction) (i : InitTree) (o : Oracle)
    (tgt : Nat) (hj : (srcDrop p r u i o).next = .jump tgt) :
    ((glue .conditional p.leaves u.isTerminate i o).exit = .ok ∨
      (glue .conditional p.leaves u.isTerminate i o).exit = .panicked) ∧
    (srcDrop p r u i o).init = (glue .conditional p.leaves u.isTerminate i o).init ∧
    (tgt = r ∨ u = .cleanup tgt) := by
  unfold srcDrop at hj ⊢
  generalize glue .conditional p.leaves u.isTerminate i o = g at hj ⊢
  cases g with
  | mk ev i' o' ex =>
    cases ex with
    | ok =>
      simp at hj
      exact ⟨Or.inl rfl, rfl, Or.inl hj.symm⟩
    | panicked =>
      refine ⟨Or.inr rfl, rfl, ?_⟩
      cases u with
      | terminate =>
        simp [UnwindAction.isTerminate] at hj
        exact Or.inl hj.symm
      | cleanup c =>
        simp [UnwindAction.isTerminate, kontOf, kontNext] at hj
        exact Or.inr (by rw [hj])
      | continue_ => simp [UnwindAction.isTerminate, kontOf, kontNext] at hj
      | unreachable => simp [UnwindAction.isTerminate, kontOf, kontNext] at hj
    | aborted => simp at hj
    | doubleDrop mp => simp at hj

theorem srcCall_jump (r : Nat) (u : UnwindAction) (i : InitTree) (o : Oracle) (tgt : Nat)
    (hj : (srcTerm (.call r u) i o).next = .jump tgt) :
    (srcTerm (.call r u) i o).init = i ∧ (tgt = r ∨ u = .cleanup tgt) := by
  simp only [srcTerm] at hj ⊢
  revert hj
  cases o.next.1 with
  | true =>
    intro hj
    have hj' : kontNext i (kontOf u) = .jump tgt := hj
    refine ⟨rfl, ?_⟩
    cases u with
    | cleanup c =>
      have hc : c = tgt := by simpa [kontOf, kontNext] using hj'
      exact Or.inr (by rw [hc])
    | continue_ => simp [kontOf, kontNext] at hj'
    | terminate => simp [kontOf, kontNext] at hj'
    | unreachable => simp [kontOf, kontNext] at hj'
  | false =>
    intro hj
    have hj' : Next.jump r = .jump tgt := hj
    refine ⟨rfl, Or.inl ?_⟩
    injection hj' with h
    exact h.symm

/-- Wherever the reference terminator jumps, the invariant holds for the facts recorded there. -/
theorem inv_next (b : Body) (f : Facts) (t : Term) (fl : DropFlagEnv) (i : InitTree) (o : Oracle)
    (hok : termOk b f t = true) (hinv : Inv b f fl i) :
    ∀ (tgt : Nat) (blk : Block), (srcTerm t i o).next = .jump tgt → b.blocks[tgt]? = some blk →
      Inv b blk.facts fl (srcTerm t i o).init := by
  intro tgt blk hj hb
  cases t with
  | goto t' =>
    simp [srcTerm] at hj
    subst hj
    exact edge_inv (by simpa [termOk] using hok) hb hinv
  | branch a c =>
    simp only [termOk, Bool.and_eq_true] at hok
    have hj' : Next.jump (if o.next.1 then a else c) = .jump tgt := hj
    show Inv b blk.facts fl i
    injection hj' with h
    subst h
    cases hc : o.next.1 with
    | true =>
      rw [hc] at hb
      exact edge_inv hok.1 hb hinv
    | false =>
      rw [hc] at hb
      exact edge_inv hok.2 hb hinv
  | call r u =>
    simp only [termOk, Bool.and_eq_true] at hok
    obtain ⟨hi, htgt⟩ := srcCall_jump r u i o tgt hj
    rw [hi]
    rcases htgt with h | h
    · subst h; exact edge_inv hok.1 hb hinv
    · subst h; exact edge_inv (by simpa [unwindOk] using hok.2) hb hinv
  | drop p r u =>
    simp only [termOk, Bool.and_eq_true] at hok
    obtain ⟨⟨_, hr⟩, hu⟩ := hok
    obtain ⟨hx, hi, htgt⟩ := srcDrop_jump p r u i o tgt hj
    show Inv b blk.facts fl (srcDrop p r u i o).init
    rw [hi]
    have hinv' := inv_after_glue b f fl i p _ o hinv hx
    rcases htgt with h | h
    · subst h; exact edge_inv hr hb hinv'
    · subst h; exact edge_inv (by simpa [unwindOk] using hu) hb hinv'
  | ret => simp [srcTerm] at hj
  | resume => simp [srcTerm] at hj
  | abort => simp [srcTerm] at hj
  | unreachable => simp [srcTerm] at hj

theorem SRel.prepend (es : List Event) {t s : StepRes} (h : SRel t s) :
    SRel ⟨es ++ t.events, t.init, t.oracle, t.next⟩ ⟨es ++ s.events, s.init, s.oracle, s.next⟩ := by
  rcases h with h | ⟨hs, ht, e, he⟩
  · subst h; exact Or.inl rfl
  · exact Or.inr ⟨hs, ht, e, by simp [he, List.append_assoc]⟩

/-- One block: elaborated versus reference, and the invariant at the successor. -/
theorem sim_block (b : Body) (blk : Block) (fl : DropFlagEnv) (i : InitTree) (o : Oracle)
    (hok : blockOk b blk = true) (hinv : Inv b blk.facts fl i) :
    SRel (tgtBlock .checked (elabBlock b.flagged blk) fl i o).2 (srcBlock blk i o) ∧
    (∀ (tgt : Nat) (blk' : Block), (srcBlock blk i o).next = .jump tgt →
      b.blocks[tgt]? = some blk' →
      Inv b blk'.facts (tgtBlock .checked (elabBlock b.flagged blk) fl i o).1
        (srcBlock blk i o).init) := by
  unfold blockOk at hok
  rw [Bool.and_eq_true] at hok
  obtain ⟨h1, h2, h3⟩ := sim_stmts b blk.stmts blk.facts fl i hok.1 hinv
  constructor
  · show SRel
      ⟨(texecStmts (elabStmts b.flagged blk.stmts) fl i).1 ++
          (tgtTerm .checked (elabTerm (xferStmts blk.facts blk.stmts) blk.term)
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.1
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.2 o).events,
        (tgtTerm .checked (elabTerm (xferStmts blk.facts blk.stmts) blk.term)
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.1
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.2 o).init,
        (tgtTerm .checked (elabTerm (xferStmts blk.facts blk.stmts) blk.term)
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.1
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.2 o).oracle,
        (tgtTerm .checked (elabTerm (xferStmts blk.facts blk.stmts) blk.term)
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.1
            (texecStmts (elabStmts b.flagged blk.stmts) fl i).2.2 o).next⟩
      ⟨(execStmts blk.stmts i).1 ++ (srcTerm blk.term (execStmts blk.stmts i).2 o).events,
        (srcTerm blk.term (execStmts blk.stmts i).2 o).init,
        (srcTerm blk.term (execStmts blk.stmts i).2 o).oracle,
        (srcTerm blk.term (execStmts blk.stmts i).2 o).next⟩
    rw [h1, h2]
    exact SRel.prepend _ (sim_term b _ blk.term _ _ o hok.2 h3)
  · intro tgt blk' hj hb
    exact inv_next b _ blk.term _ _ o hok.2 h3 tgt blk' hj hb

/-- An elaborated run `t` against the reference run `s`: identical, or both abort and the
elaborated run ran additional destructors after the fatal panic. -/
def RRel (t s : Result) : Prop :=
  t = s ∨ (s.outcome = .aborted ∧ t.outcome = .aborted ∧ ∃ extra, t.trace = s.trace ++ extra)

theorem RRel.ofStep (tS sS : StepRes) (kT kS : Nat → Result) (h : SRel tS sS)
    (hk : tS = sS → ∀ t, sS.next = .jump t → RRel (kT t) (kS t)) :
    RRel (Result.ofStep tS kT) (Result.ofStep sS kS) := by
  rcases h with h | ⟨hs, ht, e, he⟩
  · subst h
    unfold Result.ofStep
    cases hn : tS.next with
    | jump t =>
      rcases hk rfl t hn with hr | ⟨h1, h2, e, he⟩
      · simp only [hr]; exact Or.inl rfl
      · exact Or.inr ⟨h1, h2, e, by simp [he, List.append_assoc]⟩
    | exit oc => exact Or.inl rfl
  · unfold Result.ofStep
    rw [hs, ht]
    exact Or.inr ⟨rfl, rfl, e, he⟩

theorem check_block (b : Body) (hc : check b = true) (pc : Nat) (blk : Block)
    (hb : b.blocks[pc]? = some blk) : blockOk b blk = true := by
  unfold check at hc
  rw [Bool.and_eq_true] at hc
  exact List.all_eq_true.mp hc.1 blk (List.mem_of_getElem? hb)

/-- The simulation: from any block, in states related by the invariant. -/
theorem sim_run (b : Body) (hc : check b = true) :
    ∀ (n pc : Nat) (fl : DropFlagEnv) (i : InitTree) (o : Oracle),
      (∀ blk, b.blocks[pc]? = some blk → Inv b blk.facts fl i) →
      RRel (runTgt .checked (elaborate b) n pc fl i o) (runSrc b n pc i o) := by
  intro n
  induction n with
  | zero => intro pc fl i o _; exact Or.inl rfl
  | succ n ih =>
    intro pc fl i o hinv
    have hlook : (elaborate b).blocks[pc]? = (b.blocks[pc]?).map (elabBlock b.flagged) := by
      simp [elaborate]
    rw [runTgt, runSrc, hlook]
    cases hb : b.blocks[pc]? with
    | none => exact Or.inl rfl
    | some blk =>
      obtain ⟨hs, hnext⟩ := sim_block b blk fl i o (check_block b hc pc blk hb) (hinv blk hb)
      show RRel (Result.ofStep (tgtBlock .checked (elabBlock b.flagged blk) fl i o).2 _)
        (Result.ofStep (srcBlock blk i o) _)
      apply RRel.ofStep _ _ _ _ hs
      intro heq t hj
      rw [heq]
      exact ih t _ _ _ (fun blk' hb' => hnext t blk' hj hb')

theorem inv_entry (b : Body) (hc : check b = true) :
    ∀ blk, b.blocks[0]? = some blk →
      Inv b blk.facts (fun _ => false) (InitTree.ofPlace b.frame) := by
  intro blk hb
  have he : entryOk b = true := by
    unfold check at hc; rw [Bool.and_eq_true] at hc; exact hc.2
  unfold entryOk at he
  rw [hb] at he
  have hdi : blk.facts.di = [] := by simpa using he
  refine ⟨InitTree.ids_ofPlace _, ?_, ?_, ?_⟩
  · intro l hl; rw [hdi] at hl; cases hl
  · intro l hl; rw [InitTree.get_ofPlace] at hl; cases hl
  · intro l _ _; rw [InitTree.get_ofPlace]

/-- **Refinement.** For a body whose certificate checks, the elaborated body has the same
outcome as the reference semantics for every fuel bound and every oracle, and the same trace of
initializations, moves, destructor runs and panics; the one exception is an aborting run, where
the elaborated trace extends the reference trace. -/
theorem elaborate_refines (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    RRel (runElab .checked b fuel o) (runRef b fuel o) :=
  sim_run b hc fuel 0 _ _ o (inv_entry b hc)

theorem elaborate_outcome (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    (runElab .checked b fuel o).outcome = (runRef b fuel o).outcome := by
  rcases elaborate_refines b hc fuel o with h | ⟨h1, h2, _⟩
  · rw [h]
  · rw [h1, h2]

theorem elaborate_exact_unless_aborted (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle)
    (h : (runRef b fuel o).outcome ≠ .aborted) :
    runElab .checked b fuel o = runRef b fuel o := by
  rcases elaborate_refines b hc fuel o with h' | ⟨h1, _, _⟩
  · exact h'
  · exact absurd h1 h

theorem elaborate_trace_extends (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    ∃ extra, (runElab .checked b fuel o).trace = (runRef b fuel o).trace ++ extra := by
  rcases elaborate_refines b hc fuel o with h | ⟨_, _, e, he⟩
  · exact ⟨[], by rw [h, List.append_nil]⟩
  · exact ⟨e, he⟩

/-- The reference semantics never reports a double drop. -/
theorem srcTerm_no_doubleDrop (t : Term) (i : InitTree) (o : Oracle) (mp : MovePath) :
    (srcTerm t i o).next ≠ .exit (.doubleDrop mp) := by
  cases t with
  | goto t => simp [srcTerm]
  | branch a c => simp [srcTerm]
  | call r u =>
    simp only [srcTerm]
    cases o.next.1 <;> cases u <;> simp [kontOf, kontNext]
  | drop p r u =>
    show (srcDrop p r u i o).next ≠ _
    unfold srcDrop
    cases hx : (glue .conditional p.leaves u.isTerminate i o).exit with
    | ok => simp
    | panicked =>
      simp only
      cases u.isTerminate <;> cases u <;> simp [kontOf, kontNext]
    | aborted => simp
    | doubleDrop mp' => exact absurd hx (glue_conditional_no_doubleDrop _ _ _ _ mp')
  | ret => simp [srcTerm]
  | resume => simp [srcTerm]
  | abort => simp [srcTerm]
  | unreachable => simp [srcTerm]

theorem runSrc_no_doubleDrop (b : Body) :
    ∀ (n pc : Nat) (i : InitTree) (o : Oracle) (mp : MovePath),
      (runSrc b n pc i o).outcome ≠ .doubleDrop mp := by
  intro n
  induction n with
  | zero => intro pc i o mp; simp [runSrc]
  | succ n ih =>
    intro pc i o mp
    rw [runSrc]
    cases hb : b.blocks[pc]? with
    | none => simp
    | some blk =>
      show (Result.ofStep (srcBlock blk i o) _).outcome ≠ _
      unfold Result.ofStep
      cases hn : (srcBlock blk i o).next with
      | jump t => exact ih t _ _ mp
      | exit oc =>
        intro h
        have h' : oc = .doubleDrop mp := h
        subst h'
        exact srcTerm_no_doubleDrop blk.term _ o mp hn

/-- No unconditional drop of the elaborated body ever runs on an uninitialized leaf. -/
def NoDoubleDrop (r : Result) : Prop := ∀ mp, r.outcome ≠ .doubleDrop mp

/-- Every leaf is uninitialized when the frame is left by `return` or by unwinding. -/
def NoLeak (r : Result) : Prop :=
  ∀ live, (r.outcome = .returned live ∨ r.outcome = .unwound live) → live = []

/-- **NoDoubleDrop.** On normal, unwinding and aborting paths alike. -/
theorem elaborate_no_double_drop (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    NoDoubleDrop (runElab .checked b fuel o) := by
  intro mp
  rw [elaborate_outcome b hc fuel o]
  exact runSrc_no_doubleDrop b fuel 0 _ o mp

/-- **NoLeak.** The elaborated body leaves a leaf initialized at exit only if the reference does. -/
theorem elaborate_no_leak (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle)
    (h : NoLeak (runRef b fuel o)) : NoLeak (runElab .checked b fuel o) := by
  intro live hl
  rw [elaborate_outcome b hc fuel o] at hl
  exact h live hl

/-! ### The unchecked machine

`.checked` mode consults the ghost `InitTree` to report a drop of an uninitialized leaf. A real
machine does not. Where the checked run reports nothing, the two coincide, so every statement
above also holds for the unchecked (`.blind`) execution of the elaborated body. -/

theorem Ladder.eval_blind_eq_checked (fl : DropFlagEnv) (l : Ladder) :
    ∀ (i : InitTree) (o : Oracle), (∀ mp, (l.eval .checked fl i o).exit ≠ .doubleDrop mp) →
      l.eval .blind fl i o = l.eval .checked fl i o := by
  induction l with
  | exit k => intro i o _; rw [Ladder.eval_exit, Ladder.eval_exit]
  | test flag s u ihs ihu =>
    intro i o h
    rw [Ladder.eval_test] at h ⊢
    rw [Ladder.eval_test]
    cases hf : fl flag with
    | true => rw [hf] at h; simp only [ite_true] at h ⊢; exact ihs i o h
    | false =>
      rw [hf] at h; simp only [Bool.false_eq_true, ite_false] at h ⊢; exact ihu i o h
  | drop p ret unw ihr ihu =>
    intro i o h
    rw [Ladder.eval_drop] at h ⊢
    rw [Ladder.eval_drop]
    have hg : ∀ mp, (glue .checked p.leaves false i o).exit ≠ .doubleDrop mp := by
      intro mp hx
      apply h mp
      generalize glue .checked p.leaves false i o = g at hx
      cases g with
      | mk ev i' o' ex => simp at hx; subst hx; rfl
    rw [glue_blind_eq_checked p.leaves false i o hg]
    generalize glue .checked p.leaves false i o = g at h
    cases g with
    | mk ev i' o' ex =>
      cases ex with
      | ok =>
        show (ret.eval .blind fl i' o').prepend ev = (ret.eval .checked fl i' o').prepend ev
        rw [ihr i' o' (fun mp hx => h mp hx)]
      | panicked =>
        show (unw.eval .blind fl i' o').prepend ev = (unw.eval .checked fl i' o').prepend ev
        rw [ihu i' o' (fun mp hx => h mp hx)]
      | aborted => rfl
      | doubleDrop mp => rfl

theorem tgtBlock_blind_eq_checked (blk : TBlock) (fl : DropFlagEnv) (i : InitTree) (o : Oracle)
    (h : ∀ mp, (tgtBlock .checked blk fl i o).2.next ≠ .exit (.doubleDrop mp)) :
    tgtBlock .blind blk fl i o = tgtBlock .checked blk fl i o := by
  have ht : tgtTerm .blind blk.term (texecStmts blk.stmts fl i).2.1 (texecStmts blk.stmts fl i).2.2 o =
      tgtTerm .checked blk.term (texecStmts blk.stmts fl i).2.1 (texecStmts blk.stmts fl i).2.2 o := by
    have h' : ∀ mp, (tgtTerm .checked blk.term (texecStmts blk.stmts fl i).2.1
        (texecStmts blk.stmts fl i).2.2 o).next ≠ .exit (.doubleDrop mp) := h
    cases hterm : blk.term with
    | ladder l =>
      rw [hterm] at h'
      simp only [tgtTerm] at h' ⊢
      rw [Ladder.eval_blind_eq_checked]
      intro mp hx
      apply h' mp
      unfold stepOfLadder
      rw [hx]
    | goto t => rfl
    | branch a c => rfl
    | call r u => rfl
    | ret => rfl
    | resume => rfl
    | abort => rfl
    | unreachable => rfl
  unfold tgtBlock
  rw [ht]

theorem runTgt_blind_eq_checked (b : TBody) :
    ∀ (n pc : Nat) (fl : DropFlagEnv) (i : InitTree) (o : Oracle),
      (∀ mp, (runTgt .checked b n pc fl i o).outcome ≠ .doubleDrop mp) →
      runTgt .blind b n pc fl i o = runTgt .checked b n pc fl i o := by
  intro n
  induction n with
  | zero => intro pc fl i o _; rfl
  | succ n ih =>
    intro pc fl i o h
    rw [runTgt] at h ⊢
    rw [runTgt]
    cases hb : b.blocks[pc]? with
    | none => rfl
    | some blk =>
      rw [hb] at h
      have h' : ∀ mp, (Result.ofStep (tgtBlock .checked blk fl i o).2
          (fun t => runTgt .checked b n t (tgtBlock .checked blk fl i o).1
            (tgtBlock .checked blk fl i o).2.init (tgtBlock .checked blk fl i o).2.oracle)).outcome ≠
          .doubleDrop mp := h
      have hblk : tgtBlock .blind blk fl i o = tgtBlock .checked blk fl i o := by
        apply tgtBlock_blind_eq_checked
        intro mp hx
        apply h' mp
        unfold Result.ofStep
        rw [hx]
      show Result.ofStep (tgtBlock .blind blk fl i o).2 _ = Result.ofStep (tgtBlock .checked blk fl i o).2 _
      rw [hblk]
      unfold Result.ofStep at h' ⊢
      cases hn : (tgtBlock .checked blk fl i o).2.next with
      | jump t =>
        rw [hn] at h'
        simp only
        rw [ih t _ _ _ (fun mp hx => h' mp hx)]
      | exit oc => rfl

/-- **Refinement for the unchecked machine.** -/
theorem elaborate_refines_blind (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    RRel (runElab .blind b fuel o) (runRef b fuel o) := by
  have h := elaborate_no_double_drop b hc fuel o
  unfold runElab at h ⊢
  rw [runTgt_blind_eq_checked _ fuel 0 _ _ o h]
  exact elaborate_refines b hc fuel o

/-! ### The double-panic law

For bodies that respect the cleanup discipline of the MIR validator, the reference semantics
satisfies: a run that returns saw no panic, and a run that unwinds out of the frame saw exactly
one. A second panic therefore never ends in `return` or in continued unwinding. -/

noncomputable def panicCount : List Event → Nat
  | [] => 0
  | .panic :: tr => panicCount tr + 1
  | .init _ :: tr => panicCount tr
  | .moved _ :: tr => panicCount tr
  | .drop _ :: tr => panicCount tr

theorem panicCount_append (a b : List Event) :
    panicCount (a ++ b) = panicCount a + panicCount b := by
  induction a with
  | nil => simp [panicCount]
  | cons e tr ih =>
    cases e with
    | panic => simp [panicCount, ih, Nat.add_right_comm]
    | init mp => simp [panicCount, ih]
    | moved mp => simp [panicCount, ih]
    | drop mp => simp [panicCount, ih]

theorem panicCount_map_init (l : List MovePath) : panicCount (l.map Event.init) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [panicCount, ih]

theorem panicCount_map_moved (l : List MovePath) : panicCount (l.map Event.moved) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [panicCount, ih]

theorem panicCount_stmts (ss : List Stmt) : ∀ (i : InitTree), panicCount (execStmts ss i).1 = 0 := by
  induction ss with
  | nil => intro i; rfl
  | cons s ss ih =>
    intro i
    have hs : panicCount (execStmt s i).1 = 0 := by
      cases s with
      | init p => exact panicCount_map_init _
      | move p => exact panicCount_map_moved _
      | nop => rfl
    show panicCount ((execStmt s i).1 ++ (execStmts ss (execStmt s i).2).1) = 0
    rw [panicCount_append, hs, ih]

/-- Panics inside conditional drop glue: none if it completes normally, and exactly one if it
completes unwinding after having been entered normally. -/
theorem glue_panicCount (ls : List MovePath) :
    ∀ (unw : Bool) (i : InitTree) (o : Oracle),
      ((glue .conditional ls unw i o).exit = .ok →
        panicCount (glue .conditional ls unw i o).events = 0) ∧
      ((glue .conditional ls unw i o).exit = .panicked →
        panicCount (glue .conditional ls unw i o).events = if unw then 0 else 1) := by
  induction ls with
  | nil => intro unw i o; cases unw <;> simp [glue, panicCount]
  | cons l ls ih =>
    intro unw i o
    by_cases hg : i.get l = true
    · rw [glue_cons_init .conditional l ls unw i o hg]
      unfold glueStep
      cases o.next.1 with
      | true =>
        cases unw with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ite_false, ite_true]
          constructor
          · intro h
            exact absurd h (glue_conditional_unwinding_not_ok ls _ _)
          · intro h
            have := (ih true (i.setAll [l] false) o.next.2).2 h
            simp only [ite_true] at this
            show panicCount (Event.drop l :: Event.panic ::
              (glue .conditional ls true (i.setAll [l] false) o.next.2).events) = 1
            simp [panicCount, this]
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have := ih unw (i.setAll [l] false) o.next.2
        constructor
        · intro h
          show panicCount (Event.drop l ::
            (glue .conditional ls unw (i.setAll [l] false) o.next.2).events) = 0
          simp [panicCount, this.1 h]
        · intro h
          show panicCount (Event.drop l ::
            (glue .conditional ls unw (i.setAll [l] false) o.next.2).events) = _
          simp [panicCount, this.2 h]
    · have hg' : i.get l = false := by simpa using hg
      rw [glue_cons_uninit_conditional l ls unw i o hg']
      exact ih unw i o

/-- Block `t` exists and has cleanup marker `c`, or does not exist. -/
noncomputable def isCleanupAt (b : Body) (t : Nat) (c : Bool) : Bool :=
  match b.blocks[t]? with
  | some blk => blk.cleanup == c
  | none => true

/-- Unwind actions permitted in a block with cleanup marker `c` (`check_unwind_edge` of the MIR
validator): `Continue` and `Cleanup` only outside cleanup blocks, `Terminate(InCleanup)` only
inside, and a `Cleanup` edge must lead to a cleanup block. -/
noncomputable def unwindDiscipline (b : Body) (c : Bool) : UnwindAction → Bool
  | .continue_ => !c
  | .cleanup t => !c && isCleanupAt b t true
  | .terminate => c
  | .unreachable => true

/-- Terminators permitted in a block with cleanup marker `c`: ordinary edges stay on the same
side, `return` only outside cleanup blocks, `resume` only inside. -/
noncomputable def termDiscipline (b : Body) (c : Bool) : Term → Bool
  | .goto t => isCleanupAt b t c
  | .branch t e => isCleanupAt b t c && isCleanupAt b e c
  | .call r u => isCleanupAt b r c && unwindDiscipline b c u
  | .drop _ r u => isCleanupAt b r c && unwindDiscipline b c u
  | .ret => !c
  | .resume => c
  | .abort => true
  | .unreachable => true

/-- The whole body respects the cleanup discipline and its entry block is not a cleanup block. -/
noncomputable def cleanupDiscipline (b : Body) : Bool :=
  b.blocks.all (fun blk => termDiscipline b blk.cleanup blk.term) && isCleanupAt b 0 false

/-- What one block step can do to the number of panics in flight. -/
structure StepClass (b : Body) (c : Bool) (s : StepRes) : Prop where
  jump : ∀ t, s.next = .jump t →
    (panicCount s.events = 0 ∧ isCleanupAt b t c = true) ∨
    (c = false ∧ panicCount s.events = 1 ∧ isCleanupAt b t true = true)
  returned : ∀ live, s.next = .exit (.returned live) → c = false ∧ panicCount s.events = 0
  unwound : ∀ live, s.next = .exit (.unwound live) → panicCount s.events = if c then 0 else 1

theorem stepClass_drop (b : Body) (c : Bool) (p : PlaceTree) (r : Nat) (u : UnwindAction)
    (i : InitTree) (o : Oracle) (hr : isCleanupAt b r c = true)
    (hu : unwindDiscipline b c u = true) : StepClass b c (srcDrop p r u i o) := by
  have hg := glue_panicCount p.leaves u.isTerminate i o
  unfold srcDrop
  generalize glue .conditional p.leaves u.isTerminate i o = g at hg ⊢
  cases g with
  | mk ev i' o' ex =>
    cases ex with
    | ok =>
      have h0 : panicCount ev = 0 := hg.1 rfl
      exact ⟨fun t hj => by simp at hj; subst hj; exact Or.inl ⟨h0, hr⟩,
        fun live hj => by simp at hj, fun live hj => by simp at hj⟩
    | panicked =>
      have h1 := hg.2 rfl
      cases u with
      | terminate =>
        simp only [UnwindAction.isTerminate, ite_true] at h1 ⊢
        exact ⟨fun t hj => by simp at hj; subst hj; exact Or.inl ⟨h1, hr⟩,
          fun live hj => by simp at hj, fun live hj => by simp at hj⟩
      | cleanup t' =>
        simp only [unwindDiscipline, Bool.and_eq_true] at hu
        have hc : c = false := by simpa using hu.1
        subst hc
        simp only [UnwindAction.isTerminate, Bool.false_eq_true, ite_false] at h1 ⊢
        exact ⟨fun t hj => by
            simp [kontOf, kontNext] at hj; subst hj; exact Or.inr ⟨rfl, h1, hu.2⟩,
          fun live hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj⟩
      | continue_ =>
        have hc : c = false := by simpa [unwindDiscipline] using hu
        subst hc
        simp only [UnwindAction.isTerminate, Bool.false_eq_true, ite_false] at h1 ⊢
        exact ⟨fun t hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simpa using h1⟩
      | unreachable =>
        simp only [UnwindAction.isTerminate, Bool.false_eq_true, ite_false]
        exact ⟨fun t hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj⟩
    | aborted =>
      exact ⟨fun t hj => by simp at hj, fun live hj => by simp at hj, fun live hj => by simp at hj⟩
    | doubleDrop mp =>
      exact ⟨fun t hj => by simp at hj, fun live hj => by simp at hj, fun live hj => by simp at hj⟩

theorem stepClass_term (b : Body) (c : Bool) (t : Term) (i : InitTree) (o : Oracle)
    (hd : termDiscipline b c t = true) : StepClass b c (srcTerm t i o) := by
  cases t with
  | goto t' =>
    have h : isCleanupAt b t' c = true := by simpa [termDiscipline] using hd
    exact ⟨fun t hj => by simp [srcTerm] at hj; subst hj; exact Or.inl ⟨rfl, h⟩,
      fun live hj => by simp [srcTerm] at hj, fun live hj => by simp [srcTerm] at hj⟩
  | branch a e =>
    simp only [termDiscipline, Bool.and_eq_true] at hd
    refine ⟨?_, fun live hj => by simp [srcTerm] at hj, fun live hj => by simp [srcTerm] at hj⟩
    intro t hj
    have hj' : Next.jump (if o.next.1 then a else e) = .jump t := hj
    injection hj' with h
    subst h
    refine Or.inl ⟨rfl, ?_⟩
    cases o.next.1 with
    | true => exact hd.1
    | false => exact hd.2
  | call r u =>
    simp only [termDiscipline, Bool.and_eq_true] at hd
    obtain ⟨hr, hu⟩ := hd
    simp only [srcTerm]
    cases o.next.1 with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨fun t hj => by simp at hj; subst hj; exact Or.inl ⟨rfl, hr⟩,
        fun live hj => by simp at hj, fun live hj => by simp at hj⟩
    | true =>
      simp only [ite_true]
      cases u with
      | continue_ =>
        have hc : c = false := by simpa [unwindDiscipline] using hu
        subst hc
        exact ⟨fun t hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [panicCount]⟩
      | cleanup t' =>
        simp only [unwindDiscipline, Bool.and_eq_true] at hu
        have hc : c = false := by simpa using hu.1
        subst hc
        exact ⟨fun t hj => by
            simp [kontOf, kontNext] at hj; subst hj
            exact Or.inr ⟨rfl, by simp [panicCount], hu.2⟩,
          fun live hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj⟩
      | terminate =>
        exact ⟨fun t hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj⟩
      | unreachable =>
        exact ⟨fun t hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj,
          fun live hj => by simp [kontOf, kontNext] at hj⟩
  | drop p r u =>
    simp only [termDiscipline, Bool.and_eq_true] at hd
    exact stepClass_drop b c p r u i o hd.1 hd.2
  | ret =>
    have hc : c = false := by simpa [termDiscipline] using hd
    subst hc
    exact ⟨fun t hj => by simp [srcTerm] at hj, fun live hj => ⟨rfl, rfl⟩,
      fun live hj => by simp [srcTerm] at hj⟩
  | resume =>
    have hc : c = true := by simpa [termDiscipline] using hd
    subst hc
    exact ⟨fun t hj => by simp [srcTerm] at hj, fun live hj => by simp [srcTerm] at hj,
      fun live hj => rfl⟩
  | abort =>
    exact ⟨fun t hj => by simp [srcTerm] at hj, fun live hj => by simp [srcTerm] at hj,
      fun live hj => by simp [srcTerm] at hj⟩
  | unreachable =>
    exact ⟨fun t hj => by simp [srcTerm] at hj, fun live hj => by simp [srcTerm] at hj,
      fun live hj => by simp [srcTerm] at hj⟩

theorem stepClass_block (b : Body) (blk : Block) (i : InitTree) (o : Oracle)
    (hd : termDiscipline b blk.cleanup blk.term = true) :
    StepClass b blk.cleanup (srcBlock blk i o) := by
  have ht := stepClass_term b blk.cleanup blk.term (execStmts blk.stmts i).2 o hd
  have he : panicCount (srcBlock blk i o).events =
      panicCount (srcTerm blk.term (execStmts blk.stmts i).2 o).events := by
    show panicCount ((execStmts blk.stmts i).1 ++ _) = _
    rw [panicCount_append, panicCount_stmts, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · intro t hj; rw [he]; exact ht.jump t hj
  · intro live hj; rw [he]; exact ht.returned live hj
  · intro live hj; rw [he]; exact ht.unwound live hj

theorem law_run (b : Body)
    (hd : ∀ blk, blk ∈ b.blocks → termDiscipline b blk.cleanup blk.term = true) :
    ∀ (n pc : Nat) (i : InitTree) (o : Oracle) (c : Bool), isCleanupAt b pc c = true →
      (∀ live, (runSrc b n pc i o).outcome = .returned live →
        c = false ∧ panicCount (runSrc b n pc i o).trace = 0) ∧
      (∀ live, (runSrc b n pc i o).outcome = .unwound live →
        panicCount (runSrc b n pc i o).trace = if c then 0 else 1) := by
  intro n
  induction n with
  | zero =>
    intro pc i o c _
    exact ⟨fun live h => by simp [runSrc] at h, fun live h => by simp [runSrc] at h⟩
  | succ n ih =>
    intro pc i o c hc
    unfold isCleanupAt at hc
    cases hb : b.blocks[pc]? with
    | none =>
      rw [runSrc_succ_none b n pc i o hb]
      exact ⟨fun live h => by simp at h, fun live h => by simp at h⟩
    | some blk =>
      rw [hb] at hc
      have hcc : blk.cleanup = c := by simpa using hc
      have hs := stepClass_block b blk i o (hd blk (List.mem_of_getElem? hb))
      rw [hcc] at hs
      rw [runSrc_succ_some b n pc i o blk hb]
      cases hn : (srcBlock blk i o).next with
      | jump t =>
        rw [Result.ofStep_jump _ _ t hn]
        rcases hs.jump t hn with ⟨h0, ht⟩ | ⟨hcf, h1, ht⟩
        · have := ih t (srcBlock blk i o).init (srcBlock blk i o).oracle c ht
          constructor
          · intro live h
            obtain ⟨g1, g2⟩ := this.1 live h
            refine ⟨g1, ?_⟩
            show panicCount (_ ++ _) = 0
            rw [panicCount_append, h0, g2]
          · intro live h
            show panicCount (_ ++ _) = _
            rw [panicCount_append, h0, this.2 live h, Nat.zero_add]
        · subst hcf
          have := ih t (srcBlock blk i o).init (srcBlock blk i o).oracle true ht
          constructor
          · intro live h
            exact absurd (this.1 live h).1 (by simp)
          · intro live h
            have g : panicCount
                (runSrc b n t (srcBlock blk i o).init (srcBlock blk i o).oracle).trace = 0 :=
              this.2 live h
            show panicCount (_ ++ _) = _
            rw [panicCount_append, h1, g]
            rfl
      | exit oc =>
        rw [Result.ofStep_exit _ _ oc hn]
        constructor
        · intro live h
          have h' : oc = .returned live := h
          subst h'
          exact hs.returned live hn
        · intro live h
          have h' : oc = .unwound live := h
          subst h'
          exact hs.unwound live hn

/-- **Double-panic law.** Under the cleanup discipline, a run of the reference semantics that
returns contains no panic and a run that unwinds out of the frame contains exactly one. -/
theorem double_panic_aborts (b : Body) (hd : cleanupDiscipline b = true) (fuel : Nat) (o : Oracle) :
    (∀ live, (runRef b fuel o).outcome = .returned live →
      panicCount (runRef b fuel o).trace = 0) ∧
    (∀ live, (runRef b fuel o).outcome = .unwound live →
      panicCount (runRef b fuel o).trace = 1) := by
  unfold cleanupDiscipline at hd
  rw [Bool.and_eq_true] at hd
  have hall : ∀ blk, blk ∈ b.blocks → termDiscipline b blk.cleanup blk.term = true :=
    fun blk hblk => List.all_eq_true.mp hd.1 blk hblk
  have h := law_run b hall fuel 0 (InitTree.ofPlace b.frame) o false hd.2
  unfold runRef
  exact ⟨fun live hl => (h.1 live hl).2, fun live hl => h.2 live hl⟩

/-- The law carries over to the elaborated body, checked or unchecked. -/
theorem double_panic_aborts_elaborated (m : GlueMode) (hm : m = .checked ∨ m = .blind) (b : Body)
    (hc : check b = true) (hd : cleanupDiscipline b = true) (fuel : Nat) (o : Oracle) :
    (∀ live, (runElab m b fuel o).outcome = .returned live →
      panicCount (runElab m b fuel o).trace = 0) ∧
    (∀ live, (runElab m b fuel o).outcome = .unwound live →
      panicCount (runElab m b fuel o).trace = 1) := by
  have hchk : runElab .blind b fuel o = runElab .checked b fuel o := by
    have h := elaborate_no_double_drop b hc fuel o
    unfold runElab at h ⊢
    exact runTgt_blind_eq_checked _ fuel 0 _ _ o h
  have hm' : runElab m b fuel o = runElab .checked b fuel o := by
    rcases hm with h | h
    · rw [h]
    · rw [h, hchk]
  rw [hm']
  have hlaw := double_panic_aborts b hd fuel o
  have hout := elaborate_outcome b hc fuel o
  constructor
  · intro live hl
    have hl' : (runRef b fuel o).outcome = .returned live := by rw [← hout]; exact hl
    rw [elaborate_exact_unless_aborted b hc fuel o (by rw [hl']; simp)]
    exact hlaw.1 live hl'
  · intro live hl
    have hl' : (runRef b fuel o).outcome = .unwound live := by rw [← hout]; exact hl
    rw [elaborate_exact_unless_aborted b hc fuel o (by rw [hl']; simp)]
    exact hlaw.2 live hl'

/-! ## 9. Concrete bodies: non-vacuity and counterexamples -/

/-- Number of initializations of leaf `mp` in a trace. -/
noncomputable def initCount (mp : MovePath) (tr : List Event) : Nat :=
  (tr.filter (fun e => e == Event.init mp)).length

/-- Number of destructor runs on leaf `mp` in a trace. -/
noncomputable def dropCount (mp : MovePath) (tr : List Event) : Nat :=
  (tr.filter (fun e => e == Event.drop mp)).length

/-- Number of times ownership of leaf `mp`'s value was given up in a trace: destroyed in place, or
moved out of the frame to an owner that destroys it. Exactly-once destruction means that this
equals `initCount`. -/
noncomputable def dischargeCount (mp : MovePath) (tr : List Event) : Nat :=
  (tr.filter (fun e => e == Event.drop mp || e == Event.moved mp)).length

/-- Run a hand-written lowered body from function entry over the frame `frame`. -/
noncomputable def runLowered (m : GlueMode) (frame : PlaceTree) (t : TBody) (fuel : Nat)
    (o : Oracle) : Result :=
  runTgt m t fuel 0 (fun _ => false) (InitTree.ofPlace frame) o

/-! ### A lowering that reads no flag cannot tell whether a value was moved -/

/-- The ladder contains no flag test. -/
noncomputable def Ladder.flagFree : Ladder → Bool
  | .exit _ => true
  | .test _ _ _ => false
  | .drop _ ret unw => ret.flagFree && unw.flagFree

/-- An unchecked drop does the same thing whatever the ownership state is. -/
theorem glue_blind_state_independent (ls : List MovePath) :
    ∀ (unw : Bool) (i i' : InitTree) (o : Oracle),
      (glue .blind ls unw i o).events = (glue .blind ls unw i' o).events ∧
      (glue .blind ls unw i o).oracle = (glue .blind ls unw i' o).oracle ∧
      (glue .blind ls unw i o).exit = (glue .blind ls unw i' o).exit := by
  induction ls with
  | nil => intro unw i i' o; simp [glue]
  | cons l ls ih =>
    intro unw i i' o
    have hstep : ∀ (j : InitTree), glue .blind (l :: ls) unw j o = glueStep .blind l ls unw j o := by
      intro j
      by_cases hg : j.get l = true
      · exact glue_cons_init .blind l ls unw j o hg
      · exact glue_cons_uninit_blind l ls unw j o (by simpa using hg)
    rw [hstep i, hstep i']
    unfold glueStep
    cases o.next.1 with
    | true =>
      cases unw with
      | true => simp
      | false =>
        have := ih true (i.setAll [l] false) (i'.setAll [l] false) o.next.2
        simp [GlueRes.prepend, this.1, this.2.1, this.2.2]
    | false =>
      have := ih unw (i.setAll [l] false) (i'.setAll [l] false) o.next.2
      simp [GlueRes.prepend, this.1, this.2.1, this.2.2]

/-- A flag-free ladder, executed by a machine, emits the same events and exits the same way
whatever the ownership state and whatever the drop flags are. -/
theorem flagFree_state_independent (l : Ladder) (hl : l.flagFree = true) :
    ∀ (fl fl' : DropFlagEnv) (i i' : InitTree) (o : Oracle),
      (l.eval .blind fl i o).events = (l.eval .blind fl' i' o).events ∧
      (l.eval .blind fl i o).oracle = (l.eval .blind fl' i' o).oracle ∧
      (l.eval .blind fl i o).exit = (l.eval .blind fl' i' o).exit := by
  induction l with
  | exit k => intro fl fl' i i' o; simp [Ladder.eval_exit]
  | test flag s u _ _ => simp [Ladder.flagFree] at hl
  | drop p ret unw ihr ihu =>
    simp only [Ladder.flagFree, Bool.and_eq_true] at hl
    intro fl fl' i i' o
    rw [Ladder.eval_drop, Ladder.eval_drop]
    obtain ⟨g1, g2, g3⟩ := glue_blind_state_independent p.leaves false i i' o
    generalize glue .blind p.leaves false i o = g at g1 g2 g3
    generalize glue .blind p.leaves false i' o = g' at g1 g2 g3
    cases g with
    | mk ev j o1 ex =>
      cases g' with
      | mk ev' j' o1' ex' =>
        simp at g1 g2 g3
        subst g1 g2 g3
        cases ex with
        | ok =>
          have := ihr hl.1 fl fl' j j' o1
          simp [GlueRes.toLadder, LadderRes.prepend, this.1, this.2.1, this.2.2]
        | panicked =>
          have := ihu hl.2 fl fl' j j' o1
          simp [GlueRes.toLadder, LadderRes.prepend, this.1, this.2.1, this.2.2]
        | aborted => simp [GlueRes.toLadder]
        | doubleDrop mp => simp [GlueRes.toLadder]

/-- **Sharpness of the drop flag (general form).** No flag-free ladder runs a destructor when the
value is still owned and none when it was moved out: the two situations are indistinguishable to
it. -/
theorem no_flagFree_ladder_is_conditional (l : Ladder) (hl : l.flagFree = true)
    (fl fl' : DropFlagEnv) (owned moved : InitTree) (o : Oracle) (mp : MovePath) :
    ¬ ((l.eval .blind fl owned o).events = [.drop mp] ∧ (l.eval .blind fl' moved o).events = []) := by
  intro h
  have := (flagFree_state_independent l hl fl fl' owned moved o).1
  rw [h.1, h.2] at this
  cases this

namespace Example

/-! ### Conditional move: `let x = ..; if c { consume(x) }`, then the scope-end drop of `x` -/

/-- Block 2 is the join point: `x` (move path 0) may or may not be initialized there. -/
noncomputable def condMove : Body where
  frame := .leaf 0
  flagged := [0]
  blocks := [
    ⟨⟨[], [], []⟩, false, [.init (.leaf 0)], .branch 1 2⟩,
    ⟨⟨[0], [0], []⟩, false, [.move (.leaf 0)], .goto 2⟩,
    ⟨⟨[0], [], []⟩, false, [], .drop (.leaf 0) 3 .continue_⟩,
    ⟨⟨[], [], [0]⟩, false, [], .ret⟩]

theorem condMove_check : check condMove = true := by decide

theorem condMove_discipline : cleanupDiscipline condMove = true := by decide

/-- The join-point drop becomes a flag test in front of an unconditional drop. -/
theorem condMove_elaborated_join :
    ((elaborate condMove).blocks[2]?).map (fun b => b.term) =
      some (.ladder (.test 0 (.drop (.leaf 0) (.exit (.goto 3)) (.exit .resume)) (.exit (.goto 3)))) := by
  rfl

/-- The flag is written at the initialization and at the move, as in the real pass. -/
theorem condMove_elaborated_flag_writes :
    ((elaborate condMove).blocks.map (fun b => b.stmts)) =
      [[.setFlag 0 true, .init (.leaf 0)], [.setFlag 0 false, .move (.leaf 0)], [], []] := by
  rfl

theorem condMove_moved :
    runElab .blind condMove 10 [true] = ⟨[.init 0, .moved 0], .returned []⟩ := by decide

theorem condMove_kept :
    runElab .blind condMove 10 [false] = ⟨[.init 0, .drop 0], .returned []⟩ := by decide

/-- With the flag, the value is given up exactly once on both paths. -/
theorem condMove_exactly_once :
    dischargeCount 0 (runElab .blind condMove 10 [true]).trace = 1 ∧
    dischargeCount 0 (runElab .blind condMove 10 [false]).trace = 1 := by decide

/-- The join lowered without a flag, keeping the drop (as if it were `DropStyle::Static`). -/
noncomputable def condMoveAlwaysDrop : TBody :=
  ⟨[⟨[.init (.leaf 0)], .branch 1 2⟩,
    ⟨[.move (.leaf 0)], .goto 2⟩,
    ⟨[], .ladder (.drop (.leaf 0) (.exit (.goto 3)) (.exit .resume))⟩,
    ⟨[], .ret⟩]⟩

/-- The join lowered without a flag, deleting the drop (as if it were `DropStyle::Dead`). -/
noncomputable def condMoveNeverDrop : TBody :=
  ⟨[⟨[.init (.leaf 0)], .branch 1 2⟩,
    ⟨[.move (.leaf 0)], .goto 2⟩,
    ⟨[], .goto 3⟩,
    ⟨[], .ret⟩]⟩

/-- **CE1, first half.** Keeping the drop without a flag: on the path that moved `x` out, the
value is given up twice (moved to its consumer, then destroyed again at the join). The checked
semantics reports the second one as a double drop. -/
theorem ce1_no_flag_always_drop_double_drop :
    runLowered .blind (.leaf 0) condMoveAlwaysDrop 10 [true] =
      ⟨[.init 0, .moved 0, .drop 0], .returned []⟩ ∧
    initCount 0 (runLowered .blind (.leaf 0) condMoveAlwaysDrop 10 [true]).trace = 1 ∧
    dischargeCount 0 (runLowered .blind (.leaf 0) condMoveAlwaysDrop 10 [true]).trace = 2 ∧
    (runLowered .checked (.leaf 0) condMoveAlwaysDrop 10 [true]).outcome = .doubleDrop 0 := by
  decide

/-- **CE1, second half.** Deleting the drop without a flag: on the path that kept `x`, the value
is never given up and is still initialized at `return`. -/
theorem ce1_no_flag_never_drop_leak :
    runLowered .blind (.leaf 0) condMoveNeverDrop 10 [false] = ⟨[.init 0], .returned [0]⟩ ∧
    initCount 0 (runLowered .blind (.leaf 0) condMoveNeverDrop 10 [false]).trace = 1 ∧
    dischargeCount 0 (runLowered .blind (.leaf 0) condMoveNeverDrop 10 [false]).trace = 0 := by
  decide

/-- Neither flag-free lowering refines the reference semantics. -/
theorem ce1_neither_refines :
    ¬ RRel (runLowered .blind (.leaf 0) condMoveAlwaysDrop 10 [true]) (runRef condMove 10 [true]) ∧
    ¬ RRel (runLowered .blind (.leaf 0) condMoveNeverDrop 10 [false]) (runRef condMove 10 [false]) := by
  constructor
  · intro h
    rcases h with h | ⟨h, _, _⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · intro h
    rcases h with h | ⟨h, _, _⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-! ### Move out of one field: `let p = (a, b); if c { consume(p.0) }`

Move path 0 is `p.0`; move path 1 stands for the rest of `p` (here `p.1`). -/

noncomputable def condFieldMove : Body where
  frame := .node (.leaf 0) (.leaf 1)
  flagged := [0]
  blocks := [
    ⟨⟨[], [], []⟩, false, [.init (.node (.leaf 0) (.leaf 1))], .branch 1 2⟩,
    ⟨⟨[0, 1], [0, 1], []⟩, false, [.move (.leaf 0)], .goto 2⟩,
    ⟨⟨[0, 1], [1], []⟩, false, [], .drop (.node (.leaf 0) (.leaf 1)) 3 .continue_⟩,
    ⟨⟨[], [], [0, 1]⟩, false, [], .ret⟩]

theorem condFieldMove_check : check condFieldMove = true := by decide

/-- The open drop: test the flag of `p.0`, drop `p.0`, then drop `p.1` unconditionally; if the
destructor of `p.0` panics, `p.1` is dropped on the unwind path with "abort on panic". -/
theorem condFieldMove_ladder :
    ((elaborate condFieldMove).blocks[2]?).map (fun b => b.term) =
      some (.ladder
        (.test 0
          (.drop (.leaf 0)
            (.drop (.leaf 1) (.exit (.goto 3)) (.exit .resume))
            (.drop (.leaf 1) (.exit .resume) (.exit .abort)))
          (.drop (.leaf 1) (.exit (.goto 3)) (.exit .resume)))) := by
  rfl

/-- The unmoved sibling is dropped on its own. -/
theorem condFieldMove_moved :
    runElab .blind condFieldMove 10 [true] =
      ⟨[.init 0, .init 1, .moved 0, .drop 1], .returned []⟩ := by decide

/-- The destructor of `p.0` panics: `p.1` is still dropped, then unwinding leaves the frame. -/
theorem condFieldMove_first_dtor_panics :
    runElab .blind condFieldMove 10 [false, true] =
      ⟨[.init 0, .init 1, .drop 0, .panic, .drop 1], .unwound []⟩ := by decide

/-- Both destructors panic: abort. -/
theorem condFieldMove_both_dtors_panic :
    runElab .blind condFieldMove 10 [false, true, true] =
      ⟨[.init 0, .init 1, .drop 0, .panic, .drop 1, .panic], .aborted⟩ := by decide

/-! ### Assignment over an initialized place: `x = new_value`

Move path 0 is `x`, move path 1 is the temporary holding the new value. Blocks 4, 7 and 8 are
cleanup blocks. If the destructor of the old value panics (block 2), the assignment is still
completed on the unwind path (block 4) and the new value is dropped by the cleanup chain. -/

noncomputable def assignOverwrite : Body where
  frame := .node (.leaf 0) (.leaf 1)
  flagged := []
  blocks := [
    ⟨⟨[], [], []⟩, false, [], .call 1 .continue_⟩,
    ⟨⟨[], [], []⟩, false, [.init (.leaf 0)], .call 2 (.cleanup 7)⟩,
    ⟨⟨[0], [0], []⟩, false, [.init (.leaf 1)], .drop (.leaf 0) 3 (.cleanup 4)⟩,
    ⟨⟨[1], [1], [0]⟩, false, [.move (.leaf 1), .init (.leaf 0)], .call 5 (.cleanup 7)⟩,
    ⟨⟨[1], [1], [0]⟩, true, [.move (.leaf 1), .init (.leaf 0)], .goto 7⟩,
    ⟨⟨[0], [0], []⟩, false, [], .drop (.leaf 0) 6 .continue_⟩,
    ⟨⟨[], [], [0]⟩, false, [], .ret⟩,
    ⟨⟨[0], [0], []⟩, true, [], .drop (.leaf 0) 8 .terminate⟩,
    ⟨⟨[], [], [0]⟩, true, [], .resume⟩]

theorem assignOverwrite_check : check assignOverwrite = true := by decide

theorem assignOverwrite_discipline : cleanupDiscipline assignOverwrite = true := by decide

/-- No panic: the old value is dropped before the new one is written; the new one at scope end. -/
theorem assignOverwrite_normal :
    runElab .blind assignOverwrite 20 [] =
      ⟨[.init 0, .init 1, .drop 0, .moved 1, .init 0, .drop 0], .returned []⟩ := by decide

/-- The constructor of the new value panics (second call): the old value is dropped once. -/
theorem assignOverwrite_constructor_panics :
    runElab .blind assignOverwrite 20 [false, true] =
      ⟨[.init 0, .panic, .drop 0], .unwound []⟩ := by decide

/-- The destructor of the old value panics: the new value is still assigned, then dropped while
unwinding. Leaf 0 is initialized twice and destroyed twice. -/
theorem assignOverwrite_old_dtor_panics :
    runElab .blind assignOverwrite 20 [false, false, true] =
      ⟨[.init 0, .init 1, .drop 0, .panic, .moved 1, .init 0, .drop 0], .unwound []⟩ ∧
    initCount 0 (runElab .blind assignOverwrite 20 [false, false, true]).trace = 2 ∧
    dropCount 0 (runElab .blind assignOverwrite 20 [false, false, true]).trace = 2 := by decide

/-- The destructors of the old and of the new value both panic: abort. -/
theorem assignOverwrite_double_panic :
    runElab .blind assignOverwrite 20 [false, false, true, true] =
      ⟨[.init 0, .init 1, .drop 0, .panic, .moved 1, .init 0, .drop 0, .panic], .aborted⟩ := by
  decide

/-! ### A loop: `loop { let x = ..; if c { consume(x) }; <scope end>; if !again { break } }` -/

noncomputable def loopBody : Body where
  frame := .leaf 0
  flagged := [0]
  blocks := [
    ⟨⟨[], [], []⟩, false, [], .goto 1⟩,
    ⟨⟨[], [], []⟩, false, [.init (.leaf 0)], .branch 2 3⟩,
    ⟨⟨[0], [0], []⟩, false, [.move (.leaf 0)], .goto 3⟩,
    ⟨⟨[0], [], []⟩, false, [], .drop (.leaf 0) 4 .continue_⟩,
    ⟨⟨[], [], [0]⟩, false, [.move (.leaf 0)], .branch 1 5⟩,
    ⟨⟨[], [], []⟩, false, [], .ret⟩]

theorem loopBody_check : check loopBody = true := by decide

/-- First iteration moves `x` out, second iteration keeps it. -/
theorem loopBody_two_iterations :
    runElab .blind loopBody 20 [true, true, false, false] =
      ⟨[.init 0, .moved 0, .init 0, .drop 0], .returned []⟩ := by decide

/-! ### CE2: continuing to unwind after a nested panic

`let t = (a, b, c); if cond { consume(t.2) }` followed by the scope-end drop of `t`. Move paths 0,
1, 2 are the three fields. The drop of `t` is open. If the destructor of `t.0` panics, `t.1` and
`t.2` are dropped on the unwind path; if the destructor of `t.1` then panics too, the process must
abort. -/

noncomputable def threeFields : Body where
  frame := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))
  flagged := [2]
  blocks := [
    ⟨⟨[], [], []⟩, false, [.init (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))], .branch 1 2⟩,
    ⟨⟨[0, 1, 2], [0, 1, 2], []⟩, false, [.move (.leaf 2)], .goto 2⟩,
    ⟨⟨[0, 1, 2], [0, 1], []⟩, false, [],
      .drop (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) 3 .continue_⟩,
    ⟨⟨[], [], [0, 1, 2]⟩, false, [], .ret⟩]

theorem threeFields_check : check threeFields = true := by decide

/-- The same elaboration, except that a panic on the unwind half of a ladder continues to the
enclosing unwind target (`nested`) instead of aborting. -/
noncomputable def elabCleanupContinue (f : Facts) : PlaceTree → Ladder → Ladder → Ladder
  | .leaf l, k, nested =>
    if !f.mi.contains l then k
    else if f.di.contains l then .drop (.leaf l) k nested
    else .test l (.drop (.leaf l) k nested) k
  | .node a b, k, nested =>
    if (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) then k
    else if (a.leaves ++ b.leaves).all (fun l => f.di.contains l) then .drop (.node a b) k nested
    else elabCleanupContinue f a (elabCleanupContinue f b k nested) nested

noncomputable def elabDropContinue (f : Facts) : PlaceTree → Ladder → Ladder → Ladder
  | .leaf l, ret, unw =>
    if !f.mi.contains l then ret
    else if f.di.contains l then .drop (.leaf l) ret unw
    else .test l (.drop (.leaf l) ret unw) ret
  | .node a b, ret, unw =>
    if (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) then ret
    else if (a.leaves ++ b.leaves).all (fun l => f.di.contains l) then .drop (.node a b) ret unw
    else elabDropContinue f a (elabDropContinue f b ret unw) (elabCleanupContinue f b unw unw)

noncomputable def elabTermContinue (f : Facts) : Term → TTerm
  | .drop p r u =>
    if u.isTerminate then .ladder (elabCleanup f p (.exit (.goto r)))
    else .ladder (elabDropContinue f p (.exit (.goto r)) (.exit (kontOf u)))
  | t => elabTerm f t

noncomputable def elaborateContinue (b : Body) : TBody :=
  ⟨b.blocks.map (fun blk =>
    ⟨elabStmts b.flagged blk.stmts, elabTermContinue (xferStmts blk.facts blk.stmts) blk.term⟩)⟩

/-- Reference: `t.0` and `t.1` both panic, the run aborts, `t.2` is never dropped. -/
theorem ce2_reference_aborts :
    runRef threeFields 10 [false, true, true] =
      ⟨[.init 0, .init 1, .init 2, .drop 0, .panic, .drop 1, .panic], .aborted⟩ := by decide

/-- The real elaboration (abort on nested panic) agrees. -/
theorem ce2_terminate_lowering_aborts :
    runElab .blind threeFields 10 [false, true, true] = runRef threeFields 10 [false, true, true] := by
  decide

/-- **CE2.** With "continue" instead of "terminate" on the nested panic, the run does not abort: it
keeps unwinding into the caller after two panics, the remaining ladder step is skipped, and `t.2`
is still initialized when the frame is left (initialized once, destroyed zero times). -/
theorem ce2_continue_lowering_unwinds :
    runLowered .blind threeFields.frame (elaborateContinue threeFields) 10 [false, true, true] =
      ⟨[.init 0, .init 1, .init 2, .drop 0, .panic, .drop 1, .panic], .unwound [2]⟩ ∧
    panicCount (runLowered .blind threeFields.frame (elaborateContinue threeFields) 10
      [false, true, true]).trace = 2 ∧
    initCount 2 (runLowered .blind threeFields.frame (elaborateContinue threeFields) 10
      [false, true, true]).trace = 1 ∧
    dropCount 2 (runLowered .blind threeFields.frame (elaborateContinue threeFields) 10
      [false, true, true]).trace = 0 := by
  decide

/-- The "continue" variant is not a refinement, even for bodies whose certificate checks. -/
theorem ce2_continue_is_not_a_refinement :
    ¬ ∀ (b : Body) (fuel : Nat) (o : Oracle), check b = true →
        RRel (runLowered .blind b.frame (elaborateContinue b) fuel o) (runRef b fuel o) := by
  intro h
  rcases h threeFields 10 [false, true, true] threeFields_check with h | ⟨_, h, _⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- CE2 at the level of unwind actions: a cleanup-block drop labelled `continue_` instead of
`terminate`. Move path 0 is `a` (declared last, dropped first), move path 1 is `b`. Block 0
initializes both and calls a function that panics; blocks 3 to 5 are the cleanup chain. -/
noncomputable def cleanupChain (onNestedPanic : UnwindAction) : Body where
  frame := .node (.leaf 0) (.leaf 1)
  flagged := []
  blocks := [
    ⟨⟨[], [], []⟩, false, [.init (.leaf 1), .init (.leaf 0)], .call 1 (.cleanup 3)⟩,
    ⟨⟨[0, 1], [0, 1], []⟩, false, [], .drop (.leaf 0) 2 (.cleanup 4)⟩,
    ⟨⟨[1], [1], [0]⟩, false, [], .drop (.leaf 1) 6 .continue_⟩,
    ⟨⟨[0, 1], [0, 1], []⟩, true, [], .drop (.leaf 0) 4 onNestedPanic⟩,
    ⟨⟨[1], [1], [0]⟩, true, [], .drop (.leaf 1) 5 .terminate⟩,
    ⟨⟨[], [], [0, 1]⟩, true, [], .resume⟩,
    ⟨⟨[], [], [0, 1]⟩, false, [], .ret⟩]

theorem cleanupChain_terminate_ok :
    check (cleanupChain .terminate) = true ∧ cleanupDiscipline (cleanupChain .terminate) = true := by
  decide

/-- With `terminate`, the nested panic aborts; `b` is not dropped. -/
theorem cleanupChain_terminate_aborts :
    runRef (cleanupChain .terminate) 10 [true, true] =
      ⟨[.init 1, .init 0, .panic, .drop 0, .panic], .aborted⟩ := by decide

/-- With `continue_`, the discipline check fails, and the run leaves the frame unwinding after two
panics with `b` still initialized: the conclusion of `double_panic_aborts` is false for it. -/
theorem cleanupChain_continue_violates_law :
    cleanupDiscipline (cleanupChain .continue_) = false ∧
    runRef (cleanupChain .continue_) 10 [true, true] =
      ⟨[.init 1, .init 0, .panic, .drop 0, .panic], .unwound [1]⟩ ∧
    panicCount (runRef (cleanupChain .continue_) 10 [true, true]).trace = 2 := by
  decide

/-! ### CE3: a stale flag

`x` is dropped on one branch and dropped again at the join. The first drop is `Static` and, as in
the real pass, does not clear the flag; at the join the dataflow says "maybe initialized", the
flag is tested, and it is still set. -/

noncomputable def staleFlagJoin : Body where
  frame := .leaf 0
  flagged := [0]
  blocks := [
    ⟨⟨[], [], []⟩, false, [.init (.leaf 0)], .branch 1 2⟩,
    ⟨⟨[0], [0], []⟩, false, [], .drop (.leaf 0) 2 .continue_⟩,
    ⟨⟨[0], [], [0]⟩, false, [], .drop (.leaf 0) 3 .continue_⟩,
    ⟨⟨[], [], [0]⟩, false, [], .ret⟩]

/-- The certificate does not check: the flag read at the join may be stale. -/
theorem staleFlagJoin_rejected : check staleFlagJoin = false := by decide

/-- The reference semantics drops `x` once. -/
theorem staleFlagJoin_reference :
    runRef staleFlagJoin 10 [true] = ⟨[.init 0, .drop 0], .returned []⟩ := by decide

/-- **CE3.** The elaborated body runs the destructor twice. -/
theorem staleFlagJoin_double_drop :
    runElab .blind staleFlagJoin 10 [true] = ⟨[.init 0, .drop 0, .drop 0], .returned []⟩ ∧
    initCount 0 (runElab .blind staleFlagJoin 10 [true]).trace = 1 ∧
    dropCount 0 (runElab .blind staleFlagJoin 10 [true]).trace = 2 ∧
    (runElab .checked staleFlagJoin 10 [true]).outcome = .doubleDrop 0 := by decide

/-- The same body with a `StorageDead`-style move-out after the first drop: the flag is cleared,
the certificate checks, and `x` is dropped once. -/
noncomputable def staleFlagJoinStorageDead : Body where
  frame := .leaf 0
  flagged := [0]
  blocks := [
    ⟨⟨[], [], []⟩, false, [.init (.leaf 0)], .branch 1 2⟩,
    ⟨⟨[0], [0], []⟩, false, [], .drop (.leaf 0) 4 .continue_⟩,
    ⟨⟨[0], [], []⟩, false, [], .drop (.leaf 0) 3 .continue_⟩,
    ⟨⟨[], [], [0]⟩, false, [], .ret⟩,
    ⟨⟨[], [], [0]⟩, false, [.move (.leaf 0)], .goto 2⟩]

theorem staleFlagJoinStorageDead_ok :
    check staleFlagJoinStorageDead = true ∧
    runElab .blind staleFlagJoinStorageDead 10 [true] = ⟨[.init 0, .drop 0], .returned []⟩ := by
  decide

/-! ### The trace before an abort depends on the certificate

Two certificates for the same blocks. Both check. In block 2 (a cleanup block) the pair `p` is
dropped: the precise certificate knows both fields are initialized (`Static`: one call of the drop
glue of the pair), the imprecise one only knows it for `p.0` (`Open`: a ladder). When the
destructor of `p.0` panics during unwinding, the glue still drops `p.1` before the abort; the
ladder does not. -/

noncomputable def pairInCleanup (diAtCleanup : List MovePath) : Body where
  frame := .node (.leaf 0) (.leaf 1)
  flagged := [1]
  blocks := [
    ⟨⟨[], [], []⟩, false, [.init (.node (.leaf 0) (.leaf 1))], .call 1 (.cleanup 2)⟩,
    ⟨⟨[0, 1], [0, 1], []⟩, false, [], .drop (.node (.leaf 0) (.leaf 1)) 3 .continue_⟩,
    ⟨⟨[0, 1], diAtCleanup, []⟩, true, [], .drop (.node (.leaf 0) (.leaf 1)) 4 .terminate⟩,
    ⟨⟨[], [], [0, 1]⟩, false, [], .ret⟩,
    ⟨⟨[], [], [0, 1]⟩, true, [], .resume⟩]

theorem pairInCleanup_both_check :
    check (pairInCleanup [0, 1]) = true ∧ check (pairInCleanup [0]) = true := by decide

/-- The reference run is the same for both certificates and stops at the fatal panic. -/
theorem pairInCleanup_reference :
    runRef (pairInCleanup [0, 1]) 10 [true, true] =
      ⟨[.init 0, .init 1, .panic, .drop 0, .panic], .aborted⟩ ∧
    runRef (pairInCleanup [0]) 10 [true, true] =
      ⟨[.init 0, .init 1, .panic, .drop 0, .panic], .aborted⟩ := by decide

/-- `Static` under the precise certificate: `p.1` is dropped after the fatal panic. -/
theorem pairInCleanup_static_trace :
    runElab .blind (pairInCleanup [0, 1]) 10 [true, true] =
      ⟨[.init 0, .init 1, .panic, .drop 0, .panic, .drop 1], .aborted⟩ := by decide

/-- `Open` under the imprecise certificate: it is not. -/
theorem pairInCleanup_open_trace :
    runElab .blind (pairInCleanup [0]) 10 [true, true] =
      ⟨[.init 0, .init 1, .panic, .drop 0, .panic], .aborted⟩ := by decide

/-- Hence trace equality on aborting runs cannot be part of any correctness statement that covers
both lowerings: the "extends" clause of `elaborate_refines` is necessary. -/
theorem trace_before_abort_depends_on_certificate :
    (runElab .blind (pairInCleanup [0, 1]) 10 [true, true]).trace ≠
      (runElab .blind (pairInCleanup [0]) 10 [true, true]).trace := by decide

end Example

end DropElab
